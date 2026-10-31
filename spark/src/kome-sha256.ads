--  Kome.SHA256: SPARK mirror of src/sha256.h / src/sha256.cpp (FIPS 180-4
--  SHA-256, incremental Update/Finish plus the one-shot helper). The C++ is
--  the deterministic state digest primitive; this package is a full
--  reimplementation, not a binding (CONVENTIONS.md: SHA-256 is translated).
--
--  Observable semantics mirrored exactly: same digest for the same byte
--  stream, however it is chunked; Finish pads (0x80, zeros to 56 mod 64,
--  64-bit big-endian bit length) and leaves the object needing a Reset.
--
--  Counter discipline. The C++ holds `bitlen_` as a uint64 bit count and
--  bumps it with `bitlen_ += len * 8`, which wraps silently once more than
--  2**61 - 1 bytes have been fed. The mirror counts *bytes* (Byte_Count) and
--  refuses, by precondition, any Update that would carry the count past
--  Max_Message_Bytes, so the bit length written by Finish never wraps.
--
--  Functional model. The private part defines the C++ update loop as a
--  function: `Fill` is one iteration (copy `take` bytes into the buffer,
--  compress when it is full) and the ghost `Absorbed` is the loop itself,
--  recursive over the chunks the C++ takes. `Absorb`, the implementation,
--  has `Absorb'Result = Absorbed (Ctx, Data)` as its postcondition and
--  `Updated` is `Absorb`; the chunking law `Lemma_Update_Concat` is then a
--  proof by induction over `Absorbed` (see the body), not an assumption.
pragma Ada_2022;
package Kome.SHA256 with SPARK_Mode, Pure is

   Block_Len : constant := 64;   --  sha256.cpp: buf_[64]

   --  Largest message the bit counter can describe: 8 * N must fit in U64.
   --  (sha256.cpp: bitlen_ is uint64_t and is bumped by len * 8 unguarded.)
   --  DIVERGENCE CANDIDATE: Sha256::update does `bitlen_ += (uint64_t)len * 8`
   --  with no guard, so past 2**61 - 1 total bytes the C++ wraps the length
   --  it later pads with (a wrong digest, silently). The mirror refuses such
   --  an Update by precondition (Update/Updated below); the proof wants the
   --  C++ to guard or saturate the counter. Unreachable with real inputs.
   Max_Message_Bytes : constant U64 := 2**61 - 1;

   --  Longest single Update. Byte_Array is indexed by Natural, so a full-range
   --  array holds 2**31 elements, one more than Natural can count; excluding
   --  that one shape keeps every offset computation inside Natural.
   Max_Update_Len : constant := Natural'Last;

   type Context is private;

   --  True once Finish has run; the C++ comment says "the object must be
   --  reset to reuse", and the mirror makes that a precondition.
   --  DIVERGENCE CANDIDATE: the C++ does not enforce its own comment. A
   --  second update()/finish() on a finished Sha256 silently hashes the
   --  padding bytes as message (bitlen_ already counts them) and pads again.
   --  Every caller in src/ uses a fresh object, so nothing observable depends
   --  on it; the mirror refuses by precondition instead of reproducing it.
   --  (No Post: Byte_Count's Post names Is_Finished, so a Post here naming
   --  Byte_Count would recurse at run time; Lemma_Finished_Block_Aligned
   --  states what a finished context satisfies.)
   function Is_Finished (Ctx : Context) return Boolean
     with Global => null;

   --  Bytes absorbed so far. Before Finish this is the message length; after
   --  Finish it also counts the padding (the C++ bitlen_ does the same since
   --  finish() pads through update()).
   function Byte_Count (Ctx : Context) return U64
     with Global => null,
          Post => (if not Is_Finished (Ctx)
                   then Byte_Count'Result <= Max_Message_Bytes);

   --  Length of the padded stream Finish produces for an N-byte message:
   --  the unique multiple of 64 in N + 9 .. N + 72.
   function Padded_Length (N : U64) return U64 is
     (Block_Len * ((N + 8) / Block_Len + 1))
     with Global => null,
          Pre  => N <= Max_Message_Bytes;

   function Initial return Context
     with Global => null,
          Post   => not Is_Finished (Initial'Result)
                    and then Byte_Count (Initial'Result) = 0;

   --  Sha256::reset(): IV, zero counters.
   procedure Reset (Ctx : out Context)
     with Global => null,
          Post   => Ctx = Initial;

   --  Functional form of Update: the context after absorbing Data. Completed
   --  in the private part as `Absorb (Ctx, Data)`, whose postcondition is
   --  the functional model `Absorbed`.
   function Updated (Ctx : Context; Data : Byte_Array) return Context
     with Global => null,
          Pre    => not Is_Finished (Ctx)
                    and then Data'Length <= Max_Update_Len
                    and then U64 (Data'Length) <= Max_Message_Bytes - Byte_Count (Ctx),
          Post   => not Is_Finished (Updated'Result)
                    and then Byte_Count (Updated'Result) = Byte_Count (Ctx) + U64 (Data'Length)
                    and then (if Data'Length = 0 then Updated'Result = Ctx);

   --  Sha256::update(data, len).
   procedure Update (Ctx : in out Context; Data : Byte_Array)
     with Global => null,
          Pre    => not Is_Finished (Ctx)
                    and then Data'Length <= Max_Update_Len
                    and then U64 (Data'Length) <= Max_Message_Bytes - Byte_Count (Ctx),
          Post   => Ctx = Updated (Ctx'Old, Data)
                    and then not Is_Finished (Ctx)
                    and then Byte_Count (Ctx) = Byte_Count (Ctx'Old) + U64 (Data'Length);

   --  Functional form of Finish: the digest of the message absorbed so far.
   function Digest_Of (Ctx : Context) return Hash256
     with Global => null,
          Pre    => not Is_Finished (Ctx);

   --  Sha256::finish(out): pad, absorb the length, emit the state big-endian.
   procedure Finish (Ctx : in out Context; Digest : out Hash256)
     with Global => null,
          Pre    => not Is_Finished (Ctx),
          Post   => Is_Finished (Ctx)
                    and then Byte_Count (Ctx) = Padded_Length (Byte_Count (Ctx'Old))
                    and then Byte_Count (Ctx) mod Block_Len = 0
                    and then Byte_Count (Ctx) - Byte_Count (Ctx'Old) in 9 .. 72
                    and then Digest = Digest_Of (Ctx'Old);

   --  sha256(data, len, out): the one-shot helper.
   function Hash (Data : Byte_Array) return Hash256
     with Global => null,
          Pre    => Data'Length <= Max_Update_Len,
          Post   => Hash'Result = Digest_Of (Updated (Initial, Data));

   procedure Hash (Data : Byte_Array; Digest : out Hash256)
     with Global => null,
          Pre    => Data'Length <= Max_Update_Len,
          Post   => Digest = Hash (Data);

   --  Laws.

   --  Chunking is invisible: absorbing A then B equals absorbing A & B. This
   --  is what makes the incremental and one-shot forms agree, and it is the
   --  property the split vectors in vectors/sha256.txt exercise.
   --
   --  The Pre bounds A'Last as well as the lengths: `A & B` is indexed from
   --  A'First when A is not null (RM 4.5.3; a null A gives B's bounds), so
   --  its upper bound A'Last + B'Length must fit in Natural or the Post
   --  itself overflows.
   --
   --  Proof status: proven, no `pragma Assume`. `Updated` unfolds to
   --  `Absorb`, whose Post is the functional model `Absorbed`; the body calls
   --  `Lemma_Absorbed_Concat`, a ghost lemma proven by induction on A over
   --  the chunk structure of `Absorbed` (private part, body). Under -gnata
   --  every step of that induction is an executed assertion, and
   --  tests/test_sha256.adb drives it at every buffer fill 0 .. 63 against
   --  pieces that stop short of, land on, and cross the block boundary, with
   --  operands whose 'First differ (the rebase step), and the split vectors.
   procedure Lemma_Update_Concat (Ctx : Context; A, B : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => not Is_Finished (Ctx)
                    and then A'Length <= Max_Update_Len
                    and then B'Length <= Max_Update_Len - A'Length
                    and then (A'Length = 0
                              or else A'Last <= Natural'Last - B'Length)
                    and then U64 (A'Length) + U64 (B'Length)
                             <= Max_Message_Bytes - Byte_Count (Ctx),
          Post   => Updated (Ctx, A & B) = Updated (Updated (Ctx, A), B);

   --  A finished context holds a whole number of blocks, at least one
   --  (follows from the Type_Invariant on Context).
   procedure Lemma_Finished_Block_Aligned (Ctx : Context)
     with Ghost,
          Global => null,
          Pre    => Is_Finished (Ctx),
          Post   => Byte_Count (Ctx) mod Block_Len = 0
                    and then Byte_Count (Ctx) >= Block_Len;

   --  The padded length is block-aligned and adds between 9 and 72 bytes
   --  (0x80, 0..63 zeros, 8 length bytes).
   procedure Lemma_Padded_Length (N : U64)
     with Ghost,
          Global => null,
          Pre    => N <= Max_Message_Bytes,
          Post   => Padded_Length (N) mod Block_Len = 0
                    and then Padded_Length (N) >= N + 9
                    and then Padded_Length (N) <= N + 72;

private

   type State_Words is array (Natural range 0 .. 7) of U32;
   subtype Block is Byte_Array (0 .. Block_Len - 1);
   subtype Buffer_Fill is Natural range 0 .. Block_Len - 1;

   --  sha256.cpp Sha256::reset(): FIPS 180-4 §5.3.3 initial hash value.
   Initial_State : constant State_Words :=
     [16#6a09e667#, 16#bb67ae85#, 16#3c6ef372#, 16#a54ff53a#,
      16#510e527f#, 16#9b05688c#, 16#1f83d9ab#, 16#5be0cd19#];

   --  Defaults equal Initial, mirroring the C++ constructor calling reset().
   --  Buf is zeroed (the C++ leaves it indeterminate; its bytes beyond
   --  Buf_Len are never observable, and zeroing makes Context equality in
   --  the contracts well defined).
   type Context is record
      State    : State_Words := Initial_State;
      Total    : U64         := 0;        --  bytes absorbed (bitlen_ / 8)
      Buf      : Block       := [others => 0];
      Buf_Len  : Buffer_Fill := 0;        --  buflen_, always < 64 between calls
      Finished : Boolean     := False;
   end record
     with Type_Invariant =>
       Context.Buf_Len = Natural (Context.Total mod Block_Len)
       and then (if Context.Finished
                 then Context.Buf_Len = 0 and then Context.Total >= Block_Len
                 else Context.Total <= Max_Message_Bytes);

   function Is_Finished (Ctx : Context) return Boolean is (Ctx.Finished);
   function Byte_Count (Ctx : Context) return U64 is (Ctx.Total);

   function Initial return Context is
     (State    => Initial_State,
      Total    => 0,
      Buf      => [others => 0],
      Buf_Len  => 0,
      Finished => False);

   ---------------------------------------------------------------------------
   --  Functional model of Sha256::update. Everything below is declared in the
   --  private part, so none of it is a boundary subprogram of Context (SPARK
   --  RM 7.3.2): the Type_Invariant is neither assumed on arguments nor
   --  checked on results, and the facts each needs are in its own Pre.
   ---------------------------------------------------------------------------

   --  Sha256::block(p) as a function: one 64-byte block into the state.
   function Compressed (S : State_Words; P : Block) return State_Words
     with Global => null;

   --  memcpy(buf_ + buflen_, p, take): Chunk written into Buf at Pos, as an
   --  aggregate so that the elementwise definition every lemma below reasons
   --  from is the function itself (no loop, so no executed loop invariant).
   --  Pos may be Block_Len only with an empty Chunk (writes nothing).
   function Written (Buf : Block; Pos : Natural; Chunk : Byte_Array) return Block
     with Global => null,
          Pre    => Pos <= Block_Len
                    and then Chunk'Length <= Block_Len - Pos;

   function Written (Buf : Block; Pos : Natural; Chunk : Byte_Array) return Block is
     ([for I in Block'Range =>
         (if I >= Pos and then I < Pos + Chunk'Length
          then Chunk (Chunk'First + (I - Pos))
          else Buf (I))]);

   --  size_t take = 64 - buflen_; if (take > len) take = len;
   function Take_Len (Ctx : Context; Len : Natural) return Natural is
     (Natural'Min (Block_Len - Ctx.Buf_Len, Len))
     with Global => null;

   --  One iteration of the C++ update loop: copy Chunk (at most the room
   --  left in the buffer) and compress when the block is complete. The C++
   --  bumps bitlen_ once before its loop; adding Chunk'Length here per chunk
   --  sums to the same count and is not observable between the two.
   --  Filled is the step on the already written buffer W, so that Fill
   --  evaluates Written once.
   function Filled (Ctx : Context; W : Block; Len : Natural) return Context is
     (if Ctx.Buf_Len + Len = Block_Len
      then (State    => Compressed (Ctx.State, W),
            Total    => Ctx.Total + U64 (Len),
            Buf      => W,
            Buf_Len  => 0,
            Finished => Ctx.Finished)
      else (State    => Ctx.State,
            Total    => Ctx.Total + U64 (Len),
            Buf      => W,
            Buf_Len  => Ctx.Buf_Len + Len,
            Finished => Ctx.Finished))
     with Global => null,
          Pre    => Len <= Block_Len - Ctx.Buf_Len
                    and then U64 (Len) <= U64'Last - Ctx.Total;

   function Fill (Ctx : Context; Chunk : Byte_Array) return Context is
     (Filled (Ctx, Written (Ctx.Buf, Ctx.Buf_Len, Chunk), Chunk'Length))
     with Global => null,
          Pre    => Chunk'Length <= Block_Len - Ctx.Buf_Len
                    and then U64 (Chunk'Length) <= U64'Last - Ctx.Total;

   --  The whole update loop as a recursive function over the chunks the C++
   --  takes (Take_Len bytes per iteration, so at most Data'Length / 64 + 1
   --  levels). Ghost: this is the specification Absorb is proven against,
   --  and the object Lemma_Update_Concat's induction runs over.
   function Absorbed (Ctx : Context; Data : Byte_Array) return Context
     with Ghost,
          Global => null,
          Subprogram_Variant => (Decreases => Data'Length),
          Pre    => Data'Length <= Max_Update_Len
                    and then U64 (Data'Length) <= U64'Last - Ctx.Total,
          Post   => Absorbed'Result.Total = Ctx.Total + U64 (Data'Length)
                    and then Absorbed'Result.Buf_Len
                             = Natural ((U64 (Ctx.Buf_Len) + U64 (Data'Length))
                                        mod Block_Len)
                    and then Absorbed'Result.Finished = Ctx.Finished
                    and then (if Data'Length = 0 then Absorbed'Result = Ctx);

   function Absorbed (Ctx : Context; Data : Byte_Array) return Context is
     (if Data'Length = 0 then Ctx
      elsif Take_Len (Ctx, Data'Length) = Data'Length then Fill (Ctx, Data)
      else Absorbed
             (Fill (Ctx, Data (Data'First
                               .. Data'First + Take_Len (Ctx, Data'Length) - 1)),
              Data (Data'First + Take_Len (Ctx, Data'Length) .. Data'Last)));

   --  The implementation: the loop of Sha256::update without the bit-count
   --  guard, shared by Updated (message bytes) and Finalize (padding bytes),
   --  so the counter bound is a precondition of the public Update, not of
   --  this. Post: it computes the model.
   function Absorb (Ctx : Context; Data : Byte_Array) return Context
     with Global => null,
          Pre    => Data'Length <= Max_Update_Len
                    and then U64 (Data'Length) <= U64'Last - Ctx.Total
                    and then Ctx.Buf_Len = Natural (Ctx.Total mod Block_Len),
          Post   => Absorb'Result = Absorbed (Ctx, Data)
                    and then Absorb'Result.Total = Ctx.Total + U64 (Data'Length)
                    and then Absorb'Result.Buf_Len
                             = Natural (Absorb'Result.Total mod Block_Len)
                    and then Absorb'Result.Finished = Ctx.Finished
                    and then (if Data'Length = 0 then Absorb'Result = Ctx);

   function Updated (Ctx : Context; Data : Byte_Array) return Context is
     (Absorb (Ctx, Data));

   --  Finish produces both the finalized context and the digest; Digest_Of
   --  is the projection so that Finish's postcondition can name it.
   type Finish_Result is record
      State  : Context;
      Digest : Hash256;
   end record;

   --  Finalize is declared here, in the private part, so it is not a
   --  boundary subprogram of Context (SPARK RM 7.3.2): the Type_Invariant is
   --  neither assumed on Ctx nor checked on the result. The facts it needs
   --  from the invariant are therefore stated in its own Pre; the callers
   --  (Digest_Of, Finish) are boundary subprograms and get them for free.
   function Finalize (Ctx : Context) return Finish_Result
     with Global => null,
          Pre    => not Ctx.Finished
                    and then Ctx.Total <= Max_Message_Bytes
                    and then Ctx.Buf_Len = Natural (Ctx.Total mod Block_Len),
          Post   => Is_Finished (Finalize'Result.State)
                    and then Byte_Count (Finalize'Result.State)
                             = Padded_Length (Byte_Count (Ctx))
                    and then Byte_Count (Finalize'Result.State) - Byte_Count (Ctx)
                             in 9 .. 72
                    --  What Finish needs to re-establish the invariant on
                    --  its (boundary) return: the padding ends a block.
                    and then Finalize'Result.State.Buf_Len = 0
                    and then Byte_Count (Finalize'Result.State) >= Block_Len;

   function Digest_Of (Ctx : Context) return Hash256 is
     (Finalize (Ctx).Digest);

end Kome.SHA256;
