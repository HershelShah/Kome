--  Kome.SHA256: FIPS 180-4 SHA-256 in SPARK, incremental (Update/Finish)
--  plus the one-shot helper. CONVENTIONS.md: SHA-256 is part of the fixed
--  primitive set and is implemented here rather than bound from C; its
--  reference is the standard (FIPS 180-4 §5.1.1 padding, §5.3.3 initial
--  hash value, §6.2 computation), and vectors/sha256.txt checks it against
--  the NIST examples, the NIST CAVP vectors and an independent
--  implementation.
--
--  Evidence for the compression. The proof covers the chunking, the
--  padding and the counter, not the round function: Compress_Words (body)
--  is the FIPS 180-4 §6.2.2 computation, and that it computes SHA-256 is
--  established by test, against independent references. Of the two ways
--  to strengthen that evidence (known gap, IMPLEMENTATION_PLAN.md), the
--  NIST vectors were done and the ghost model was not:
--  * done: vectors/sha256.txt carries the NIST CAVP SHA-256 byte-oriented
--    vectors, all of them (SHA256ShortMsg, 65 messages of 0 .. 64 bytes;
--    SHA256LongMsg, 64 messages of up to 6 400 bytes; SHA256Monte, the
--    seed and its 100 checkpoints of 1000 chained hashes each), with their
--    provenance in the file header, and tests/test_sha256.adb checks every
--    line one-shot and incrementally;
--  * not done: a ghost functional model of Compress_Words proved equal to
--    it. Its loop invariants would have to name the model of the first I
--    rounds, which -gnata evaluates at every iteration: quadratic work per
--    block, run on every block the tests hash (the 2**29-byte repeat
--    vector included: some 2**23 blocks, a 30-fold slowdown of the whole
--    test), and no new Assertion_Policy (Ignore) may switch proved
--    assertions off to avoid it. A model written with the same equations
--    as the body would also add little that the Monte Carlo chain
--    (100 000 compressions of data no one chose) does not.
--
--  Observable semantics: the same digest for the same byte stream, however
--  it is chunked; Finish pads (0x80, zeros to 56 mod 64, the 64-bit
--  big-endian bit length) and leaves the object needing a Reset.
--
--  Counter discipline. FIPS 180-4 limits a message to fewer than 2**64
--  bits. The context counts *bytes* (Byte_Count) and refuses, by
--  precondition, any Update that would carry the count past
--  Max_Message_Bytes, so the bit length written by Finish never wraps.
--
--  Functional model. The private part defines the update loop as a
--  function: `Fill` is one iteration (copy `take` bytes into the buffer,
--  compress when it is full) and the ghost `Absorbed` is the loop itself,
--  recursive over the chunks it takes. `Absorb`, the implementation, has
--  `Absorb'Result = Absorbed (Ctx, Data)` as its postcondition and `Updated`
--  is `Absorb` (through `Absorb_Message`, which carries the U64 bound); the
--  chunking law `Lemma_Update_Concat` is then a proof by induction over
--  `Absorbed` (see the body), not an assumption. Finish's digest is defined
--  in the private part as the big-endian image of the state after absorbing
--  `Padding`, so equal contexts give equal digests (Lemma_Digest_Of_Eq).
--
--  Proof status (gnatprove --level=3, cvc5 + z3): every check is proved,
--  with no pragma Assume and no Annotate. The U64 image of the byte counter
--  is related to integer addition by Lemma_U64_Add in the body, proved from
--  bit-level facts the solvers do discharge (see the body).
pragma Ada_2022;
package Kome.SHA256 with SPARK_Mode, Pure is

   Block_Len : constant := 64;   --  FIPS 180-4: 512-bit blocks

   --  Largest message the bit counter can describe: 8 * N must fit in U64
   --  (FIPS 180-4 §5.1.1: the length field is 64 bits). An Update past it is
   --  refused by precondition (Update/Updated below) rather than wrapping
   --  the length that Finish pads with. Unreachable with real inputs.
   Max_Message_Bytes : constant U64 := 2**61 - 1;

   --  Longest single Update. Byte_Array is indexed by Natural, so a full-range
   --  array holds 2**31 elements, one more than Natural can count; excluding
   --  that one shape keeps every offset computation inside Natural.
   Max_Update_Len : constant := Natural'Last;

   type Context is private;

   --  True once Finish has run. A finished context must be Reset before it
   --  is reused: Update and Finish refuse it by precondition (absorbing more
   --  bytes after the padding would hash the padding as message).
   --  (No Post: Byte_Count's Post names Is_Finished, so a Post here naming
   --  Byte_Count would recurse at run time; Lemma_Finished_Block_Aligned
   --  states what a finished context satisfies.)
   function Is_Finished (Ctx : Context) return Boolean
     with Global => null;

   --  Bytes absorbed so far. Before Finish this is the message length; after
   --  Finish it also counts the padding, which Finish absorbs like message
   --  bytes.
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

   --  FIPS 180-4 §5.3.3 initial hash value, zero counters.
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

   --  Absorb Data into the context.
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

   --  Pad (FIPS 180-4 §5.1.1), absorb the padding, emit the state big-endian.
   procedure Finish (Ctx : in out Context; Digest : out Hash256)
     with Global => null,
          Pre    => not Is_Finished (Ctx),
          Post   => Is_Finished (Ctx)
                    and then Byte_Count (Ctx) = Padded_Length (Byte_Count (Ctx'Old))
                    and then Byte_Count (Ctx) mod Block_Len = 0
                    and then Byte_Count (Ctx) - Byte_Count (Ctx'Old) in 9 .. 72
                    and then Digest = Digest_Of (Ctx'Old);

   --  The one-shot helper.
   function Hash (Data : Byte_Array) return Hash256
     with Global => null,
          Pre    => Data'Length <= Max_Update_Len,
          Post   => Hash'Result = Digest_Of (Updated (Initial, Data));

   procedure Hash (Data : Byte_Array; Digest : out Hash256)
     with Global => null,
          Pre    => Data'Length <= Max_Update_Len,
          Post   => Digest = Hash (Data);

   --  Laws.
   --
   --  Running the lemmas. Lemma_Update_Concat and Lemma_Updated_Eq are
   --  proved for every length the Pre allows. Their bodies are inductions
   --  over the 64-byte chunks of the data, and under -gnata (the tests'
   --  build) each level executes a Post that evaluates the recursive model
   --  on the rest of the data, so executing either lemma costs time
   --  quadratic in Length / 64 and recursion depth about 2 * Length / 64.
   --  Known gap closed: the former proof of Lemma_Update_Concat copied A & B
   --  and ran two inductive lemmas at every level (cubic time, a copy per
   --  level on the stack); it is now one induction with constant work per
   --  level (body, Lemma_Absorbed_Concat), and the two inductions on
   --  equal contexts and on rebased bytes are one (Lemma_Absorbed_Cong).
   --  Run bound: tests/test_sha256.adb executes both lemmas on data of up
   --  to 64 KiB (Lemma_Run_Bound there; about 15 s for six calls at the
   --  bound, with stack to spare) and no further. A client compiled with
   --  -gnata should call them only on data of that order: at 4 MiB the
   --  recursion alone is 2**17 frames deep, which overflows a default
   --  8 MiB stack, and the quadratic time is hours. The proof is not
   --  bounded; only the executed check is.

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
   --  the chunk structure of `Absorbed` (private part, body), on a copy of
   --  A & B made once. Executed, it is quadratic: see "Running the lemmas"
   --  above for the bound the tests keep to. Under -gnata
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

   --  Equal contexts stay equal under Updated and give equal digests.
   --  Context holds arrays, so its "=" is Ada equality, which the prover does
   --  not substitute under a function (CONVENTIONS.md, rule 1); these two
   --  lemmas are the substitution steps a caller needs to chain the
   --  contracts above, e.g. from `Update (Ctx, A); Finish (Ctx, D)` (Update's
   --  Post: Ctx = Updated (Initial, A)) to `D = Hash (A)`:
   --
   --     Update (Ctx, A);
   --     Lemma_Digest_Of_Eq (Ctx, Updated (Initial, A));
   --     Finish (Ctx, D);   --  D = Digest_Of (Updated (Initial, A)) = Hash (A)
   --
   --  and, with Lemma_Update_Concat, from two Updates to `Hash (A & B)`.
   --  Lemma_Updated_Eq is an induction over Data's chunks: executed, it is
   --  quadratic in Data'Length / 64 ("Running the lemmas" above; the tests
   --  run it up to 64 KiB). Lemma_Digest_Of_Eq only absorbs the padding
   --  (at most 72 bytes) and is cheap at any length.
   procedure Lemma_Updated_Eq (C1, C2 : Context; Data : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => C1 = C2
                    and then not Is_Finished (C1)
                    and then Data'Length <= Max_Update_Len
                    and then U64 (Data'Length) <= Max_Message_Bytes - Byte_Count (C1),
          Post   => not Is_Finished (C2)
                    and then Byte_Count (C2) = Byte_Count (C1)
                    and then Updated (C1, Data) = Updated (C2, Data);

   procedure Lemma_Digest_Of_Eq (C1, C2 : Context)
     with Ghost,
          Global => null,
          Pre    => C1 = C2 and then not Is_Finished (C1),
          Post   => not Is_Finished (C2)
                    and then Byte_Count (C2) = Byte_Count (C1)
                    and then Digest_Of (C1) = Digest_Of (C2);

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

   --  The byte counter is a semantic integer, so it is a range type
   --  (CONVENTIONS.md: modular types only for wire encoding and hashing);
   --  every addition to it is then an overflow obligation, not a wrap, and
   --  the model below reasons in plain integer arithmetic. Byte_Count is its
   --  U64 image. Max_Message is Max_Message_Bytes as a named number; a
   --  finished context also counts the padding (at most 72 bytes, see
   --  Lemma_Padded_Length), hence the upper bound.
   Max_Message : constant := 2**61 - 1;
   Max_Total   : constant := Max_Message + 72;
   type Byte_Total is range 0 .. Max_Total with Size => 64;

   --  FIPS 180-4 §5.3.3 initial hash value.
   Initial_State : constant State_Words :=
     [16#6a09e667#, 16#bb67ae85#, 16#3c6ef372#, 16#a54ff53a#,
      16#510e527f#, 16#9b05688c#, 16#1f83d9ab#, 16#5be0cd19#];

   --  Defaults equal Initial. Buf is zeroed: its bytes beyond Buf_Len are
   --  never observable, and zeroing makes Context equality in the contracts
   --  well defined.
   type Context is record
      State    : State_Words := Initial_State;
      Total    : Byte_Total  := 0;        --  bytes absorbed
      Buf      : Block       := [others => 0];
      Buf_Len  : Buffer_Fill := 0;        --  bytes in Buf, always < 64 between calls
      Finished : Boolean     := False;
   end record
     with Type_Invariant =>
       Context.Buf_Len = Natural (Context.Total mod Block_Len)
       and then (if Context.Finished
                 then Context.Buf_Len = 0 and then Context.Total >= Block_Len
                 else Context.Total <= Max_Message);

   function Is_Finished (Ctx : Context) return Boolean is (Ctx.Finished);
   function Byte_Count (Ctx : Context) return U64 is (U64 (Ctx.Total));

   function Initial return Context is
     (State    => Initial_State,
      Total    => 0,
      Buf      => [others => 0],
      Buf_Len  => 0,
      Finished => False);

   ---------------------------------------------------------------------------
   --  Functional model of Update. Everything below is declared in the
   --  private part, so none of it is a boundary subprogram of Context (SPARK
   --  RM 7.3.2): the Type_Invariant is neither assumed on arguments nor
   --  checked on results, and the facts each needs are in its own Pre.
   --
   --  Every Pre that compares a 'Length with an Integer expression first
   --  bounds it against a named number: a Byte_Array may span all of
   --  Natural, whose 'Length (2**31) does not fit in Integer.
   ---------------------------------------------------------------------------

   --  FIPS 180-4 §6.2.2 as a function: one 64-byte block into the state.
   --  The compression proper (Compress_Words) takes records of words, not
   --  arrays, and Compressed only loads them: Ada equality on an array is
   --  not logical equality for the prover (CONVENTIONS.md, rule 1), so an
   --  opaque function of arrays could not be shown to return equal results
   --  on elementwise-equal arguments. On records of scalars it can, and
   --  every chunking lemma below needs exactly that step.
   type Hash_Words is record
      H0, H1, H2, H3, H4, H5, H6, H7 : U32;
   end record;

   --  FIPS 180-4 §6.2.2 step 1, W0 .. W15: the block as big-endian words.
   type Message_Words is record
      M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15 : U32;
   end record;

   function Compress_Words (H : Hash_Words; M : Message_Words) return State_Words
     with Global => null;

   --  Bytes 4I .. 4I + 3 of P as a big-endian word.
   function Big_Endian_Word (P : Block; I : Natural) return U32 is
     (U32 (P (4 * I)) * 2**24 + U32 (P (4 * I + 1)) * 2**16
      + U32 (P (4 * I + 2)) * 2**8 + U32 (P (4 * I + 3)))
     with Global => null,
          Pre    => I < 16;

   function Compressed (S : State_Words; P : Block) return State_Words is
     (Compress_Words
        ((S (0), S (1), S (2), S (3), S (4), S (5), S (6), S (7)),
         (Big_Endian_Word (P, 0),  Big_Endian_Word (P, 1),
          Big_Endian_Word (P, 2),  Big_Endian_Word (P, 3),
          Big_Endian_Word (P, 4),  Big_Endian_Word (P, 5),
          Big_Endian_Word (P, 6),  Big_Endian_Word (P, 7),
          Big_Endian_Word (P, 8),  Big_Endian_Word (P, 9),
          Big_Endian_Word (P, 10), Big_Endian_Word (P, 11),
          Big_Endian_Word (P, 12), Big_Endian_Word (P, 13),
          Big_Endian_Word (P, 14), Big_Endian_Word (P, 15))))
     with Global => null;

   --  Chunk copied into Buf at Pos, as an
   --  aggregate so that the elementwise definition every lemma below reasons
   --  from is the function itself (no loop, so no executed loop invariant).
   --  Pos may be Block_Len only with an empty Chunk (writes nothing).
   function Written (Buf : Block; Pos : Natural; Chunk : Byte_Array) return Block
     with Global => null,
          Pre    => Chunk'Length <= Block_Len
                    and then Pos <= Block_Len
                    and then Chunk'Length <= Block_Len - Pos;

   function Written (Buf : Block; Pos : Natural; Chunk : Byte_Array) return Block is
     ([for I in Block'Range =>
         (if I >= Pos and then I < Pos + Chunk'Length
          then Chunk (Chunk'First + (I - Pos))
          else Buf (I))]);

   --  How many of Len bytes the next iteration takes: the room left.
   function Take_Len (Ctx : Context; Len : Natural) return Natural is
     (Natural'Min (Block_Len - Ctx.Buf_Len, Len))
     with Global => null;

   --  One iteration of the update loop: copy Chunk (at most the room left
   --  in the buffer), count it, and compress when the block is complete.
   --  Filled is the step on the already written buffer W, so that Fill
   --  evaluates Written once.
   function Filled (Ctx : Context; W : Block; Len : Natural) return Context is
     (if Ctx.Buf_Len + Len = Block_Len
      then (State    => Compressed (Ctx.State, W),
            Total    => Ctx.Total + Byte_Total (Len),
            Buf      => W,
            Buf_Len  => 0,
            Finished => Ctx.Finished)
      else (State    => Ctx.State,
            Total    => Ctx.Total + Byte_Total (Len),
            Buf      => W,
            Buf_Len  => Ctx.Buf_Len + Len,
            Finished => Ctx.Finished))
     with Global => null,
          Pre    => Len <= Block_Len - Ctx.Buf_Len
                    and then Byte_Total (Len) <= Max_Total - Ctx.Total;

   function Fill (Ctx : Context; Chunk : Byte_Array) return Context is
     (Filled (Ctx, Written (Ctx.Buf, Ctx.Buf_Len, Chunk), Chunk'Length))
     with Global => null,
          Pre    => Chunk'Length <= Block_Len
                    and then Chunk'Length <= Block_Len - Ctx.Buf_Len
                    and then Byte_Total (Chunk'Length) <= Max_Total - Ctx.Total,
          Post   => Fill'Result.Total = Ctx.Total + Byte_Total (Chunk'Length)
                    and then Fill'Result.Finished = Ctx.Finished
                    and then Fill'Result.Buf_Len
                             = (if Ctx.Buf_Len + Chunk'Length = Block_Len then 0
                                else Ctx.Buf_Len + Chunk'Length);

   --  The whole update loop as a recursive function over the chunks it
   --  takes (Take_Len bytes per iteration, so at most Data'Length / 64 + 1
   --  levels). Ghost: this is the specification Absorb is proven against,
   --  and the object Lemma_Update_Concat's induction runs over.
   function Absorbed (Ctx : Context; Data : Byte_Array) return Context
     with Ghost,
          Global => null,
          Subprogram_Variant => (Decreases => Data'Length),
          Pre    => Data'Length <= Max_Update_Len
                    and then Byte_Total (Data'Length) <= Max_Total - Ctx.Total,
          Post   => Absorbed'Result.Total = Ctx.Total + Byte_Total (Data'Length)
                    and then Absorbed'Result.Finished = Ctx.Finished
                    and then (if Data'Length = 0 then Absorbed'Result = Ctx);

   function Absorbed (Ctx : Context; Data : Byte_Array) return Context is
     (if Data'Length = 0 then Ctx
      elsif Take_Len (Ctx, Data'Length) = Data'Length then Fill (Ctx, Data)
      else Absorbed
             (Fill (Ctx, Data (Data'First
                               .. Data'First + Take_Len (Ctx, Data'Length) - 1)),
              Data (Data'First + Take_Len (Ctx, Data'Length) .. Data'Last)));

   ---------------------------------------------------------------------------
   --  Finish. Padding and the digest bytes are expression functions of
   --  scalars and of the state words, so the digest is a function of the
   --  context that respects its equality (Lemma_Digest_Of_Eq).
   ---------------------------------------------------------------------------

   function Shift_Right (Value : U32; Amount : Natural) return U32
     with Import, Convention => Intrinsic, Global => null;
   function Shift_Right (Value : U64; Amount : Natural) return U64
     with Import, Convention => Intrinsic, Global => null;

   --  FIPS 180-4 §5.1.1: 0x80, then zeros up to 56 mod 64, then the 8-byte
   --  length, after a message whose last block holds B bytes. The padding
   --  is 64 - B bytes when the length still fits in that block (B <= 55),
   --  and runs into one more block (128 - B bytes) otherwise.
   subtype Pad_Count is Positive range 9 .. 72;

   function Pad_Len (B : Buffer_Fill) return Pad_Count is
     (if B <= 55 then Block_Len - B else 2 * Block_Len - B)
     with Global => null;

   --  Byte I of the N-byte padding of a T-byte message: the length field is
   --  the bit count 8 * T, big-endian, in the last 8 bytes.
   function Pad_Byte (T : Byte_Total; N : Pad_Count; I : Natural) return Byte is
     (if I = 0 then 16#80#
      elsif I < N - 8 then 0
      else Byte (Shift_Right (U64 (T) * 8, 8 * (N - 1 - I)) and 16#FF#))
     with Global => null,
          Pre    => T <= Max_Message and then I < N;

   function Padding (T : Byte_Total; B : Buffer_Fill) return Byte_Array is
     ([for I in 0 .. Pad_Len (B) - 1 => Pad_Byte (T, Pad_Len (B), I)])
     with Global => null,
          Pre    => T <= Max_Message,
          Post   => Padding'Result'First = 0
                    and then Padding'Result'Length = Pad_Len (B);

   --  FIPS 180-4 §6.2.2 step 4 output: the eight state words, big-endian.
   function Digest_Bytes (S : State_Words) return Hash256 is
     ([for I in 0 .. Hash_Len - 1 =>
         Byte (Shift_Right (S (I / 4), 24 - 8 * (I mod 4)) and 16#FF#)])
     with Global => null;

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
                    and then Ctx.Total <= Max_Message
                    and then Ctx.Buf_Len = Natural (Ctx.Total mod Block_Len),
          Post   => Is_Finished (Finalize'Result.State)
                    and then Byte_Count (Finalize'Result.State)
                             = Padded_Length (Byte_Count (Ctx))
                    and then Byte_Count (Finalize'Result.State) - Byte_Count (Ctx)
                             in 9 .. 72
                    --  What Finish needs to re-establish the invariant on
                    --  its (boundary) return: the padding ends a block.
                    and then Finalize'Result.State.Buf_Len = 0
                    and then Finalize'Result.State.Total mod Block_Len = 0
                    and then Finalize'Result.State.Total >= Block_Len
                    --  The digest: the state after absorbing the padding.
                    and then Finalize'Result.Digest
                             = Digest_Bytes
                                 (Absorbed (Ctx, Padding (Ctx.Total, Ctx.Buf_Len)).State);

   function Digest_Of (Ctx : Context) return Hash256 is
     (Finalize (Ctx).Digest);

   ---------------------------------------------------------------------------
   --  The implementation of Update. Run-time assertion policy: the two Posts
   --  below state `= Absorbed (Ctx, Data)`, and the ghost Absorbed recurses
   --  once per chunk, Data'Length / 64 levels deep, so an executed Post
   --  (-gnata, as kome_spark.gpr builds) would exhaust the stack on a long
   --  Update (a 4 MiB Update did). gnatprove proves Posts whatever the
   --  policy, so the contracts are unchanged; at run time Absorb_Message
   --  checks the model equation itself for Updates of up to Model_Check_Len
   --  bytes (body), and the cheap facts are checked again by Updated's Post.
   --  The pragma applies from here to the end of this private part (the
   --  body keeps the policy it is compiled with).
   ---------------------------------------------------------------------------

   Model_Check_Len : constant := 2**16;

   pragma Assertion_Policy (Post => Ignore);

   --  The implementation: the update loop without the message bound, shared
   --  by Updated (message bytes) and Finalize (padding bytes), so the bound
   --  is a precondition of the public Update, not of this. Post: it computes
   --  the model.
   function Absorb (Ctx : Context; Data : Byte_Array) return Context
     with Global => null,
          Pre    => Data'Length <= Max_Update_Len
                    and then Byte_Total (Data'Length) <= Max_Total - Ctx.Total
                    and then Ctx.Buf_Len = Natural (Ctx.Total mod Block_Len),
          Post   => Absorb'Result = Absorbed (Ctx, Data)
                    and then Absorb'Result.Total = Ctx.Total + Byte_Total (Data'Length)
                    and then Absorb'Result.Buf_Len
                             = Natural (Absorb'Result.Total mod Block_Len)
                    and then Absorb'Result.Finished = Ctx.Finished
                    and then (if Data'Length = 0 then Absorb'Result = Ctx);

   --  Absorb under the public Update precondition, which bounds the count
   --  in U64. The body carries that bound over to Byte_Total and the sum
   --  back to U64 (Lemma_U64_Add in the body), so Updated's contract, which
   --  speaks of Byte_Count, follows from this Post.
   function Absorb_Message (Ctx : Context; Data : Byte_Array) return Context
     with Global => null,
          Pre    => not Ctx.Finished
                    and then Ctx.Total <= Max_Message
                    and then Ctx.Buf_Len = Natural (Ctx.Total mod Block_Len)
                    and then Data'Length <= Max_Update_Len
                    and then U64 (Data'Length) <= Max_Message_Bytes - U64 (Ctx.Total),
          Post   => Absorb_Message'Result = Absorbed (Ctx, Data)
                    and then Absorb_Message'Result.Total
                             = Ctx.Total + Byte_Total (Data'Length)
                    and then Absorb_Message'Result.Total <= Max_Message
                    and then U64 (Absorb_Message'Result.Total)
                             = U64 (Ctx.Total) + U64 (Data'Length)
                    and then Absorb_Message'Result.Buf_Len
                             = Natural (Absorb_Message'Result.Total mod Block_Len)
                    and then not Absorb_Message'Result.Finished
                    and then (if Data'Length = 0 then Absorb_Message'Result = Ctx);

   function Updated (Ctx : Context; Data : Byte_Array) return Context is
     (Absorb_Message (Ctx, Data));

end Kome.SHA256;
