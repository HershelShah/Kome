--  Body of Kome.SHA256. See the spec and src/sha256.cpp.
pragma Ada_2022;
package body Kome.SHA256 with SPARK_Mode is

   --  Shift and rotate intrinsics for the modular word types (GNAT RM
   --  "Shifts and Rotates"); gnatprove models them as division/multiplication
   --  by powers of two.
   function Shift_Left (Value : U32; Amount : Natural) return U32
     with Import, Convention => Intrinsic, Global => null;
   function Shift_Right (Value : U32; Amount : Natural) return U32
     with Import, Convention => Intrinsic, Global => null;
   function Rotate_Right (Value : U32; Amount : Natural) return U32
     with Import, Convention => Intrinsic, Global => null;
   function Shift_Right (Value : U64; Amount : Natural) return U64
     with Import, Convention => Intrinsic, Global => null;

   --  sha256.cpp K[64]: FIPS 180-4 §4.2.2 round constants.
   K : constant array (Natural range 0 .. 63) of U32 :=
     [16#428a2f98#, 16#71374491#, 16#b5c0fbcf#, 16#e9b5dba5#,
      16#3956c25b#, 16#59f111f1#, 16#923f82a4#, 16#ab1c5ed5#,
      16#d807aa98#, 16#12835b01#, 16#243185be#, 16#550c7dc3#,
      16#72be5d74#, 16#80deb1fe#, 16#9bdc06a7#, 16#c19bf174#,
      16#e49b69c1#, 16#efbe4786#, 16#0fc19dc6#, 16#240ca1cc#,
      16#2de92c6f#, 16#4a7484aa#, 16#5cb0a9dc#, 16#76f988da#,
      16#983e5152#, 16#a831c66d#, 16#b00327c8#, 16#bf597fc7#,
      16#c6e00bf3#, 16#d5a79147#, 16#06ca6351#, 16#14292967#,
      16#27b70a85#, 16#2e1b2138#, 16#4d2c6dfc#, 16#53380d13#,
      16#650a7354#, 16#766a0abb#, 16#81c2c92e#, 16#92722c85#,
      16#a2bfe8a1#, 16#a81a664b#, 16#c24b8b70#, 16#c76c51a3#,
      16#d192e819#, 16#d6990624#, 16#f40e3585#, 16#106aa070#,
      16#19a4c116#, 16#1e376c08#, 16#2748774c#, 16#34b0bcb5#,
      16#391c0cb3#, 16#4ed8aa4a#, 16#5b9cca4f#, 16#682e6ff3#,
      16#748f82ee#, 16#78a5636f#, 16#84c87814#, 16#8cc70208#,
      16#90befffa#, 16#a4506ceb#, 16#bef9a3f7#, 16#c67178f2#];

   ---------------------------------------------------------------------------
   --  Compressed: Sha256::block(p). One 64-byte block into the state. All
   --  word arithmetic is modular U32, which is the wrap the C++ intends.
   ---------------------------------------------------------------------------

   function Compressed (S : State_Words; P : Block) return State_Words is
      type Schedule is array (Natural range 0 .. 63) of U32;
      W : Schedule := [others => 0];
      R : State_Words := S;
      A, B, C, D, E, F, G, H : U32;
      S0, S1, Ch, Maj, T1, T2 : U32;
   begin
      for I in 0 .. 15 loop
         W (I) := Shift_Left (U32 (P (4 * I)), 24)
           or Shift_Left (U32 (P (4 * I + 1)), 16)
           or Shift_Left (U32 (P (4 * I + 2)), 8)
           or U32 (P (4 * I + 3));
      end loop;
      for I in 16 .. 63 loop
         S0 := Rotate_Right (W (I - 15), 7) xor Rotate_Right (W (I - 15), 18)
           xor Shift_Right (W (I - 15), 3);
         S1 := Rotate_Right (W (I - 2), 17) xor Rotate_Right (W (I - 2), 19)
           xor Shift_Right (W (I - 2), 10);
         W (I) := W (I - 16) + S0 + W (I - 7) + S1;
      end loop;
      A := S (0); B := S (1); C := S (2); D := S (3);
      E := S (4); F := S (5); G := S (6); H := S (7);
      for I in 0 .. 63 loop
         S1  := Rotate_Right (E, 6) xor Rotate_Right (E, 11) xor Rotate_Right (E, 25);
         Ch  := (E and F) xor ((not E) and G);
         T1  := H + S1 + Ch + K (I) + W (I);
         S0  := Rotate_Right (A, 2) xor Rotate_Right (A, 13) xor Rotate_Right (A, 22);
         Maj := (A and B) xor (A and C) xor (B and C);
         T2  := S0 + Maj;
         H := G; G := F; F := E; E := D + T1;
         D := C; C := B; B := A; A := T1 + T2;
      end loop;
      R (0) := S (0) + A; R (1) := S (1) + B; R (2) := S (2) + C; R (3) := S (3) + D;
      R (4) := S (4) + E; R (5) := S (5) + F; R (6) := S (6) + G; R (7) := S (7) + H;
      return R;
   end Compressed;

   ------------
   -- Absorb --
   ------------

   function Absorb (Ctx : Context; Data : Byte_Array) return Context is
      --  The invariant that ties each iteration to the model evaluates
      --  Absorbed over the unread suffix, which would make an executed
      --  Absorb quadratic in Data'Length. gnatprove analyses loop invariants
      --  whatever the assertion policy, so proof is unaffected; at run time
      --  the same equation is checked once, by the Post, and the cheap
      --  invariants are repeated as Asserts so -gnata still checks them
      --  every iteration.
      pragma Assertion_Policy (Loop_Invariant => Ignore);
      Len       : constant Natural := Data'Length;
      R         : Context := Ctx;
      Remaining : Natural := Len;
      Take      : Natural;
   begin
      while Remaining > 0 loop
         pragma Loop_Invariant (Remaining <= Len);
         pragma Loop_Invariant (R.Total = Ctx.Total + U64 (Len - Remaining));
         pragma Loop_Invariant (R.Finished = Ctx.Finished);
         pragma Loop_Invariant (R.Buf_Len = Natural (R.Total mod Block_Len));
         --  The unread suffix is Data (Data'Last - (Remaining - 1) .. Data'Last).
         pragma Loop_Invariant
           (Absorbed (Ctx, Data)
            = Absorbed (R, Data (Data'Last - (Remaining - 1) .. Data'Last)));
         pragma Loop_Variant (Decreases => Remaining);
         pragma Assert (Remaining <= Len);
         pragma Assert (R.Total = Ctx.Total + U64 (Len - Remaining));
         pragma Assert (R.Finished = Ctx.Finished);
         pragma Assert (R.Buf_Len = Natural (R.Total mod Block_Len));
         Take := Take_Len (R, Remaining);
         --  One unfolding of Absorbed on the suffix: its first Take bytes.
         R := Fill (R, Data (Data'Last - (Remaining - 1)
                             .. Data'Last - (Remaining - Take)));
         Remaining := Remaining - Take;
      end loop;
      return R;
   end Absorb;

   ------------
   -- Update --
   ------------

   procedure Update (Ctx : in out Context; Data : Byte_Array) is
   begin
      Ctx := Updated (Ctx, Data);
   end Update;

   -----------
   -- Reset --
   -----------

   procedure Reset (Ctx : out Context) is
   begin
      Ctx := Initial;
   end Reset;

   --------------
   -- Finalize --
   --------------

   --  Sha256::finish(out). The C++ pushes 0x80, then single zero bytes until
   --  buflen_ == 56, then the 8 length bytes, each through update(). The
   --  mirror computes the zero run (0 .. 63 bytes) and absorbs the whole
   --  padding in one call; the byte stream, and so the digest and the
   --  counter, are identical.
   function Finalize (Ctx : Context) return Finish_Result is
      R      : Finish_Result := (State => Ctx, Digest => [others => 0]);
      Bits   : constant U64 := Ctx.Total * 8;   --  cannot wrap: Total <= 2**61 - 1
      After1 : constant Buffer_Fill := (Ctx.Buf_Len + 1) mod Block_Len;
      Zeros  : constant Natural :=
        (if After1 <= 56 then 56 - After1 else 56 + Block_Len - After1);
      Pad    : Byte_Array (0 .. 71) := [others => 0];
      N      : constant Natural := 1 + Zeros + 8;
   begin
      Pad (0) := 16#80#;
      for I in 0 .. 7 loop
         Pad (1 + Zeros + I) :=
           Byte (Shift_Right (Bits, 56 - 8 * I) and 16#FF#);
      end loop;
      --  0x80 plus the zero run lands on 56 mod 64; the 8 length bytes then
      --  complete the block. With the Pre's Buf_Len = Total mod 64 this
      --  makes the padded count block-aligned.
      pragma Assert ((Ctx.Buf_Len + 1 + Zeros) mod Block_Len = 56);
      pragma Assert ((Ctx.Buf_Len + N) mod Block_Len = 0);
      pragma Assert (U64 (Ctx.Buf_Len) = Ctx.Total mod Block_Len);
      pragma Assert ((Ctx.Total + U64 (N)) mod Block_Len = 0);
      R.State := Absorb (R.State, Pad (0 .. N - 1));
      pragma Assert (R.State.Total = Ctx.Total + U64 (N));
      pragma Assert (R.State.Total mod Block_Len = 0);
      pragma Assert (R.State.Buf_Len = 0);
      pragma Assert (R.State.Total >= Ctx.Total + 9 and then R.State.Total <= Ctx.Total + 72);
      pragma Assert (R.State.Total = Padded_Length (Ctx.Total));
      for I in 0 .. 7 loop
         R.Digest (4 * I)     := Byte (Shift_Right (R.State.State (I), 24) and 16#FF#);
         R.Digest (4 * I + 1) := Byte (Shift_Right (R.State.State (I), 16) and 16#FF#);
         R.Digest (4 * I + 2) := Byte (Shift_Right (R.State.State (I), 8) and 16#FF#);
         R.Digest (4 * I + 3) := Byte (R.State.State (I) and 16#FF#);
      end loop;
      R.State.Finished := True;
      return R;
   end Finalize;

   ------------
   -- Finish --
   ------------

   procedure Finish (Ctx : in out Context; Digest : out Hash256) is
      R : constant Finish_Result := Finalize (Ctx);
   begin
      Ctx    := R.State;
      Digest := R.Digest;
   end Finish;

   ----------
   -- Hash --
   ----------

   function Hash (Data : Byte_Array) return Hash256 is
     (Digest_Of (Updated (Initial, Data)));

   procedure Hash (Data : Byte_Array; Digest : out Hash256) is
   begin
      Digest := Hash (Data);
   end Hash;

   ---------------------------------------------------------------------------
   --  Lemmas about the functional model. Each is a ghost procedure whose
   --  Post is the law and whose body is the proof: a chain of assertions
   --  gnatprove discharges from the expression functions in the spec
   --  (Written, Filled, Fill, Take_Len, Absorbed, Updated) and the recursive
   --  calls (induction, bounded by the Subprogram_Variant). Under -gnata every assertion and every Post is
   --  executed, so the test main checks each proof step on real data.
   ---------------------------------------------------------------------------

   --  X and Y hold the same bytes, whatever their bounds.
   function Same_Bytes (X, Y : Byte_Array) return Boolean is
     (X'Length = Y'Length
      and then (for all I in 0 .. X'Length - 1 =>
                  X (X'First + I) = Y (Y'First + I)))
     with Ghost, Global => null;

   --  Writing A at Pos and then B right after it is writing A & B at Pos.
   procedure Lemma_Written_Concat
     (Buf : Block; Pos : Natural; A, B : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => Pos <= Block_Len
                    and then A'Length <= Block_Len - Pos
                    and then B'Length <= Block_Len - Pos - A'Length
                    and then (A'Length = 0
                              or else A'Last <= Natural'Last - B'Length),
          Post   => Written (Written (Buf, Pos, A), Pos + A'Length, B)
                    = Written (Buf, Pos, A & B);

   procedure Lemma_Written_Concat
     (Buf : Block; Pos : Natural; A, B : Byte_Array)
   is
      W1 : constant Block := Written (Buf, Pos, A);
      W2 : constant Block := Written (W1, Pos + A'Length, B);
      W  : constant Block := Written (Buf, Pos, A & B);
   begin
      pragma Assert (for all I in Block'Range => W2 (I) = W (I));
      pragma Assert (W2 = W);
   end Lemma_Written_Concat;

   --  Fill composes across a chunk split as long as both pieces fit the room
   --  left in the buffer.
   procedure Lemma_Fill_Concat (Ctx : Context; A, B : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => A'Length <= Block_Len - Ctx.Buf_Len
                    and then B'Length <= Block_Len - Ctx.Buf_Len - A'Length
                    and then (A'Length = 0
                              or else A'Last <= Natural'Last - B'Length)
                    and then U64 (A'Length) + U64 (B'Length)
                             <= U64'Last - Ctx.Total,
          Post   => Fill (Ctx, A & B) = Fill (Fill (Ctx, A), B);

   procedure Lemma_Fill_Concat (Ctx : Context; A, B : Byte_Array) is
      CA : constant Context := Fill (Ctx, A);
   begin
      Lemma_Written_Concat (Ctx.Buf, Ctx.Buf_Len, A, B);
      if Ctx.Buf_Len + A'Length = Block_Len then
         --  A completes the block, so B is empty and Fill (CA, B) rewrites
         --  nothing: Written with an empty chunk is the identity.
         pragma Assert (B'Length = 0);
         pragma Assert (CA.Buf_Len = 0);
         pragma Assert (for all I in Block'Range =>
                          Written (CA.Buf, 0, B) (I) = CA.Buf (I));
         pragma Assert (Written (CA.Buf, 0, B) = CA.Buf);
         pragma Assert (Fill (CA, B) = CA);
         pragma Assert (A & B = A);
         pragma Assert (Fill (Ctx, A & B) = CA);
      else
         --  A leaves room, so CA has A in its buffer and the same state;
         --  Fill (CA, B) writes B after A, which Lemma_Written_Concat makes
         --  the write of A & B, and compresses exactly when A & B fills the
         --  block, as Fill (Ctx, A & B) does.
         pragma Assert (CA.Buf_Len = Ctx.Buf_Len + A'Length);
         pragma Assert (CA.State = Ctx.State);
         pragma Assert (CA.Buf = Written (Ctx.Buf, Ctx.Buf_Len, A));
         pragma Assert (Written (CA.Buf, CA.Buf_Len, B)
                        = Written (Ctx.Buf, Ctx.Buf_Len, A & B));
         pragma Assert (Fill (CA, B).Total = Ctx.Total + U64 (A'Length) + U64 (B'Length));
         pragma Assert (Fill (CA, B).Buf = Fill (Ctx, A & B).Buf);
         pragma Assert (Fill (CA, B).Buf_Len = Fill (Ctx, A & B).Buf_Len);
         pragma Assert (Fill (CA, B).State = Fill (Ctx, A & B).State);
      end if;
   end Lemma_Fill_Concat;

   --  Fill depends on the bytes of its chunk, not on their bounds.
   procedure Lemma_Fill_Rebase (Ctx : Context; X, Y : Byte_Array)
     with Ghost,
          Global => null,
          Pre    => X'Length <= Block_Len - Ctx.Buf_Len
                    and then U64 (X'Length) <= U64'Last - Ctx.Total
                    and then Same_Bytes (X, Y),
          Post   => Fill (Ctx, X) = Fill (Ctx, Y);

   procedure Lemma_Fill_Rebase (Ctx : Context; X, Y : Byte_Array) is
   begin
      pragma Assert (for all I in Block'Range =>
                       Written (Ctx.Buf, Ctx.Buf_Len, X) (I)
                       = Written (Ctx.Buf, Ctx.Buf_Len, Y) (I));
      pragma Assert (Written (Ctx.Buf, Ctx.Buf_Len, X)
                     = Written (Ctx.Buf, Ctx.Buf_Len, Y));
   end Lemma_Fill_Rebase;

   --  So does Absorbed: induction over its chunks, each rebased by
   --  Lemma_Fill_Rebase.
   procedure Lemma_Absorbed_Rebase (Ctx : Context; X, Y : Byte_Array)
     with Ghost,
          Global => null,
          Subprogram_Variant => (Decreases => X'Length),
          Pre    => X'Length <= Max_Update_Len
                    and then U64 (X'Length) <= U64'Last - Ctx.Total
                    and then Same_Bytes (X, Y),
          Post   => Absorbed (Ctx, X) = Absorbed (Ctx, Y);

   procedure Lemma_Absorbed_Rebase (Ctx : Context; X, Y : Byte_Array) is
      T : constant Natural := Take_Len (Ctx, X'Length);
   begin
      if X'Length = 0 then
         null;
      elsif T = X'Length then
         Lemma_Fill_Rebase (Ctx, X, Y);
      else
         declare
            CX : constant Context := Fill (Ctx, X (X'First .. X'First + T - 1));
         begin
            pragma Assert (Same_Bytes (X (X'First .. X'First + T - 1),
                                       Y (Y'First .. Y'First + T - 1)));
            Lemma_Fill_Rebase (Ctx, X (X'First .. X'First + T - 1),
                                    Y (Y'First .. Y'First + T - 1));
            pragma Assert (CX = Fill (Ctx, Y (Y'First .. Y'First + T - 1)));
            pragma Assert (Same_Bytes (X (X'First + T .. X'Last),
                                       Y (Y'First + T .. Y'Last)));
            Lemma_Absorbed_Rebase (CX, X (X'First + T .. X'Last),
                                       Y (Y'First + T .. Y'Last));
            pragma Assert (Absorbed (Ctx, X)
                           = Absorbed (CX, X (X'First + T .. X'Last)));
            pragma Assert (Absorbed (Ctx, Y)
                           = Absorbed (CX, Y (Y'First + T .. Y'Last)));
         end;
      end if;
   end Lemma_Absorbed_Rebase;

   --  The chunking law on the model. Induction on A'Length: the recursive
   --  call is on A minus its first chunk, which is strictly shorter.
   procedure Lemma_Absorbed_Concat (Ctx : Context; A, B : Byte_Array)
     with Ghost,
          Global => null,
          Subprogram_Variant => (Decreases => A'Length),
          Pre    => A'Length <= Max_Update_Len
                    and then B'Length <= Max_Update_Len - A'Length
                    and then (A'Length = 0
                              or else A'Last <= Natural'Last - B'Length)
                    and then U64 (A'Length) + U64 (B'Length)
                             <= U64'Last - Ctx.Total,
          Post   => Absorbed (Ctx, A & B) = Absorbed (Absorbed (Ctx, A), B);

   procedure Lemma_Absorbed_Concat (Ctx : Context; A, B : Byte_Array) is
      Room : constant Positive   := Block_Len - Ctx.Buf_Len;
      AB   : constant Byte_Array := A & B;
   begin
      if A'Length = 0 then
         --  A & B is B itself (RM 4.5.3: a null left operand gives the
         --  right operand) and Absorbed (Ctx, A) = Ctx.
         pragma Assert (AB = B);
         pragma Assert (Absorbed (Ctx, A) = Ctx);
      elsif B'Length = 0 then
         --  A & B is A and absorbing nothing after A changes nothing.
         pragma Assert (AB = A);
         pragma Assert (Absorbed (Absorbed (Ctx, A), B) = Absorbed (Ctx, A));
      elsif A'Length >= Room then
         --  Both sides take the same first chunk: A's first Room bytes.
         declare
            C1 : constant Context :=
              Fill (Ctx, A (A'First .. A'First + Room - 1));
         begin
            pragma Assert (AB'First = A'First
                           and then AB'Last = A'Last + B'Length);
            pragma Assert (Take_Len (Ctx, A'Length) = Room);
            pragma Assert (Take_Len (Ctx, AB'Length) = Room);
            pragma Assert (AB (A'First .. A'First + Room - 1)
                           = A (A'First .. A'First + Room - 1));
            pragma Assert (Fill (Ctx, AB (A'First .. A'First + Room - 1)) = C1);
            pragma Assert (Absorbed (Ctx, AB)
                           = Absorbed (C1, AB (A'First + Room .. AB'Last)));
            if A'Length = Room then
               --  A is exactly the chunk; what is left of A & B is B's
               --  bytes at A's indices.
               pragma Assert (Absorbed (Ctx, A) = C1);
               pragma Assert (Same_Bytes (AB (A'First + Room .. AB'Last), B));
               Lemma_Absorbed_Rebase (C1, AB (A'First + Room .. AB'Last), B);
            else
               --  What is left of A & B is (the rest of A) & B: induction.
               pragma Assert (Absorbed (Ctx, A)
                              = Absorbed (C1, A (A'First + Room .. A'Last)));
               pragma Assert (AB (A'First + Room .. AB'Last)
                              = A (A'First + Room .. A'Last) & B);
               Lemma_Absorbed_Concat (C1, A (A'First + Room .. A'Last), B);
            end if;
         end;
      else
         --  A fits in the buffer: Absorbed (Ctx, A) = Fill (Ctx, A), and the
         --  first chunk of A & B is A followed by the first T2 bytes of B,
         --  which is also the first chunk B contributes after A.
         declare
            CA : constant Context    := Fill (Ctx, A);
            T2 : constant Positive   := Natural'Min (Room - A'Length, B'Length);
            B1 : constant Byte_Array := B (B'First .. B'First + T2 - 1);
         begin
            pragma Assert (Absorbed (Ctx, A) = CA);
            pragma Assert (CA.Buf_Len = Ctx.Buf_Len + A'Length);
            pragma Assert (Take_Len (CA, B'Length) = T2);
            pragma Assert (Take_Len (Ctx, AB'Length) = A'Length + T2);
            Lemma_Fill_Concat (Ctx, A, B1);
            pragma Assert (A & B1 = AB (A'First .. A'Last + T2));
            pragma Assert (Fill (Ctx, AB (A'First .. A'Last + T2)) = Fill (CA, B1));
            if T2 = B'Length then
               --  A & B is a single chunk on both sides.
               pragma Assert (B1 = B);
               pragma Assert (Absorbed (CA, B) = Fill (CA, B));
               pragma Assert (Absorbed (Ctx, AB) = Fill (Ctx, AB));
            else
               --  Both sides continue from the same context with the same
               --  bytes (the rest of B), at different indices.
               pragma Assert (Absorbed (Ctx, AB)
                              = Absorbed (Fill (Ctx, AB (A'First .. A'Last + T2)),
                                          AB (A'Last + T2 + 1 .. AB'Last)));
               pragma Assert (Absorbed (CA, B)
                              = Absorbed (Fill (CA, B1), B (B'First + T2 .. B'Last)));
               pragma Assert (Same_Bytes (AB (A'Last + T2 + 1 .. AB'Last),
                                          B (B'First + T2 .. B'Last)));
               Lemma_Absorbed_Rebase (Fill (CA, B1),
                                      AB (A'Last + T2 + 1 .. AB'Last),
                                      B (B'First + T2 .. B'Last));
            end if;
         end;
      end if;
   end Lemma_Absorbed_Concat;

   -------------------------
   -- Lemma_Update_Concat --
   -------------------------

   --  Updated is Absorb, whose Post is the model; the law on the model is
   --  Lemma_Absorbed_Concat.
   procedure Lemma_Update_Concat (Ctx : Context; A, B : Byte_Array) is
   begin
      Lemma_Absorbed_Concat (Ctx, A, B);
      pragma Assert (Updated (Ctx, A & B) = Absorbed (Ctx, A & B));
      pragma Assert (Updated (Ctx, A) = Absorbed (Ctx, A));
      pragma Assert (Updated (Updated (Ctx, A), B)
                     = Absorbed (Absorbed (Ctx, A), B));
   end Lemma_Update_Concat;

   procedure Lemma_Finished_Block_Aligned (Ctx : Context) is null;

   procedure Lemma_Padded_Length (N : U64) is null;

end Kome.SHA256;
