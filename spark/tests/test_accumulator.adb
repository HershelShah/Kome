--  Test main for Kome.Accumulator (DESIGN.md §8, T6). The test has these
--  parts:
--    (a) Hand vectors: a carry out of one limb, a carry through 32 and
--        through 63 limbs, the wraparound of 2^4096 - 1 + 1, and a borrow
--        through each limb.
--    (b) The vectors in vectors/accumulator.txt, through the wire form.
--        Python integers computed them, independently of the SPARK model:
--        random-looking, sparse, carry-chain and wraparound cases.
--    (c) The laws on a grid of accumulators, both as plain equalities and
--        through the ghost lemmas. The Posts of the lemmas (with the
--        Big_Integer model) and their bodies run under -gnata. The
--        exception is the limb-by-limb steps that the "Run-time cost" note
--        of the spec exempts.
--    (d) The byte order as an integer: Value (From_Bytes (B)) =
--        Σ B (I) · 256^I on the vectors and on hand cases (bytes 0, 8 and
--        511).
--    (e) The acc(e) construction of DESIGN.md §8 (D7): sixteen 32-byte
--        blocks, with B_0 the least significant.
--    (f) A chain of the laws through Lemma_Eq_Iff_Value and the
--        congruence lemmas.
pragma Ada_2022;
with Ada.Text_IO;       use Ada.Text_IO;
with Ada.Command_Line;  use Ada.Command_Line;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Kome;              use Kome;
with Kome.Accumulator;  use Kome.Accumulator;

procedure Test_Accumulator with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   All_Ones : constant Acc := [others => U64'Last];
   One      : constant Acc := [0 => 1, others => 0];

   function Hex_Digit (C : Character) return Byte is
     (case C is
        when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
        when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
        when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
        when others     => raise Constraint_Error);

   function From_Hex (S : String) return Acc_Byte_Array is
      R : Acc_Byte_Array;
   begin
      for I in R'Range loop
         R (I) := Hex_Digit (S (S'First + 2 * I)) * 16
                  + Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end From_Hex;

   function Shift_Right (V : U64; N : Natural) return U64 is
     (V / 2 ** N);
   function Shift_Left (V : U64; N : Natural) return U64 is
     (V * 2 ** N);

   --  A deterministic, random-looking accumulator (xorshift64*).
   function Pseudo (Seed : U64) return Acc is
      X : U64 := Seed xor 16#9E37_79B9_7F4A_7C15#;
      R : Acc;
   begin
      for L in Limb_Index loop
         X := X xor Shift_Right (X, 12);
         X := X xor Shift_Left (X, 25);
         X := X xor Shift_Right (X, 27);
         R (L) := X * 16#2545_F491_4F6C_DD1D#;
      end loop;
      return R;
   end Pseudo;

begin
   ----------------------------------------------------------------------
   --  (a) Hand vectors
   ----------------------------------------------------------------------
   declare
      A : constant Acc := [0 => U64'Last, others => 0];
      R : constant Acc := Add (A, One);
   begin
      Check ("carry out of limb 0",
             R = Acc'[0 => 0, 1 => 1, others => 0]);
      Check ("borrow back into limb 0", Sub (R, One) = A);
   end;

   declare
      Low32 : constant Acc :=
        [for L in Limb_Index => (if L < 32 then U64'Last else 0)];
      Low63 : constant Acc :=
        [for L in Limb_Index => (if L < 63 then U64'Last else 0)];
   begin
      Check ("carry through 32 limbs",
             Add (Low32, One) = Acc'[32 => 1, others => 0]);
      Check ("carry through 63 limbs into the top limb",
             Add (Low63, One) = Acc'[63 => 1, others => 0]);
      Check ("2^4096 - 1 + 1 wraps to 0", Add (All_Ones, One) = Zero);
      Check ("0 - 1 borrows through every limb", Sub (Zero, One) = All_Ones);
      Check ("(2^4096 - 1) + (2^4096 - 1) = 2^4096 - 2",
             Add (All_Ones, All_Ones)
             = Acc'[0 => U64'Last - 1, others => U64'Last]);
      Check ("top bit + top bit wraps to 0",
             Add (Acc'[63 => 2**63, others => 0], Acc'[63 => 2**63, others => 0])
             = Zero);
      Check ("2^2048 - 1 borrows through 32 limbs",
             Sub (Acc'[32 => 1, others => 0], One) = Low32);
   end;

   declare
      --  Y = 2^4096 - X: each limb makes a carry into the next limb.
      X : constant Acc :=
        [for L in Limb_Index => (if L mod 2 = 0 then U64'Last else 0)];
      Y : constant Acc :=
        [for L in Limb_Index =>
           (if L = 0 then 1 elsif L mod 2 = 0 then 0 else U64'Last)];
   begin
      Check ("alternating carries sum to 0", Add (X, Y) = Zero);
      Check ("alternating carries, sub",
             Sub (Zero, X) = Y and then Sub (Zero, Y) = X);
   end;

   ----------------------------------------------------------------------
   --  (b) Vectors (independent Python reference)
   ----------------------------------------------------------------------
   declare
      F      : File_Type;
      N_Add  : Natural := 0;
      N_Sub  : Natural := 0;
      Ok_Op  : Boolean := True;
      Ok_Rt  : Boolean := True;
      Hex    : constant := 2 * Acc_Bytes;
   begin
      Open (F, In_File, "vectors/accumulator.txt");
      while not End_Of_File (F) loop
         declare
            Line : constant String := Get_Line (F);
         begin
            if Line'Length > 0 and then Line (Line'First) /= '#' then
               declare
                  Op : constant String := Line (Line'First .. Line'First + 2);
                  P  : constant Positive := Line'First + 4;
                  AB : constant Acc_Byte_Array :=
                    From_Hex (Line (P .. P + Hex - 1));
                  BB : constant Acc_Byte_Array :=
                    From_Hex (Line (P + Hex + 1 .. P + 2 * Hex));
                  RB : constant Acc_Byte_Array :=
                    From_Hex (Line (P + 2 * Hex + 2 .. P + 3 * Hex + 1));
                  A  : constant Acc := From_Bytes (AB);
                  B  : constant Acc := From_Bytes (BB);
               begin
                  if Op = "ADD" then
                     N_Add := N_Add + 1;
                     Ok_Op := Ok_Op and then To_Bytes (Add (A, B)) = RB;
                     --  The bytes, read as little-endian integers, are the
                     --  values (the Posts of the lemmas check this under
                     --  -gnata).
                     Lemma_Value_From_Bytes (AB);
                     Lemma_Value_To_Bytes (B);
                     Lemma_Value_From_Bytes (RB);
                  elsif Op = "SUB" then
                     N_Sub := N_Sub + 1;
                     Ok_Op := Ok_Op and then To_Bytes (Sub (A, B)) = RB;
                     Lemma_From_To_Bytes (A);
                     Lemma_To_From_Bytes (RB);
                  else
                     Ok_Op := False;
                  end if;
                  Ok_Rt := Ok_Rt
                    and then To_Bytes (A) = AB
                    and then From_Bytes (To_Bytes (B)) = B
                    and then To_Bytes (From_Bytes (RB)) = RB;
               end;
            end if;
         end;
      end loop;
      Close (F);
      Check ("vectors: ADD and SUB match the Python reference", Ok_Op);
      Check ("vectors: wire form round-trips", Ok_Rt);
      Check ("vectors: ADD count >= 40 (" & N_Add'Image & ")", N_Add >= 40);
      Check ("vectors: SUB count >= 40 (" & N_Sub'Image & ")", N_Sub >= 40);
   end;

   --  The wire form is little-endian, limb by limb.
   declare
      B : constant Acc_Byte_Array := To_Bytes (Acc'[0 => 16#0807_0605_0403_0201#,
                                                63 => 16#FF00_0000_0000_0000#,
                                                others => 0]);
   begin
      Check ("wire form: limb 0 little-endian",
             B (0) = 1 and then B (1) = 2 and then B (7) = 8
             and then B (8) = 0);
      Check ("wire form: top byte is the top limb's top byte",
             B (511) = 16#FF# and then B (510) = 0);
   end;

   ----------------------------------------------------------------------
   --  (c) Laws on a grid
   ----------------------------------------------------------------------
   declare
      type Grid is array (Positive range <>) of Acc;
      G : constant Grid :=
        [Zero, One, All_Ones, Pseudo (1), Pseudo (2),
         Acc'[0 => U64'Last, 1 => U64'Last, others => 0]];
      Small : constant Grid := [One, All_Ones, Pseudo (3), Pseudo (4)];
      Comm, Zero_Law, Sub_Add, Add_Sub, Self, Assoc : Boolean := True;
   begin
      for A of G loop
         Lemma_Add_Zero (A);
         Lemma_Sub_Self (A);
         Lemma_Value_Bounds (A);
         Zero_Law := Zero_Law and then Add (A, Zero) = A
                     and then Add (Zero, A) = A;
         Self := Self and then Sub (A, A) = Zero;
         for B of G loop
            Lemma_Add_Comm (A, B);
            Lemma_Sub_Add (A, B);
            Lemma_Add_Sub (A, B);
            Comm := Comm and then Add (A, B) = Add (B, A);
            Sub_Add := Sub_Add and then Sub (Add (A, B), B) = A;
            Add_Sub := Add_Sub and then Add (Sub (A, B), B) = A;
         end loop;
      end loop;
      for A of Small loop
         for B of Small loop
            for C of Small loop
               Lemma_Add_Assoc (A, B, C);
               Assoc := Assoc
                 and then Add (Add (A, B), C) = Add (A, Add (B, C));
            end loop;
         end loop;
      end loop;
      Check ("law: Add commutative on the grid", Comm);
      Check ("law: Zero is the unit on the grid", Zero_Law);
      Check ("law: Sub (Add (A, B), B) = A on the grid", Sub_Add);
      Check ("law: Add (Sub (A, B), B) = A on the grid", Add_Sub);
      Check ("law: Sub (A, A) = Zero on the grid", Self);
      Check ("law: Add associative on the grid", Assoc);
      Lemma_Value_Zero;
      Lemma_Value_Injective (Pseudo (5), Pseudo (5));
      --  Different computations with equal Value.
      Lemma_Value_Injective (Add (Pseudo (5), Pseudo (6)),
                             Add (Pseudo (6), Pseudo (5)));
      Lemma_Value_Injective (Sub (Add (Pseudo (7), All_Ones), All_Ones),
                             Pseudo (7));
      Lemma_Value_Congruent (Add (Pseudo (5), Pseudo (6)),
                             Add (Pseudo (6), Pseudo (5)));
      Check ("ghost lemmas executed on the grid (-gnata)", True);
   end;

   ----------------------------------------------------------------------
   --  (d) Byte order as an integer (DESIGN.md §8 "as an integer";
   --  little-endian). Each pragma Assert runs under -gnata and raises an
   --  exception on failure. Thus, if the test gets to the PASS line, all of
   --  them held.
   ----------------------------------------------------------------------
   declare
      Two  : constant Big_Integer := To_Big_Integer (2);
      B8   : constant Acc_Byte_Array := [8 => 1, others => 0];
      B511 : constant Acc_Byte_Array := [511 => 16#80#, others => 0];
      B0   : constant Acc_Byte_Array := [0 => 16#2A#, others => 0];
      Mix  : constant Acc_Byte_Array :=
        [0 => 1, 1 => 2, 9 => 3, others => 0];
   begin
      pragma Assert (Bytes_Value (B0) = 42);
      pragma Assert (Value (From_Bytes (B0)) = 42);
      pragma Assert (Bytes_Value (B8) = Two ** 64);
      pragma Assert (Value (From_Bytes (B8)) = Two ** 64);
      pragma Assert (From_Bytes (B8) = Acc'[1 => 1, others => 0]);
      pragma Assert (Bytes_Value (B511) = Two ** 4095);
      pragma Assert (Value (From_Bytes (B511)) = Two ** 4095);
      pragma Assert (Bytes_Value (Mix)
                     = 1 + 2 * 256 + 3 * Two ** 72);
      pragma Assert (Value (From_Bytes (Mix)) = Bytes_Value (Mix));
      pragma Assert (Modulus = Two ** 4096);
      pragma Assert (Value (All_Ones) = Two ** 4096 - 1);
      Lemma_Value_From_Bytes (Mix);
      Lemma_Value_To_Bytes (Pseudo (9));
      Check ("byte order: Value (From_Bytes (B)) = sum B (I) * 256^I "
             & "(bytes 0, 8, 9, 511; 2^4096 - 1)", True);
   end;

   ----------------------------------------------------------------------
   --  (e) DESIGN.md §8 (D7): acc(e) := Σ_{i=0..15} LE(B_i) · 2^(256·i),
   --  LE(B) := Σ_j B[j] · 256^j. The sixteen 32-byte blocks, concatenated
   --  in counter order and read by From_Bytes, denote exactly that sum.
   --  This test computes the sum block by block with Big_Integers,
   --  independently of the byte-level model of the package.
   ----------------------------------------------------------------------
   declare
      subtype Block is Byte_Array (0 .. 31);
      type Blocks is array (0 .. 15) of Block;
      Bs   : Blocks;
      Cat  : Acc_Byte_Array;
      X    : U64 := 16#0123_4567_89AB_CDEF#;
      Sum  : Big_Integer := 0;
      Two  : constant Big_Integer := To_Big_Integer (2);

      function LE (B : Block) return Big_Integer is
         R : Big_Integer := 0;
      begin
         for J in reverse B'Range loop
            R := R * 256 + To_Big_Integer (Integer (B (J)));
         end loop;
         return R;
      end LE;
   begin
      for I in Blocks'Range loop
         for J in Block'Range loop
            X := X xor Shift_Right (X, 12);
            X := X xor Shift_Left (X, 25);
            X := X xor Shift_Right (X, 27);
            Bs (I) (J) := Byte (Shift_Right (X * 16#2545_F491_4F6C_DD1D#, 56));
         end loop;
         Cat (32 * I .. 32 * I + 31) := Bs (I);
         Sum := Sum + LE (Bs (I)) * Two ** (256 * I);
      end loop;
      pragma Assert (Sum < Modulus);
      pragma Assert (Value (From_Bytes (Cat)) = Sum);
      pragma Assert (Bytes_Value (Cat) = Sum);
      Check ("D7: B_0 .. B_15 concatenated read little-endian = "
             & "sum LE(B_i) * 2^(256 i)", True);
      --  B_0 is the least significant block: a 1 in byte 0 of B_15 is
      --  2^(256*15), not 1.
      declare
         Top : constant Acc_Byte_Array := [32 * 15 => 1, others => 0];
      begin
         pragma Assert (Value (From_Bytes (Top)) = Two ** (256 * 15));
         Check ("D7: B_15 is the most significant block",
                From_Bytes (Top) = Acc'[60 => 1, others => 0]);
      end;
   end;

   ----------------------------------------------------------------------
   --  (f) A chain of the laws: Lemma_Eq_Iff_Value, Lemma_Add_Congruent and
   --  Lemma_Sub_Congruent. The Post of each lemma runs under -gnata on
   --  pairs that are equal but computed differently, and on pairs that are
   --  not equal.
   ----------------------------------------------------------------------
   declare
      P5   : constant Acc := Pseudo (5);
      P6   : constant Acc := Pseudo (6);
      P7   : constant Acc := Pseudo (7);
      L    : constant Acc := Add (P5, P6);
      R    : constant Acc := Add (P6, P5);
      Top  : constant Acc := [63 => 1, others => 0];
   begin
      --  Equal, computed two ways.
      Lemma_Eq_Iff_Value (L, R);
      pragma Assert (Value (L) = Value (R));
      --  Not equal: the Post of the lemma is (False) = (False).
      Lemma_Eq_Iff_Value (P5, P6);
      pragma Assert (Value (P5) /= Value (P6));
      --  The two differ only in the top limb.
      Lemma_Eq_Iff_Value (Zero, Top);
      pragma Assert (Value (Zero) /= Value (Top));
      Lemma_Eq_Iff_Value (Sub (Add (P7, All_Ones), All_Ones), P7);
      Check ("Lemma_Eq_Iff_Value: equal and unequal pairs",
             L = R and then P5 /= P6 and then Zero /= Top);

      --  Congruence: substitute L for R inside Add and Sub.
      Lemma_Add_Congruent (L, R, P7, P7);
      Lemma_Sub_Congruent (L, R, P7, P7);
      Lemma_Add_Congruent (P7, P7, L, R);
      Lemma_Sub_Congruent (P7, P7, L, R);
      Check ("Lemma_Add_Congruent / Lemma_Sub_Congruent",
             Add (L, P7) = Add (R, P7) and then Sub (L, P7) = Sub (R, P7)
             and then Add (P7, L) = Add (P7, R)
             and then Sub (P7, L) = Sub (P7, R));

      --  The recipe in the spec: Add (Add (A, B), C) = Add (Add (B, A), C)
      --  from Lemma_Add_Comm, and transitivity through three calls of
      --  Lemma_Eq_Iff_Value.
      Lemma_Add_Comm (P5, P6);
      Lemma_Add_Congruent (Add (P5, P6), Add (P6, P5), P7, P7);
      Lemma_Add_Assoc (P6, P5, P7);
      declare
         X : constant Acc := Add (Add (P5, P6), P7);
         Y : constant Acc := Add (Add (P6, P5), P7);
         Z : constant Acc := Add (P6, Add (P5, P7));
      begin
         Lemma_Eq_Iff_Value (X, Y);
         Lemma_Eq_Iff_Value (Y, Z);
         Lemma_Eq_Iff_Value (X, Z);
         Check ("chained laws: (A + B) + C = B + (A + C)", X = Z);
      end;
   end;

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Accumulator;
