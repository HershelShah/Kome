--  Test main for Kome.Accumulator (DESIGN.md §8, T6). (a) Hand vectors:
--  a carry out of one limb, a carry through 32 and through 63 limbs, the
--  wraparound of 2^4096 - 1 + 1, a borrow through every limb. (b) The
--  vectors in vectors/accumulator.txt, computed with Python integers,
--  independently of the SPARK model: random-looking, sparse, carry-chain
--  and wraparound cases, through the wire form. (c) The laws on a grid of
--  accumulators, both as plain equalities and through the ghost lemmas,
--  whose bodies (and every Post, Loop_Invariant and Assert, including the
--  Big_Integer model) run under -gnata. (d) The byte order as an integer:
--  Value (From_Bytes (B)) = Σ B (I) · 256^I on the vectors and on hand
--  cases (bytes 0, 8 and 511).
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
      --  Y = 2^4096 - X: every limb produces a carry into the next.
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
                     --  values (checked by the lemmas' Posts under -gnata).
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

   --  Wire form is little-endian, limb by limb.
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
      --  Distinct computations with equal Value.
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
   --  little-endian). Each pragma Assert runs under -gnata and raises on
   --  failure, so reaching the PASS line means all of them held.
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

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Accumulator;
