--  Test main for Kome.Versions: the order is lexicographic on
--  (t, author, seq, h) with byte strings as unsigned big-endian integers;
--  the ghost lemmas are evaluated at run time (-gnata) on a grid of values.
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with Kome;             use Kome;
with Kome.Versions;     use Kome.Versions;

procedure Test_Versions with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   function Key (B : Byte) return Key256 is (others => Word (B));
   function Hsh (B : Byte) return Key256 is (others => Word (B));

   function V (T : U48; A : Byte; Seq : U48; H : Byte) return Version is
     (T => T, Author => Key (A), Seq => Seq, H => Hsh (H));

   --  Big-endian: the first word is the most significant.
   A_Hi : constant Key256 := (W0 => 1, others => 0);
   A_Lo : constant Key256 := (W7 => 2**32 - 1, others => 0);

   Grid : constant array (Positive range <>) of Version :=
     [V (1, 1, 1, 1), V (1, 1, 1, 2), V (1, 1, 2, 1), V (1, 2, 1, 1),
      V (2, 1, 1, 1), V (0, 0, 0, 0), V (2**48 - 1, 255, 2**48 - 1, 255),
      V (5, 3, 9, 0), V (5, 3, 9, 0)];
begin
   Check ("t decides first", Lt (V (1, 9, 9, 9), V (2, 0, 0, 0)));
   Check ("author decides second", Lt (V (1, 1, 9, 9), V (1, 2, 0, 0)));
   Check ("seq decides third", Lt (V (1, 1, 1, 9), V (1, 1, 2, 0)));
   Check ("h decides last", Lt (V (1, 1, 1, 1), V (1, 1, 1, 2)));
   Check ("equal is not less", not Lt (V (5, 3, 9, 0), V (5, 3, 9, 0)));
   Check ("keys are big-endian unsigned", Lt (A_Lo, A_Hi) and not Lt (A_Hi, A_Lo));
   Check ("0 and 2**48-1 are ordinary values",
          Lt (V (0, 0, 0, 0), V (0, 0, 0, 1)) and Lt (V (2**48 - 2, 0, 0, 0), V (2**48 - 1, 0, 0, 0)));

   for I in Grid'Range loop
      Lemma_Lt_Irrefl (Grid (I));
      for J in Grid'Range loop
         Lemma_Trichotomy (Grid (I), Grid (J));
         if Lt (Grid (I), Grid (J)) then
            Lemma_Lt_Asym (Grid (I), Grid (J));
         end if;
         for K in Grid'Range loop
            if Lt (Grid (I), Grid (J)) and then Lt (Grid (J), Grid (K)) then
               Lemma_Lt_Trans (Grid (I), Grid (J), Grid (K));
            end if;
         end loop;
      end loop;
   end loop;
   Check ("lemmas hold on the grid", True);

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Versions;
