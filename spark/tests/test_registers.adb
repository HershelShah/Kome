--  Test main for Kome.Registers: the ceiling only rises, Add_Writer counts
--  distinct writers exactly, and Added / Extends say what the lemmas claim.
--  Contracts and ghost lemmas are evaluated at run time (-gnata).
pragma Ada_2022;
with Ada.Text_IO;      use Ada.Text_IO;

with Ada.Command_Line; use Ada.Command_Line;
with Kome;             use Kome;
with Kome.Registers;   use Kome.Registers;

procedure Test_Registers with SPARK_Mode => Off is

   Failed : Boolean := False;

   procedure Check (Name : String; Cond : Boolean) is
   begin
      Put_Line ((if Cond then "PASS " else "FAIL ") & Name);
      if not Cond then
         Failed := True;
      end if;
   end Check;

   function Key (B : Natural) return Key256 is (W7 => Word (B), others => 0);

   R, Old : Register_File := Empty;
begin
   Check ("empty: no ceiling, no writers",
          Ceil (R) = 0 and then Registers.Count (R) = 0 and then not In_W (R, Key (1)));

   Raise_Ceiling (R, 500);
   Raise_Ceiling (R, 100);
   Check ("ceiling is a max-register", Ceil (R) = 500);

   Old := R;
   Add_Writer (R, Key (1));
   Lemma_Added_In_W (Old, R, Key (1), Key (1));
   Lemma_Added_In_W (Old, R, Key (1), Key (2));
   Check ("a new writer counts once", Registers.Count (R) = 1 and then In_W (R, Key (1))
          and then not In_W (R, Key (2)) and then Ceil (R) = 500);

   Old := R;
   Add_Writer (R, Key (1));
   Lemma_Added_Refl (Old, Key (1));
   Check ("an existing writer is not counted again",
          Registers.Count (R) = 1 and then Added (Old, R, Key (1)) and then Added (Old, Old, Key (1)));

   for I in 2 .. 40 loop
      Add_Writer (R, Key (I));
      Add_Writer (R, Key (I / 2));
   end loop;
   Check ("count is the number of distinct writers", Registers.Count (R) = 40 and then Distinct (R));
   for I in 1 .. 40 loop
      Lemma_In_W_Iff (R, Key (I));
   end loop;
   Lemma_Distinct (R, 1, 2);
   Check ("extends is inclusion", Extends (Old, R) and then not Extends (R, Old));

   --  Writers_Max is not filled here: under -gnata every Add_Writer
   --  evaluates Extends and Distinct, quadratic in Count, so a fill to 8 192
   --  would take hours. The bound is a proof obligation (Add_Writer's Pre).

   if Failed then
      Set_Exit_Status (Failure);
   end if;
end Test_Registers;
