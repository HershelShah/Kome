pragma Ada_2022;
package body Kome.Registers with SPARK_Mode is

   function Empty return Register_File is
     (C => 0, NW => 0, W => [others => (others => 0)]);

   procedure Raise_Ceiling (R : in out Register_File; C : U48) is
   begin
      if C > R.C then
         R.C := C;
      end if;
   end Raise_Ceiling;

   procedure Add_Writer (R : in out Register_File; A : Key256) is
      Old : constant Register_File := R with Ghost;
   begin
      for I in 1 .. R.NW loop
         if R.W (I) = A then
            Lemma_Extends_Refl (R);
            return;
         end if;
         pragma Loop_Invariant (for all J in 1 .. I => R.W (J) /= A);
      end loop;
      if R.NW < Writers_Max then
         R.NW := R.NW + 1;
         R.W (R.NW) := A;
         pragma Assert (for all I in 1 .. Old.NW => R.W (I) = Old.W (I));
         pragma Assert (for all I in 1 .. Old.NW => In_W (R, Old.W (I)));
      else
         Lemma_Extends_Refl (R);
      end if;
   end Add_Writer;

   procedure Lemma_Extends_Refl (A : Register_File) is null;

   procedure Lemma_Extends_Trans (A, B, C : Register_File) is
   begin
      for I in 1 .. A.NW loop
         Lemma_Extends_In_W (B, C, A.W (I));
         pragma Loop_Invariant (for all J in 1 .. I => In_W (C, A.W (J)));
      end loop;
   end Lemma_Extends_Trans;

   procedure Lemma_Extends_In_W (A, B : Register_File; X : Key256) is null;

end Kome.Registers;
