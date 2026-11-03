pragma Ada_2022;
package body Kome.Registers with SPARK_Mode is

   --  The quantified definitions live here, out of every client's view.

   function In_W (R : Register_File; A : Key256) return Boolean is
     (for some I in 1 .. R.NW => R.W (I) = A);

   function Extends (A, B : Register_File) return Boolean is
     (for all I in 1 .. A.NW => In_W (B, A.W (I)));

   function Distinct (R : Register_File) return Boolean is
     (for all I in 1 .. R.NW =>
        (for all J in 1 .. R.NW => (if I /= J then R.W (I) /= R.W (J))));

   function Added (Old, Upd : Register_File; A : Key256) return Boolean is
     (Upd.NW = Old.NW + (if In_W (Old, A) then 0 else 1)
      and then (for all I in 1 .. Old.NW => Upd.W (I) = Old.W (I))
      and then (if not In_W (Old, A) then Upd.W (Upd.NW) = A));

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
            pragma Assert (In_W (Old, A));
            return;
         end if;
         pragma Loop_Invariant (for all J in 1 .. I => R.W (J) /= A);
      end loop;
      pragma Assert (not In_W (Old, A));
      R.NW := R.NW + 1;
      R.W (R.NW) := A;
      pragma Assert (for all I in 1 .. Old.NW => R.W (I) = Old.W (I));
      pragma Assert (for all I in 1 .. Old.NW => In_W (R, Old.W (I)));
      pragma Assert (In_W (R, A));
   end Add_Writer;

   procedure Lemma_In_W_Iff (R : Register_File; A : Key256) is null;

   procedure Lemma_Added_In_W (Old, Upd : Register_File; A, K : Key256) is
   begin
      if In_W (Old, K) then
         pragma Assert (In_W (Upd, K));
      elsif K = A then
         pragma Assert (Upd.W (Upd.NW) = A);
      else
         pragma Assert (for all I in 1 .. Old.NW => Upd.W (I) /= K);
         pragma Assert (not In_W (Upd, K));
      end if;
   end Lemma_Added_In_W;

   procedure Lemma_Added_Refl (R : Register_File; A : Key256) is null;

   procedure Lemma_Added_Extends (Old, Upd : Register_File; A : Key256) is
   begin
      pragma Assert (for all I in 1 .. Old.NW => In_W (Upd, Old.W (I)));
   end Lemma_Added_Extends;

   procedure Lemma_Distinct (R : Register_File; I, J : Writer_Index) is null;

   procedure Lemma_Eq (A, B : Register_File) is
   begin
      pragma Assert (for all I in 1 .. A.NW => A.W (I) = B.W (I));
      pragma Assert (for all I in 1 .. A.NW => In_W (B, A.W (I)));
      pragma Assert (for all I in 1 .. B.NW => In_W (A, B.W (I)));
   end Lemma_Eq;

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
