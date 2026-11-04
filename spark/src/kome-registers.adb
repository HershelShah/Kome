pragma Ada_2022;
package body Kome.Registers with SPARK_Mode is

   --  The quantified definitions are here, where no client can see them.

   function In_W (R : Register_File; A : Key256) return Boolean is
     (for some I in 1 .. R.NW => R.W (I) = A);

   --  The first index of A, 0 if A is not a writer.
   function First_Index (R : Register_File; A : Key256) return Writer_Count with
     Global => null,
     Post   => (if First_Index'Result = 0
                then (for all I in 1 .. R.NW => R.W (I) /= A)
                else First_Index'Result <= R.NW
                     and then R.W (First_Index'Result) = A
                     and then (for all I in 1 .. First_Index'Result - 1 => R.W (I) /= A))
   is
   begin
      for I in 1 .. R.NW loop
         if R.W (I) = A then
            return I;
         end if;
         pragma Loop_Invariant (for all J in 1 .. I => R.W (J) /= A);
      end loop;
      return 0;
   end First_Index;

   function W_Cap (R : Register_File; A : Key256) return U48 is
     (declare
        I : constant Writer_Count := First_Index (R, A);
      begin
        (if I = 0 then 0 else R.WC (I)));

   function Extends (A, B : Register_File) return Boolean is
     (for all I in 1 .. A.NW =>
        In_W (B, A.W (I)) and then W_Cap (B, A.W (I)) >= W_Cap (A, A.W (I)));

   function Distinct (R : Register_File) return Boolean is
     (for all I in 1 .. R.NW =>
        (for all J in 1 .. R.NW => (if I /= J then R.W (I) /= R.W (J))));

   --  Every index of A gets the larger cap; the other indices keep theirs;
   --  a new writer is appended at Cap.
   function Added (Old, Upd : Register_File; A : Key256; Cap : U48) return Boolean is
     (Upd.NW = Old.NW + (if In_W (Old, A) then 0 else 1)
      and then (for all I in 1 .. Old.NW => Upd.W (I) = Old.W (I))
      and then (for all I in 1 .. Old.NW =>
                  Upd.WC (I) = (if Old.W (I) = A then U48'Max (Old.WC (I), Cap) else Old.WC (I)))
      and then (if not In_W (Old, A)
                then Upd.W (Upd.NW) = A and then Upd.WC (Upd.NW) = Cap));

   function Empty return Register_File is
     (C => 0, NW => 0, W => [others => (others => 0)], WC => [others => 0]);

   procedure Raise_Ceiling (R : in out Register_File; C : U48) is
   begin
      if C > R.C then
         R.C := C;
      end if;
   end Raise_Ceiling;

   --  After Added (Old, R, A, Cap), R extends Old: each old writer keeps its
   --  first index, and its cap rises or stays.
   procedure Lemma_Extends_After_Add (Old, R : Register_File; A : Key256; Cap : U48) with
     Ghost, Global => null,
     Pre  => Added (Old, R, A, Cap),
     Post => Extends (Old, R)
   is
   begin
      for I in 1 .. Old.NW loop
         pragma Assert (R.W (I) = Old.W (I));
         pragma Assert (In_W (R, Old.W (I)));
         pragma Assert (First_Index (R, Old.W (I)) = First_Index (Old, Old.W (I)));
         pragma Assert (W_Cap (R, Old.W (I)) >= W_Cap (Old, Old.W (I)));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              In_W (R, Old.W (J)) and then W_Cap (R, Old.W (J)) >= W_Cap (Old, Old.W (J)));
      end loop;
   end Lemma_Extends_After_Add;

   procedure Add_Writer (R : in out Register_File; A : Key256; Cap : U48) is
      Old   : constant Register_File := R with Ghost;
      Found : Boolean := False;
   begin
      for I in 1 .. R.NW loop
         if R.W (I) = A then
            R.WC (I) := U48'Max (R.WC (I), Cap);
            Found := True;
         end if;
         pragma Loop_Invariant (R.NW = Old.NW and then R.C = Old.C);
         pragma Loop_Invariant (for all J in Writer_Index => R.W (J) = Old.W (J));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              R.WC (J) = (if Old.W (J) = A then U48'Max (Old.WC (J), Cap) else Old.WC (J)));
         pragma Loop_Invariant (for all J in I + 1 .. Writers_Max => R.WC (J) = Old.WC (J));
         pragma Loop_Invariant (Found = (for some J in 1 .. I => Old.W (J) = A));
      end loop;
      pragma Assert (Found = In_W (Old, A));
      if not Found then
         R.NW := R.NW + 1;
         R.W (R.NW) := A;
         R.WC (R.NW) := Cap;
      end if;
      pragma Assert (for all I in 1 .. Old.NW => R.W (I) = Old.W (I));
      pragma Assert (In_W (R, A));
      pragma Assert (Added (Old, R, A, Cap));
      --  W_Cap (R, A) = max (W_Cap (Old, A), Cap): the first index of A is
      --  the same in Old and R (or the new last index).
      if Found then
         pragma Assert (First_Index (Old, A) /= 0);
         pragma Assert (First_Index (R, A) = First_Index (Old, A));
      else
         pragma Assert (First_Index (R, A) = R.NW);
         pragma Assert (First_Index (Old, A) = 0);
      end if;
      pragma Assert (W_Cap (R, A) = U48'Max (W_Cap (Old, A), Cap));
      --  Extends (Old, R): each old writer keeps its first index and its cap
      --  rises or stays. (A ghost loop: the bound is the ghost copy.)
      Lemma_Extends_After_Add (Old, R, A, Cap);
   end Add_Writer;

   procedure Lemma_In_W_Iff (R : Register_File; A : Key256) is null;

   procedure Lemma_W_Cap_Def (R : Register_File; A : Key256) is
      I : constant Writer_Count := First_Index (R, A);
   begin
      if I /= 0 then
         pragma Assert (R.W (I) = A and then R.WC (I) = W_Cap (R, A));
      end if;
   end Lemma_W_Cap_Def;

   procedure Lemma_Added_In_W (Old, Upd : Register_File; A : Key256; Cap : U48; K : Key256) is
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

   procedure Lemma_Added_Cap (Old, Upd : Register_File; A : Key256; Cap : U48; K : Key256) is
      IO : constant Writer_Count := First_Index (Old, K);
      IU : constant Writer_Count := First_Index (Upd, K);
   begin
      if IO /= 0 then
         --  The first index of K in Old is its first index in Upd.
         pragma Assert (Upd.W (IO) = K);
         pragma Assert (for all I in 1 .. IO - 1 => Upd.W (I) /= K);
         pragma Assert (IU = IO);
         pragma Assert (Upd.WC (IU) = (if K = A then U48'Max (Old.WC (IO), Cap) else Old.WC (IO)));
      elsif K = A then
         pragma Assert (not In_W (Old, A));
         pragma Assert (Upd.NW = Old.NW + 1);
         pragma Assert (for all I in 1 .. Old.NW => Upd.W (I) /= K);
         pragma Assert (Upd.W (Upd.NW) = K);
         pragma Assert (IU = Upd.NW);
         pragma Assert (Upd.WC (IU) = Cap);
      else
         pragma Assert (for all I in 1 .. Old.NW => Upd.W (I) /= K);
         pragma Assert (if Upd.NW > Old.NW then Upd.W (Upd.NW) = A);
         pragma Assert (for all I in 1 .. Upd.NW => Upd.W (I) /= K);
         pragma Assert (IU = 0);
      end if;
   end Lemma_Added_Cap;

   procedure Lemma_Added_Refl (R : Register_File; A : Key256; Cap : U48) is
      I : constant Writer_Count := First_Index (R, A);
   begin
      pragma Assert (I /= 0);
      pragma Assert (R.WC (I) = W_Cap (R, A));
      --  Distinct: I is the only index of A, and Cap <= WC (I).
      pragma Assert (for all J in 1 .. R.NW => (if R.W (J) = A then J = I));
      pragma Assert (for all J in 1 .. R.NW =>
                       R.WC (J) = (if R.W (J) = A then U48'Max (R.WC (J), Cap) else R.WC (J)));
   end Lemma_Added_Refl;

   procedure Lemma_Distinct (R : Register_File; I, J : Writer_Index) is null;

   procedure Lemma_Eq (A, B : Register_File) is
   begin
      pragma Assert (for all I in 1 .. A.NW => A.W (I) = B.W (I));
      pragma Assert (for all I in 1 .. A.NW => A.WC (I) = B.WC (I));
      pragma Assert (for all I in 1 .. A.NW => First_Index (B, A.W (I)) = First_Index (A, A.W (I)));
      pragma Assert (for all I in 1 .. A.NW => In_W (B, A.W (I)));
      pragma Assert (for all I in 1 .. A.NW => W_Cap (B, A.W (I)) = W_Cap (A, A.W (I)));
      pragma Assert (for all I in 1 .. B.NW => In_W (A, B.W (I)));
      pragma Assert (for all I in 1 .. B.NW => W_Cap (A, B.W (I)) = W_Cap (B, B.W (I)));
   end Lemma_Eq;

   procedure Lemma_Extends_Refl (A : Register_File) is null;

   procedure Lemma_Extends_In_W (A, B : Register_File; X : Key256) is null;

end Kome.Registers;
