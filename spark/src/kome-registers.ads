--  Kome.Registers: the grow-only registers of one collection (DESIGN.md §4,
--  §6): the ceiling max-register `maxceil` and the writer set `W`. Both only
--  ever widen, which is what makes admission monotone (T4').
--
--  The type is opaque and so are `In_W` and `Extends`: other units reason
--  about writers only through the lemmas, which keeps every quantifier over
--  the writer array inside this package. (Frontier.lean models `W` as a
--  list joined by union; `Extends` is list inclusion.)
pragma Ada_2022;
package Kome.Registers with SPARK_Mode is

   type Writer_Count is range 0 .. Writers_Max;

   type Register_File is private;

   function Ceil (R : Register_File) return U48 with Global => null;
   function Count (R : Register_File) return Writer_Count with Global => null;
   function In_W (R : Register_File; A : Key256) return Boolean with Global => null;

   --  Extends (A, B): every writer of A is a writer of B.
   function Extends (A, B : Register_File) return Boolean with Global => null;

   function Empty return Register_File with
     Post => Ceil (Empty'Result) = 0 and then Count (Empty'Result) = 0;

   --  maxceil := max (maxceil, C). W unchanged.
   procedure Raise_Ceiling (R : in out Register_File; C : U48) with
     Post => Ceil (R) = U48'Max (Ceil (R'Old), C)
             and then Count (R) = Count (R'Old)
             and then Extends (R'Old, R) and then Extends (R, R'Old);

   --  W := W ∪ {A}. Bounded by Writers_Max: a collection that lists more
   --  keys than Members_Max + Revocations_Max over its life is malformed
   --  and the key is dropped (the record is still applied; DESIGN.md §7).
   procedure Add_Writer (R : in out Register_File; A : Key256) with
     Post => Ceil (R) = Ceil (R'Old)
             and then Count (R) >= Count (R'Old)
             and then Extends (R'Old, R)
             and then (if Count (R'Old) < Writers_Max then In_W (R, A));

   procedure Lemma_Extends_Refl (A : Register_File) with
     Ghost, Global => null,
     Post => Extends (A, A);

   procedure Lemma_Extends_Trans (A, B, C : Register_File) with
     Ghost, Global => null,
     Pre  => Extends (A, B) and then Extends (B, C),
     Post => Extends (A, C);

   procedure Lemma_Extends_In_W (A, B : Register_File; X : Key256) with
     Ghost, Global => null,
     Pre  => Extends (A, B) and then In_W (A, X),
     Post => In_W (B, X);

private

   type Writer_Array is array (Writer_Count range 1 .. Writers_Max) of Key256;

   type Register_File is record
      C  : U48 := 0;
      NW : Writer_Count := 0;
      W  : Writer_Array := [others => (others => 0)];
   end record;

   function Ceil (R : Register_File) return U48 is (R.C);
   function Count (R : Register_File) return Writer_Count is (R.NW);

   function In_W (R : Register_File; A : Key256) return Boolean is
     (for some I in 1 .. R.NW => R.W (I) = A);

   function Extends (A, B : Register_File) return Boolean is
     (for all I in 1 .. A.NW => In_W (B, A.W (I)));

end Kome.Registers;
