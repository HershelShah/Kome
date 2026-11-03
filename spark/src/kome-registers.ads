--  Kome.Registers: the admission registers of one collection (DESIGN.md §3,
--  §4): the ceiling max-register `maxceil` and the writer set `W`. Both
--  only ever widen, which is what makes admission monotone (T4').
--
--  This is a cache, not a second source of truth. maxceil(F) and W(F) are
--  views of the frontier (the largest ceiling_t of the held rosters, and
--  the subjects of the held GRANTs); Kome.Frontier keeps a Register_File
--  equal to those views on every state (its invariant `Coherent`, with
--  the lemmas Lemma_Ceil_Bound, Lemma_Ceil_Witness, Lemma_W_Sound and
--  Lemma_W_Complete), so admission reads them in constant time.
--
--  Count is the number of DISTINCT writers: Add_Writer appends a key only
--  if it is not already in W (its Post states Count exactly), and Empty
--  has none. The capacity is Writers_Max = Signers_Max * Slice_Max; W holds
--  at most one subject per held GRANT, so on a frontier it never fills on
--  its own (DESIGN.md §7). Add_Writer requires room (or the key already
--  present) and never drops a key silently (E2); the caller refuses with
--  Auth_Full first.
--
--  The type is opaque and so are `In_W`, `Extends` and `Added`: other units
--  reason about writers only through the lemmas, which keeps every
--  quantifier over the writer array inside this package (CONVENTIONS.md
--  rule 2). (Frontier.lean models `W` as a list joined by union; `Extends`
--  is list inclusion.)
pragma Ada_2022;
package Kome.Registers with SPARK_Mode is

   type Writer_Count is range 0 .. Writers_Max;
   subtype Writer_Index is Writer_Count range 1 .. Writers_Max;

   type Register_File is private;

   function Ceil (R : Register_File) return U48 with Global => null;
   function Count (R : Register_File) return Writer_Count with Global => null;

   --  The I-th writer, in insertion order.
   function Writer (R : Register_File; I : Writer_Index) return Key256 with
     Global => null,
     Pre    => I <= Count (R);

   function In_W (R : Register_File; A : Key256) return Boolean with Global => null;

   --  Extends (A, B): every writer of A is a writer of B.
   function Extends (A, B : Register_File) return Boolean with Global => null;

   --  No writer is listed twice, so Count is the number of distinct writers.
   function Distinct (R : Register_File) return Boolean with Global => null;

   --  Added (Old, Upd, A): Upd is Old with A added to W (nothing changes in
   --  W if A was already there). Opaque; read it with Lemma_Added_In_W.
   function Added (Old, Upd : Register_File; A : Key256) return Boolean with
     Global => null;

   function Empty return Register_File with
     Global => null,
     Post   => Ceil (Empty'Result) = 0 and then Count (Empty'Result) = 0
               and then Distinct (Empty'Result);

   --  maxceil := max (maxceil, C). W unchanged.
   procedure Raise_Ceiling (R : in out Register_File; C : U48) with
     Global => null,
     Post   => Ceil (R) = U48'Max (Ceil (R'Old), C)
               and then Count (R) = Count (R'Old)
               and then (for all I in 1 .. Count (R) => Writer (R, I) = Writer (R'Old, I))
               and then Extends (R'Old, R) and then Extends (R, R'Old)
               and then (if Distinct (R'Old) then Distinct (R));

   --  W := W ∪ {A}. Requires room unless A is already a writer; the caller
   --  refuses beforehand (Auth_Full), so no key is ever dropped (E2).
   procedure Add_Writer (R : in out Register_File; A : Key256) with
     Global => null,
     Pre    => In_W (R, A) or else Count (R) < Writers_Max,
     Post   => Ceil (R) = Ceil (R'Old)
               and then In_W (R, A)
               and then Extends (R'Old, R)
               and then Count (R) = Count (R'Old) + (if In_W (R'Old, A) then 0 else 1)
               and then Added (R'Old, R, A)
               and then (if Distinct (R'Old) then Distinct (R));

   --  The membership test is the existence of an index.
   procedure Lemma_In_W_Iff (R : Register_File; A : Key256) with
     Ghost, Global => null,
     Post => In_W (R, A) = (for some I in 1 .. Count (R) => Writer (R, I) = A);

   procedure Lemma_Added_In_W (Old, Upd : Register_File; A, K : Key256) with
     Ghost, Global => null,
     Pre  => Added (Old, Upd, A),
     Post => In_W (Upd, K) = (In_W (Old, K) or else K = A);

   --  Adding a writer that is already present changes nothing.
   procedure Lemma_Added_Refl (R : Register_File; A : Key256) with
     Ghost, Global => null,
     Pre  => In_W (R, A),
     Post => Added (R, R, A);

   procedure Lemma_Added_Extends (Old, Upd : Register_File; A : Key256) with
     Ghost, Global => null,
     Pre  => Added (Old, Upd, A),
     Post => Extends (Old, Upd)
             and then Count (Upd) = Count (Old) + (if In_W (Old, A) then 0 else 1);

   --  Distinct counting: two indices name two different keys.
   procedure Lemma_Distinct (R : Register_File; I, J : Writer_Index) with
     Ghost, Global => null,
     Pre  => Distinct (R) and then I <= Count (R) and then J <= Count (R)
             and then I /= J,
     Post => Writer (R, I) /= Writer (R, J);

   --  Ada "=" on a Register_File (a record with an array) is not logical
   --  equality for the prover (CONVENTIONS.md rule 1); this lemma turns it
   --  into the views.
   procedure Lemma_Eq (A, B : Register_File) with
     Ghost, Global => null,
     Pre  => A = B,
     Post => Ceil (A) = Ceil (B) and then Count (A) = Count (B)
             and then (for all I in 1 .. Count (A) => Writer (A, I) = Writer (B, I))
             and then Extends (A, B) and then Extends (B, A)
             and then Distinct (A) = Distinct (B);

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

   type Writer_Array is array (Writer_Index) of Key256;

   type Register_File is record
      C  : U48 := 0;
      NW : Writer_Count := 0;
      W  : Writer_Array := [others => (others => 0)];
   end record;

   function Ceil (R : Register_File) return U48 is (R.C);
   function Count (R : Register_File) return Writer_Count is (R.NW);
   function Writer (R : Register_File; I : Writer_Index) return Key256 is (R.W (I));

end Kome.Registers;
