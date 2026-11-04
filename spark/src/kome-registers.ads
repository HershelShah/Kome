--  Kome.Registers: the admission registers of one collection (DESIGN.md §3,
--  §4). They are the ceiling max-register `maxceil`, the writer set `W`
--  and the per-writer write cap `wcap` (AUDIT.md A1). Each register only
--  becomes wider. This makes admission monotone (T4').
--
--  This is a cache, not a second source of truth. maxceil(F), W(F) and
--  wcap(F, k) are views of the frontier: the largest ceiling_t of the held
--  rosters, the subjects of the held GRANTs, and the largest cap of the
--  held GRANTs of k. Kome.Frontier keeps a Register_File equal to those
--  views in each state, so admission reads them in constant time. Its
--  invariant `Coherent` and the lemmas Lemma_Ceil_Bound,
--  Lemma_Ceil_Witness, Lemma_W_Sound, Lemma_W_Complete, Lemma_W_Cap_Bound
--  and Lemma_W_Cap_Sound state this.
--
--  Count is the number of DISTINCT writers, and Empty has none. Add_Writer
--  appends a key only if the key is not already in W, and raises the key's
--  cap to the larger of the old cap and the new one. Its Post states Count
--  and W_Cap exactly. The capacity is Writers_Max = Signers_Max *
--  Slice_Max. W holds at most one subject for each held GRANT, so on a
--  frontier W never becomes full on its own (DESIGN.md §7). Add_Writer
--  requires room (or the key already present), and it never drops a key
--  silently (E2). The caller refuses with Auth_Full first.
--
--  The type is opaque, and `In_W`, `W_Cap`, `Extends` and `Added` are also
--  opaque. Other units reason about writers only through the lemmas. This
--  keeps each quantifier over the writer array in this package
--  (CONVENTIONS.md rule 2). (Frontier.lean models `W` as a list joined by
--  union and `wcap` as a maximum over it; `Extends` is list inclusion with
--  caps that do not go down.)
pragma Ada_2022;
package Kome.Registers with SPARK_Mode is

   type Writer_Count is range 0 .. Writers_Max;
   subtype Writer_Index is Writer_Count range 1 .. Writers_Max;

   type Register_File is private;

   function Ceil (R : Register_File) return U48 with Global => null;
   function Count (R : Register_File) return Writer_Count with Global => null;

   --  The I-th writer, in insertion order, and its cap.
   function Writer (R : Register_File; I : Writer_Index) return Key256 with
     Global => null,
     Pre    => I <= Count (R);

   function Cap_At (R : Register_File; I : Writer_Index) return U48 with
     Global => null,
     Pre    => I <= Count (R);

   function In_W (R : Register_File; A : Key256) return Boolean with Global => null;

   --  wcap(A): the cap of writer A (at its first index), 0 if A is not a
   --  writer. Admission reads it: a data record of A needs t <= W_Cap (A).
   function W_Cap (R : Register_File; A : Key256) return U48 with
     Global => null,
     Post   => (if not In_W (R, A) then W_Cap'Result = 0);

   --  Extends (A, B): every writer of A is a writer of B, with a cap at
   --  least as large.
   function Extends (A, B : Register_File) return Boolean with Global => null;

   --  No writer is listed twice, so Count is the number of distinct writers.
   function Distinct (R : Register_File) return Boolean with Global => null;

   --  Added (Old, Upd, A, Cap): Upd is Old with A added to W at cap Cap. If
   --  A was already in W, only its cap changes, to the larger value. Added
   --  is opaque; use Lemma_Added_In_W and Lemma_Added_Cap to read it.
   function Added (Old, Upd : Register_File; A : Key256; Cap : U48) return Boolean with
     Global => null;

   function Empty return Register_File with
     Global => null,
     Post   => Ceil (Empty'Result) = 0 and then Count (Empty'Result) = 0
               and then Distinct (Empty'Result);

   --  maxceil := max (maxceil, C). W and the caps do not change.
   procedure Raise_Ceiling (R : in out Register_File; C : U48) with
     Global => null,
     Post   => Ceil (R) = U48'Max (Ceil (R'Old), C)
               and then Count (R) = Count (R'Old)
               and then (for all I in 1 .. Count (R) =>
                           Writer (R, I) = Writer (R'Old, I)
                           and then Cap_At (R, I) = Cap_At (R'Old, I))
               and then Extends (R'Old, R) and then Extends (R, R'Old)
               and then (if Distinct (R'Old) then Distinct (R));

   --  W := W ∪ {A}, wcap(A) := max (wcap(A), Cap). This requires room,
   --  unless A is already a writer. The caller refuses first (Auth_Full),
   --  so the code never drops a key (E2).
   procedure Add_Writer (R : in out Register_File; A : Key256; Cap : U48) with
     Global => null,
     Pre    => In_W (R, A) or else Count (R) < Writers_Max,
     Post   => Ceil (R) = Ceil (R'Old)
               and then In_W (R, A)
               and then W_Cap (R, A) = U48'Max (W_Cap (R'Old, A), Cap)
               and then Extends (R'Old, R)
               and then Count (R) = Count (R'Old) + (if In_W (R'Old, A) then 0 else 1)
               and then Added (R'Old, R, A, Cap)
               and then (if Distinct (R'Old) then Distinct (R));

   --  The membership test is the existence of an index.
   procedure Lemma_In_W_Iff (R : Register_File; A : Key256) with
     Ghost, Global => null,
     Post => In_W (R, A) = (for some I in 1 .. Count (R) => Writer (R, I) = A);

   --  The cap of a writer is the cap at its first index.
   procedure Lemma_W_Cap_Def (R : Register_File; A : Key256) with
     Ghost, Global => null,
     Post => (if In_W (R, A)
              then (for some I in 1 .. Count (R) =>
                      Writer (R, I) = A and then Cap_At (R, I) = W_Cap (R, A))
              else W_Cap (R, A) = 0);

   procedure Lemma_Added_In_W (Old, Upd : Register_File; A : Key256; Cap : U48; K : Key256) with
     Ghost, Global => null,
     Pre  => Added (Old, Upd, A, Cap),
     Post => In_W (Upd, K) = (In_W (Old, K) or else K = A);

   procedure Lemma_Added_Cap (Old, Upd : Register_File; A : Key256; Cap : U48; K : Key256) with
     Ghost, Global => null,
     Pre  => Added (Old, Upd, A, Cap),
     Post => W_Cap (Upd, K) = (if K = A then U48'Max (W_Cap (Old, K), Cap) else W_Cap (Old, K));

   --  The addition of a writer that is already present, at a cap that is
   --  not larger, changes nothing (on a Distinct file, where the writer has
   --  one index).
   procedure Lemma_Added_Refl (R : Register_File; A : Key256; Cap : U48) with
     Ghost, Global => null,
     Pre  => Distinct (R) and then In_W (R, A) and then Cap <= W_Cap (R, A),
     Post => Added (R, R, A, Cap);

   --  Distinct counting: two indices name two different keys.
   procedure Lemma_Distinct (R : Register_File; I, J : Writer_Index) with
     Ghost, Global => null,
     Pre  => Distinct (R) and then I <= Count (R) and then J <= Count (R)
             and then I /= J,
     Post => Writer (R, I) /= Writer (R, J);

   --  Ada "=" on a Register_File (a record with arrays) is not logical
   --  equality for the prover (CONVENTIONS.md rule 1). This lemma converts
   --  it into the views.
   procedure Lemma_Eq (A, B : Register_File) with
     Ghost, Global => null,
     Pre  => A = B,
     Post => Ceil (A) = Ceil (B) and then Count (A) = Count (B)
             and then (for all I in 1 .. Count (A) =>
                         Writer (A, I) = Writer (B, I) and then Cap_At (A, I) = Cap_At (B, I))
             and then Extends (A, B) and then Extends (B, A)
             and then Distinct (A) = Distinct (B);

   procedure Lemma_Extends_Refl (A : Register_File) with
     Ghost, Global => null,
     Post => Extends (A, A);

   procedure Lemma_Extends_In_W (A, B : Register_File; X : Key256) with
     Ghost, Global => null,
     Pre  => Extends (A, B) and then In_W (A, X),
     Post => In_W (B, X) and then W_Cap (B, X) >= W_Cap (A, X);

private

   type Writer_Array is array (Writer_Index) of Key256;
   type Cap_Array is array (Writer_Index) of U48;

   type Register_File is record
      C  : U48 := 0;
      NW : Writer_Count := 0;
      W  : Writer_Array := [others => (others => 0)];
      WC : Cap_Array := [others => 0];
   end record;

   function Ceil (R : Register_File) return U48 is (R.C);
   function Count (R : Register_File) return Writer_Count is (R.NW);
   function Writer (R : Register_File; I : Writer_Index) return Key256 is (R.W (I));
   function Cap_At (R : Register_File; I : Writer_Index) return U48 is (R.WC (I));

end Kome.Registers;
