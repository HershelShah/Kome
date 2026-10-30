/-
The frontier store: the model of docs/redesign/DESIGN.md.

A replica holds a finite set of signed records. Its state is the FRONTIER of
that set: the records not dominated by a newer one, under one strict total
order on versions. Admission (the far-future ceiling) is a monotone filter;
revocation is a view flag; nothing else exists.

Sets are modelled as lists up to membership (order and duplication are the
things the theorems must not depend on, so the statements are all of the form
`x ∈ F A ↔ x ∈ F B`). Identifiers, authors, values and hashes are `Nat`: every
theorem uses only decidable equality and, for versions, a total order.

Theorem numbers refer to DESIGN.md §9.
-/
import Kome.LWW

namespace Kome.Frontier

/-! ### Versions (T1) -/

/-- `v = (t, author, seq, h)`, compared lexicographically. `h` is the record's
content hash, so distinct records never tie. -/
structure Version where
  t : Nat
  author : Nat
  seq : Nat
  h : Nat
deriving DecidableEq, Repr

def Version.lt (a b : Version) : Prop :=
  a.t < b.t ∨ (a.t = b.t ∧
    (a.author < b.author ∨ (a.author = b.author ∧
      (a.seq < b.seq ∨ (a.seq = b.seq ∧ a.h < b.h)))))

instance (a b : Version) : Decidable (Version.lt a b) := by
  unfold Version.lt; exact inferInstance

theorem Version.lt_irrefl (a : Version) : ¬ Version.lt a a := by
  unfold Version.lt; omega

theorem Version.lt_trans {a b c : Version} (h₁ : Version.lt a b) (h₂ : Version.lt b c) :
    Version.lt a c := by
  unfold Version.lt at *; omega

theorem Version.lt_trichotomy (a b : Version) :
    Version.lt a b ∨ a = b ∨ Version.lt b a := by
  obtain ⟨t, au, s, h⟩ := a
  obtain ⟨t', au', s', h'⟩ := b
  simp only [Version.lt, Version.mk.injEq]
  omega

/-- T1: the version order is a strict total order. -/
instance : StrictTotal Version where
  lt := Version.lt
  dec := fun _ _ => inferInstance
  irrefl := Version.lt_irrefl
  trans := Version.lt_trans
  trichotomy := Version.lt_trichotomy

/-! ### Records -/

/-- One collection's records. `put`/`del` carry a version; `roster` carries
the generation, the ceiling and its own hash (its domination key); `revoke`
is never dominated. -/
inductive Record where
  | put (ent field : Nat) (v : Version) (value : Nat)
  | del (ent : Nat) (v : Version)
  | roster (gen ceiling h : Nat)
  | revoke (author fromT revSeq : Nat)
deriving DecidableEq, Repr

open Record

/-- `dominates q p`: `q` dominates `p` (DESIGN.md §3, `dom`'s witness). -/
def dominates : Record → Record → Bool
  | put e' f' v' _, put e f v _ => decide (e = e' ∧ f = f' ∧ Version.lt v v')
  | del e' v',      put e _ v _ => decide (e = e' ∧ Version.lt v v')
  | del e' v',      del e v     => decide (e = e' ∧ Version.lt v v')
  | roster g' _ h', roster g _ h => decide (g < g' ∨ (g = g' ∧ h < h'))
  | _, _ => false

theorem dominates_irrefl (x : Record) : dominates x x = false := by
  cases x <;> simp [dominates, Version.lt] <;> omega

/-- T2' (upward closure): a dominator of a dominator is a dominator. This is
the lemma the frontier homomorphism rests on, and the reason `revoke` must not
dominate anything. -/
theorem dominates_trans {x y z : Record} (hyx : dominates y x = true)
    (hzy : dominates z y = true) : dominates z x = true := by
  cases x <;> cases y <;> cases z <;>
    simp only [dominates, decide_eq_true_eq, Bool.false_eq_true] at * <;>
    (try simp only [Version.lt] at *) <;> omega

/-- T12 (part): a revocation is never dominated. -/
theorem revoke_never_dominated (q : Record) (a f s : Nat) :
    dominates q (revoke a f s) = false := by
  cases q <;> simp [dominates]

/-! ### Domination and the frontier -/

/-- `x` is dominated by something in `H`. -/
def Dom (x : Record) (H : List Record) : Prop := ∃ q, q ∈ H ∧ dominates q x = true

def dom (x : Record) (H : List Record) : Bool := H.any (fun q => dominates q x)

theorem dom_eq_true_iff {x : Record} {H : List Record} : dom x H = true ↔ Dom x H := by
  simp [dom, Dom, List.any_eq_true]

/-- T2: domination is monotone in the held set. -/
theorem Dom_mono {x : Record} {H H' : List Record} (hd : Dom x H) (hs : H ⊆ H') : Dom x H' :=
  let ⟨q, hq, hqx⟩ := hd
  ⟨q, hs hq, hqx⟩

theorem Dom_congr {x : Record} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') :
    Dom x H ↔ Dom x H' :=
  ⟨fun ⟨q, hq, hqx⟩ => ⟨q, (h q).mp hq, hqx⟩, fun ⟨q, hq, hqx⟩ => ⟨q, (h q).mpr hq, hqx⟩⟩

/-- The frontier: the records of `H` not dominated within `H`. This is the state. -/
def F (H : List Record) : List Record := H.filter (fun x => !dom x H)

theorem mem_F_iff {x : Record} {H : List Record} : x ∈ F H ↔ x ∈ H ∧ ¬ Dom x H := by
  unfold F
  rw [List.mem_filter]
  constructor
  · rintro ⟨hx, hb⟩
    refine ⟨hx, ?_⟩
    rw [← dom_eq_true_iff]
    intro hd
    rw [hd] at hb
    exact Bool.false_ne_true hb
  · rintro ⟨hx, hnd⟩
    refine ⟨hx, ?_⟩
    have hfalse : dom x H = false := by
      cases hb : dom x H
      · rfl
      · exact absurd (dom_eq_true_iff.mp hb) hnd
    rw [hfalse]
    rfl

theorem F_subset (H : List Record) : F H ⊆ H :=
  fun _ hx => (mem_F_iff.mp hx).1

theorem F_congr {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (x : Record) :
    x ∈ F H ↔ x ∈ F H' := by
  rw [mem_F_iff, mem_F_iff, h x, Dom_congr h]

/-- Every dominated record has a dominator that is itself undominated: pick a
maximal one. Finite sets under a strict order always have one. -/
theorem exists_max_dominator :
    ∀ (H : List Record) (x : Record), Dom x H →
      ∃ y, y ∈ H ∧ dominates y x = true ∧ ¬ Dom y H := by
  intro H
  induction H with
  | nil =>
    intro x hx
    obtain ⟨q, hq, _⟩ := hx
    exact absurd hq List.not_mem_nil
  | cons q H' ih =>
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hx
    by_cases hx' : Dom x H'
    · obtain ⟨y, hy, hyx, hymax⟩ := ih x hx'
      by_cases hqy : dominates q y = true
      · refine ⟨q, List.mem_cons.mpr (Or.inl rfl), dominates_trans hyx hqy, ?_⟩
        rintro ⟨z, hz, hzq⟩
        rcases List.mem_cons.mp hz with hzq' | hz'
        · rw [hzq', dominates_irrefl] at hzq
          exact Bool.false_ne_true hzq
        · exact hymax ⟨z, hz', dominates_trans hqy hzq⟩
      · refine ⟨y, List.mem_cons.mpr (Or.inr hy), hyx, ?_⟩
        rintro ⟨z, hz, hzy⟩
        rcases List.mem_cons.mp hz with hzq' | hz'
        · rw [hzq'] at hzy
          exact hqy hzy
        · exact hymax ⟨z, hz', hzy⟩
    · have hdq : d = q := by
        rcases List.mem_cons.mp hd with h | h
        · exact h
        · exact absurd ⟨d, h, hdx⟩ hx'
      have hqx : dominates q x = true := hdq ▸ hdx
      refine ⟨q, List.mem_cons.mpr (Or.inl rfl), hqx, ?_⟩
      rintro ⟨z, hz, hzq⟩
      rcases List.mem_cons.mp hz with hzq' | hz'
      · rw [hzq', dominates_irrefl] at hzq
        exact Bool.false_ne_true hzq
      · exact hx' ⟨z, hz', dominates_trans hqx hzq⟩

/-- The sandwich lemma: a subset that still contains the whole frontier has
the same frontier. Every GC theorem below is an instance of it. -/
theorem F_sandwich {A A' : List Record} (h1 : ∀ x, x ∈ F A → x ∈ A')
    (h2 : ∀ x, x ∈ A' → x ∈ A) (x : Record) : x ∈ F A' ↔ x ∈ F A := by
  rw [mem_F_iff, mem_F_iff]
  constructor
  · rintro ⟨hx, hnd⟩
    refine ⟨h2 x hx, ?_⟩
    intro hd
    obtain ⟨y, hy, hyx, hymax⟩ := exists_max_dominator A x hd
    exact hnd ⟨y, h1 y (mem_F_iff.mpr ⟨hy, hymax⟩), hyx⟩
  · rintro ⟨hx, hnd⟩
    refine ⟨h1 x (mem_F_iff.mpr ⟨hx, hnd⟩), ?_⟩
    rintro ⟨y, hy, hyx⟩
    exact hnd ⟨y, h2 y hy, hyx⟩

/-- Dropping dominated records from a prefix does not change the frontier. -/
theorem F_prefix (s t : List Record) (x : Record) : x ∈ F (F s ++ t) ↔ x ∈ F (s ++ t) := by
  apply F_sandwich
  · intro y hy
    obtain ⟨hy, hnd⟩ := mem_F_iff.mp hy
    rw [List.mem_append] at hy ⊢
    rcases hy with h | h
    · exact Or.inl (mem_F_iff.mpr ⟨h, fun hd => hnd (Dom_mono hd (List.subset_append_left _ _))⟩)
    · exact Or.inr h
  · intro y hy
    rw [List.mem_append] at hy ⊢
    rcases hy with h | h
    · exact Or.inl (F_subset s h)
    · exact Or.inr h

theorem F_suffix (s t : List Record) (x : Record) : x ∈ F (s ++ F t) ↔ x ∈ F (s ++ t) := by
  apply F_sandwich
  · intro y hy
    obtain ⟨hy, hnd⟩ := mem_F_iff.mp hy
    rw [List.mem_append] at hy ⊢
    rcases hy with h | h
    · exact Or.inl h
    · exact Or.inr (mem_F_iff.mpr ⟨h, fun hd => hnd (Dom_mono hd (List.subset_append_right _ _))⟩)
  · intro y hy
    rw [List.mem_append] at hy ⊢
    rcases hy with h | h
    · exact Or.inl h
    · exact Or.inr (F_subset t h)

/-- T3 (frontier homomorphism): `F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))`. Dominated
records may be dropped anywhere, at any time, on any subset of replicas. -/
theorem frontier_hom (H₁ H₂ : List Record) (x : Record) :
    x ∈ F (F H₁ ++ F H₂) ↔ x ∈ F (H₁ ++ H₂) := by
  rw [F_prefix H₁ (F H₂) x, F_suffix H₁ H₂ x]

/-- T3 (idempotence). -/
theorem F_idem (H : List Record) (x : Record) : x ∈ F (F H) ↔ x ∈ F H := by
  apply F_sandwich
  · intro y hy; exact hy
  · intro y hy; exact F_subset H hy

/-! ### T4 without admission: apply-with-GC in any order -/

/-- Apply one record and drop what it dominates (and what dominates nothing new). -/
def applyF (S : List Record) (r : Record) : List Record := F (S ++ [r])

def applyAllF (S : List Record) (l : List Record) : List Record := l.foldl applyF S

/-- Applying with GC after every record yields the frontier of the whole set. -/
theorem applyAllF_mem (l : List Record) :
    ∀ (s : List Record) (x : Record), x ∈ applyAllF (F s) l ↔ x ∈ F (s ++ l) := by
  induction l with
  | nil =>
    intro s x
    show x ∈ F s ↔ x ∈ F (s ++ [])
    rw [List.append_nil]
  | cons r l ih =>
    intro s x
    show x ∈ applyAllF (F (F s ++ [r])) l ↔ x ∈ F (s ++ r :: l)
    rw [ih (F s ++ [r]) x, List.append_assoc, List.singleton_append, F_prefix]

/-- T4 (no admission): two replicas that applied the same set of records, in
any order, with any duplication, from the same start, hold the same frontier. -/
theorem convergence_F {l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') (s : List Record)
    (x : Record) : x ∈ applyAllF (F s) l ↔ x ∈ applyAllF (F s) l' := by
  rw [applyAllF_mem, applyAllF_mem]
  apply F_congr
  intro y
  rw [List.mem_append, List.mem_append, h y]

/-! ### Admission by the ceiling (T4', T9) -/

def ceilOf : Record → Nat
  | roster _ ce _ => ce
  | _ => 0

/-- A data record is admitted iff its `t` is at most the ceiling; authorization
records always are. -/
def adm (c : Nat) : Record → Bool
  | put _ _ v _ => decide (v.t ≤ c)
  | del _ v => decide (v.t ≤ c)
  | _ => true

/-- T4': admission is monotone in the ceiling. -/
theorem adm_mono {c c' : Nat} (h : c ≤ c') {r : Record} (ha : adm c r = true) :
    adm c' r = true := by
  cases r <;> simp [adm] at * <;> omega

/-- T9: no admitted data record is above the ceiling. -/
theorem adm_put_le {c e f : Nat} {v : Version} {x : Nat} (h : adm c (put e f v x) = true) :
    v.t ≤ c := by
  simp [adm] at h; exact h

def admitted (c : Nat) (H : List Record) : List Record := H.filter (adm c)

theorem mem_admitted {c : Nat} {H : List Record} {x : Record} :
    x ∈ admitted c H ↔ x ∈ H ∧ adm c x = true := List.mem_filter

/-- A replica: the records it holds and its ceiling max-register. -/
structure State where
  held : List Record
  ceil : Nat

/-- What the replica presents: the frontier of its admitted records. -/
def view (S : State) : List Record := F (admitted S.ceil S.held)

/-- GC relative to the admitted set: keep what no admitted record dominates. -/
def keep (c : Nat) (U : List Record) : List Record :=
  U.filter (fun x => !dom x (admitted c U))

theorem mem_keep {c : Nat} {U : List Record} {x : Record} :
    x ∈ keep c U ↔ x ∈ U ∧ ¬ Dom x (admitted c U) := by
  unfold keep
  rw [List.mem_filter]
  constructor
  · rintro ⟨hx, hb⟩
    refine ⟨hx, ?_⟩
    rw [← dom_eq_true_iff]
    intro hd
    rw [hd] at hb
    exact Bool.false_ne_true hb
  · rintro ⟨hx, hnd⟩
    refine ⟨hx, ?_⟩
    have hfalse : dom x (admitted c U) = false := by
      cases hb : dom x (admitted c U)
      · rfl
      · exact absurd (dom_eq_true_iff.mp hb) hnd
    rw [hfalse]
    rfl

/-- Apply one record: raise the ceiling if it is a roster, then GC. -/
def applyA (S : State) (r : Record) : State :=
  ⟨keep (max S.ceil (ceilOf r)) (S.held ++ [r]), max S.ceil (ceilOf r)⟩

def applyAllA (S : State) (l : List Record) : State := l.foldl applyA S

/-- The ceiling after applying `l` from `c`. -/
def ceilAll (c : Nat) : List Record → Nat
  | [] => c
  | r :: l => ceilAll (max c (ceilOf r)) l

theorem le_ceilAll (c : Nat) (l : List Record) : c ≤ ceilAll c l := by
  induction l generalizing c with
  | nil => exact Nat.le_refl c
  | cons r l ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem mem_append_cons {y r : Record} {s l : List Record} :
    y ∈ s ++ r :: l ↔ y ∈ s ++ [r] ∨ y ∈ l := by
  simp [List.mem_append, or_assoc]

/-- T4 with admission and GC: whatever the order of arrival, the view is the
frontier of the admitted records under the final ceiling. Inadmissible
records are held (never dominated by an admitted one) and surface once the
ceiling rises; dropping a record dominated by an admitted one is safe forever
because admission is monotone. -/
theorem applyAllA_view (l : List Record) :
    ∀ (s : List Record) (c : Nat) (x : Record),
      x ∈ view (applyAllA ⟨s, c⟩ l) ↔ x ∈ F (admitted (ceilAll c l) (s ++ l)) := by
  induction l with
  | nil =>
    intro s c x
    show x ∈ F (admitted c s) ↔ x ∈ F (admitted c (s ++ []))
    rw [List.append_nil]
  | cons r l ih =>
    intro s c x
    show x ∈ view (applyAllA ⟨keep (max c (ceilOf r)) (s ++ [r]), max c (ceilOf r)⟩ l) ↔
      x ∈ F (admitted (ceilAll (max c (ceilOf r)) l) (s ++ r :: l))
    rw [ih]
    have hc : max c (ceilOf r) ≤ ceilAll (max c (ceilOf r)) l := le_ceilAll _ _
    apply F_sandwich
    · intro y hy
      obtain ⟨hyA, hnd⟩ := mem_F_iff.mp hy
      obtain ⟨hyU, hadm⟩ := mem_admitted.mp hyA
      rw [mem_admitted, List.mem_append]
      refine ⟨?_, hadm⟩
      rcases mem_append_cons.mp hyU with hsr | hl
      · left
        rw [mem_keep]
        refine ⟨hsr, ?_⟩
        rintro ⟨z, hz, hzy⟩
        obtain ⟨hzU, hzadm⟩ := mem_admitted.mp hz
        apply hnd
        refine ⟨z, mem_admitted.mpr ⟨?_, adm_mono hc hzadm⟩, hzy⟩
        exact mem_append_cons.mpr (Or.inl hzU)
      · exact Or.inr hl
    · intro y hy
      obtain ⟨hyU, hadm⟩ := mem_admitted.mp hy
      rw [mem_admitted]
      refine ⟨?_, hadm⟩
      rw [List.mem_append] at hyU
      rcases hyU with hk | hl
      · exact mem_append_cons.mpr (Or.inl (mem_keep.mp hk).1)
      · exact mem_append_cons.mpr (Or.inr hl)

/-- The ceiling reached depends only on which rosters were applied. -/
def maxCeil : List Record → Nat
  | [] => 0
  | r :: l => max (ceilOf r) (maxCeil l)

theorem ceilAll_eq (c : Nat) (l : List Record) : ceilAll c l = max c (maxCeil l) := by
  induction l generalizing c with
  | nil => simp [ceilAll, maxCeil]
  | cons r l ih => simp only [ceilAll, maxCeil]; rw [ih]; omega

theorem maxCeil_ge {r : Record} {l : List Record} (h : r ∈ l) : ceilOf r ≤ maxCeil l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons q l ih =>
    simp only [maxCeil]
    rcases List.mem_cons.mp h with hq | hl
    · rw [hq]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hl) (Nat.le_max_right _ _)

theorem maxCeil_le {l : List Record} {m : Nat} (h : ∀ r, r ∈ l → ceilOf r ≤ m) :
    maxCeil l ≤ m := by
  induction l with
  | nil => exact Nat.zero_le m
  | cons q l ih =>
    simp only [maxCeil]
    exact Nat.max_le.mpr ⟨h q (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun r hr => h r (List.mem_cons.mpr (Or.inr hr)))⟩

theorem maxCeil_congr {l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') : maxCeil l = maxCeil l' :=
  Nat.le_antisymm
    (maxCeil_le fun r hr => maxCeil_ge ((h r).mp hr))
    (maxCeil_le fun r hr => maxCeil_ge ((h r).mpr hr))

/-- T4 (full): two replicas that applied the same set of records, in any order
and with any duplication, from the same start, present the same view and hold
the same ceiling. -/
theorem convergence {l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') (s : List Record)
    (c : Nat) (x : Record) :
    x ∈ view (applyAllA ⟨s, c⟩ l) ↔ x ∈ view (applyAllA ⟨s, c⟩ l') := by
  rw [applyAllA_view, applyAllA_view, ceilAll_eq, ceilAll_eq, maxCeil_congr h]
  apply F_congr
  intro y
  rw [mem_admitted, mem_admitted, List.mem_append, List.mem_append, h y]

/-! ### T5: one value per cell -/

/-- Two frontier PUTs on one cell with versions that are equal only when the
records are (hash injectivity) are the same record: there is one value per
cell. -/
theorem cell_unique {H : List Record} {e f : Nat} {vx vy : Version} {ax ay : Nat}
    (hx : put e f vx ax ∈ F H) (hy : put e f vy ay ∈ F H)
    (hinj : vx = vy → put e f vx ax = put e f vy ay) :
    put e f vx ax = put e f vy ay := by
  rcases Version.lt_trichotomy vx vy with hlt | heq | hgt
  · exact absurd ⟨put e f vy ay, (mem_F_iff.mp hy).1, by simp [dominates, hlt]⟩
      (mem_F_iff.mp hx).2
  · exact hinj heq
  · exact absurd ⟨put e f vx ax, (mem_F_iff.mp hx).1, by simp [dominates, hgt]⟩
      (mem_F_iff.mp hy).2

/-! ### T8: the chase -/

/-- The emitted `t`: the wall clock, or just above the cell's floor, capped at
the ceiling. -/
def emitT (now floorT c : Nat) : Nat := min (max now (floorT + 1)) c

/-- T8: below the ceiling, a local write beats the cell's floor on `t` alone,
whatever the authors (read-your-writes). -/
theorem chase {now floorT c : Nat} (h : floorT < c) : floorT < emitT now floorT c := by
  unfold emitT; omega

/-- T13 (part): the emitted `t` never exceeds the ceiling. -/
theorem emitT_le (now floorT c : Nat) : emitT now floorT c ≤ c := by
  unfold emitT; omega

end Kome.Frontier
