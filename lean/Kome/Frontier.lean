/-
The frontier store: the model of docs/design/DESIGN.md (round three).

A replica of one collection holds a finite set of signed records. Its state
is the FRONTIER of that set: the records not dominated by another record of
the set (§3). There are five record kinds (§2): the data records `put` and
`del`, versioned by `(t, author, seq, h)` under one strict total order; and
the authorization records `roster` (per signer, with its ceiling, generation
and tombstone lifetime), `revoke` (issuer, subject, `from_t`) and `grant`
(issuer, subject). Domination is per key: a `put` by a newer `put` of its
cell or a newer `del` of its entity, a `del` by a newer `del`, a roster by a
roster of the same signer that is greater in `(gen, h)` and not lower in
ceiling (a product order), a grant by a grant of the same issuer and subject
with a greater hash. A `revoke` is never dominated and dominates nothing.

Admission (§4) is a function of the authorization records alone: a data
record is admitted iff its `t` is at most `maxceil` (the largest roster
ceiling) and its author is in `W` (the subjects of the grants). Both
registers are functions of the frontier that never shrink (T4'), so
admission is monotone; it never reads `revoke`, `root_void` or `W_eff`.
Inadmissible records are discarded, not held (§4, §10.1), and convergence
(T4) is stated for that model: one authorization-first pass (the shape of a
batch and of replay after compaction, T18), or two passes in any order.
Tombstone expiry (§7, T11) is an operation on the state that removes `del`s
at or below a horizon. Revocation is a set of views (§3, §6; T5, T12):
`root_void`, the effective-writer view `W_eff`, `void`, `ROSTER_eff` (the
maximum under the whole roster tuple, so it does not depend on list order)
and `del_ttl_eff`; none of them feeds admission.

Scope. The model assumes well-formed records. Who may sign an authorization
record (the founding key, or a root it certified) is checked on the
record's bytes, by its certificate (DESIGN §2), and is not modelled: every
record here is taken to be well-formed. Capacity (data capacity, the
per-signer slices, `NO_SPACE`, `AUTH_FULL`), the clock clamp of the horizon
(`min(now_local, maxceil) − del_ttl_eff`: the horizon is a parameter here,
computed outside the model) and assumption A7 (revocation arrives first)
are outside the model.

Sets are modelled as lists up to membership (order and duplication are the
things the theorems must not depend on, so the statements are all of the form
`x ∈ A ↔ x ∈ B`). Identifiers, authors, values and hashes are `Nat`: every
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

/-! ### Records (DESIGN §2, §3) -/

/-- One collection's records, reduced to what the lattice and the views read.
`put`/`del` carry a version. `roster` carries its signer, its ceiling, its
generation, its `del_ttl` and its hash; `revoke` its issuer, its subject,
`from_t`, `rev_seq` and its hash; `grant` its issuer, its subject and its
hash. -/
inductive Record where
  | put (ent field : Nat) (v : Version) (value : Nat)
  | del (ent : Nat) (v : Version)
  | roster (signer ceil gen ttl h : Nat)
  | revoke (issuer subject fromT revSeq h : Nat)
  | grant (issuer subject h : Nat)
deriving DecidableEq, Repr

open Record

/-- `dominates q p`: `q` dominates `p` (DESIGN.md §3, `dom`'s witness). Rosters
are compared by the product order (R4): same signer, ceiling not lower, and
greater in `(gen, h)`. Grants are keyed by `(issuer, subject)`. Nothing else
dominates: `revoke` is never dominated and never dominates, and there is no
cross-kind clause for authorization records. -/
def dominates : Record → Record → Bool
  | put e' f' v' _, put e f v _ => decide (e = e' ∧ f = f' ∧ Version.lt v v')
  | del e' v',      put e _ v _ => decide (e = e' ∧ Version.lt v v')
  | del e' v',      del e v     => decide (e = e' ∧ Version.lt v v')
  | roster s' c' g' _ h', roster s c g _ h =>
      decide (s = s' ∧ c ≤ c' ∧ (g < g' ∨ (g = g' ∧ h < h')))
  | grant i' j' h', grant i j h => decide (i = i' ∧ j = j' ∧ h < h')
  | _, _ => false

theorem dominates_irrefl (x : Record) : dominates x x = false := by
  cases x <;> simp [dominates, Version.lt] <;> omega

/-- T2' (upward closure): a dominator of a dominator is a dominator, for every
kind triple. This is the lemma the frontier homomorphism rests on, and the
reason `revoke` must not dominate anything. -/
theorem dominates_trans {x y z : Record} (hyx : dominates y x = true)
    (hzy : dominates z y = true) : dominates z x = true := by
  cases x <;> cases y <;> cases z <;>
    simp only [dominates, decide_eq_true_eq, Bool.false_eq_true] at * <;>
    (try simp only [Version.lt] at *) <;> omega

/-- T12 (part): a revocation is never dominated. -/
theorem revoke_never_dominated (q : Record) (i s f r h : Nat) :
    dominates q (revoke i s f r h) = false := by
  cases q <;> simp [dominates]

/-- A revocation dominates nothing. -/
theorem revoke_never_dominates (x : Record) (i s f r h : Nat) :
    dominates (revoke i s f r h) x = false := by
  cases x <;> simp [dominates]

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

/-- `y` is held in `T` or dominated by something held in `T`: nothing that
was in a set and is "covered" by `T` can resurface against `T`. -/
def Cov (y : Record) (T : List Record) : Prop := y ∈ T ∨ Dom y T

theorem Cov_mono {y : Record} {T T' : List Record} (h : Cov y T) (hs : T ⊆ T') : Cov y T' :=
  h.elim (fun hy => Or.inl (hs hy)) (fun hd => Or.inr (Dom_mono hd hs))

/-- A record dominated in `H` is dominated in `F H` (by a maximal dominator). -/
theorem Dom_F {y : Record} {H : List Record} (hd : Dom y H) : Dom y (F H) := by
  obtain ⟨z, hz, hzy, hzmax⟩ := exists_max_dominator H y hd
  exact ⟨z, mem_F_iff.mpr ⟨hz, hzmax⟩, hzy⟩

/-- `F H` covers every record of `H`. -/
theorem F_covers {y : Record} {H : List Record} (hy : y ∈ H) : Cov y (F H) := by
  by_cases hd : Dom y H
  · exact Or.inr (Dom_F hd)
  · exact Or.inl (mem_F_iff.mpr ⟨hy, hd⟩)

theorem Cov_F {y : Record} {H : List Record} (h : Cov y H) : Cov y (F H) :=
  h.elim (fun hy => F_covers hy) (fun hd => Or.inr (Dom_F hd))

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

/-! ### Kinds, and what dominates what -/

/-- The authorization kinds. -/
def isAuth : Record → Bool
  | roster .. => true
  | revoke .. => true
  | grant .. => true
  | _ => false

/-- A dominator of an authorization record is an authorization record (in
fact of the same kind and issuer). -/
theorem dominates_auth {q y : Record} (hy : isAuth y = true) (h : dominates q y = true) :
    isAuth q = true := by
  cases y <;> cases q <;> simp [isAuth, dominates] at hy h ⊢

/-- An authorization record dominates no data record (T12). -/
theorem auth_not_dominates_data {q y : Record} (hq : isAuth q = true) (hy : isAuth y = false) :
    dominates q y = false := by
  cases q <;> cases y <;> simp [isAuth, dominates] at hq hy ⊢

theorem dominates_grant {q : Record} {i k h : Nat} (hq : dominates q (grant i k h) = true) :
    ∃ h', q = grant i k h' := by
  cases q with
  | grant i' k' h' =>
    simp only [dominates, decide_eq_true_eq] at hq
    obtain ⟨rfl, rfl, _⟩ := hq
    exact ⟨h', rfl⟩
  | _ => simp [dominates] at hq

theorem dominates_roster {q : Record} {s c g t h : Nat}
    (hq : dominates q (roster s c g t h) = true) :
    ∃ c' g' t' h', q = roster s c' g' t' h' ∧ c ≤ c' ∧ (g < g' ∨ (g = g' ∧ h < h')) := by
  cases q with
  | roster s' c' g' t' h' =>
    simp only [dominates, decide_eq_true_eq] at hq
    obtain ⟨rfl, hc, hg⟩ := hq
    exact ⟨c', g', t', h', rfl, hc, hg⟩
  | _ => simp [dominates] at hq

/-! ### Derived registers: `maxceil` and `W` (§3, T4') -/

def ceilOf : Record → Nat
  | roster _ c _ _ _ => c
  | _ => 0

theorem ceilOf_of_not_auth {r : Record} (h : isAuth r = false) : ceilOf r = 0 := by
  cases r <;> simp [isAuth, ceilOf] at h ⊢

/-- A dominator's ceiling is at least the dominated record's (the product
order on rosters; every other kind has ceiling 0). -/
theorem dominates_ceil {q y : Record} (h : dominates q y = true) : ceilOf y ≤ ceilOf q := by
  cases y <;> cases q <;> simp [dominates, ceilOf] at h ⊢ <;> omega

/-- `maxceil`: the largest roster ceiling, 0 if there is none. -/
def maxCeil : List Record → Nat
  | [] => 0
  | r :: l => max (ceilOf r) (maxCeil l)

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

/-- `k ∈ W(H)`: some grant in `H` names `k`. -/
def isWriter (H : List Record) (k : Nat) : Prop := ∃ i hh, grant i k hh ∈ H

/-- The grant-to-`k` test. -/
def grantsTo (k : Nat) : Record → Bool
  | grant _ j _ => decide (j = k)
  | _ => false

/-- `W` as a Boolean test. -/
def writerB (H : List Record) (k : Nat) : Bool := H.any (grantsTo k)

theorem grantsTo_iff {k : Nat} {r : Record} : grantsTo k r = true ↔ ∃ i hh, r = grant i k hh := by
  cases r with
  | grant i j h =>
    simp only [grantsTo, decide_eq_true_eq]
    constructor
    · intro hj; subst hj; exact ⟨i, h, rfl⟩
    · rintro ⟨i', hh, he⟩; cases he; rfl
  | _ => simp [grantsTo]

theorem writerB_iff {H : List Record} {k : Nat} : writerB H k = true ↔ isWriter H k := by
  unfold writerB isWriter
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hg⟩
    obtain ⟨i, hh, rfl⟩ := grantsTo_iff.mp hg
    exact ⟨i, hh, hr⟩
  · rintro ⟨i, hh, hm⟩
    exact ⟨_, hm, grantsTo_iff.mpr ⟨i, hh, rfl⟩⟩

/-- If `T` holds only records of `U` and covers every authorization record of
`U`, the two have the same `maxceil`. -/
theorem maxCeil_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) : maxCeil T = maxCeil U := by
  apply Nat.le_antisymm
  · exact maxCeil_le fun r hr => maxCeil_ge (hsub r hr)
  · apply maxCeil_le
    intro r hr
    cases ha : isAuth r
    · rw [ceilOf_of_not_auth ha]; exact Nat.zero_le _
    · rcases hcov r hr ha with hT | ⟨q, hq, hqr⟩
      · exact maxCeil_ge hT
      · exact Nat.le_trans (dominates_ceil hqr) (maxCeil_ge hq)

/-- The same for `W`. -/
theorem isWriter_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) (k : Nat) : isWriter T k ↔ isWriter U k := by
  constructor
  · rintro ⟨i, hh, hm⟩; exact ⟨i, hh, hsub _ hm⟩
  · rintro ⟨i, hh, hm⟩
    rcases hcov _ hm rfl with hT | ⟨q, hq, hqg⟩
    · exact ⟨i, hh, hT⟩
    · obtain ⟨h', rfl⟩ := dominates_grant hqg
      exact ⟨i, h', hq⟩

theorem writerB_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) (k : Nat) : writerB T k = writerB U k :=
  Bool.eq_iff_iff.mpr (by rw [writerB_iff, writerB_iff]; exact isWriter_cover hsub hcov k)

/-- T4': `maxceil(F(H)) = maxceil(H)`. A dominated roster has an undominated
dominator, of the same signer and with a ceiling at least its own. -/
theorem maxCeil_F (H : List Record) : maxCeil (F H) = maxCeil H :=
  maxCeil_cover (fun _ hy => F_subset H hy) (fun _ hy _ => F_covers hy)

/-- T4': `W(F(H)) = W(H)`. A dominated grant has an undominated dominator with
the same issuer and subject. -/
theorem isWriter_F (H : List Record) (k : Nat) : isWriter (F H) k ↔ isWriter H k :=
  isWriter_cover (fun _ hy => F_subset H hy) (fun _ hy _ => F_covers hy) k

theorem maxCeil_mono_auth {H H' : List Record} (h : ∀ x ∈ H, isAuth x = true → x ∈ H') :
    maxCeil H ≤ maxCeil H' := by
  apply maxCeil_le
  intro r hr
  cases ha : isAuth r
  · rw [ceilOf_of_not_auth ha]; exact Nat.zero_le _
  · exact maxCeil_ge (h r hr ha)

theorem isWriter_mono_auth {H H' : List Record} (h : ∀ x ∈ H, isAuth x = true → x ∈ H')
    {k : Nat} (hw : isWriter H k) : isWriter H' k :=
  let ⟨i, hh, hm⟩ := hw
  ⟨i, hh, h _ hm rfl⟩

/-! ### Admission (§4; T4', T9) -/

/-- A data record is admitted iff its `t` is at most `maxceil` and its author
is in `W`; authorization records always are. Admission reads neither
`revoke`, nor `root_void`, nor `W_eff`. -/
def adm (H : List Record) : Record → Bool
  | put _ _ v _ => decide (v.t ≤ maxCeil H) && writerB H v.author
  | del _ v => decide (v.t ≤ maxCeil H) && writerB H v.author
  | _ => true

theorem adm_auth {H : List Record} {r : Record} (hr : isAuth r = true) : adm H r = true := by
  cases r <;> first | rfl | simp [isAuth] at hr

/-- Admission depends only on the authorization records, up to covering. -/
theorem adm_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) {r : Record} : adm T r = adm U r := by
  cases r <;> simp only [adm, maxCeil_cover hsub hcov, writerB_cover hsub hcov]

theorem adm_congr {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') {r : Record} :
    adm H r = adm H' r :=
  adm_cover (fun y hy => (h y).mp hy) (fun y hy _ => Or.inl ((h y).mpr hy))

/-- T4' (monotone admission): if every authorization record of `H` is in `H'`,
whatever `H` admits `H'` admits. -/
theorem adm_mono {H H' : List Record} (h : ∀ x ∈ H, isAuth x = true → x ∈ H') {r : Record}
    (ha : adm H r = true) : adm H' r = true := by
  have hc := maxCeil_mono_auth h
  have hw : ∀ k, writerB H k = true → writerB H' k = true :=
    fun k hk => writerB_iff.mpr (isWriter_mono_auth h (writerB_iff.mp hk))
  cases r with
  | put e f v x =>
    simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
    exact ⟨Nat.le_trans ha.1 hc, hw _ ha.2⟩
  | del e v =>
    simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
    exact ⟨Nat.le_trans ha.1 hc, hw _ ha.2⟩
  | _ => rfl

/-- T4': admission under the frontier is admission under the whole set. -/
theorem adm_F (H : List Record) {r : Record} : adm (F H) r = adm H r :=
  adm_cover (fun _ hy => F_subset H hy) (fun _ hy _ => F_covers hy)

/-- Data records do not change admission. -/
theorem adm_data_irrelevant {H D : List Record} (hD : ∀ x ∈ D, isAuth x = false) {r : Record} :
    adm (H ++ D) r = adm H r := by
  refine (adm_cover (T := H) (U := H ++ D) (fun y hy => List.mem_append_left _ hy) ?_).symm
  intro y hy ha
  rcases List.mem_append.mp hy with h | h
  · exact Or.inl h
  · rw [hD y h] at ha; exact absurd ha Bool.false_ne_true

/-- T9: no admitted data record is above the ceiling. -/
theorem adm_put_le {H : List Record} {e f : Nat} {v : Version} {x : Nat}
    (h : adm H (put e f v x) = true) : v.t ≤ maxCeil H := by
  simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

theorem adm_del_le {H : List Record} {e : Nat} {v : Version}
    (h : adm H (del e v) = true) : v.t ≤ maxCeil H := by
  simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

def admitted (H : List Record) : List Record := H.filter (adm H)

theorem mem_admitted {H : List Record} {x : Record} :
    x ∈ admitted H ↔ x ∈ H ∧ adm H x = true := List.mem_filter

/-! ### The discard model (§4, §10.1) -/

/-- Apply one record: an admitted record is added and the result reduced to
its frontier; an inadmissible record is discarded (it is re-offered later). -/
def applyD (S : List Record) (r : Record) : List Record := if adm S r then F (S ++ [r]) else S

def applyAllD (S : List Record) (l : List Record) : List Record := l.foldl applyD S

/-- `S` is its own frontier. -/
def Frontier (S : List Record) : Prop := ∀ x ∈ S, ¬ Dom x S

/-- Every record of `S` is admitted by `S`. -/
def Admitted (S : List Record) : Prop := ∀ x ∈ S, adm S x = true

theorem applyD_pos {S : List Record} {r : Record} (h : adm S r = true) :
    applyD S r = F (S ++ [r]) := by
  simp [applyD, h]

theorem applyD_neg {S : List Record} {r : Record} (h : adm S r = false) : applyD S r = S := by
  simp [applyD, h]

theorem applyAllD_cons (S : List Record) (r : Record) (l : List Record) :
    applyAllD S (r :: l) = applyAllD (applyD S r) l := rfl

theorem applyAllD_append (S l₁ l₂ : List Record) :
    applyAllD S (l₁ ++ l₂) = applyAllD (applyAllD S l₁) l₂ := by
  simp only [applyAllD, List.foldl_append]

theorem F_frontier (H : List Record) : Frontier (F H) :=
  fun _ hx hd => (mem_F_iff.mp hx).2 (Dom_mono hd (F_subset H))

theorem frontier_mem_F {S : List Record} (hF : Frontier S) {x : Record} : x ∈ F S ↔ x ∈ S :=
  ⟨fun hx => (mem_F_iff.mp hx).1, fun hx => mem_F_iff.mpr ⟨hx, hF x hx⟩⟩

theorem applyD_frontier {S : List Record} {r : Record} (hF : Frontier S) :
    Frontier (applyD S r) := by
  cases hr : adm S r
  · rw [applyD_neg hr]; exact hF
  · rw [applyD_pos hr]; exact F_frontier _

theorem applyD_admitted {S : List Record} {r : Record} (hA : Admitted S) :
    Admitted (applyD S r) := by
  cases hr : adm S r
  · rw [applyD_neg hr]; exact hA
  · rw [applyD_pos hr]
    intro x hx
    rw [adm_F]
    have hmono : ∀ y ∈ S, isAuth y = true → y ∈ S ++ [r] :=
      fun y hy _ => List.mem_append_left _ hy
    rcases List.mem_append.mp (F_subset _ hx) with hs | hs
    · exact adm_mono hmono (hA x hs)
    · rw [List.mem_singleton] at hs; subst hs; exact adm_mono hmono hr

theorem applyD_sub {S : List Record} {r y : Record} (hy : y ∈ applyD S r) : y ∈ S ∨ y = r := by
  cases hr : adm S r
  · rw [applyD_neg hr] at hy; exact Or.inl hy
  · rw [applyD_pos hr] at hy
    rcases List.mem_append.mp (F_subset _ hy) with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)

theorem applyD_cov {S : List Record} {r y : Record} (h : Cov y S) : Cov y (applyD S r) := by
  cases hr : adm S r
  · rw [applyD_neg hr]; exact h
  · rw [applyD_pos hr]; exact Cov_F (Cov_mono h (List.subset_append_left _ _))

theorem applyD_auth {S : List Record} {r : Record} (ha : isAuth r = true) :
    Cov r (applyD S r) := by
  rw [applyD_pos (adm_auth ha)]
  exact F_covers (List.mem_append_right _ (List.mem_singleton_self r))

theorem adm_applyD_mono {S : List Record} {r x : Record} (h : adm S x = true) :
    adm (applyD S r) x = true := by
  cases hr : adm S r
  · rw [applyD_neg hr]; exact h
  · rw [applyD_pos hr, adm_F]
    exact adm_mono (fun y hy _ => List.mem_append_left _ hy) h

theorem applyAllD_frontier {S : List Record} (l : List Record) (hF : Frontier S) :
    Frontier (applyAllD S l) := by
  induction l generalizing S with
  | nil => exact hF
  | cons r l ih => exact ih (applyD_frontier hF)

theorem applyAllD_admitted {S : List Record} (l : List Record) (hA : Admitted S) :
    Admitted (applyAllD S l) := by
  induction l generalizing S with
  | nil => exact hA
  | cons r l ih => exact ih (applyD_admitted hA)

theorem applyAllD_sub {S l : List Record} {y : Record} (hy : y ∈ applyAllD S l) :
    y ∈ S ∨ y ∈ l := by
  induction l generalizing S with
  | nil => exact Or.inl hy
  | cons r l ih =>
    rcases ih hy with h | h
    · rcases applyD_sub h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons.mpr (Or.inl h'))
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem applyAllD_cov {S l : List Record} {y : Record} (h : Cov y S) :
    Cov y (applyAllD S l) := by
  induction l generalizing S with
  | nil => exact h
  | cons r l ih => exact ih (applyD_cov h)

/-- Every authorization record applied stays covered: it is never discarded. -/
theorem applyAllD_auth {S l : List Record} {y : Record} (hy : y ∈ l) (ha : isAuth y = true) :
    Cov y (applyAllD S l) := by
  induction l generalizing S with
  | nil => exact absurd hy List.not_mem_nil
  | cons r l ih =>
    rcases List.mem_cons.mp hy with h | h
    · subst h; rw [applyAllD_cons]; exact applyAllD_cov (applyD_auth ha)
    · exact ih h

theorem adm_applyAllD_mono {S : List Record} (l : List Record) {x : Record}
    (h : adm S x = true) : adm (applyAllD S l) x = true := by
  induction l generalizing S with
  | nil => exact h
  | cons r l ih => exact ih (adm_applyD_mono h)

/-- The sandwich lemma under a filter that passes the whole prefix. -/
theorem F_prefix_filter (A : Record → Bool) (s t : List Record) (hs : ∀ y ∈ s, A y = true)
    (x : Record) : x ∈ F ((F s ++ t).filter A) ↔ x ∈ F ((s ++ t).filter A) := by
  apply F_sandwich
  · intro y hy
    obtain ⟨hy, hnd⟩ := mem_F_iff.mp hy
    obtain ⟨hy, hA⟩ := List.mem_filter.mp hy
    refine List.mem_filter.mpr ⟨?_, hA⟩
    rcases List.mem_append.mp hy with h | h
    · refine List.mem_append_left _ (mem_F_iff.mpr ⟨h, fun hd => hnd ?_⟩)
      obtain ⟨q, hq, hqy⟩ := hd
      exact ⟨q, List.mem_filter.mpr ⟨List.mem_append_left _ hq, hs q hq⟩, hqy⟩
    · exact List.mem_append_right _ h
  · intro y hy
    obtain ⟨hy, hA⟩ := List.mem_filter.mp hy
    refine List.mem_filter.mpr ⟨?_, hA⟩
    rcases List.mem_append.mp hy with h | h
    · exact List.mem_append_left _ (F_subset s h)
    · exact List.mem_append_right _ h

/-- A pass in which admission is already fixed: from a state that holds only
records of `U` and covers every authorization record of `U`, applying records
of `U` in any order is GC-with-filter under `adm U`. -/
theorem applyAllD_fixed (U : List Record) (x : Record) :
    ∀ (l T : List Record), Frontier T → Admitted T → (∀ y ∈ T, y ∈ U) →
      (∀ y ∈ U, isAuth y = true → Cov y T) → (∀ r ∈ l, r ∈ U) →
      (x ∈ applyAllD T l ↔ x ∈ F ((T ++ l).filter (adm U))) := by
  intro l
  induction l with
  | nil =>
    intro T hF hA hsub hcov _
    show x ∈ T ↔ _
    rw [List.append_nil]
    have hfilt : ∀ y, y ∈ T.filter (adm U) ↔ y ∈ T := by
      intro y
      rw [List.mem_filter]
      exact ⟨And.left, fun hy => ⟨hy, by rw [← adm_cover hsub hcov]; exact hA y hy⟩⟩
    rw [F_congr hfilt, frontier_mem_F hF]
  | cons r l ih =>
    intro T hF hA hsub hcov hl
    have hrU : r ∈ U := hl r (List.mem_cons_self ..)
    have hlU : ∀ r' ∈ l, r' ∈ U := fun r' h => hl r' (List.mem_cons_of_mem _ h)
    have hsub' : ∀ y ∈ applyD T r, y ∈ U := by
      intro y hy
      rcases applyD_sub hy with h | h
      · exact hsub y h
      · rw [h]; exact hrU
    have hcov' : ∀ y ∈ U, isAuth y = true → Cov y (applyD T r) :=
      fun y hy ha => applyD_cov (hcov y hy ha)
    rw [applyAllD_cons, ih (applyD T r) (applyD_frontier hF) (applyD_admitted hA) hsub' hcov' hlU]
    have hTU : adm T r = adm U r := adm_cover hsub hcov
    cases hr : adm T r
    · have hUr : adm U r = false := hTU ▸ hr
      rw [applyD_neg hr]
      apply F_congr
      intro y
      simp only [List.mem_filter, List.mem_append, List.mem_cons]
      constructor
      · rintro ⟨h | h, ha⟩
        · exact ⟨Or.inl h, ha⟩
        · exact ⟨Or.inr (Or.inr h), ha⟩
      · rintro ⟨h | h | h, ha⟩
        · exact ⟨Or.inl h, ha⟩
        · subst h; rw [hUr] at ha; exact absurd ha Bool.false_ne_true
        · exact ⟨Or.inr h, ha⟩
    · rw [applyD_pos hr]
      have hall : ∀ y ∈ T ++ [r], adm U y = true := by
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · rw [← adm_cover hsub hcov]; exact hA y h
        · rw [List.mem_singleton.mp h, ← hTU]; exact hr
      rw [F_prefix_filter (adm U) (T ++ [r]) l hall x, List.append_assoc, List.singleton_append]

/-- The shape every T4 statement reduces to: after a first phase that leaves a
state `T` holding only records of `U`, covering every authorization record
of `U` and every record of the part `P` already processed, applying the rest
`l` of `U` yields the frontier of the admitted records of `U`. -/
theorem finish {T U P l : List Record} (x : Record) (hF : Frontier T) (hA : Admitted T)
    (hsub : ∀ y ∈ T, y ∈ U) (hcov : ∀ y ∈ U, isAuth y = true → Cov y T)
    (hP : ∀ y ∈ P, Cov y T) (hU : ∀ y, y ∈ U ↔ y ∈ P ∨ y ∈ l) :
    x ∈ applyAllD T l ↔ x ∈ F (admitted U) := by
  have hlU : ∀ r ∈ l, r ∈ U := fun r h => (hU r).mpr (Or.inr h)
  rw [applyAllD_fixed U x l T hF hA hsub hcov hlU]
  unfold admitted
  apply F_sandwich
  · intro y hy
    obtain ⟨hy, hnd⟩ := mem_F_iff.mp hy
    obtain ⟨hyU, ha⟩ := List.mem_filter.mp hy
    refine List.mem_filter.mpr ⟨?_, ha⟩
    rcases (hU y).mp hyU with hp | hl
    · rcases hP y hp with hT | ⟨q, hq, hqy⟩
      · exact List.mem_append_left _ hT
      · have hq' : adm U q = true := by rw [← adm_cover hsub hcov]; exact hA q hq
        exact (hnd ⟨q, List.mem_filter.mpr ⟨hsub q hq, hq'⟩, hqy⟩).elim
    · exact List.mem_append_right _ hl
  · intro y hy
    obtain ⟨hy, ha⟩ := List.mem_filter.mp hy
    refine List.mem_filter.mpr ⟨?_, ha⟩
    rcases List.mem_append.mp hy with h | h
    · exact hsub y h
    · exact hlU y h

/-- T4 (a), T18: one pass that applies a set's authorization records before
its data records, from a frontier whose records are admitted, yields the
frontier of the admitted records of the union. This is a batch applied in
element-key order (§4) and the replay of a compacted log (§7). -/
theorem auth_first {S la ld : List Record} (x : Record) (hF : Frontier S) (hA : Admitted S)
    (hla : ∀ y ∈ la, isAuth y = true) (hld : ∀ y ∈ ld, isAuth y = false) :
    x ∈ applyAllD S (la ++ ld) ↔ x ∈ F (admitted (S ++ la ++ ld)) := by
  rw [applyAllD_append]
  have hP : ∀ y ∈ S ++ la, Cov y (applyAllD S la) := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · exact applyAllD_cov (Or.inl h)
    · exact applyAllD_auth h (hla y h)
  refine finish (P := S ++ la) x (applyAllD_frontier la hF) (applyAllD_admitted la hA)
    ?_ ?_ hP (fun y => List.mem_append)
  · intro y hy
    rcases applyAllD_sub hy with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact List.mem_append_left _ (List.mem_append_right _ h)
  · intro y hy ha
    rcases List.mem_append.mp hy with h | h
    · exact hP y h
    · rw [hld y h] at ha; exact absurd ha Bool.false_ne_true

/-- T4 (b): two passes over the same records, in any order and with any
duplication (the second re-offering what the first refused), yield the
frontier of the admitted records of the union. -/
theorem convergence_two_pass {S l : List Record} (x : Record) (hF : Frontier S)
    (hA : Admitted S) :
    x ∈ applyAllD (applyAllD S l) l ↔ x ∈ F (admitted (S ++ l)) := by
  refine finish (P := S) x (applyAllD_frontier l hF) (applyAllD_admitted l hA)
    ?_ ?_ ?_ (fun y => List.mem_append)
  · intro y hy; exact List.mem_append.mpr (applyAllD_sub hy)
  · intro y hy ha
    rcases List.mem_append.mp hy with h | h
    · exact applyAllD_cov (Or.inl h)
    · exact applyAllD_auth h ha
  · intro y hy; exact applyAllD_cov (Or.inl hy)

/-- T4: two replicas that started from the same admitted frontier and applied
the same set of records (twice each, in any order, with any duplication)
hold the same frontier. -/
theorem convergence {S l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') (x : Record)
    (hF : Frontier S) (hA : Admitted S) :
    x ∈ applyAllD (applyAllD S l) l ↔ x ∈ applyAllD (applyAllD S l') l' := by
  rw [convergence_two_pass x hF hA, convergence_two_pass x hF hA]
  have hm : ∀ y, y ∈ S ++ l ↔ y ∈ S ++ l' := fun y => by
    rw [List.mem_append, List.mem_append, h y]
  apply F_congr
  intro y
  rw [mem_admitted, mem_admitted, hm y, adm_congr hm]

/-- The empty store is an admitted frontier, and `applyD` preserves both
(`applyD_frontier`, `applyD_admitted`), so every state a replica reaches
meets the hypotheses of `auth_first`, `convergence_two_pass` and
`convergence`. -/
theorem frontier_nil : Frontier [] := fun _ hx => absurd hx List.not_mem_nil

theorem admitted_nil : Admitted [] := fun _ hx => absurd hx List.not_mem_nil

/-- T4 from the empty store. -/
theorem convergence_empty {l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') (x : Record) :
    x ∈ applyAllD (applyAllD [] l) l ↔ x ∈ applyAllD (applyAllD [] l') l' :=
  convergence h x frontier_nil admitted_nil

/-! ### Tombstone expiry (§7, T11) -/

/-- A `del` at or below the horizon `h`. The horizon itself (with its clock
clamp, `min(now_local, maxceil) − del_ttl_eff`) is computed outside the
model. -/
def isExpiredDel (h : Nat) : Record → Bool
  | del _ v => decide (v.t ≤ h)
  | _ => false

/-- `Frontier.Expire` at horizon `h`: remove exactly the expired `del`s. -/
def expire (h : Nat) (S : List Record) : List Record := S.filter (fun x => !isExpiredDel h x)

theorem mem_expire {h : Nat} {S : List Record} {x : Record} :
    x ∈ expire h S ↔ x ∈ S ∧ isExpiredDel h x = false := by
  simp [expire]

theorem isAuth_of_expired {h : Nat} {d : Record} (hd : isExpiredDel h d = true) :
    isAuth d = false := by
  cases d <;> simp [isExpiredDel, isAuth] at hd ⊢

theorem isExpiredDel_auth {h : Nat} {x : Record} (hx : isAuth x = true) :
    isExpiredDel h x = false := by
  cases x <;> simp [isExpiredDel, isAuth] at hx ⊢

theorem expire_subset (h : Nat) (S : List Record) : expire h S ⊆ S :=
  fun _ hx => (mem_expire.mp hx).1

theorem expire_keeps {h : Nat} {S : List Record} {x : Record} (hx : x ∈ S)
    (hn : isExpiredDel h x = false) : x ∈ expire h S :=
  mem_expire.mpr ⟨hx, hn⟩

/-- T11 (a): after `expire h`, no `del` with `t ≤ h` is held. -/
theorem expire_none {h : Nat} {S : List Record} {x : Record} (hx : x ∈ expire h S) :
    isExpiredDel h x = false :=
  (mem_expire.mp hx).2

/-- Expiry removes nothing but `del`s at or below the horizon. -/
theorem expire_only_del {h : Nat} {S : List Record} {x : Record} (hx : x ∈ S)
    (hn : x ∉ expire h S) : ∃ e v, x = del e v ∧ v.t ≤ h := by
  cases hk : isExpiredDel h x
  · exact absurd (expire_keeps hx hk) hn
  · cases x with
    | del e v => simp only [isExpiredDel, decide_eq_true_eq] at hk; exact ⟨e, v, rfl, hk⟩
    | _ => simp [isExpiredDel] at hk

/-- T11 (a): expiring a frontier leaves a frontier. -/
theorem expire_frontier {h : Nat} {S : List Record} (hF : Frontier S) :
    Frontier (expire h S) :=
  fun x hx hd => hF x (expire_subset h S hx) (Dom_mono hd (expire_subset h S))

/-- T11 (a): expiry keeps every authorization record, so it changes no
register and no admission. -/
theorem expire_adm {h : Nat} {S : List Record} {r : Record} : adm (expire h S) r = adm S r :=
  adm_cover (fun _ hy => expire_subset h S hy)
    (fun _ hy ha => Or.inl (expire_keeps hy (isExpiredDel_auth ha)))

theorem expire_admitted {h : Nat} {S : List Record} (hA : Admitted S) :
    Admitted (expire h S) := by
  intro x hx
  rw [expire_adm]
  exact hA x (expire_subset h S hx)

/-- Two replicas, one holding the data record `d` (state `A`) and one not
(state `B`), stay related by `A = F(B ∪ {d})` through any further records. -/
theorem reapply_rel {d : Record} (hd : isAuth d = false) :
    ∀ (l A B : List Record), (∀ y, y ∈ A ↔ y ∈ F (B ++ [d])) →
      ∀ y, y ∈ applyAllD A l ↔ y ∈ F (applyAllD B l ++ [d]) := by
  intro l
  induction l with
  | nil => intro A B h; exact h
  | cons r l ih =>
    intro A B h
    have hD : ∀ x ∈ [d], isAuth x = false := by
      intro x hx; rw [List.mem_singleton.mp hx]; exact hd
    have hadm : adm A r = adm B r := by
      rw [adm_congr h, adm_F, adm_data_irrelevant hD]
    apply ih
    intro y
    cases hr : adm B r
    · rw [applyD_neg (hadm.trans hr), applyD_neg hr]; exact h y
    · rw [applyD_pos (hadm.trans hr), applyD_pos hr]
      have hm : ∀ z, z ∈ A ++ [r] ↔ z ∈ F (B ++ [d]) ++ [r] := fun z => by
        rw [List.mem_append, List.mem_append, h z]
      rw [F_congr hm y, F_prefix, F_prefix]
      apply F_congr
      intro z
      simp only [List.mem_append, List.mem_singleton]
      exact or_right_comm

/-- T11 (b), apply-then-expire: a replica that holds the expired `del` `d` and
one that does not agree, after the same further records `l`, a re-sent `d`
and an expiry at `h`, on every record. No hypothesis beyond the statement's
is needed (in fact the two agree before the expiry already). -/
theorem expire_reapply {S l : List Record} {d : Record} {h : Nat} (x : Record)
    (hF : Frontier S) (hA : Admitted S) (hd : d ∈ S) (hexp : isExpiredDel h d = true) :
    x ∈ expire h (applyD (applyAllD (S.erase d) l) d) ↔ x ∈ expire h (applyAllD S l) := by
  have hdata : isAuth d = false := isAuth_of_expired hexp
  have hD : ∀ y ∈ [d], isAuth y = false := by
    intro y hy; rw [List.mem_singleton.mp hy]; exact hdata
  have hmem : ∀ y, y ∈ S.erase d ++ [d] ↔ y ∈ S := by
    intro y
    rw [List.mem_append, List.mem_singleton]
    by_cases hyd : y = d
    · subst hyd; exact ⟨fun _ => hd, fun _ => Or.inr rfl⟩
    · rw [List.mem_erase_of_ne hyd]; exact ⟨fun h' => h'.resolve_right hyd, Or.inl⟩
  have hbase : ∀ y, y ∈ S ↔ y ∈ F (S.erase d ++ [d]) := by
    intro y; rw [F_congr hmem y, frontier_mem_F hF]
  have hrel := reapply_rel hdata l S (S.erase d) hbase
  have hadmB : adm (applyAllD (S.erase d) l) d = true := by
    have h1 : adm (applyAllD S l) d = true := adm_applyAllD_mono l (hA d hd)
    rw [adm_congr hrel, adm_F, adm_data_irrelevant hD] at h1
    exact h1
  rw [applyD_pos hadmB, mem_expire, mem_expire, ← hrel x]

/-! ### Views (§3, §6; T5, T12). `founding` is the collection's founding key. -/

/-- `root_void(k)`: the founding key revoked `k` (its `from_t` is ignored);
the founding key is never root-voided. -/
def rootVoid (founding : Nat) (H : List Record) (k : Nat) : Prop :=
  k ≠ founding ∧ ∃ f r hh, revoke founding k f r hh ∈ H

/-- `k ∈ W_eff`: a grant of `k` by an issuer that is not root-voided. -/
def wEff (founding : Nat) (H : List Record) (k : Nat) : Prop :=
  ∃ i hh, grant i k hh ∈ H ∧ ¬ rootVoid founding H i

/-- The `REVOKE` clause of `void` for a record by `a` at time `t`. -/
def revokeVoids (founding : Nat) (H : List Record) (a t : Nat) : Prop :=
  ∃ i f r hh, revoke i a f r hh ∈ H ∧ f ≤ t ∧ ¬ rootVoid founding H i

/-- `void(p)` for a data record; false for the other kinds. -/
def voided (founding : Nat) (H : List Record) : Record → Prop
  | put _ _ v _ => revokeVoids founding H v.author v.t ∨ ¬ wEff founding H v.author
  | del _ v => revokeVoids founding H v.author v.t ∨ ¬ wEff founding H v.author
  | _ => False

theorem revoke_mem_F {H : List Record} {i s f r h : Nat} :
    revoke i s f r h ∈ F H ↔ revoke i s f r h ∈ H :=
  ⟨fun hx => F_subset H hx, fun hx => mem_F_iff.mpr ⟨hx, fun ⟨q, _, hq⟩ => by
    rw [revoke_never_dominated] at hq; exact Bool.false_ne_true hq⟩⟩

/-- T12: `root_void` is monotone in the held set. -/
theorem rootVoid_mono {f : Nat} {H H' : List Record} {k : Nat} (hs : H ⊆ H')
    (h : rootVoid f H k) : rootVoid f H' k :=
  let ⟨hk, fr, r, hh, hm⟩ := h
  ⟨hk, fr, r, hh, hs hm⟩

theorem rootVoid_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (k : Nat) :
    rootVoid f H k ↔ rootVoid f H' k :=
  ⟨rootVoid_mono (fun y hy => (h y).mp hy), rootVoid_mono (fun y hy => (h y).mpr hy)⟩

/-- T5: `root_void(F(H)) = root_void(H)`, because revocations are never
dominated. -/
theorem rootVoid_F {f : Nat} {H : List Record} {k : Nat} : rootVoid f (F H) k ↔ rootVoid f H k := by
  unfold rootVoid
  constructor
  · rintro ⟨hk, fr, r, hh, hm⟩; exact ⟨hk, fr, r, hh, revoke_mem_F.mp hm⟩
  · rintro ⟨hk, fr, r, hh, hm⟩; exact ⟨hk, fr, r, hh, revoke_mem_F.mpr hm⟩

theorem wEff_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (k : Nat) :
    wEff f H k ↔ wEff f H' k := by
  unfold wEff
  constructor
  · rintro ⟨i, hh, hm, hv⟩; exact ⟨i, hh, (h _).mp hm, fun hv' => hv ((rootVoid_congr h i).mpr hv')⟩
  · rintro ⟨i, hh, hm, hv⟩; exact ⟨i, hh, (h _).mpr hm, fun hv' => hv ((rootVoid_congr h i).mp hv')⟩

/-- T5: `W_eff(F(H)) = W_eff(H)`. A dominated grant has an undominated
dominator with the same issuer and subject. -/
theorem wEff_F {f : Nat} {H : List Record} {k : Nat} : wEff f (F H) k ↔ wEff f H k := by
  unfold wEff
  constructor
  · rintro ⟨i, hh, hm, hv⟩
    exact ⟨i, hh, F_subset H hm, fun hv' => hv (rootVoid_F.mpr hv')⟩
  · rintro ⟨i, hh, hm, hv⟩
    have hv' : ¬ rootVoid f (F H) i := fun h' => hv (rootVoid_F.mp h')
    rcases F_covers hm with hF | ⟨q, hq, hqg⟩
    · exact ⟨i, hh, hF, hv'⟩
    · obtain ⟨h', rfl⟩ := dominates_grant hqg
      exact ⟨i, h', hq, hv'⟩

/-- T12: for a fixed `root_void` set, `W_eff` is monotone (a `GRANT` can only
un-void). -/
theorem wEff_mono_fixed {f : Nat} {H H' : List Record} {k : Nat} (hs : H ⊆ H')
    (hfix : ∀ i, rootVoid f H' i → rootVoid f H i) (h : wEff f H k) : wEff f H' k :=
  let ⟨i, hh, hm, hv⟩ := h
  ⟨i, hh, hs hm, fun hv' => hv (hfix i hv')⟩

/-- T12: for a fixed `root_void` set, the `REVOKE` clause of `void` is
monotone (a `REVOKE` can only void). -/
theorem voided_revoke_mono {f : Nat} {H H' : List Record} {a t : Nat} (hs : H ⊆ H')
    (hfix : ∀ i, rootVoid f H' i → rootVoid f H i) (h : revokeVoids f H a t) :
    revokeVoids f H' a t :=
  let ⟨i, fr, r, hh, hm, hle, hv⟩ := h
  ⟨i, fr, r, hh, hs hm, hle, fun hv' => hv (hfix i hv')⟩

theorem revokeVoids_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (a t : Nat) :
    revokeVoids f H a t ↔ revokeVoids f H' a t := by
  unfold revokeVoids
  constructor
  · rintro ⟨i, fr, r, hh, hm, hle, hv⟩
    exact ⟨i, fr, r, hh, (h _).mp hm, hle, fun hv' => hv ((rootVoid_congr h i).mpr hv')⟩
  · rintro ⟨i, fr, r, hh, hm, hle, hv⟩
    exact ⟨i, fr, r, hh, (h _).mpr hm, hle, fun hv' => hv ((rootVoid_congr h i).mp hv')⟩

theorem revokeVoids_F {f : Nat} {H : List Record} {a t : Nat} :
    revokeVoids f (F H) a t ↔ revokeVoids f H a t := by
  unfold revokeVoids
  constructor
  · rintro ⟨i, fr, r, hh, hm, hle, hv⟩
    exact ⟨i, fr, r, hh, revoke_mem_F.mp hm, hle, fun hv' => hv (rootVoid_F.mpr hv')⟩
  · rintro ⟨i, fr, r, hh, hm, hle, hv⟩
    exact ⟨i, fr, r, hh, revoke_mem_F.mpr hm, hle, fun hv' => hv (rootVoid_F.mp hv')⟩

/-- T5: `void` is a function of the held set. -/
theorem voided_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (x : Record) :
    voided f H x ↔ voided f H' x := by
  cases x <;> simp only [voided, revokeVoids_congr h, wEff_congr h]

/-- T5: `void(F(H)) = void(H)`. -/
theorem voided_F {f : Nat} {H : List Record} (x : Record) : voided f (F H) x ↔ voided f H x := by
  cases x <;> simp only [voided, revokeVoids_F, wEff_F]

/-! #### `ROSTER_eff` and `del_ttl_eff` -/

/-- `root_void` as a Boolean test. -/
def revokesRoot (founding k : Nat) : Record → Bool
  | revoke i j _ _ _ => decide (i = founding ∧ j = k)
  | _ => false

def rootVoidB (founding : Nat) (H : List Record) (k : Nat) : Bool :=
  decide (k ≠ founding) && H.any (revokesRoot founding k)

theorem revokesRoot_iff {f k : Nat} {r : Record} :
    revokesRoot f k r = true ↔ ∃ fr rs hh, r = revoke f k fr rs hh := by
  cases r with
  | revoke i j fr rs hh =>
    simp only [revokesRoot, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨fr, rs, hh, rfl⟩
    · rintro ⟨_, _, _, he⟩; cases he; exact ⟨rfl, rfl⟩
  | _ => simp [revokesRoot]

theorem rootVoidB_iff {f : Nat} {H : List Record} {k : Nat} :
    rootVoidB f H k = true ↔ rootVoid f H k := by
  unfold rootVoidB rootVoid
  rw [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨hk, r, hr, hrv⟩
    obtain ⟨fr, rs, hh, rfl⟩ := revokesRoot_iff.mp hrv
    exact ⟨hk, fr, rs, hh, hr⟩
  · rintro ⟨hk, fr, rs, hh, hm⟩
    exact ⟨hk, _, hm, revokesRoot_iff.mpr ⟨fr, rs, hh, rfl⟩⟩

theorem rootVoidB_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (k : Nat) :
    rootVoidB f H k = rootVoidB f H' k :=
  Bool.eq_iff_iff.mpr (by rw [rootVoidB_iff, rootVoidB_iff]; exact rootVoid_congr h k)

theorem rootVoidB_F {f : Nat} {H : List Record} (k : Nat) : rootVoidB f (F H) k = rootVoidB f H k :=
  Bool.eq_iff_iff.mpr (by rw [rootVoidB_iff, rootVoidB_iff]; exact rootVoid_F)

/-- The candidates for `ROSTER_eff` and `del_ttl_eff`: rosters whose signer is
not root-voided. -/
def isRosterOK (founding : Nat) (H : List Record) : Record → Bool
  | roster s _ _ _ _ => !rootVoidB founding H s
  | _ => false

theorem isRosterOK_roster {f : Nat} {H : List Record} {r : Record} (h : isRosterOK f H r = true) :
    ∃ s c g t hh, r = roster s c g t hh := by
  cases r with
  | roster s c g t hh => exact ⟨s, c, g, t, hh, rfl⟩
  | _ => simp [isRosterOK] at h

theorem isRosterOK_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') :
    isRosterOK f H = isRosterOK f H' := by
  funext r
  cases r <;> simp only [isRosterOK, rootVoidB_congr h]

theorem isRosterOK_F {f : Nat} {H : List Record} : isRosterOK f (F H) = isRosterOK f H := by
  funext r
  cases r <;> simp only [isRosterOK, rootVoidB_F]

/-- The whole roster tuple, in comparison order: `(gen, h, signer, ceil, ttl)`. -/
def rkey : Record → Nat × Nat × Nat × Nat × Nat
  | roster s c g t h => (g, h, s, c, t)
  | _ => (0, 0, 0, 0, 0)

/-- Lexicographic order on five-tuples. -/
def lexLt (p q : Nat × Nat × Nat × Nat × Nat) : Bool :=
  decide (p.1 < q.1 ∨ (p.1 = q.1 ∧ (p.2.1 < q.2.1 ∨ (p.2.1 = q.2.1 ∧
    (p.2.2.1 < q.2.2.1 ∨ (p.2.2.1 = q.2.2.1 ∧
      (p.2.2.2.1 < q.2.2.2.1 ∨ (p.2.2.2.1 = q.2.2.2.1 ∧ p.2.2.2.2 < q.2.2.2.2))))))))

/-- The order `ROSTER_eff` maximizes. On rosters it is a strict total order. -/
def rkLt (a b : Record) : Bool := lexLt (rkey a) (rkey b)

theorem lexLt_asymm {p q : Nat × Nat × Nat × Nat × Nat} (h : lexLt p q = true) :
    lexLt q p = false := by
  simp only [lexLt, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega

theorem lexLt_irrefl (p : Nat × Nat × Nat × Nat × Nat) : lexLt p p = false := by
  simp only [lexLt, decide_eq_false_iff_not]; omega

theorem lexLt_le_trans {p q r : Nat × Nat × Nat × Nat × Nat} (h₁ : lexLt p q = false)
    (h₂ : lexLt q r = false) : lexLt p r = false := by
  simp only [lexLt, decide_eq_false_iff_not] at h₁ h₂ ⊢; omega

theorem lexLt_antisymm {p q : Nat × Nat × Nat × Nat × Nat} (h₁ : lexLt p q = false)
    (h₂ : lexLt q p = false) : p = q := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := p
  obtain ⟨b1, b2, b3, b4, b5⟩ := q
  simp only [lexLt, decide_eq_false_iff_not] at h₁ h₂
  simp only [Prod.mk.injEq]
  omega

theorem rkey_inj {a b : Record} (ha : ∃ s c g t hh, a = roster s c g t hh)
    (hb : ∃ s c g t hh, b = roster s c g t hh) (h : rkey a = rkey b) : a = b := by
  obtain ⟨s, c, g, t, hh, rfl⟩ := ha
  obtain ⟨s', c', g', t', hh', rfl⟩ := hb
  simp only [rkey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- A dominating roster is strictly greater in the `ROSTER_eff` order. -/
theorem dominates_rkLt {s c g t hh : Nat} {p : Record}
    (h : dominates p (roster s c g t hh) = true) : rkLt (roster s c g t hh) p = true := by
  obtain ⟨c', g', t', h', rfl, _, hg⟩ := dominates_roster h
  simp only [rkLt, rkey, lexLt, decide_eq_true_eq]
  omega

/-- One fold step of `ROSTER_eff`: keep the larger candidate. -/
def maxStep (cand : Record → Bool) (acc : Option Record) (r : Record) : Option Record :=
  if cand r then
    match acc with
    | none => some r
    | some a => if rkLt a r then some r else some a
  else acc

/-- `ROSTER_eff`: the roster with a signer that is not root-voided that is
maximal under `(gen, h, signer, ceil, ttl)` (a strict total order on
rosters), or `none`. -/
def rosterEff (founding : Nat) (H : List Record) : Option Record :=
  H.foldl (maxStep (isRosterOK founding H)) none

/-- `m` is the candidate of `l` that no candidate exceeds. -/
def IsMaxR (cand : Record → Bool) (l : List Record) (m : Record) : Prop :=
  m ∈ l ∧ cand m = true ∧ ∀ r ∈ l, cand r = true → rkLt m r = false

theorem foldl_maxStep_none (cand : Record → Bool) :
    ∀ (l : List Record) (acc : Option Record),
      l.foldl (maxStep cand) acc = none ↔ acc = none ∧ ∀ r ∈ l, cand r = false := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons r l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    cases hc : cand r <;> cases acc <;>
      simp [maxStep, hc] <;> (try split) <;> simp_all

theorem foldl_maxStep_some (cand : Record → Bool) :
    ∀ (l : List Record) (acc : Option Record) (m : Record),
      l.foldl (maxStep cand) acc = some m →
        (acc = some m ∨ (m ∈ l ∧ cand m = true)) ∧
        (∀ a, acc = some a → rkLt m a = false) ∧
        (∀ r ∈ l, cand r = true → rkLt m r = false) := by
  intro l
  induction l with
  | nil =>
    intro acc m h
    simp only [List.foldl_nil] at h
    refine ⟨Or.inl h, ?_, fun r hr => absurd hr List.not_mem_nil⟩
    intro a ha; rw [h] at ha; cases ha; exact lexLt_irrefl _
  | cons r l ih =>
    intro acc m h
    rw [List.foldl_cons] at h
    obtain ⟨hmem, hacc, hl⟩ := ih _ m h
    cases hc : cand r with
    | false =>
      have hs : maxStep cand acc r = acc := by simp [maxStep, hc]
      rw [hs] at hmem hacc
      refine ⟨hmem.imp id (fun ⟨h1, h2⟩ => ⟨List.mem_cons_of_mem _ h1, h2⟩), hacc, ?_⟩
      intro r' hr' hc'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · rw [hc] at hc'; exact absurd hc' Bool.false_ne_true
      · exact hl r' hr' hc'
    | true =>
      cases acc with
      | none =>
        have hs : maxStep cand none r = some r := by simp [maxStep, hc]
        rw [hs] at hmem hacc
        refine ⟨Or.inr ?_, (fun a ha => by cases ha), ?_⟩
        · rcases hmem with he | ⟨h1, h2⟩
          · cases he; exact ⟨List.mem_cons_self .., hc⟩
          · exact ⟨List.mem_cons_of_mem _ h1, h2⟩
        · intro r' hr' hc'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact hacc _ rfl
          · exact hl r' hr' hc'
      | some a =>
        cases hlt : rkLt a r with
        | true =>
          have hs : maxStep cand (some a) r = some r := by simp [maxStep, hc, hlt]
          rw [hs] at hmem hacc
          have hmr : rkLt m r = false := hacc r rfl
          refine ⟨?_, ?_, ?_⟩
          · rcases hmem with he | ⟨h1, h2⟩
            · cases he; exact Or.inr ⟨List.mem_cons_self .., hc⟩
            · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
          · intro a' ha'; cases ha'; exact lexLt_le_trans hmr (lexLt_asymm hlt)
          · intro r' hr' hc'
            rcases List.mem_cons.mp hr' with rfl | hr'
            · exact hmr
            · exact hl r' hr' hc'
        | false =>
          have hs : maxStep cand (some a) r = some a := by simp [maxStep, hc, hlt]
          rw [hs] at hmem hacc
          have hma : rkLt m a = false := hacc a rfl
          refine ⟨hmem.imp id (fun ⟨h1, h2⟩ => ⟨List.mem_cons_of_mem _ h1, h2⟩), hacc, ?_⟩
          intro r' hr' hc'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · exact lexLt_le_trans hma hlt
          · exact hl r' hr' hc'

theorem maxOf_none {cand : Record → Bool} {l : List Record} :
    l.foldl (maxStep cand) none = none ↔ ∀ r ∈ l, cand r = false := by
  rw [foldl_maxStep_none]; simp

theorem maxOf_some {cand : Record → Bool} {l : List Record} {m : Record}
    (h : l.foldl (maxStep cand) none = some m) : IsMaxR cand l m := by
  obtain ⟨hmem, _, hl⟩ := foldl_maxStep_some cand l none m h
  rcases hmem with he | ⟨h1, h2⟩
  · cases he
  · exact ⟨h1, h2, hl⟩

theorem IsMaxR_unique {cand : Record → Bool} {l : List Record} {m m' : Record}
    (hc : ∀ r, cand r = true → ∃ s c g t hh, r = roster s c g t hh)
    (h : IsMaxR cand l m) (h' : IsMaxR cand l m') : m = m' :=
  rkey_inj (hc m h.2.1) (hc m' h'.2.1)
    (lexLt_antisymm (h.2.2 m' h'.1 h'.2.1) (h'.2.2 m h.1 h.2.1))

theorem maxOf_eq {cand : Record → Bool} {l : List Record} {m : Record}
    (hc : ∀ r, cand r = true → ∃ s c g t hh, r = roster s c g t hh)
    (h : IsMaxR cand l m) : l.foldl (maxStep cand) none = some m := by
  cases hr : l.foldl (maxStep cand) none with
  | none =>
    have := maxOf_none.mp hr m h.1
    rw [h.2.1] at this; exact absurd this (by decide)
  | some m' => rw [IsMaxR_unique hc (maxOf_some hr) h]

/-- T5: `ROSTER_eff` is a function of the held set. -/
theorem rosterEff_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') :
    rosterEff f H = rosterEff f H' := by
  unfold rosterEff
  rw [← isRosterOK_congr h]
  have hc : ∀ r, isRosterOK f H r = true → ∃ s c g t hh, r = roster s c g t hh :=
    fun _ hr => isRosterOK_roster hr
  cases hr : H.foldl (maxStep (isRosterOK f H)) none with
  | none =>
    have hn := maxOf_none.mp hr
    exact (maxOf_none.mpr fun r hr' => hn r ((h r).mpr hr')).symm
  | some m =>
    obtain ⟨h1, h2, h3⟩ := maxOf_some hr
    exact (maxOf_eq hc ⟨(h m).mp h1, h2, fun r hr' hc' => h3 r ((h r).mpr hr') hc'⟩).symm

/-- T5: `ROSTER_eff(F(H)) = ROSTER_eff(H)`. The maximum is undominated: a
dominator has the same signer (so it is a candidate too) and a strictly
greater `(gen, h)`. -/
theorem rosterEff_F {f : Nat} {H : List Record} : rosterEff f (F H) = rosterEff f H := by
  unfold rosterEff
  rw [isRosterOK_F]
  have hc : ∀ r, isRosterOK f H r = true → ∃ s c g t hh, r = roster s c g t hh :=
    fun _ hr => isRosterOK_roster hr
  cases hr : H.foldl (maxStep (isRosterOK f H)) none with
  | none =>
    have hn := maxOf_none.mp hr
    exact maxOf_none.mpr fun r hr' => hn r (F_subset H hr')
  | some m =>
    obtain ⟨h1, h2, h3⟩ := maxOf_some hr
    have hmF : m ∈ F H := by
      refine mem_F_iff.mpr ⟨h1, ?_⟩
      rintro ⟨q, hq, hqm⟩
      obtain ⟨s, c, g, t, hh, rfl⟩ := hc m h2
      obtain ⟨c', g', t', h', rfl, _, _⟩ := dominates_roster hqm
      have hqc : isRosterOK f H (roster s c' g' t' h') = true := by
        simp only [isRosterOK] at h2 ⊢; exact h2
      have hlt := dominates_rkLt hqm
      rw [h3 _ hq hqc] at hlt
      exact Bool.false_ne_true hlt
    exact maxOf_eq hc ⟨hmF, h2, fun r hr' hc' => h3 r (F_subset H hr') hc'⟩

/-- `ROSTER_eff` is present whenever a roster signed by the founding key is held. -/
theorem rosterEff_present {f : Nat} {H : List Record}
    (h : ∃ c g t hh, roster f c g t hh ∈ H) : rosterEff f H ≠ none := by
  obtain ⟨c, g, t, hh, hm⟩ := h
  intro hn
  have := maxOf_none.mp hn _ hm
  have hnv : rootVoidB f H f = false := by
    cases hb : rootVoidB f H f
    · rfl
    · exact absurd (rootVoidB_iff.mp hb).1 (fun h' => h' rfl)
  simp [isRosterOK, hnv] at this

def ttlOf : Record → Nat
  | roster _ _ _ t _ => t
  | _ => 0

/-- The largest `ttl` among the candidates (0 if none). -/
def maxTtl (cand : Record → Bool) : List Record → Nat
  | [] => 0
  | r :: l => if cand r then max (ttlOf r) (maxTtl cand l) else maxTtl cand l

/-- `del_ttl_eff`: the largest `del_ttl` of the rosters whose signer is not
root-voided, or `dflt` if there is none. -/
def delTtlEff (founding : Nat) (H : List Record) (dflt : Nat) : Nat :=
  if H.any (isRosterOK founding H) then maxTtl (isRosterOK founding H) H else dflt

theorem maxTtl_ge {cand : Record → Bool} {r : Record} {l : List Record} (h : r ∈ l)
    (hc : cand r = true) : ttlOf r ≤ maxTtl cand l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons q l ih =>
    simp only [maxTtl]
    rcases List.mem_cons.mp h with rfl | hl
    · simp only [hc, ↓reduceIte]; exact Nat.le_max_left _ _
    · split
      · exact Nat.le_trans (ih hl) (Nat.le_max_right _ _)
      · exact ih hl

theorem maxTtl_le {cand : Record → Bool} {l : List Record} {m : Nat}
    (h : ∀ r ∈ l, cand r = true → ttlOf r ≤ m) : maxTtl cand l ≤ m := by
  induction l with
  | nil => exact Nat.zero_le m
  | cons q l ih =>
    simp only [maxTtl]
    have ih' := ih (fun r hr hc => h r (List.mem_cons_of_mem _ hr) hc)
    split
    · next hq => exact Nat.max_le.mpr ⟨h q (List.mem_cons_self ..) hq, ih'⟩
    · exact ih'

/-- T5: `del_ttl_eff` is a function of the held set. -/
theorem delTtlEff_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (dflt : Nat) :
    delTtlEff f H dflt = delTtlEff f H' dflt := by
  unfold delTtlEff
  rw [← isRosterOK_congr h]
  have hany : H.any (isRosterOK f H) = H'.any (isRosterOK f H) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, List.any_eq_true]
    exact ⟨fun ⟨r, hr, hc⟩ => ⟨r, (h r).mp hr, hc⟩, fun ⟨r, hr, hc⟩ => ⟨r, (h r).mpr hr, hc⟩⟩
  have hmax : maxTtl (isRosterOK f H) H = maxTtl (isRosterOK f H) H' :=
    Nat.le_antisymm (maxTtl_le fun r hr hc => maxTtl_ge ((h r).mp hr) hc)
      (maxTtl_le fun r hr hc => maxTtl_ge ((h r).mpr hr) hc)
  rw [hany, hmax]

/-! ### T12: authorization records do not touch data -/

/-- T12: applying an authorization record `a` neither adds nor removes a
`put` or `del`: the data records of `F (S ++ [a])` are those of `F S`. (This
holds for every `S`; for a frontier `S`, `F S` is `S`.) -/
theorem data_F_auth_free {S : List Record} {a x : Record} (ha : isAuth a = true)
    (hx : isAuth x = false) : x ∈ F (S ++ [a]) ↔ x ∈ F S := by
  have hxa : x ≠ a := fun he => by rw [he, ha] at hx; exact absurd hx (by decide)
  have hmem : x ∈ S ++ [a] ↔ x ∈ S := by
    rw [List.mem_append, List.mem_singleton]
    exact ⟨fun h => h.resolve_right hxa, Or.inl⟩
  have hdom : Dom x (S ++ [a]) ↔ Dom x S := by
    constructor
    · rintro ⟨q, hq, hqx⟩
      rcases List.mem_append.mp hq with h | h
      · exact ⟨q, h, hqx⟩
      · rw [List.mem_singleton.mp h, auth_not_dominates_data ha hx] at hqx
        exact absurd hqx Bool.false_ne_true
    · intro hd; exact Dom_mono hd (List.subset_append_left _ _)
  rw [mem_F_iff, mem_F_iff, hmem, hdom]

theorem data_F_auth_free_frontier {S : List Record} {a x : Record} (hF : Frontier S)
    (ha : isAuth a = true) (hx : isAuth x = false) : x ∈ F (S ++ [a]) ↔ x ∈ S := by
  rw [data_F_auth_free ha hx, frontier_mem_F hF]

/-- T12 (locality): applying any record removes from the frontier only records
it dominates itself (so, for an authorization record, only records of its own
kind and key). -/
theorem applyF_local {S : List Record} {a y : Record} (hy : y ∈ F S) (hy' : y ∉ F (S ++ [a])) :
    dominates a y = true := by
  obtain ⟨hyS, hnd⟩ := mem_F_iff.mp hy
  have hd : Dom y (S ++ [a]) := by
    apply Classical.byContradiction
    intro hnd'
    exact hy' (mem_F_iff.mpr ⟨List.mem_append_left _ hyS, hnd'⟩)
  obtain ⟨q, hq, hqy⟩ := hd
  rcases List.mem_append.mp hq with h | h
  · exact absurd ⟨q, h, hqy⟩ hnd
  · rw [List.mem_singleton.mp h] at hqy; exact hqy

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

/-! ### T8: the chase, and D8 -/

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

/-- The version order on the `(t, author, seq)` prefix alone. -/
def prefixLt (a b : Version) : Prop :=
  a.t < b.t ∨ (a.t = b.t ∧ (a.author < b.author ∨ (a.author = b.author ∧ a.seq < b.seq)))

/-- D8, T8: two versions with different `(t, author, seq)` prefixes compare by
the prefix alone, so the outcome of emission does not depend on `h`. -/
theorem lt_iff_prefix {a b : Version}
    (h : (a.t, a.author, a.seq) ≠ (b.t, b.author, b.seq)) :
    Version.lt a b ↔ prefixLt a b := by
  simp only [ne_eq, Prod.mk.injEq] at h
  unfold Version.lt prefixLt
  constructor <;> intro h' <;> omega

end Kome.Frontier
