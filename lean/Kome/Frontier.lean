/-
The frontier store: the model of docs/design/DESIGN.md.

A replica of one collection holds a finite set of signed records. Its state
is the FRONTIER of that set: the records that no other record of the set
dominates (§3).

There are five record kinds (§2):
- The data records `put` and `del`. Each one has a version
  `(t, author, seq, h)`. One strict total order compares the versions.
- The authorization records:
  - `roster`: one for each signer, with its ceiling and its generation.
  - `revoke`: issuer, subject, `from_t`.
  - `grant`: issuer, subject, write cap.

Domination is per key:
- A newer `put` of the same cell, or a newer `del` of the same entity,
  dominates a `put`.
- A newer `del` dominates a `del`.
- A roster of the same signer dominates a roster if it is strictly greater
  in `gen` and not lower in ceiling (a product order). Two rosters of one
  signer at equal `gen` never dominate each other.
- A grant of the same issuer and subject with a greater hash and a cap that
  is not lower dominates a grant (a product order).
- A `revoke` of the same issuer and subject with a lower `from_t`, or an
  equal `from_t` and a greater hash, dominates a `revoke` (S5). A `revoke`
  dominates no other kind, so it never dominates a data record.

The tombstone lifetime `del_ttl` is fixed at founding (S2). It is a
parameter `delTtl` of the definitions that read it, not a roster field.
There is no epoch (S4).

Admission (§4) is a function of the authorization records alone. A data
record is admitted iff its `t` is at most `maxceil` (the largest roster
ceiling), its author is in `W` (the subjects of the grants) and its `t` is
at most `wcap(author)` (the largest cap of the author's grants). All three
registers are functions of the frontier that never shrink (T4'). So
admission is monotone. Admission never reads `revoke`, `root_void` or
`W_eff`.

The model discards inadmissible records and does not hold them (§4, §10.1).
This file states convergence (T4) for that model in two forms:
- One pass that applies the authorization records first. This is the shape
  of a batch and of replay after compaction (T18).
- Two passes in any order.

Tombstone expiry (§7, T11) is an operation on the state. It removes the
`del`s at or below a horizon. The store's horizon is a function of the
state (S7): `hz(F) = maxceil(F) − del_ttl` when `maxceil(F) ≥ del_ttl`, and
no horizon otherwise. `hz` never decreases as authorization records arrive
(`hz_mono`), and the store's apply (`applyH`) expires at `hz` of the state
it reaches, so a roster that raises the ceiling expires in the same step.

Revocation is a set of views (§3, §6; T5, T12): `root_void`, the
effective-writer view `W_eff`, `void` and `ROSTER_eff`. `ROSTER_eff` is the
maximum under `(gen, h)` (then the remaining roster fields), so it does not
depend on list order. None of these views feeds admission. The views read
the minimum `from_t` of the held revocations of a key, which the REVOKE
clause of domination does not change (`isMinFrom_F`).

Scope. The model assumes well-formed records. An authorization record's
certificate controls who may sign it: the founding key, or a root that the
founding key certified. A check on the record's bytes applies this rule
(DESIGN §2). The model does not include this check: it takes every
record to be well-formed. These items are also outside the model:
- Capacity (data capacity, the per-signer slices, `NO_SPACE`, `AUTH_FULL`).
- Assumption A7 (revocation arrives first).

The model uses lists for sets, up to membership. The theorems must not
depend on order or duplication, so every statement has the form
`x ∈ A ↔ x ∈ B`. Identifiers, authors, values and hashes are `Nat`. Every
theorem uses only decidable equality and, for versions, a total order.

Theorem numbers are from DESIGN.md §9.
-/
namespace Kome

/-- A strict total order with a decidable comparison. T1 gives an instance of
it for versions. -/
class StrictTotal (α : Type) where
  lt : α → α → Prop
  dec : ∀ a b, Decidable (lt a b)
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ {a b c}, lt a b → lt b c → lt a c
  trichotomy : ∀ a b, lt a b ∨ a = b ∨ lt b a

end Kome

namespace Kome.Frontier

/-! ### Versions (T1) -/

/-- `v = (t, author, seq, h)`. The comparison is lexicographic. `h` is the
record's content hash, so two different records never tie. -/
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

/-- The records of one collection, reduced to the fields that the lattice and
the views read:
- `put` and `del` carry a version.
- `roster` carries its signer, its ceiling, its generation and its hash.
- `revoke` carries its issuer, its subject, `from_t` and its hash.
- `grant` carries its issuer, its subject, its write cap and its hash. -/
inductive Record where
  | put (ent field : Nat) (v : Version) (value : Nat)
  | del (ent : Nat) (v : Version)
  | roster (signer ceil gen h : Nat)
  | revoke (issuer subject fromT h : Nat)
  | grant (issuer subject cap h : Nat)
deriving DecidableEq, Repr

open Record

/-- `dominates q p`: `q` dominates `p` (DESIGN.md §3, the witness of `dom`).
The product order (D3) compares rosters: the same signer, a ceiling that is
not lower and a strictly greater `gen`. The hash takes no part: two rosters
of one signer at equal `gen` never dominate each other
(`roster_same_gen`). A grant's key is `(issuer, subject)`; a grant
dominates a grant of the same key when its hash is greater and its cap is
not lower. A revocation's key is also `(issuer, subject)`; a revocation
dominates a revocation of the same key when its `from_t` is lower, or equal
with a greater hash (S5). No other record dominates. No clause compares
authorization records of different kinds, and none lets an authorization
record dominate a data record. -/
def dominates : Record → Record → Bool
  | put e' f' v' _, put e f v _ => decide (e = e' ∧ f = f' ∧ Version.lt v v')
  | del e' v',      put e _ v _ => decide (e = e' ∧ Version.lt v v')
  | del e' v',      del e v     => decide (e = e' ∧ Version.lt v v')
  | roster s' c' g' _, roster s c g _ => decide (s = s' ∧ c ≤ c' ∧ g < g')
  | revoke i' j' f' h', revoke i j f h =>
      decide (i = i' ∧ j = j' ∧ (f' < f ∨ (f' = f ∧ h < h')))
  | grant i' j' c' h', grant i j c h => decide (i = i' ∧ j = j' ∧ c ≤ c' ∧ h < h')
  | _, _ => false

theorem dominates_irrefl (x : Record) : dominates x x = false := by
  cases x <;> simp [dominates, Version.lt] <;> omega

/-- T2' (upward closure): a dominator of a dominator is a dominator, for every
triple of kinds. The frontier homomorphism rests on this lemma. It is also
the reason that no clause crosses kinds: a `revoke` that dominated a data
record would need every dominator of that `revoke` to dominate it too. -/
theorem dominates_trans {x y z : Record} (hyx : dominates y x = true)
    (hzy : dominates z y = true) : dominates z x = true := by
  cases x <;> cases y <;> cases z <;>
    simp only [dominates, decide_eq_true_eq, Bool.false_eq_true] at * <;>
    (try simp only [Version.lt] at *) <;> omega

/-- T12 (part): a dominator of a revocation is a revocation of the same issuer
and subject whose `from_t` is not higher (S5). -/
theorem dominates_revoke {q : Record} {i s f h : Nat}
    (hq : dominates q (revoke i s f h) = true) :
    ∃ f' h', q = revoke i s f' h' ∧ f' ≤ f := by
  cases q with
  | revoke i' s' f' h' =>
    simp only [dominates, decide_eq_true_eq] at hq
    obtain ⟨rfl, rfl, hf⟩ := hq
    exact ⟨f', h', rfl, by omega⟩
  | _ => simp [dominates] at hq

/-- A revocation dominates only revocations of its own issuer and subject. In
particular it dominates no data record. -/
theorem revoke_dominates {x : Record} {i s f h : Nat}
    (hx : dominates (revoke i s f h) x = true) :
    ∃ f' h', x = revoke i s f' h' ∧ f ≤ f' := by
  cases x with
  | revoke i' s' f' h' =>
    simp only [dominates, decide_eq_true_eq] at hx
    obtain ⟨rfl, rfl, hf⟩ := hx
    exact ⟨f', h', rfl, by omega⟩
  | _ => simp [dominates] at hx

/-- Two rosters of one signer at equal `gen` never dominate each other
(S4: domination stays strict in `gen`). -/
theorem roster_same_gen (s s' c c' g h h' : Nat) :
    dominates (roster s' c' g h') (roster s c g h) = false := by
  simp [dominates]

/-! ### Domination and the frontier -/

/-- A record in `H` dominates `x`. -/
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

/-- The frontier: the records of `H` that no record of `H` dominates. This is
the state. -/
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

/-- Every dominated record has a dominator that is itself undominated. The
proof picks a maximal dominator. A finite set under a strict order always
has one. -/
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

/-- The removal of dominated records from a prefix does not change the
frontier. -/
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

/-- T3 (frontier homomorphism): `F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))`. Any subset
of replicas can remove dominated records, at any place and at any time. -/
theorem frontier_hom (H₁ H₂ : List Record) (x : Record) :
    x ∈ F (F H₁ ++ F H₂) ↔ x ∈ F (H₁ ++ H₂) := by
  rw [F_prefix H₁ (F H₂) x, F_suffix H₁ H₂ x]

/-- T3 (idempotence). -/
theorem F_idem (H : List Record) (x : Record) : x ∈ F (F H) ↔ x ∈ F H := by
  apply F_sandwich
  · intro y hy; exact hy
  · intro y hy; exact F_subset H hy

/-- `T` holds `y`, or a record that `T` holds dominates `y`. If `T` "covers" a
record of a set, that record cannot resurface against `T`. -/
def Cov (y : Record) (T : List Record) : Prop := y ∈ T ∨ Dom y T

theorem Cov_mono {y : Record} {T T' : List Record} (h : Cov y T) (hs : T ⊆ T') : Cov y T' :=
  h.elim (fun hy => Or.inl (hs hy)) (fun hd => Or.inr (Dom_mono hd hs))

/-- If a record of `H` dominates `y`, then a record of `F H` (a maximal
dominator) also dominates `y`. -/
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

/-- Add one record and keep the frontier. The result drops every record that
the new set dominates. This includes `r` when a held record dominates `r`. -/
def applyF (S : List Record) (r : Record) : List Record := F (S ++ [r])

def applyAllF (S : List Record) (l : List Record) : List Record := l.foldl applyF S

/-- If GC runs after each record, the result is the frontier of the whole
set. -/
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

/-- T4 (no admission): two replicas start from the same state and apply the
same set of records. Each replica can use any order and any duplication.
The two replicas then hold the same frontier. -/
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

/-- A dominator of a grant is a grant of the same key with a cap that is not
lower. -/
theorem dominates_grant {q : Record} {i k c h : Nat} (hq : dominates q (grant i k c h) = true) :
    ∃ c' h', q = grant i k c' h' ∧ c ≤ c' := by
  cases q with
  | grant i' k' c' h' =>
    simp only [dominates, decide_eq_true_eq] at hq
    obtain ⟨rfl, rfl, hc, _⟩ := hq
    exact ⟨c', h', rfl, hc⟩
  | _ => simp [dominates] at hq

/-- A dominator of a roster is a roster of the same signer, with a ceiling
that is not lower and a strictly greater `gen`. -/
theorem dominates_roster {q : Record} {s c g h : Nat}
    (hq : dominates q (roster s c g h) = true) :
    ∃ c' g' h', q = roster s c' g' h' ∧ c ≤ c' ∧ g < g' := by
  cases q with
  | roster s' c' g' h' =>
    simp only [dominates, decide_eq_true_eq] at hq
    obtain ⟨rfl, hc, hg⟩ := hq
    exact ⟨c', g', h', rfl, hc, hg⟩
  | _ => simp [dominates] at hq

/-! ### Derived registers: `maxceil`, `W` and `wcap` (§3, T4')

`maxceil` and `wcap(k)` are the maximum, over the held set, of a projection
`p : Record → Nat` that is 0 on data records and that a dominator never
lowers (`dominates q y → p y ≤ p q`). One family of lemmas (`maxP_*`)
serves both registers. `W` is a membership test, not a maximum, and keeps
its own lemmas. -/

/-- The largest `p` of a list, 0 if the list is empty. -/
def maxP (p : Record → Nat) : List Record → Nat
  | [] => 0
  | r :: l => max (p r) (maxP p l)

theorem maxP_ge {p : Record → Nat} {r : Record} {l : List Record} (h : r ∈ l) :
    p r ≤ maxP p l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons q l ih =>
    simp only [maxP]
    rcases List.mem_cons.mp h with hq | hl
    · rw [hq]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hl) (Nat.le_max_right _ _)

theorem maxP_le {p : Record → Nat} {l : List Record} {m : Nat} (h : ∀ r, r ∈ l → p r ≤ m) :
    maxP p l ≤ m := by
  induction l with
  | nil => exact Nat.zero_le m
  | cons q l ih =>
    simp only [maxP]
    exact Nat.max_le.mpr ⟨h q (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun r hr => h r (List.mem_cons.mpr (Or.inr hr)))⟩

theorem maxP_congr (p : Record → Nat) {l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') :
    maxP p l = maxP p l' :=
  Nat.le_antisymm
    (maxP_le fun r hr => maxP_ge ((h r).mp hr))
    (maxP_le fun r hr => maxP_ge ((h r).mpr hr))

/-- If every authorization record of `H` is in `H'`, then `maxP p H ≤ maxP p H'`
(for `p` that is 0 on data records). -/
theorem maxP_mono_auth {p : Record → Nat} (hp : ∀ r, isAuth r = false → p r = 0)
    {H H' : List Record} (h : ∀ x ∈ H, isAuth x = true → x ∈ H') : maxP p H ≤ maxP p H' := by
  apply maxP_le
  intro r hr
  cases ha : isAuth r
  · rw [hp r ha]; exact Nat.zero_le _
  · exact maxP_ge (h r hr ha)

/-- If every authorization record of `H` is covered by `H'`, then
`maxP p H ≤ maxP p H'` (for `p` that is 0 on data records and that a
dominator never lowers). -/
theorem maxP_le_cov {p : Record → Nat} (hp : ∀ r, isAuth r = false → p r = 0)
    (hd : ∀ q y, dominates q y = true → p y ≤ p q) {H H' : List Record}
    (hcov : ∀ y ∈ H, isAuth y = true → Cov y H') : maxP p H ≤ maxP p H' := by
  apply maxP_le
  intro r hr
  cases ha : isAuth r
  · rw [hp r ha]; exact Nat.zero_le _
  · rcases hcov r hr ha with hT | ⟨q, hq, hqr⟩
    · exact maxP_ge hT
    · exact Nat.le_trans (hd q r hqr) (maxP_ge hq)

/-- If `T` holds only records of `U` and covers every authorization record of
`U`, the two have the same `maxP p`. -/
theorem maxP_cover {p : Record → Nat} (hp : ∀ r, isAuth r = false → p r = 0)
    (hd : ∀ q y, dominates q y = true → p y ≤ p q) {T U : List Record}
    (hsub : ∀ y ∈ T, y ∈ U) (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) :
    maxP p T = maxP p U :=
  Nat.le_antisymm (maxP_le fun r hr => maxP_ge (hsub r hr)) (maxP_le_cov hp hd hcov)

def ceilOf : Record → Nat
  | roster _ c _ _ => c
  | _ => 0

theorem ceilOf_of_not_auth (r : Record) (h : isAuth r = false) : ceilOf r = 0 := by
  cases r <;> simp [isAuth, ceilOf] at h ⊢

/-- A dominator's ceiling is at least the ceiling of the dominated
record. For rosters, this follows from the product order. Every other kind
has ceiling 0. -/
theorem dominates_ceil (q y : Record) (h : dominates q y = true) : ceilOf y ≤ ceilOf q := by
  cases y <;> cases q <;> simp [dominates, ceilOf] at h ⊢ <;> omega

/-- `maxceil`: the largest roster ceiling, 0 if there is none. -/
abbrev maxCeil (H : List Record) : Nat := maxP ceilOf H

/-- The cap that a grant of subject `k` gives; 0 for every other record. -/
def capOf (k : Nat) : Record → Nat
  | grant _ j c _ => if j = k then c else 0
  | _ => 0

theorem capOf_of_not_auth (k : Nat) (r : Record) (h : isAuth r = false) : capOf k r = 0 := by
  cases r <;> simp [isAuth, capOf] at h ⊢

/-- A dominator's cap for `k` is at least the cap of the dominated record. For
grants, this follows from the product order. Every other kind has cap 0. -/
theorem dominates_cap (k : Nat) (q y : Record) (h : dominates q y = true) :
    capOf k y ≤ capOf k q := by
  cases y <;> cases q <;> simp [dominates, capOf] at h ⊢ <;> (try obtain ⟨rfl, rfl, hc, _⟩ := h) <;>
    (try split) <;> omega

/-- `wcap(k)`: the largest cap of the grants of subject `k`, 0 if there is
none. -/
abbrev wcap (H : List Record) (k : Nat) : Nat := maxP (capOf k) H

/-- A grant of `k` with cap `c` gives `c ≤ wcap(k)`. -/
theorem wcap_ge_grant {k i c hh : Nat} {l : List Record} (h : grant i k c hh ∈ l) :
    c ≤ wcap l k := by
  have := maxP_ge (p := capOf k) h
  simpa [capOf] using this

theorem maxCeil_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) : maxCeil T = maxCeil U :=
  maxP_cover ceilOf_of_not_auth dominates_ceil hsub hcov

theorem wcap_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) (k : Nat) : wcap T k = wcap U k :=
  maxP_cover (capOf_of_not_auth k) (dominates_cap k) hsub hcov

/-- `k ∈ W(H)`: some grant in `H` names `k`. -/
def isWriter (H : List Record) (k : Nat) : Prop := ∃ i c hh, grant i k c hh ∈ H

/-- The grant-to-`k` test. -/
def grantsTo (k : Nat) : Record → Bool
  | grant _ j _ _ => decide (j = k)
  | _ => false

/-- `W` as a Boolean test. -/
def writerB (H : List Record) (k : Nat) : Bool := H.any (grantsTo k)

theorem grantsTo_iff {k : Nat} {r : Record} :
    grantsTo k r = true ↔ ∃ i c hh, r = grant i k c hh := by
  cases r with
  | grant i j c h =>
    simp only [grantsTo, decide_eq_true_eq]
    constructor
    · intro hj; subst hj; exact ⟨i, c, h, rfl⟩
    · rintro ⟨i', c', hh, he⟩; cases he; rfl
  | _ => simp [grantsTo]

theorem writerB_iff {H : List Record} {k : Nat} : writerB H k = true ↔ isWriter H k := by
  unfold writerB isWriter
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hg⟩
    obtain ⟨i, c, hh, rfl⟩ := grantsTo_iff.mp hg
    exact ⟨i, c, hh, hr⟩
  · rintro ⟨i, c, hh, hm⟩
    exact ⟨_, hm, grantsTo_iff.mpr ⟨i, c, hh, rfl⟩⟩

/-- The same as `maxCeil_cover`, for `W`. -/
theorem isWriter_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) (k : Nat) : isWriter T k ↔ isWriter U k := by
  constructor
  · rintro ⟨i, c, hh, hm⟩; exact ⟨i, c, hh, hsub _ hm⟩
  · rintro ⟨i, c, hh, hm⟩
    rcases hcov _ hm rfl with hT | ⟨q, hq, hqg⟩
    · exact ⟨i, c, hh, hT⟩
    · obtain ⟨c', h', rfl, _⟩ := dominates_grant hqg
      exact ⟨i, c', h', hq⟩

theorem writerB_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) (k : Nat) : writerB T k = writerB U k :=
  Bool.eq_iff_iff.mpr (by rw [writerB_iff, writerB_iff]; exact isWriter_cover hsub hcov k)

/-- T4': `maxceil(F(H)) = maxceil(H)`. A dominated roster has an undominated
dominator. This dominator has the same signer and a ceiling that is at least
as high. -/
theorem maxCeil_F (H : List Record) : maxCeil (F H) = maxCeil H :=
  maxCeil_cover (fun _ hy => F_subset H hy) (fun _ hy _ => F_covers hy)

/-- T4': `W(F(H)) = W(H)`. A dominated grant has an undominated dominator with
the same issuer and subject. -/
theorem isWriter_F (H : List Record) (k : Nat) : isWriter (F H) k ↔ isWriter H k :=
  isWriter_cover (fun _ hy => F_subset H hy) (fun _ hy _ => F_covers hy) k

/-- T4': `wcap(F(H)) = wcap(H)`. A dominated grant has an undominated
dominator with the same subject and a cap that is at least as high. -/
theorem wcap_F (H : List Record) (k : Nat) : wcap (F H) k = wcap H k :=
  wcap_cover (fun _ hy => F_subset H hy) (fun _ hy _ => F_covers hy) k

theorem isWriter_mono_auth {H H' : List Record} (h : ∀ x ∈ H, isAuth x = true → x ∈ H')
    {k : Nat} (hw : isWriter H k) : isWriter H' k :=
  let ⟨i, c, hh, hm⟩ := hw
  ⟨i, c, hh, h _ hm rfl⟩

/-! ### Admission (§4; T4', T9) -/

/-- A data record is admitted iff its `t` is at most `maxceil`, its author is
in `W` and its `t` is at most `wcap(author)`. Authorization records are
always admitted. Admission reads `W`, `maxceil` and `wcap` and nothing else;
it does not read `revoke`, `root_void` or `W_eff`. -/
def adm (H : List Record) : Record → Bool
  | put _ _ v _ => decide (v.t ≤ maxCeil H) && writerB H v.author && decide (v.t ≤ wcap H v.author)
  | del _ v => decide (v.t ≤ maxCeil H) && writerB H v.author && decide (v.t ≤ wcap H v.author)
  | _ => true

theorem adm_auth {H : List Record} {r : Record} (hr : isAuth r = true) : adm H r = true := by
  cases r <;> first | rfl | simp [isAuth] at hr

/-- Admission depends only on the authorization records, up to covering. -/
theorem adm_cover {T U : List Record} (hsub : ∀ y ∈ T, y ∈ U)
    (hcov : ∀ y ∈ U, isAuth y = true → Cov y T) {r : Record} : adm T r = adm U r := by
  cases r <;> simp only [adm, maxCeil_cover hsub hcov, writerB_cover hsub hcov, wcap_cover hsub hcov]

theorem adm_congr {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') {r : Record} :
    adm H r = adm H' r :=
  adm_cover (fun y hy => (h y).mp hy) (fun y hy _ => Or.inl ((h y).mpr hy))

/-- T4' (monotone admission): if every authorization record of `H` is in `H'`,
then `H'` admits every record that `H` admits. `maxceil`, `W` and `wcap`
all grow with the authorization records. -/
theorem adm_mono {H H' : List Record} (h : ∀ x ∈ H, isAuth x = true → x ∈ H') {r : Record}
    (ha : adm H r = true) : adm H' r = true := by
  have hc : maxCeil H ≤ maxCeil H' := maxP_mono_auth ceilOf_of_not_auth h
  have hw : ∀ k, writerB H k = true → writerB H' k = true :=
    fun k hk => writerB_iff.mpr (isWriter_mono_auth h (writerB_iff.mp hk))
  have hp : ∀ k, wcap H k ≤ wcap H' k := fun k => maxP_mono_auth (capOf_of_not_auth k) h
  cases r with
  | put e f v x =>
    simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
    exact ⟨⟨Nat.le_trans ha.1.1 hc, hw _ ha.1.2⟩, Nat.le_trans ha.2 (hp _)⟩
  | del e v =>
    simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
    exact ⟨⟨Nat.le_trans ha.1.1 hc, hw _ ha.1.2⟩, Nat.le_trans ha.2 (hp _)⟩
  | _ => rfl

/-- T4': admission under the frontier is the same as admission under the
whole set. -/
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
  simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem adm_del_le {H : List Record} {e : Nat} {v : Version}
    (h : adm H (del e v) = true) : v.t ≤ maxCeil H := by
  simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

/-- T9 (write cap): no admitted data record is above its author's cap. -/
theorem adm_put_le_wcap {H : List Record} {e f : Nat} {v : Version} {x : Nat}
    (h : adm H (put e f v x) = true) : v.t ≤ wcap H v.author := by
  simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

theorem adm_del_le_wcap {H : List Record} {e : Nat} {v : Version}
    (h : adm H (del e v) = true) : v.t ≤ wcap H v.author := by
  simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

/-- An admitted data record's author is in `W`. -/
theorem adm_put_writer {H : List Record} {e f : Nat} {v : Version} {x : Nat}
    (h : adm H (put e f v x) = true) : isWriter H v.author := by
  simp only [adm, Bool.and_eq_true, decide_eq_true_eq] at h; exact writerB_iff.mp h.1.2

def admitted (H : List Record) : List Record := H.filter (adm H)

theorem mem_admitted {H : List Record} {x : Record} :
    x ∈ admitted H ↔ x ∈ H ∧ adm H x = true := List.mem_filter

/-! ### The discard model (§4, §10.1) -/

/-- Apply one record. If the record is admitted, `applyD` adds it and reduces
the result to its frontier. If the record is inadmissible, `applyD`
discards it. The record is offered again later.

The store's apply is not `applyD` but `applyH` (below): `Put_Frame` applies
the record and then expires every `del` at or below the horizon `hz` of the
state reached (S7). T4 (b), T10 and T11 (b) are stated for `applyD`.
`expire_applyAllH` relates the two: after the store's expiry, a run under
`applyH` and the same run under `applyD` hold the same records, on the side
condition `NoLateDom` (no record that an expired `del` dominates arrives
after that `del`). -/
def applyD (S : List Record) (r : Record) : List Record := if adm S r then F (S ++ [r]) else S

def applyAllD (S : List Record) (l : List Record) : List Record := l.foldl applyD S

/-- `S` is its own frontier. -/
def Frontier (S : List Record) : Prop := ∀ x ∈ S, ¬ Dom x S

/-- `S` admits every record of `S`. -/
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

/-- Every authorization record that a replica applies stays covered. The
replica never discards it. -/
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

/-- A pass in which admission is already fixed. The start state holds only
records of `U` and covers every authorization record of `U`. From this
state, the application of records of `U` in any order is GC-with-filter
under `adm U`. -/
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

/-- The shape to which every T4 statement reduces. A first phase leaves a
state `T` with these properties:
- `T` holds only records of `U`.
- `T` covers every authorization record of `U`.
- `T` covers every record of the part `P` that is already processed.
Then, if the replica applies the rest `l` of `U`, the result is the
frontier of the admitted records of `U`. -/
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

/-- T4 (a), T18: one pass starts from a frontier of admitted records. It
applies a set's authorization records before its data records. The result
is the frontier of the union's admitted records. This is the shape of a
batch in element-key order (§4), and of a compacted log's replay (§7). -/
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

/-- A16 (a corollary of `auth_first`): a bundle is closed under admission
when its authorization records come first and every data record of the
bundle is admitted once they are applied. Then every data record of the
bundle is held after the bundle, unless a record of the start state or of
the bundle dominates it. No data record of such a bundle waits for a later
session. -/
theorem auth_first_closed {S la ld : List Record} {d : Record} (hF : Frontier S)
    (hA : Admitted S) (hla : ∀ y ∈ la, isAuth y = true) (hld : ∀ y ∈ ld, isAuth y = false)
    (hadm : adm (applyAllD S la) d = true) (hd : d ∈ ld) (hnd : ¬ Dom d (S ++ la ++ ld)) :
    d ∈ applyAllD S (la ++ ld) := by
  rw [auth_first d hF hA hla hld, mem_F_iff, mem_admitted]
  refine ⟨⟨List.mem_append_right _ hd, adm_mono ?_ hadm⟩, ?_⟩
  · intro x hx _
    rcases applyAllD_sub hx with h1 | h1
    · exact List.mem_append_left _ (List.mem_append_left _ h1)
    · exact List.mem_append_left _ (List.mem_append_right _ h1)
  · rintro ⟨q, hq, hqd⟩
    exact hnd ⟨q, (mem_admitted.mp hq).1, hqd⟩

/-- T4 (b): two passes apply the same records, in any order and with any
duplication. The second pass offers again the records that the first pass
refused. The result is the frontier of the union's admitted records. -/
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

/-- T4: two replicas start from the same admitted frontier. Each replica
applies the same set of records twice, in any order and with any
duplication. The two replicas then hold the same frontier. -/
theorem convergence {S l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') (x : Record)
    (hF : Frontier S) (hA : Admitted S) :
    x ∈ applyAllD (applyAllD S l) l ↔ x ∈ applyAllD (applyAllD S l') l' := by
  rw [convergence_two_pass x hF hA, convergence_two_pass x hF hA]
  have hm : ∀ y, y ∈ S ++ l ↔ y ∈ S ++ l' := fun y => by
    rw [List.mem_append, List.mem_append, h y]
  apply F_congr
  intro y
  rw [mem_admitted, mem_admitted, hm y, adm_congr hm]

/-- The empty store is an admitted frontier. `applyD` keeps both properties
(`applyD_frontier`, `applyD_admitted`). So every state that a replica
reaches meets the hypotheses of `auth_first`, `convergence_two_pass` and
`convergence`. -/
theorem frontier_nil : Frontier [] := fun _ hx => absurd hx List.not_mem_nil

theorem admitted_nil : Admitted [] := fun _ hx => absurd hx List.not_mem_nil

/-- T4 from the empty store. -/
theorem convergence_empty {l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') (x : Record) :
    x ∈ applyAllD (applyAllD [] l) l ↔ x ∈ applyAllD (applyAllD [] l') l' :=
  convergence h x frontier_nil admitted_nil

/-! ### Tombstone expiry (§7, T11) -/

/-- A `del` at or below the horizon `h`. This is `Frontier.Expire (F, Hz)`'s
kill predicate for an arbitrary horizon; the store's horizon is `hz` below
(S7). The general-horizon lemmas serve the `hz` ones. -/
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

/-- Expiry removes only `del`s at or below the horizon. -/
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

/-- N1 (general horizon): a later expiry absorbs an earlier one: `expire h₂`
gives the same state whether or not an `expire h₁` with `h₁ ≤ h₂` came
first. `expireHz_expire` is the form for the store's horizon `hz`. -/
theorem expire_expire {h₁ h₂ : Nat} (h : h₁ ≤ h₂) (S : List Record) :
    expire h₂ (expire h₁ S) = expire h₂ S := by
  induction S with
  | nil => rfl
  | cons r S ih =>
    unfold expire at ih ⊢
    cases hr : isExpiredDel h₂ r
    · have hr₁ : isExpiredDel h₁ r = false := by
        cases r <;> simp only [isExpiredDel, decide_eq_false_iff_not] at hr ⊢ <;> omega
      simp [hr, hr₁, ih]
    · cases hr₁ : isExpiredDel h₁ r <;> simp [hr, hr₁, ih]

/-- Two replicas: one holds the data record `d` (state `A`), and one does not
(state `B`). After any further records, `A = F(B ∪ {d})` stays true. -/
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

/-- Re-applying an expired `del`: one replica holds the data record `d`, and
one does not. After the same further records `l` and a re-sent `d`, the two
replicas hold the same records. -/
theorem reapply_same {S l : List Record} {d : Record} (y : Record) (hF : Frontier S)
    (hA : Admitted S) (hd : d ∈ S) (hdata : isAuth d = false) :
    y ∈ applyD (applyAllD (S.erase d) l) d ↔ y ∈ applyAllD S l := by
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
  rw [applyD_pos hadmB, ← hrel y]

/-- T11 (b), apply-then-expire (general horizon): one replica holds the
expired `del` `d`, and one does not. After the same further records `l`, a
re-sent `d` and an expiry at `h`, the two replicas agree on every record.
(In fact, the two replicas agree before the expiry: `reapply_same`.) -/
theorem expire_reapply {S l : List Record} {d : Record} {h : Nat} (x : Record)
    (hF : Frontier S) (hA : Admitted S) (hd : d ∈ S) (hexp : isExpiredDel h d = true) :
    x ∈ expire h (applyD (applyAllD (S.erase d) l) d) ↔ x ∈ expire h (applyAllD S l) := by
  rw [mem_expire, mem_expire, reapply_same x hF hA hd (isAuth_of_expired hexp)]

/-! #### The horizon as a function of the state (S7) -/

/-- `hz(F)`: `maxceil(F) − del_ttl` when `maxceil(F) ≥ del_ttl`, and no
horizon otherwise. `delTtl` is the collection's tombstone lifetime, fixed at
founding (S2); it is a constant of the model, not a roster field. -/
def hz (delTtl : Nat) (H : List Record) : Option Nat :=
  if delTtl ≤ maxCeil H then some (maxCeil H - delTtl) else none

/-- A `del` with `t + del_ttl ≤ m`. Under `m = maxceil(H)`, this is a `del`
at or below `hz(H)` (`isExpiredAt_hz`). -/
def isExpiredAt (delTtl m : Nat) : Record → Bool
  | del _ v => decide (v.t + delTtl ≤ m)
  | _ => false

/-- A `del` is at or below `hz(H)` iff `t + del_ttl ≤ maxceil(H)`. With no
horizon, nothing is expired. -/
theorem isExpiredAt_hz {delTtl : Nat} {H : List Record} {d : Record} :
    isExpiredAt delTtl (maxCeil H) d = true ↔
      ∃ h, hz delTtl H = some h ∧ isExpiredDel h d = true := by
  cases d with
  | del e v =>
    simp only [isExpiredAt, isExpiredDel, hz, decide_eq_true_eq]
    constructor
    · intro hle; exact ⟨_, ite_eq_left (by omega), by omega⟩
    · rintro ⟨h, hh, hle⟩
      split at hh
      · cases hh; omega
      · cases hh
  | _ => simp [isExpiredAt, isExpiredDel]

/-- `hz` reads only `maxceil`. -/
theorem hz_congr {delTtl : Nat} {H H' : List Record} (h : maxCeil H = maxCeil H') :
    hz delTtl H = hz delTtl H' := by
  unfold hz; rw [h]

/-- S7: `hz(F(H)) = hz(H)`. -/
theorem hz_F (delTtl : Nat) (H : List Record) : hz delTtl (F H) = hz delTtl H :=
  hz_congr (maxCeil_F H)

/-- S7: `hz` is monotone. If every authorization record of `H` is in `H'`,
then `H'` has a horizon whenever `H` has one, and not a lower one. (`maxceil`
is monotone, `maxP_mono_auth`.) -/
theorem hz_mono {delTtl : Nat} {H H' : List Record} (hs : ∀ x ∈ H, isAuth x = true → x ∈ H')
    {h : Nat} (hh : hz delTtl H = some h) : ∃ h', hz delTtl H' = some h' ∧ h ≤ h' := by
  have hm : maxCeil H ≤ maxCeil H' := maxP_mono_auth ceilOf_of_not_auth hs
  unfold hz at hh ⊢
  split at hh
  · cases hh; exact ⟨_, ite_eq_left (by omega), by omega⟩
  · cases hh

theorem isAuth_of_expiredAt {delTtl m : Nat} {d : Record} (hd : isExpiredAt delTtl m d = true) :
    isAuth d = false := by
  cases d <;> simp [isExpiredAt, isAuth] at hd ⊢

theorem isExpiredAt_mono {delTtl m m' : Nat} (hm : m ≤ m') {d : Record}
    (hd : isExpiredAt delTtl m d = true) : isExpiredAt delTtl m' d = true := by
  cases d <;> simp only [isExpiredAt, decide_eq_true_eq, Bool.false_eq_true] at hd ⊢; omega

/-- Under a ceiling at most `h + del_ttl`, an expired `del` is at or below
`h`. -/
theorem isExpiredDel_of_At {delTtl m h : Nat} (hm : m ≤ h + delTtl) {d : Record}
    (hd : isExpiredAt delTtl m d = true) : isExpiredDel h d = true := by
  cases d <;> simp only [isExpiredAt, isExpiredDel, decide_eq_true_eq, Bool.false_eq_true] at hd ⊢
  omega

/-- The store's expiry: remove exactly the `del`s at or below `hz` of the
state. -/
def expireHz (delTtl : Nat) (S : List Record) : List Record :=
  S.filter (fun x => !isExpiredAt delTtl (maxCeil S) x)

theorem mem_expireHz {delTtl : Nat} {S : List Record} {x : Record} :
    x ∈ expireHz delTtl S ↔ x ∈ S ∧ isExpiredAt delTtl (maxCeil S) x = false := by
  simp [expireHz]

/-- `expireHz` is `expire` at `hz`, and the identity when there is no
horizon. -/
theorem expireHz_eq {delTtl h : Nat} {S : List Record} (hh : hz delTtl S = some h) :
    expireHz delTtl S = expire h S := by
  unfold expireHz expire
  apply List.filter_congr
  intro x _
  congr 1
  cases he : isExpiredDel h x
  · cases ha : isExpiredAt delTtl (maxCeil S) x
    · rfl
    · obtain ⟨h', hh', he'⟩ := isExpiredAt_hz.mp ha
      rw [hh] at hh'; cases hh'; rw [he] at he'; exact he'.symm
  · exact isExpiredAt_hz.mpr ⟨h, hh, he⟩

theorem expireHz_no_hz {delTtl : Nat} {S : List Record} (hh : hz delTtl S = none) :
    expireHz delTtl S = S := by
  unfold expireHz
  apply List.filter_eq_self.mpr
  intro x _
  cases ha : isExpiredAt delTtl (maxCeil S) x
  · rfl
  · obtain ⟨h', hh', _⟩ := isExpiredAt_hz.mp ha
    rw [hh] at hh'; cases hh'

theorem expireHz_subset (delTtl : Nat) (S : List Record) : expireHz delTtl S ⊆ S :=
  fun _ hx => (mem_expireHz.mp hx).1

theorem expireHz_cover {delTtl : Nat} {S : List Record} :
    ∀ y ∈ S, isAuth y = true → Cov y (expireHz delTtl S) := by
  intro y hy ha
  refine Or.inl (mem_expireHz.mpr ⟨hy, ?_⟩)
  cases he : isExpiredAt delTtl (maxCeil S) y
  · rfl
  · rw [isAuth_of_expiredAt he] at ha; exact absurd ha Bool.false_ne_true

/-- Expiry keeps every authorization record, so it keeps `maxceil` and
`hz`. -/
theorem maxCeil_expireHz (delTtl : Nat) (S : List Record) :
    maxCeil (expireHz delTtl S) = maxCeil S :=
  maxCeil_cover (fun _ hy => expireHz_subset delTtl S hy) expireHz_cover

/-- T11 (a) with `hz`: after the store's expiry, no `del` at or below the
horizon of the resulting state is held. -/
theorem expireHz_none {delTtl : Nat} {S : List Record} {x : Record}
    (hx : x ∈ expireHz delTtl S) :
    isExpiredAt delTtl (maxCeil (expireHz delTtl S)) x = false := by
  rw [maxCeil_expireHz]; exact (mem_expireHz.mp hx).2

/-- T11 (a) with `hz`: expiry removes only `del`s at or below `hz`. -/
theorem expireHz_only_del {delTtl : Nat} {S : List Record} {x : Record} (hx : x ∈ S)
    (hn : x ∉ expireHz delTtl S) :
    ∃ e v h, x = del e v ∧ hz delTtl S = some h ∧ v.t ≤ h := by
  cases hk : isExpiredAt delTtl (maxCeil S) x
  · exact absurd (mem_expireHz.mpr ⟨hx, hk⟩) hn
  · obtain ⟨h, hh, he⟩ := isExpiredAt_hz.mp hk
    cases x with
    | del e v =>
      simp only [isExpiredDel, decide_eq_true_eq] at he; exact ⟨e, v, h, rfl, hh, he⟩
    | _ => simp [isExpiredDel] at he

/-- T11 (a) with `hz`: expiring a frontier leaves a frontier. -/
theorem expireHz_frontier {delTtl : Nat} {S : List Record} (hF : Frontier S) :
    Frontier (expireHz delTtl S) :=
  fun x hx hd => hF x (expireHz_subset _ S hx) (Dom_mono hd (expireHz_subset _ S))

/-- T11 (a) with `hz`: expiry changes no register and no admission. -/
theorem expireHz_adm {delTtl : Nat} {S : List Record} {r : Record} :
    adm (expireHz delTtl S) r = adm S r :=
  adm_cover (fun _ hy => expireHz_subset _ S hy) expireHz_cover

theorem expireHz_admitted {delTtl : Nat} {S : List Record} (hA : Admitted S) :
    Admitted (expireHz delTtl S) := by
  intro x hx
  rw [expireHz_adm]
  exact hA x (expireHz_subset _ S hx)

/-- N1 with `hz`: an earlier expiry at any horizon `h ≤ hz(S)` is absorbed by
the store's expiry. Since `hz` never decreases (`hz_mono`), the earlier
expiries of a replica do not matter. -/
theorem expireHz_expire {delTtl h : Nat} {S : List Record} (hh : h + delTtl ≤ maxCeil S) :
    expireHz delTtl (expire h S) = expireHz delTtl S := by
  have hm : maxCeil (expire h S) = maxCeil S :=
    maxCeil_cover (fun _ hy => expire_subset h S hy)
      (fun _ hy ha => Or.inl (expire_keeps hy (isExpiredDel_auth ha)))
  show (expire h S).filter (fun x => !isExpiredAt delTtl (maxCeil (expire h S)) x) = _
  rw [hm]
  unfold expireHz expire
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  cases x with
  | del e v =>
    simp only [isExpiredAt, isExpiredDel]
    by_cases h1 : v.t + delTtl ≤ maxCeil S
    · rw [decide_eq_true h1]; cases decide (v.t ≤ h) <;> rfl
    · rw [decide_eq_false h1, decide_eq_false (show ¬ v.t ≤ h by omega)]; rfl
  | _ => rfl

/-- N1 with `hz`: a second expiry does nothing. -/
theorem expireHz_idem (delTtl : Nat) (S : List Record) :
    expireHz delTtl (expireHz delTtl S) = expireHz delTtl S := by
  show (expireHz delTtl S).filter
    (fun x => !isExpiredAt delTtl (maxCeil (expireHz delTtl S)) x) = _
  rw [maxCeil_expireHz]
  unfold expireHz
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  cases (isExpiredAt delTtl (maxCeil S) x) <;> rfl

/-- The store's expiry is a function of the held set. -/
theorem expireHz_congr {delTtl : Nat} {A B : List Record} (h : ∀ y, y ∈ A ↔ y ∈ B)
    (x : Record) : x ∈ expireHz delTtl A ↔ x ∈ expireHz delTtl B := by
  rw [mem_expireHz, mem_expireHz, h x, show maxCeil A = maxCeil B from maxP_congr ceilOf h]

/-- T11 (b) with `hz`: one replica holds the expired `del` `d`, and one does
not. After the same further records `l`, a re-sent `d` and the store's
expiry, the two replicas agree on every record. -/
theorem expireHz_reapply {delTtl : Nat} {S l : List Record} {d : Record} (x : Record)
    (hF : Frontier S) (hA : Admitted S) (hd : d ∈ S)
    (hexp : isExpiredAt delTtl (maxCeil S) d = true) :
    x ∈ expireHz delTtl (applyD (applyAllD (S.erase d) l) d) ↔
      x ∈ expireHz delTtl (applyAllD S l) :=
  expireHz_congr (fun y => reapply_same y hF hA hd (isAuth_of_expiredAt hexp)) x

/-! #### Expiry on arrival (G1) -/

/-- The store's apply (`Put_Frame`, S7): `applyD`, then the store's expiry at
`hz` of the state reached. A `del` at or below the horizon is gone in the
step it arrives, and a roster that raises `maxceil` expires the `del`s that
the new horizon covers in the same step. No local clock is read. -/
def applyH (delTtl : Nat) (S : List Record) (r : Record) : List Record :=
  expireHz delTtl (applyD S r)

def applyAllH (delTtl : Nat) (S l : List Record) : List Record := l.foldl (applyH delTtl) S

/-- The store never holds a `del` at or below its own horizon, even for one
step. -/
theorem applyH_clean {delTtl : Nat} {S : List Record} {r y : Record}
    (hy : y ∈ applyH delTtl S r) :
    isExpiredAt delTtl (maxCeil (applyH delTtl S r)) y = false :=
  expireHz_none hy

/-- `maxceil` never decreases along a run. -/
theorem maxCeil_le_applyAllD (T l : List Record) : maxCeil T ≤ maxCeil (applyAllD T l) :=
  maxP_le_cov ceilOf_of_not_auth dominates_ceil fun _ hy _ => applyAllD_cov (Or.inl hy)

/-- The side condition of G1, for a bound `h` on the run's horizons: no
record that a `del` at or below `h` dominates arrives after that `del`.
Under `applyD` the `del` would stay and remove such a record; under
`applyH` the `del` may be gone before the record arrives. -/
def NoLateDom (h : Nat) : List Record → Prop
  | [] => True
  | r :: l => (isExpiredDel h r = true → ∀ q ∈ l, dominates r q = false) ∧ NoLateDom h l

/-- The invariant of a run under `applyH` (state `A`) against the same run
under `applyD` (state `B`), with the records `l` still to come and a bound
`h` on every horizon of the run:
- `A ⊆ B`, and `B` is a frontier (so `A` is one).
- `A` holds no `del` at or below the current horizon.
- Every record of `B ∖ A` is a `del` at or below the current horizon.
- No `del` of `B` at or below `h` dominates a record of `l`.
- The run's last ceiling is at most `h + del_ttl`. -/
def HRel (delTtl h : Nat) (A B l : List Record) : Prop :=
  (∀ y ∈ A, y ∈ B) ∧ Frontier B ∧
  (∀ y ∈ A, isExpiredAt delTtl (maxCeil B) y = false) ∧
  (∀ y ∈ B, y ∉ A → isExpiredAt delTtl (maxCeil B) y = true) ∧
  (∀ y ∈ B, isExpiredDel h y = true → ∀ q ∈ l, dominates y q = false) ∧
  maxCeil (applyAllD B l) ≤ h + delTtl

/-- `A` covers every authorization record of `B`: the difference holds only
`del`s. -/
theorem HRel_cov {delTtl h : Nat} {A B l : List Record} (hR : HRel delTtl h A B l) :
    ∀ y ∈ B, isAuth y = true → Cov y A := by
  obtain ⟨_, _, _, hdiff, _, _⟩ := hR
  intro y hy ha
  by_cases hyA : y ∈ A
  · exact Or.inl hyA
  · rw [isAuth_of_expiredAt (hdiff y hy hyA)] at ha; exact absurd ha Bool.false_ne_true

theorem HRel_adm {delTtl h : Nat} {A B l : List Record} (hR : HRel delTtl h A B l)
    (r : Record) : adm A r = adm B r :=
  adm_cover hR.1 (HRel_cov hR)

theorem HRel_maxCeil {delTtl h : Nat} {A B l : List Record} (hR : HRel delTtl h A B l) :
    maxCeil A = maxCeil B :=
  maxCeil_cover hR.1 (HRel_cov hR)

/-- After the store's expiry, the two states hold the same records. -/
theorem HRel_expire {delTtl h : Nat} {A B l : List Record} (hR : HRel delTtl h A B l)
    (x : Record) : x ∈ expireHz delTtl A ↔ x ∈ expireHz delTtl B := by
  have hm := HRel_maxCeil hR
  obtain ⟨hsub, _, _, hdiff, _, _⟩ := hR
  rw [mem_expireHz, mem_expireHz, hm]
  constructor
  · rintro ⟨hx, he⟩; exact ⟨hsub x hx, he⟩
  · rintro ⟨hx, he⟩
    refine ⟨?_, he⟩
    by_cases hxA : x ∈ A
    · exact hxA
    · rw [hdiff x hx hxA] at he; exact absurd he.symm Bool.false_ne_true

/-- One step keeps the invariant. A record of `B ∖ A` is a `del` at or below
the current horizon, so at or below `h`; it dominates neither a record of
`A` (`B` is a frontier) nor the new record `r`, so
`F (A ++ [r]) ⊆ F (B ++ [r])`. A `del` that the step's horizon expires
from `A` joins `B ∖ A`; the horizon only rises, so the old members of
`B ∖ A` stay expired. -/
theorem HRel_step {delTtl h : Nat} {A B : List Record} {r : Record} {l : List Record}
    (hR : HRel delTtl h A B (r :: l))
    (hr : isExpiredDel h r = true → ∀ q ∈ l, dominates r q = false) :
    HRel delTtl h (applyH delTtl A r) (applyD B r) l := by
  have hadm := HRel_adm hR r
  obtain ⟨hsub, hFB, hA, hdiff, hlate, hbound⟩ := hR
  have hdl : ∀ y ∈ B, y ∉ A → ∀ q ∈ r :: l, dominates y q = false := by
    intro y hy hyA
    refine hlate y hy (isExpiredDel_of_At ?_ (hdiff y hy hyA))
    exact Nat.le_trans (maxCeil_le_applyAllD B (r :: l)) hbound
  -- (i) `applyD A r ⊆ applyD B r`, (ii) the rest of `applyD B r` is `B ∖ A`.
  have hi : ∀ y ∈ applyD A r, y ∈ applyD B r := by
    intro y hy
    cases hB : adm B r with
    | false => rw [applyD_neg (hadm.trans hB)] at hy; rw [applyD_neg hB]; exact hsub y hy
    | true =>
      rw [applyD_pos (hadm.trans hB)] at hy; rw [applyD_pos hB]
      obtain ⟨hyA, hnd⟩ := mem_F_iff.mp hy
      have hyB : y ∈ B ++ [r] := by
        rcases List.mem_append.mp hyA with h1 | h1
        · exact List.mem_append_left _ (hsub y h1)
        · exact List.mem_append_right _ h1
      refine mem_F_iff.mpr ⟨hyB, ?_⟩
      rintro ⟨q, hq, hqy⟩
      by_cases hqA : q ∈ A ++ [r]
      · exact hnd ⟨q, hqA, hqy⟩
      · have hqB : q ∈ B := by
          rcases List.mem_append.mp hq with h1 | h1
          · exact h1
          · exact absurd (List.mem_append_right _ h1) hqA
        have hqA' : q ∉ A := fun h1 => hqA (List.mem_append_left _ h1)
        rcases List.mem_append.mp hyA with h1 | h1
        · exact hFB y (hsub y h1) ⟨q, hqB, hqy⟩
        · rw [List.mem_singleton.mp h1, hdl q hqB hqA' r (List.mem_cons_self ..)] at hqy
          exact Bool.false_ne_true hqy
  have hii : ∀ y ∈ applyD B r, y ∈ applyD A r ∨ (y ∈ B ∧ y ∉ A) := by
    intro y hy
    cases hB : adm B r with
    | false =>
      rw [applyD_neg hB] at hy; rw [applyD_neg (hadm.trans hB)]
      by_cases hyA : y ∈ A
      · exact Or.inl hyA
      · exact Or.inr ⟨hy, hyA⟩
    | true =>
      rw [applyD_pos hB] at hy; rw [applyD_pos (hadm.trans hB)]
      obtain ⟨hyB, hnd⟩ := mem_F_iff.mp hy
      have hsub' : ∀ z, z ∈ A ++ [r] → z ∈ B ++ [r] := by
        intro z hz
        rcases List.mem_append.mp hz with h1 | h1
        · exact List.mem_append_left _ (hsub z h1)
        · exact List.mem_append_right _ h1
      by_cases hyA : y ∈ A ++ [r]
      · exact Or.inl (mem_F_iff.mpr ⟨hyA, fun hd => hnd (Dom_mono hd hsub')⟩)
      · refine Or.inr ⟨?_, fun h1 => hyA (List.mem_append_left _ h1)⟩
        rcases List.mem_append.mp hyB with h1 | h1
        · exact h1
        · exact absurd (List.mem_append_right _ h1) hyA
  have hm : maxCeil (applyD A r) = maxCeil (applyD B r) := by
    refine maxCeil_cover hi ?_
    intro y hy ha
    rcases hii y hy with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · rw [isAuth_of_expiredAt (hdiff y h1 h2)] at ha; exact absurd ha Bool.false_ne_true
  have hmB : maxCeil B ≤ maxCeil (applyD B r) := maxCeil_le_applyAllD B [r]
  refine ⟨?_, applyD_frontier hFB, ?_, ?_, ?_, hbound⟩
  · intro y hy; exact hi y (expireHz_subset _ _ hy)
  · intro y hy; rw [← hm]; exact (mem_expireHz.mp hy).2
  · intro y hy hyA
    rcases hii y hy with h1 | ⟨h1, h2⟩
    · rw [← hm]
      cases he : isExpiredAt delTtl (maxCeil (applyD A r)) y
      · exact absurd (mem_expireHz.mpr ⟨h1, he⟩) hyA
      · rfl
    · exact isExpiredAt_mono hmB (hdiff y h1 h2)
  · intro y hy he q hq
    rcases applyD_sub hy with h1 | h1
    · exact hlate y h1 he q (List.mem_cons_of_mem _ hq)
    · rw [h1] at he ⊢; exact hr he q hq

theorem HRel_run {delTtl h : Nat} (l : List Record) :
    ∀ (A B : List Record), HRel delTtl h A B l → NoLateDom h l →
      ∀ x, x ∈ expireHz delTtl (applyAllH delTtl A l) ↔ x ∈ expireHz delTtl (applyAllD B l) := by
  induction l with
  | nil => intro A B hR _ x; exact HRel_expire hR x
  | cons r l ih => intro A B hR hl x; exact ih _ _ (HRel_step hR hl.1) hl.2 x

/-- G1: a run under the store's apply (`applyH`, expiry at `hz` on every
step) and the same run under the model's apply (`applyD`) agree after the
store's expiry. The hypotheses: the start state is a frontier that holds no
`del` at or below its own horizon (every state the store reaches is one,
`applyH_clean`); `h` bounds the run's last horizon (`hz` never decreases,
so it bounds every horizon of the run); and no record that a `del` at or
below `h` dominates arrives after that `del`, from the start state or from
the run (`NoLateDom`). Without the side condition the two differ: under
`applyD` the held `del` removes the late record; under `applyH` the `del`
is already gone. -/
theorem expire_applyAllH {delTtl h : Nat} {S l : List Record} (x : Record) (hF : Frontier S)
    (hS : ∀ y ∈ S, isExpiredAt delTtl (maxCeil S) y = false)
    (hSl : ∀ y ∈ S, isExpiredDel h y = true → ∀ q ∈ l, dominates y q = false)
    (hl : NoLateDom h l) (hb : maxCeil (applyAllD S l) ≤ h + delTtl) :
    x ∈ expireHz delTtl (applyAllH delTtl S l) ↔ x ∈ expireHz delTtl (applyAllD S l) :=
  HRel_run l S S ⟨fun _ hy => hy, hF, hS, fun _ hy hyA => absurd hy hyA, hSl, hb⟩ hl x

/-- G1 at the run's own horizon: `h = hz` of the state that `applyD` reaches. -/
theorem expire_applyAllH_hz {delTtl h : Nat} {S l : List Record} (x : Record) (hF : Frontier S)
    (hS : ∀ y ∈ S, isExpiredAt delTtl (maxCeil S) y = false)
    (hSl : ∀ y ∈ S, isExpiredDel h y = true → ∀ q ∈ l, dominates y q = false)
    (hl : NoLateDom h l) (hh : hz delTtl (applyAllD S l) = some h) :
    x ∈ expireHz delTtl (applyAllH delTtl S l) ↔ x ∈ expireHz delTtl (applyAllD S l) := by
  refine expire_applyAllH x hF hS hSl hl ?_
  unfold hz at hh
  split at hh
  · cases hh; omega
  · cases hh

/-- A16 under the store's apply: a bundle closed under admission (as in
`auth_first_closed`) keeps every data record that no record of the start
state or of the bundle dominates and that is above the horizon of the
state reached, on the side conditions of G1. -/
theorem auth_first_closed_H {delTtl h : Nat} {S la ld : List Record} {d : Record}
    (hF : Frontier S) (hA : Admitted S) (hla : ∀ y ∈ la, isAuth y = true)
    (hld : ∀ y ∈ ld, isAuth y = false) (hadm : adm (applyAllD S la) d = true) (hd : d ∈ ld)
    (hnd : ¬ Dom d (S ++ la ++ ld))
    (hS : ∀ y ∈ S, isExpiredAt delTtl (maxCeil S) y = false)
    (hSl : ∀ y ∈ S, isExpiredDel h y = true → ∀ q ∈ la ++ ld, dominates y q = false)
    (hl : NoLateDom h (la ++ ld)) (hb : maxCeil (applyAllD S (la ++ ld)) ≤ h + delTtl)
    (hlive : isExpiredAt delTtl (maxCeil (applyAllD S (la ++ ld))) d = false) :
    d ∈ applyAllH delTtl S (la ++ ld) := by
  have hD := auth_first_closed hF hA hla hld hadm hd hnd
  have hE : d ∈ expireHz delTtl (applyAllD S (la ++ ld)) := mem_expireHz.mpr ⟨hD, hlive⟩
  exact expireHz_subset _ _ ((expire_applyAllH d hF hS hSl hl hb).mpr hE)

/-! ### Views (§3, §6; T5, T12). `founding` is the collection's founding
key. -/

/-- `root_void(k)`: the founding key revoked `k`. This view ignores the
revocation's `from_t`. The founding key is never root-voided. -/
def rootVoid (founding : Nat) (H : List Record) (k : Nat) : Prop :=
  k ≠ founding ∧ ∃ f hh, revoke founding k f hh ∈ H

/-- `k ∈ W_eff`: a grant of `k` by an issuer that is not root-voided. -/
def wEff (founding : Nat) (H : List Record) (k : Nat) : Prop :=
  ∃ i c hh, grant i k c hh ∈ H ∧ ¬ rootVoid founding H i

/-- The `REVOKE` clause of `void` for a record by `a` at time `t`. -/
def revokeVoids (founding : Nat) (H : List Record) (a t : Nat) : Prop :=
  ∃ i f hh, revoke i a f hh ∈ H ∧ f ≤ t ∧ ¬ rootVoid founding H i

/-- `void(p)` for a data record. It is false for the other kinds. -/
def voided (founding : Nat) (H : List Record) : Record → Prop
  | put _ _ v _ => revokeVoids founding H v.author v.t ∨ ¬ wEff founding H v.author
  | del _ v => revokeVoids founding H v.author v.t ∨ ¬ wEff founding H v.author
  | _ => False

/-- A held revocation has, in `F(H)`, a revocation of the same issuer and
subject whose `from_t` is not higher (S5): a maximal dominator. -/
theorem revoke_cover_F {H : List Record} {i s f h : Nat} (hm : revoke i s f h ∈ H) :
    ∃ f' h', revoke i s f' h' ∈ F H ∧ f' ≤ f := by
  rcases F_covers hm with hF | ⟨q, hq, hqr⟩
  · exact ⟨f, h, hF, Nat.le_refl f⟩
  · obtain ⟨f', h', rfl, hle⟩ := dominates_revoke hqr
    exact ⟨f', h', hq, hle⟩

/-- `f` is the minimum `from_t` of the held revocations of `k` by `i`. -/
def IsMinFrom (H : List Record) (i k f : Nat) : Prop :=
  (∃ hh, revoke i k f hh ∈ H) ∧ ∀ f' hh, revoke i k f' hh ∈ H → f ≤ f'

/-- S5: the minimum `from_t` of the revocations of a key is the same before
and after the removal of dominated records. So `root_void`, `void` and
`revoked`, which read only that minimum, are unchanged by the REVOKE clause
of domination. -/
theorem isMinFrom_F {H : List Record} {i k f : Nat} : IsMinFrom (F H) i k f ↔ IsMinFrom H i k f := by
  constructor
  · rintro ⟨⟨hh, hm⟩, hmin⟩
    refine ⟨⟨hh, F_subset H hm⟩, fun f' hh' hm' => ?_⟩
    obtain ⟨f'', h'', hF, hle⟩ := revoke_cover_F hm'
    exact Nat.le_trans (hmin f'' h'' hF) hle
  · rintro ⟨⟨hh, hm⟩, hmin⟩
    refine ⟨?_, fun f' hh' hm' => hmin f' hh' (F_subset H hm')⟩
    obtain ⟨f'', h'', hF, hle⟩ := revoke_cover_F hm
    have : f ≤ f'' := hmin f'' h'' (F_subset H hF)
    have he : f'' = f := Nat.le_antisymm hle this
    exact ⟨h'', he ▸ hF⟩

/-- T12: `root_void` is monotone in the held set. -/
theorem rootVoid_mono {f : Nat} {H H' : List Record} {k : Nat} (hs : H ⊆ H')
    (h : rootVoid f H k) : rootVoid f H' k :=
  let ⟨hk, fr, hh, hm⟩ := h
  ⟨hk, fr, hh, hs hm⟩

theorem rootVoid_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (k : Nat) :
    rootVoid f H k ↔ rootVoid f H' k :=
  ⟨rootVoid_mono (fun y hy => (h y).mp hy), rootVoid_mono (fun y hy => (h y).mpr hy)⟩

/-- T5: `root_void(F(H)) = root_void(H)`: a dominated revocation has an
undominated dominator of the same issuer and subject. -/
theorem rootVoid_F {f : Nat} {H : List Record} {k : Nat} : rootVoid f (F H) k ↔ rootVoid f H k := by
  unfold rootVoid
  constructor
  · rintro ⟨hk, fr, hh, hm⟩; exact ⟨hk, fr, hh, F_subset H hm⟩
  · rintro ⟨hk, fr, hh, hm⟩
    obtain ⟨f', h', hF, _⟩ := revoke_cover_F hm
    exact ⟨hk, f', h', hF⟩

theorem wEff_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (k : Nat) :
    wEff f H k ↔ wEff f H' k := by
  unfold wEff
  constructor
  · rintro ⟨i, c, hh, hm, hv⟩
    exact ⟨i, c, hh, (h _).mp hm, fun hv' => hv ((rootVoid_congr h i).mpr hv')⟩
  · rintro ⟨i, c, hh, hm, hv⟩
    exact ⟨i, c, hh, (h _).mpr hm, fun hv' => hv ((rootVoid_congr h i).mp hv')⟩

/-- T5: `W_eff(F(H)) = W_eff(H)`. A dominated grant has an undominated
dominator with the same issuer and subject. -/
theorem wEff_F {f : Nat} {H : List Record} {k : Nat} : wEff f (F H) k ↔ wEff f H k := by
  unfold wEff
  constructor
  · rintro ⟨i, c, hh, hm, hv⟩
    exact ⟨i, c, hh, F_subset H hm, fun hv' => hv (rootVoid_F.mpr hv')⟩
  · rintro ⟨i, c, hh, hm, hv⟩
    have hv' : ¬ rootVoid f (F H) i := fun h' => hv (rootVoid_F.mp h')
    rcases F_covers hm with hF | ⟨q, hq, hqg⟩
    · exact ⟨i, c, hh, hF, hv'⟩
    · obtain ⟨c', h', rfl, _⟩ := dominates_grant hqg
      exact ⟨i, c', h', hq, hv'⟩

/-- T12: for a fixed `root_void` set, `W_eff` is monotone (a `GRANT` can only
un-void). -/
theorem wEff_mono_fixed {f : Nat} {H H' : List Record} {k : Nat} (hs : H ⊆ H')
    (hfix : ∀ i, rootVoid f H' i → rootVoid f H i) (h : wEff f H k) : wEff f H' k :=
  let ⟨i, c, hh, hm, hv⟩ := h
  ⟨i, c, hh, hs hm, fun hv' => hv (hfix i hv')⟩

/-- T12: for a fixed `root_void` set, the `REVOKE` clause of `void` is
monotone (a `REVOKE` can only void). -/
theorem voided_revoke_mono {f : Nat} {H H' : List Record} {a t : Nat} (hs : H ⊆ H')
    (hfix : ∀ i, rootVoid f H' i → rootVoid f H i) (h : revokeVoids f H a t) :
    revokeVoids f H' a t :=
  let ⟨i, fr, hh, hm, hle, hv⟩ := h
  ⟨i, fr, hh, hs hm, hle, fun hv' => hv (hfix i hv')⟩

theorem revokeVoids_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (a t : Nat) :
    revokeVoids f H a t ↔ revokeVoids f H' a t := by
  unfold revokeVoids
  constructor
  · rintro ⟨i, fr, hh, hm, hle, hv⟩
    exact ⟨i, fr, hh, (h _).mp hm, hle, fun hv' => hv ((rootVoid_congr h i).mpr hv')⟩
  · rintro ⟨i, fr, hh, hm, hle, hv⟩
    exact ⟨i, fr, hh, (h _).mpr hm, hle, fun hv' => hv ((rootVoid_congr h i).mp hv')⟩

theorem revokeVoids_F {f : Nat} {H : List Record} {a t : Nat} :
    revokeVoids f (F H) a t ↔ revokeVoids f H a t := by
  unfold revokeVoids
  constructor
  · rintro ⟨i, fr, hh, hm, hle, hv⟩
    exact ⟨i, fr, hh, F_subset H hm, hle, fun hv' => hv (rootVoid_F.mpr hv')⟩
  · rintro ⟨i, fr, hh, hm, hle, hv⟩
    obtain ⟨f', h', hF, hf⟩ := revoke_cover_F hm
    exact ⟨i, f', h', hF, Nat.le_trans hf hle, fun hv' => hv (rootVoid_F.mp hv')⟩

/-- T5: `void` is a function of the held set. -/
theorem voided_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (x : Record) :
    voided f H x ↔ voided f H' x := by
  cases x <;> simp only [voided, revokeVoids_congr h, wEff_congr h]

/-- T5: `void(F(H)) = void(H)`. -/
theorem voided_F {f : Nat} {H : List Record} (x : Record) : voided f (F H) x ↔ voided f H x := by
  cases x <;> simp only [voided, revokeVoids_F, wEff_F]

/-! #### `ROSTER_eff` -/

/-- `root_void` as a Boolean test. -/
def revokesRoot (founding k : Nat) : Record → Bool
  | revoke i j _ _ => decide (i = founding ∧ j = k)
  | _ => false

def rootVoidB (founding : Nat) (H : List Record) (k : Nat) : Bool :=
  decide (k ≠ founding) && H.any (revokesRoot founding k)

theorem revokesRoot_iff {f k : Nat} {r : Record} :
    revokesRoot f k r = true ↔ ∃ fr hh, r = revoke f k fr hh := by
  cases r with
  | revoke i j fr hh =>
    simp only [revokesRoot, decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨fr, hh, rfl⟩
    · rintro ⟨_, _, he⟩; cases he; exact ⟨rfl, rfl⟩
  | _ => simp [revokesRoot]

theorem rootVoidB_iff {f : Nat} {H : List Record} {k : Nat} :
    rootVoidB f H k = true ↔ rootVoid f H k := by
  unfold rootVoidB rootVoid
  rw [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨hk, r, hr, hrv⟩
    obtain ⟨fr, hh, rfl⟩ := revokesRoot_iff.mp hrv
    exact ⟨hk, fr, hh, hr⟩
  · rintro ⟨hk, fr, hh, hm⟩
    exact ⟨hk, _, hm, revokesRoot_iff.mpr ⟨fr, hh, rfl⟩⟩

theorem rootVoidB_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (k : Nat) :
    rootVoidB f H k = rootVoidB f H' k :=
  Bool.eq_iff_iff.mpr (by rw [rootVoidB_iff, rootVoidB_iff]; exact rootVoid_congr h k)

theorem rootVoidB_F {f : Nat} {H : List Record} (k : Nat) : rootVoidB f (F H) k = rootVoidB f H k :=
  Bool.eq_iff_iff.mpr (by rw [rootVoidB_iff, rootVoidB_iff]; exact rootVoid_F)

/-- The candidates for `ROSTER_eff`: rosters whose signer is not
root-voided. -/
def isRosterOK (founding : Nat) (H : List Record) : Record → Bool
  | roster s _ _ _ => !rootVoidB founding H s
  | _ => false

theorem isRosterOK_roster {f : Nat} {H : List Record} {r : Record} (h : isRosterOK f H r = true) :
    ∃ s c g hh, r = roster s c g hh := by
  cases r with
  | roster s c g hh => exact ⟨s, c, g, hh, rfl⟩
  | _ => simp [isRosterOK] at h

theorem isRosterOK_congr {f : Nat} {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') :
    isRosterOK f H = isRosterOK f H' := by
  funext r
  cases r <;> simp only [isRosterOK, rootVoidB_congr h]

theorem isRosterOK_F {f : Nat} {H : List Record} : isRosterOK f (F H) = isRosterOK f H := by
  funext r
  cases r <;> simp only [isRosterOK, rootVoidB_F]

/-- The whole roster tuple, in comparison order: `(gen, h, signer, ceil)`
(S4: `ROSTER_eff` is the `(gen, h)`-maximum; there is no epoch). The model
does not assume that `h` is injective, so the last two fields make the
order total on rosters. -/
abbrev RKey := Nat × Nat × Nat × Nat

def rkey : Record → RKey
  | roster s c g h => (g, h, s, c)
  | _ => (0, 0, 0, 0)

/-- Lexicographic order on four-tuples. -/
def lexLt (p q : RKey) : Bool :=
  decide (p.1 < q.1 ∨ (p.1 = q.1 ∧ (p.2.1 < q.2.1 ∨ (p.2.1 = q.2.1 ∧
    (p.2.2.1 < q.2.2.1 ∨ (p.2.2.1 = q.2.2.1 ∧ p.2.2.2 < q.2.2.2))))))

/-- The order that `ROSTER_eff` maximizes. On rosters, it is a strict total
order. -/
def rkLt (a b : Record) : Bool := lexLt (rkey a) (rkey b)

theorem lexLt_asymm {p q : RKey} (h : lexLt p q = true) : lexLt q p = false := by
  simp only [lexLt, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢; omega

theorem lexLt_irrefl (p : RKey) : lexLt p p = false := by
  simp only [lexLt, decide_eq_false_iff_not]; omega

theorem lexLt_le_trans {p q r : RKey} (h₁ : lexLt p q = false) (h₂ : lexLt q r = false) :
    lexLt p r = false := by
  simp only [lexLt, decide_eq_false_iff_not] at h₁ h₂ ⊢; omega

theorem lexLt_antisymm {p q : RKey} (h₁ : lexLt p q = false) (h₂ : lexLt q p = false) :
    p = q := by
  obtain ⟨a1, a2, a3, a4⟩ := p
  obtain ⟨b1, b2, b3, b4⟩ := q
  simp only [lexLt, decide_eq_false_iff_not] at h₁ h₂
  simp only [Prod.mk.injEq]
  omega

theorem rkey_inj {a b : Record} (ha : ∃ s c g hh, a = roster s c g hh)
    (hb : ∃ s c g hh, b = roster s c g hh) (h : rkey a = rkey b) : a = b := by
  obtain ⟨s, c, g, hh, rfl⟩ := ha
  obtain ⟨s', c', g', hh', rfl⟩ := hb
  simp only [rkey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- A dominating roster is strictly greater in the `ROSTER_eff` order: its
`gen` is greater. -/
theorem dominates_rkLt {s c g hh : Nat} {p : Record}
    (h : dominates p (roster s c g hh) = true) : rkLt (roster s c g hh) p = true := by
  obtain ⟨c', g', h', rfl, _, hg⟩ := dominates_roster h
  simp only [rkLt, rkey, lexLt, decide_eq_true_eq]
  omega

/-- One fold step of `ROSTER_eff`: keep the larger candidate. -/
def maxStep (cand : Record → Bool) (acc : Option Record) (r : Record) : Option Record :=
  if cand r then
    match acc with
    | none => some r
    | some a => if rkLt a r then some r else some a
  else acc

/-- `ROSTER_eff`: of the rosters whose signer is not root-voided, the one that
is maximal under `(gen, h, signer, ceil)`. This order is a strict total
order on rosters. If there is no such roster, the value is `none`. -/
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
    (hc : ∀ r, cand r = true → ∃ s c g hh, r = roster s c g hh)
    (h : IsMaxR cand l m) (h' : IsMaxR cand l m') : m = m' :=
  rkey_inj (hc m h.2.1) (hc m' h'.2.1)
    (lexLt_antisymm (h.2.2 m' h'.1 h'.2.1) (h'.2.2 m h.1 h.2.1))

theorem maxOf_eq {cand : Record → Bool} {l : List Record} {m : Record}
    (hc : ∀ r, cand r = true → ∃ s c g hh, r = roster s c g hh)
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
  have hc : ∀ r, isRosterOK f H r = true → ∃ s c g hh, r = roster s c g hh :=
    fun _ hr => isRosterOK_roster hr
  cases hr : H.foldl (maxStep (isRosterOK f H)) none with
  | none =>
    have hn := maxOf_none.mp hr
    exact (maxOf_none.mpr fun r hr' => hn r ((h r).mpr hr')).symm
  | some m =>
    obtain ⟨h1, h2, h3⟩ := maxOf_some hr
    exact (maxOf_eq hc ⟨(h m).mp h1, h2, fun r hr' hc' => h3 r ((h r).mpr hr') hc'⟩).symm

/-- T5: `ROSTER_eff(F(H)) = ROSTER_eff(H)`. The maximum is undominated. A
dominator has the same signer, so it is also a candidate. A dominator also
has a strictly greater `gen`, so it is strictly greater under
`(gen, h, …)`. -/
theorem rosterEff_F {f : Nat} {H : List Record} : rosterEff f (F H) = rosterEff f H := by
  unfold rosterEff
  rw [isRosterOK_F]
  have hc : ∀ r, isRosterOK f H r = true → ∃ s c g hh, r = roster s c g hh :=
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
      obtain ⟨s, c, g, hh, rfl⟩ := hc m h2
      obtain ⟨c', g', h', rfl, _, _⟩ := dominates_roster hqm
      have hqc : isRosterOK f H (roster s c' g' h') = true := by
        simp only [isRosterOK] at h2 ⊢; exact h2
      have hlt := dominates_rkLt hqm
      rw [h3 _ hq hqc] at hlt
      exact Bool.false_ne_true hlt
    exact maxOf_eq hc ⟨hmF, h2, fun r hr' hc' => h3 r (F_subset H hr') hc'⟩

/-- If the held set contains a roster that the founding key signed, then
`ROSTER_eff` is present. -/
theorem rosterEff_present {f : Nat} {H : List Record}
    (h : ∃ c g hh, roster f c g hh ∈ H) : rosterEff f H ≠ none := by
  obtain ⟨c, g, hh, hm⟩ := h
  intro hn
  have := maxOf_none.mp hn _ hm
  have hnv : rootVoidB f H f = false := by
    cases hb : rootVoidB f H f
    · rfl
    · exact absurd (rootVoidB_iff.mp hb).1 (fun h' => h' rfl)
  simp [isRosterOK, hnv] at this

/-! ### T12: authorization records do not touch data -/

/-- T12: the application of an authorization record `a` does not add or
remove a `put` or a `del`. The data records of `F (S ++ [a])` are those of
`F S`. This is true for every `S`. For a frontier `S`, `F S` is `S`. -/
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

/-- T12 (locality): when a replica applies a record, only records that this
record dominates leave the frontier. For an authorization record, these are
only records of its own kind and key. -/
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

/-- Take two frontier PUTs on one cell. Their versions are equal only when the
records are equal (hash injectivity). Then the two PUTs are the same record,
so there is one value per cell. -/
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

/-! ### T5: `deleted_at` and `exists` -/

theorem Version.lt_asymm {a b : Version} (h : Version.lt a b) : ¬ Version.lt b a := by
  unfold Version.lt at *; omega

theorem Version.not_lt_trans {a b c : Version} (h₁ : ¬ Version.lt a b) (h₂ : ¬ Version.lt b c) :
    ¬ Version.lt a c := by
  unfold Version.lt at *; omega

theorem Version.eq_of_not_lt {a b : Version} (h₁ : ¬ Version.lt a b) (h₂ : ¬ Version.lt b a) :
    a = b :=
  (Version.lt_trichotomy a b).elim (fun h => absurd h h₁)
    (fun h => h.elim id (fun h => absurd h h₂))

/-- One fold step of `deleted_at(e)`: keep the larger version of a `del` on
`e`. -/
def delStep (e : Nat) (acc : Option Version) : Record → Option Version
  | del e' v =>
    if e' = e then
      match acc with
      | none => some v
      | some a => if Version.lt a v then some v else some a
    else acc
  | _ => acc

/-- `deleted_at(e)`: the largest version of the held `del`s on entity `e`, or
`none` if there is no such `del`. -/
def deletedAt (H : List Record) (e : Nat) : Option Version := H.foldl (delStep e) none

/-- `v` is the version of a `del` on `e` in `H` that no `del` on `e` in `H`
exceeds. -/
def IsDelMax (H : List Record) (e : Nat) (v : Version) : Prop :=
  del e v ∈ H ∧ ∀ v', del e v' ∈ H → ¬ Version.lt v v'

theorem delStep_skip {e : Nat} {acc : Option Version} {r : Record} (h : ∀ v, r ≠ del e v) :
    delStep e acc r = acc := by
  cases r with
  | del e' v =>
    have he : e' ≠ e := fun he => h v (by rw [he])
    simp [delStep, he]
  | _ => rfl

theorem foldl_delStep_none (e : Nat) :
    ∀ (l : List Record) (acc : Option Version),
      l.foldl (delStep e) acc = none ↔ acc = none ∧ ∀ v, del e v ∉ l := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons r l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    by_cases hr : ∃ v, r = del e v
    · obtain ⟨v, rfl⟩ := hr
      cases acc with
      | none =>
        simp only [delStep, ↓reduceIte]
        constructor
        · rintro ⟨h, _⟩; cases h
        · rintro ⟨_, hv⟩; exact absurd (List.mem_cons_self ..) (hv v)
      | some a =>
        simp only [delStep, ↓reduceIte]
        split <;> simp
    · have hr' : ∀ v, r ≠ del e v := fun v h => hr ⟨v, h⟩
      rw [delStep_skip hr']
      constructor
      · rintro ⟨ha, hl⟩
        refine ⟨ha, fun v hv => ?_⟩
        rcases List.mem_cons.mp hv with h | h
        · exact hr' v h.symm
        · exact hl v h
      · rintro ⟨ha, hl⟩
        exact ⟨ha, fun v hv => hl v (List.mem_cons_of_mem _ hv)⟩

theorem foldl_delStep_some (e : Nat) :
    ∀ (l : List Record) (acc : Option Version) (m : Version),
      l.foldl (delStep e) acc = some m →
        (acc = some m ∨ del e m ∈ l) ∧
        (∀ a, acc = some a → ¬ Version.lt m a) ∧
        (∀ v, del e v ∈ l → ¬ Version.lt m v) := by
  intro l
  induction l with
  | nil =>
    intro acc m h
    simp only [List.foldl_nil] at h
    refine ⟨Or.inl h, ?_, fun v hv => absurd hv List.not_mem_nil⟩
    intro a ha; rw [h] at ha; cases ha; exact Version.lt_irrefl _
  | cons r l ih =>
    intro acc m h
    rw [List.foldl_cons] at h
    obtain ⟨hmem, hacc, hl⟩ := ih _ m h
    by_cases hr : ∃ v, r = del e v
    · obtain ⟨v, rfl⟩ := hr
      cases acc with
      | none =>
        have hs : delStep e none (del e v) = some v := by simp [delStep]
        rw [hs] at hmem hacc
        refine ⟨Or.inr ?_, (fun a ha => by cases ha), ?_⟩
        · rcases hmem with he | h1
          · cases he; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ h1
        · intro v' hv'
          rcases List.mem_cons.mp hv' with he | h1
          · cases he; exact hacc _ rfl
          · exact hl v' h1
      | some a =>
        by_cases hlt : Version.lt a v
        · have hs : delStep e (some a) (del e v) = some v := by simp [delStep, hlt]
          rw [hs] at hmem hacc
          have hmv : ¬ Version.lt m v := hacc v rfl
          refine ⟨?_, ?_, ?_⟩
          · rcases hmem with he | h1
            · cases he; exact Or.inr (List.mem_cons_self ..)
            · exact Or.inr (List.mem_cons_of_mem _ h1)
          · intro a' ha'; cases ha'
            exact Version.not_lt_trans hmv (Version.lt_asymm hlt)
          · intro v' hv'
            rcases List.mem_cons.mp hv' with he | h1
            · cases he; exact hmv
            · exact hl v' h1
        · have hs : delStep e (some a) (del e v) = some a := by simp [delStep, hlt]
          rw [hs] at hmem hacc
          have hma : ¬ Version.lt m a := hacc a rfl
          refine ⟨hmem.imp id (List.mem_cons_of_mem _), hacc, ?_⟩
          intro v' hv'
          rcases List.mem_cons.mp hv' with he | h1
          · cases he; exact Version.not_lt_trans hma hlt
          · exact hl v' h1
    · have hr' : ∀ v, r ≠ del e v := fun v h => hr ⟨v, h⟩
      rw [delStep_skip hr'] at hmem hacc
      refine ⟨hmem.imp id (List.mem_cons_of_mem _), hacc, ?_⟩
      intro v' hv'
      rcases List.mem_cons.mp hv' with he | h1
      · exact absurd he.symm (hr' v')
      · exact hl v' h1

theorem deletedAt_none {H : List Record} {e : Nat} :
    deletedAt H e = none ↔ ∀ v, del e v ∉ H := by
  unfold deletedAt; rw [foldl_delStep_none]; simp

theorem deletedAt_some {H : List Record} {e : Nat} {m : Version} (h : deletedAt H e = some m) :
    IsDelMax H e m := by
  obtain ⟨hmem, _, hl⟩ := foldl_delStep_some e H none m h
  rcases hmem with he | h1
  · cases he
  · exact ⟨h1, hl⟩

theorem IsDelMax_unique {H : List Record} {e : Nat} {m m' : Version} (h : IsDelMax H e m)
    (h' : IsDelMax H e m') : m = m' :=
  Version.eq_of_not_lt (h.2 m' h'.1) (h'.2 m h.1)

theorem deletedAt_eq {H : List Record} {e : Nat} {m : Version} (h : IsDelMax H e m) :
    deletedAt H e = some m := by
  cases hr : deletedAt H e with
  | none => exact absurd h.1 (deletedAt_none.mp hr m)
  | some m' => rw [IsDelMax_unique (deletedAt_some hr) h]

/-- T5: `deleted_at` is a function of the held set. -/
theorem deletedAt_congr {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (e : Nat) :
    deletedAt H e = deletedAt H' e := by
  cases hr : deletedAt H e with
  | none =>
    have hn := deletedAt_none.mp hr
    exact (deletedAt_none.mpr fun v hv => hn v ((h _).mpr hv)).symm
  | some m =>
    obtain ⟨h1, h2⟩ := deletedAt_some hr
    exact (deletedAt_eq ⟨(h _).mp h1, fun v hv => h2 v ((h _).mpr hv)⟩).symm

/-- T5: `deleted_at(F(H)) = deleted_at(H)`. The largest `del` on an entity is
undominated: only a `del` on the same entity with a greater version
dominates a `del`. -/
theorem deletedAt_F {H : List Record} (e : Nat) : deletedAt (F H) e = deletedAt H e := by
  cases hr : deletedAt H e with
  | none =>
    have hn := deletedAt_none.mp hr
    exact deletedAt_none.mpr fun v hv => hn v (F_subset H hv)
  | some m =>
    obtain ⟨h1, h2⟩ := deletedAt_some hr
    have hmF : del e m ∈ F H := by
      refine mem_F_iff.mpr ⟨h1, ?_⟩
      rintro ⟨q, hq, hqm⟩
      cases q with
      | del e' v =>
        simp only [dominates, decide_eq_true_eq] at hqm
        obtain ⟨rfl, hlt⟩ := hqm
        exact h2 v hq hlt
      | _ => simp [dominates] at hqm
    exact deletedAt_eq ⟨hmF, fun v hv => h2 v (F_subset H hv)⟩

/-- `exists(e)`: entity `e` has a live field, that is, the held set has a
`put` on a cell of `e`. In a frontier, this is `∃ f, cell(e, f) ≠ None`, and
`cell_unique` gives one value per cell. -/
def existsEnt (H : List Record) (e : Nat) : Prop := ∃ f v x, put e f v x ∈ H

/-- T5: `exists` is a function of the held set. (The name `exists_congr` is
taken by core Lean.) -/
theorem existsEnt_congr {H H' : List Record} (h : ∀ y, y ∈ H ↔ y ∈ H') (e : Nat) :
    existsEnt H e ↔ existsEnt H' e :=
  ⟨fun ⟨f, v, x, hm⟩ => ⟨f, v, x, (h _).mp hm⟩, fun ⟨f, v, x, hm⟩ => ⟨f, v, x, (h _).mpr hm⟩⟩

/-! ### T8: the chase, and D8 -/

/-- The emitted `t`: the larger of the wall clock and the value just above the
cell's floor, capped at the ceiling. -/
def emitT (now floorT c : Nat) : Nat := min (max now (floorT + 1)) c

/-- T8: below the ceiling, a local write beats the cell's floor on `t`
alone, for all authors (read-your-writes). -/
theorem chase {now floorT c : Nat} (h : floorT < c) : floorT < emitT now floorT c := by
  unfold emitT; omega

/-- T13 (part): the emitted `t` never exceeds the ceiling. -/
theorem emitT_le (now floorT c : Nat) : emitT now floorT c ≤ c := by
  unfold emitT; omega

/-- T9 (after a raise): a record pinned at the old ceiling `c` (every admitted
record is at or below the ceiling, `adm_put_le`) cannot shadow a write under
a new ceiling `c' > c`. The emission lands above the pin and below `c'`. -/
theorem chase_after_raise {now floorT c c' : Nat} (hpin : floorT ≤ c) (hraise : c < c') :
    floorT < emitT now floorT c' ∧ emitT now floorT c' ≤ c' :=
  ⟨chase (Nat.lt_of_le_of_lt hpin hraise), emitT_le now floorT c'⟩

/-- The `seq` of a held data record by author `k`; 0 for every other
record. -/
def seqOf (k : Nat) : Record → Nat
  | put _ _ v _ => if v.author = k then v.seq else 0
  | del _ v => if v.author = k then v.seq else 0
  | _ => 0

/-- The largest own `seq` held, 0 if there is none. -/
def maxSeq (k : Nat) : List Record → Nat
  | [] => 0
  | r :: l => max (seqOf k r) (maxSeq k l)

theorem maxSeq_ge {k : Nat} {r : Record} {l : List Record} (h : r ∈ l) :
    seqOf k r ≤ maxSeq k l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons q l ih =>
    simp only [maxSeq]
    rcases List.mem_cons.mp h with hq | hl
    · rw [hq]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hl) (Nat.le_max_right _ _)

/-- The emitted `seq` of author `k`: one more than the larger of the device's
own counter `seqSelf` (the largest `seq` that it emitted) and the largest
own `seq` held (§5). -/
def emitSeq (seqSelf : Nat) (H : List Record) (k : Nat) : Nat := max seqSelf (maxSeq k H) + 1

/-- T8 (seq clause): the emitted `seq` exceeds every `seq` that the device
emitted. -/
theorem seq_emit_gt_self (seqSelf : Nat) (H : List Record) (k : Nat) :
    seqSelf < emitSeq seqSelf H k := by
  unfold emitSeq; omega

/-- T8 (seq clause): the emitted `seq` exceeds the `seq` of every held record
of its author. -/
theorem seq_emit_gt {seqSelf k : Nat} {H : List Record} {r : Record} (hr : r ∈ H) :
    seqOf k r < emitSeq seqSelf H k := by
  unfold emitSeq
  have := maxSeq_ge (k := k) hr
  omega

theorem seq_emit_gt_put {seqSelf : Nat} {H : List Record} {e f : Nat} {v : Version} {x : Nat}
    (hr : put e f v x ∈ H) : v.seq < emitSeq seqSelf H v.author := by
  have := seq_emit_gt (seqSelf := seqSelf) (k := v.author) hr
  simpa [seqOf] using this

theorem seq_emit_gt_del {seqSelf : Nat} {H : List Record} {e : Nat} {v : Version}
    (hr : del e v ∈ H) : v.seq < emitSeq seqSelf H v.author := by
  have := seq_emit_gt (seqSelf := seqSelf) (k := v.author) hr
  simpa [seqOf] using this

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

/-! ### T10: equivocation -/

/-- T10: two different records with equal `(author, seq)` have comparable
versions (T1), so every replica puts them in the same order. -/
theorem equivocation_ordered {a b : Version} (h : a ≠ b) : Version.lt a b ∨ Version.lt b a :=
  (Version.lt_trichotomy a b).elim Or.inl (fun h' => h'.elim (fun he => absurd he h) Or.inr)

/-- T10: arrival order has no effect on the frontier (an alias of
`convergence`, for `applyD`; with a horizon, under `NoLateDom`, as in T4 (b),
`expire_applyAllH`). -/
theorem equivocation {S l l' : List Record} (h : ∀ r, r ∈ l ↔ r ∈ l') (x : Record)
    (hF : Frontier S) (hA : Admitted S) :
    x ∈ applyAllD (applyAllD S l) l ↔ x ∈ applyAllD (applyAllD S l') l' :=
  convergence h x hF hA

end Kome.Frontier
