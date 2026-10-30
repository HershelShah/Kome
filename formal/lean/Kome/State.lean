/-
Replica state and the convergence theorem.

A replica's state is the cell it holds at each key (`(namespace, entity, field)`
for registers, `(namespace, entity)` for existence); `apply` installs a record by
LWW-merging it into the held cell. The theorem: two replicas that have applied
the same *set* of records -- in any order, with any duplication, each starting
from the same state -- hold the same state. No message ordering, no version
vectors, no peer history is assumed: only that the cell order is total.
-/
import Kome.LWW

namespace Kome

/-- A replica's state: the cell held at each key, if any. -/
abbrev Store (Key α : Type) := Key → Option α

/-- One replicated record: a key and the cell to merge there. -/
structure Rec (Key α : Type) where
  key : Key
  cell : α
deriving DecidableEq

namespace Store

variable {Key : Type} [DecidableEq Key] {α : Type} [StrictTotal α]

/-- Merge an incoming cell into what is held (nothing held: install it). -/
def ins (c : Option α) (x : α) : α :=
  match c with
  | none => x
  | some c => LWW.merge c x

/-- `apply_change` on one key. -/
def apply (s : Store Key α) (k : Key) (x : α) : Store Key α :=
  fun k' => if k' = k then some (ins (s k') x) else s k'

theorem merge_ins (c : Option α) (x y : α) :
    LWW.merge (ins c x) y = LWW.merge (ins c y) x := by
  cases c with
  | none => exact LWW.merge_comm x y
  | some c =>
    show LWW.merge (LWW.merge c x) y = LWW.merge (LWW.merge c y) x
    rw [LWW.merge_assoc, LWW.merge_assoc, LWW.merge_comm x y]

@[simp] theorem ins_ins (c : Option α) (x : α) : ins (some (ins c x)) x = ins c x := by
  cases c with
  | none => exact LWW.merge_idem x
  | some c =>
    show LWW.merge (LWW.merge c x) x = LWW.merge c x
    rw [LWW.merge_assoc, LWW.merge_idem]

/-- T-STATE-1: applies commute. -/
theorem apply_comm (s : Store Key α) (k1 k2 : Key) (x1 x2 : α) :
    apply (apply s k1 x1) k2 x2 = apply (apply s k2 x2) k1 x1 := by
  funext k
  by_cases h1 : k = k1 <;> by_cases h2 : k = k2
  · subst h1; subst h2
    simp [apply, ins]
    first
      | exact merge_ins (s k) x1 x2
      | exact congrArg some (merge_ins (s k) x1 x2)
  · subst h1; simp [apply, h2]
  · subst h2; simp [apply, h1]
  · simp [apply, h1, h2]

/-- T-STATE-2: applying a record twice is applying it once. -/
theorem apply_apply (s : Store Key α) (k : Key) (x : α) :
    apply (apply s k x) k x = apply s k x := by
  funext k'
  by_cases h : k' = k
  · subst h; simp [apply]
  · simp [apply, h]

/-- Apply a sequence of records, oldest first. -/
def applyAll (s : Store Key α) (l : List (Rec Key α)) : Store Key α :=
  l.foldl (fun s r => apply s r.key r.cell) s

theorem applyAll_nil (s : Store Key α) : applyAll s [] = s := rfl

theorem applyAll_cons (s : Store Key α) (r : Rec Key α) (l : List (Rec Key α)) :
    applyAll s (r :: l) = applyAll (apply s r.key r.cell) l := rfl

/-- T-STATE-3: order of arrival does not matter. -/
theorem applyAll_perm {l l' : List (Rec Key α)} (h : l.Perm l') :
    ∀ s : Store Key α, applyAll s l = applyAll s l' := by
  induction h with
  | nil => intro s; rfl
  | cons x _ ih => intro s; rw [applyAll_cons, applyAll_cons]; exact ih _
  | swap x y l =>
    intro s
    rw [applyAll_cons, applyAll_cons, applyAll_cons, applyAll_cons, apply_comm]
  | trans _ _ ih1 ih2 => intro s; rw [ih1, ih2]

/-- T-STATE-4: a record already in the sequence can be delivered again for free. -/
theorem applyAll_mem_cons {r : Rec Key α} {l : List (Rec Key α)} (h : r ∈ l) :
    ∀ s : Store Key α, applyAll s (r :: l) = applyAll s l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons r' l ih =>
    intro s
    by_cases hr : r = r'
    · subst hr
      rw [applyAll_cons, applyAll_cons, applyAll_cons, apply_apply]
    · have hr' : r ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hr
        · exact h
      rw [applyAll_cons, applyAll_cons, apply_comm, ← applyAll_cons, ih hr', applyAll_cons]

theorem applyAll_append_subset {l l' : List (Rec Key α)} (h : ∀ r, r ∈ l' → r ∈ l) :
    ∀ s : Store Key α, applyAll s (l ++ l') = applyAll s l := by
  induction l' with
  | nil => intro s; rw [List.append_nil]
  | cons r rest ih =>
    intro s
    have hr : r ∈ l := h r (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ r', r' ∈ rest → r' ∈ l := fun r' hr' => h r' (List.mem_cons.mpr (Or.inr hr'))
    rw [applyAll_perm List.perm_middle,
        applyAll_mem_cons (List.mem_append.mpr (Or.inl hr)),
        ih hrest]

/-- T-CONV: convergence. Two replicas that applied the same set of records, in
any order and with any duplication, from the same starting state, are equal. -/
theorem convergence {l l' : List (Rec Key α)} (h : ∀ r, r ∈ l ↔ r ∈ l') (s : Store Key α) :
    applyAll s l = applyAll s l' := by
  have h1 : ∀ r, r ∈ l' → r ∈ l := fun r hr => (h r).mpr hr
  have h2 : ∀ r, r ∈ l → r ∈ l' := fun r hr => (h r).mp hr
  calc applyAll s l = applyAll s (l ++ l') := (applyAll_append_subset h1 s).symm
    _ = applyAll s (l' ++ l) := applyAll_perm List.perm_append_comm s
    _ = applyAll s l' := applyAll_append_subset h2 s

end Store
end Kome
