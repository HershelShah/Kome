/-
The existence rule as implemented is not a total order, and the merge it
induces is order-dependent. This is the divergence reproduced against the
engine in docs/legacy/FORMALIZATION_PLAN.md §5, stated as a theorem.
-/
import Kome.Cells

namespace Kome

/-- The order `apply_change` uses for EXISTENCE records today
(src/sync_engine.cpp, the `(hlc, author)` comparison): the present bit is not
part of it. -/
def Ex.ltImpl (a b : Ex) : Prop :=
  HLC.lt a.hlc b.hlc ∨ (a.hlc = b.hlc ∧ a.author < b.author)

instance (a b : Ex) : Decidable (Ex.ltImpl a b) := by unfold Ex.ltImpl; exact inferInstance

/-- The implemented merge: install iff strictly greater under `ltImpl`. -/
def Ex.mergeImpl (cur inc : Ex) : Ex := if Ex.ltImpl cur inc then inc else cur

/-- Two valid assertions by one author at one clock value, opposite present bits. -/
def addRec : Ex := ⟨⟨1000, 7⟩, 3, true⟩
def delRec : Ex := ⟨⟨1000, 7⟩, 3, false⟩

/-- T-EQUIV-1: the implemented rule is order-dependent, so two replicas that
receive these two records in opposite orders diverge, permanently. -/
theorem mergeImpl_not_comm : Ex.mergeImpl addRec delRec ≠ Ex.mergeImpl delRec addRec := by
  decide

/-- T-EQUIV-2: the root cause -- `ltImpl` is not trichotomous on `Ex`. -/
theorem ltImpl_not_trichotomous :
    ¬ (Ex.ltImpl addRec delRec ∨ addRec = delRec ∨ Ex.ltImpl delRec addRec) := by
  decide

/-- With the present bit in the order (`Ex.lt`), the same two records merge the
same way from either side: an instance of LWW.merge_comm. -/
example : LWW.merge addRec delRec = LWW.merge delRec addRec :=
  LWW.merge_comm addRec delRec

end Kome
