/-
Last-writer-wins merge over a strict total order, generically.

`register_cmp` gives registers a strict total order on (hlc, author, value);
`apply_change` installs an incoming record iff it is strictly greater than the
held one. Everything a replica needs for convergence follows from the order
being total: the merge is commutative, associative and idempotent, i.e. a
semilattice join. Those three laws are proved here once, for any `StrictTotal`
type, and instantiated for the concrete cells in `Cells.lean`.
-/
namespace Kome

/-- A strict total order with a decidable comparison. -/
class StrictTotal (α : Type) where
  lt : α → α → Prop
  dec : ∀ a b, Decidable (lt a b)
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ {a b c}, lt a b → lt b c → lt a c
  trichotomy : ∀ a b, lt a b ∨ a = b ∨ lt b a

namespace LWW

variable {α : Type} [StrictTotal α]

instance (a b : α) : Decidable (StrictTotal.lt a b) := StrictTotal.dec a b

def le (a b : α) : Prop := StrictTotal.lt a b ∨ a = b

/-- `apply_change`: keep the greater of the held and incoming cell
(`register_cmp(cand, cur) <= 0` means the incoming record is dropped). -/
def merge (cur inc : α) : α := if StrictTotal.lt cur inc then inc else cur

theorem lt_asymm {a b : α} (h : StrictTotal.lt a b) : ¬ StrictTotal.lt b a :=
  fun h' => StrictTotal.irrefl a (StrictTotal.trans h h')

/-- T-LWW-1 -/
theorem merge_idem (a : α) : merge a a = a := by
  unfold merge; rw [if_neg (StrictTotal.irrefl a)]

/-- T-LWW-2 -/
theorem merge_comm (a b : α) : merge a b = merge b a := by
  unfold merge
  rcases StrictTotal.trichotomy a b with h | h | h
  · rw [if_pos h, if_neg (lt_asymm h)]
  · subst h; rfl
  · rw [if_neg (lt_asymm h), if_pos h]

theorem merge_eq_or (a b : α) : merge a b = a ∨ merge a b = b := by
  unfold merge; split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem le_merge_left (a b : α) : le a (merge a b) := by
  unfold merge; split
  · next h => exact Or.inl h
  · exact Or.inr rfl

theorem le_merge_right (a b : α) : le b (merge a b) := by
  unfold merge; split
  · exact Or.inr rfl
  · next h =>
    rcases StrictTotal.trichotomy a b with h1 | h1 | h1
    · exact absurd h1 h
    · exact Or.inr h1.symm
    · exact Or.inl h1

theorem le_trans {a b c : α} (h₁ : le a b) (h₂ : le b c) : le a c := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (StrictTotal.trans h₁ h₂)
  · subst h₂; exact Or.inl h₁
  · subst h₁; exact Or.inl h₂
  · subst h₁; subst h₂; exact Or.inr rfl

theorem le_antisymm {a b : α} (h₁ : le a b) (h₂ : le b a) : a = b := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact absurd h₂ (lt_asymm h₁)
    · exact h₂.symm
  · exact h₁

/-- T-LWW-3: both bracketings are the maximum of {a, b, c}. -/
theorem merge_assoc (a b c : α) : merge (merge a b) c = merge a (merge b c) := by
  have l1 : le a (merge (merge a b) c) := le_trans (le_merge_left a b) (le_merge_left _ c)
  have l2 : le b (merge (merge a b) c) := le_trans (le_merge_right a b) (le_merge_left _ c)
  have l3 : le c (merge (merge a b) c) := le_merge_right _ c
  have r1 : le a (merge a (merge b c)) := le_merge_left a _
  have r2 : le b (merge a (merge b c)) := le_trans (le_merge_left b c) (le_merge_right a _)
  have r3 : le c (merge a (merge b c)) := le_trans (le_merge_right b c) (le_merge_right a _)
  have hL : merge (merge a b) c = a ∨ merge (merge a b) c = b ∨ merge (merge a b) c = c := by
    rcases merge_eq_or (merge a b) c with h | h
    · rcases merge_eq_or a b with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (Or.inl (h.trans h'))
    · exact Or.inr (Or.inr h)
  have hR : merge a (merge b c) = a ∨ merge a (merge b c) = b ∨ merge a (merge b c) = c := by
    rcases merge_eq_or a (merge b c) with h | h
    · exact Or.inl h
    · rcases merge_eq_or b c with h' | h'
      · exact Or.inr (Or.inl (h.trans h'))
      · exact Or.inr (Or.inr (h.trans h'))
  apply le_antisymm
  · rcases hL with h | h | h <;> rw [h]
    · exact r1
    · exact r2
    · exact r3
  · rcases hR with h | h | h <;> rw [h]
    · exact l1
    · exact l2
    · exact l3

theorem merge_left_comm (a b c : α) : merge a (merge b c) = merge b (merge a c) := by
  rw [← merge_assoc, merge_comm a b, merge_assoc]

end LWW
end Kome
