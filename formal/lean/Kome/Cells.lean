/-
The two cell types Kome replicates, with the orders that make LWW converge.

Authors are 32-byte public keys compared with memcmp; values are byte strings
compared with std::string's operator< (lexicographic on unsigned bytes). Both
are total orders, and every theorem here uses only that, so each is modelled by
`Nat`: the proofs transfer to any total order unchanged.
-/
import Kome.HLC
import Kome.LWW

set_option linter.unusedSimpArgs false

namespace Kome

/- Authors and values are plain `Nat` (not an `abbrev`: `omega` only
recognizes literal `Nat`). -/

/-! ### Registers -/

/-- A field register: `ke::Register` (the signature is not part of the order). -/
structure Reg where
  hlc : HLC
  author : Nat
  value : Nat
deriving DecidableEq, Repr

/-- `register_cmp`: (hlc, author, value). -/
def Reg.lt (a b : Reg) : Prop :=
  HLC.lt a.hlc b.hlc ∨
    (a.hlc = b.hlc ∧ (a.author < b.author ∨ (a.author = b.author ∧ a.value < b.value)))

instance (a b : Reg) : Decidable (Reg.lt a b) := by unfold Reg.lt; exact inferInstance

theorem Reg.lt_irrefl (a : Reg) : ¬ Reg.lt a a := by
  obtain ⟨⟨p, l⟩, au, v⟩ := a
  simp only [Reg.lt, HLC.lt, HLC.mk.injEq, true_and, and_true]
  omega

theorem Reg.lt_trans {a b c : Reg} (h₁ : Reg.lt a b) (h₂ : Reg.lt b c) : Reg.lt a c := by
  obtain ⟨⟨p, l⟩, au, v⟩ := a
  obtain ⟨⟨p', l'⟩, au', v'⟩ := b
  obtain ⟨⟨p'', l''⟩, au'', v''⟩ := c
  simp only [Reg.lt, HLC.lt, HLC.mk.injEq, true_and, and_true] at *
  omega

theorem Reg.lt_trichotomy (a b : Reg) : Reg.lt a b ∨ a = b ∨ Reg.lt b a := by
  obtain ⟨⟨p, l⟩, au, v⟩ := a
  obtain ⟨⟨p', l'⟩, au', v'⟩ := b
  simp only [Reg.lt, HLC.lt, HLC.mk.injEq, Reg.mk.injEq, true_and, and_true]
  omega

/-- T-REG: `register_cmp` is a strict total order, so register merge is a
semilattice join (LWW.merge_comm / merge_assoc / merge_idem apply). -/
instance : StrictTotal Reg where
  lt := Reg.lt
  dec := fun _ _ => inferInstance
  irrefl := Reg.lt_irrefl
  trans := Reg.lt_trans
  trichotomy := Reg.lt_trichotomy

/-! ### Existence assertions -/

/-- An entity's presence assertion: `ke::Entity`'s (present_v, presence_hlc, ex_author). -/
structure Ex where
  hlc : HLC
  author : Nat
  present : Bool
deriving DecidableEq, Repr

/-- The order a convergent existence rule needs: (hlc, author, present) with
absent < present -- the register rule with the present bit in the role of the
value. This is NOT the order the C++ implements today (see Equivocation.lean). -/
def Ex.lt (a b : Ex) : Prop :=
  HLC.lt a.hlc b.hlc ∨
    (a.hlc = b.hlc ∧
      (a.author < b.author ∨ (a.author = b.author ∧ a.present = false ∧ b.present = true)))

instance (a b : Ex) : Decidable (Ex.lt a b) := by unfold Ex.lt; exact inferInstance

theorem Ex.lt_irrefl (a : Ex) : ¬ Ex.lt a a := by
  obtain ⟨⟨p, l⟩, au, pr⟩ := a
  cases pr <;> simp only [Ex.lt, HLC.lt, HLC.mk.injEq] <;> simp <;> omega

theorem Ex.lt_trans {a b c : Ex} (h₁ : Ex.lt a b) (h₂ : Ex.lt b c) : Ex.lt a c := by
  obtain ⟨⟨p, l⟩, au, pr⟩ := a
  obtain ⟨⟨p', l'⟩, au', pr'⟩ := b
  obtain ⟨⟨p'', l''⟩, au'', pr''⟩ := c
  cases pr <;> cases pr' <;> cases pr'' <;>
    simp only [Ex.lt, HLC.lt, HLC.mk.injEq] at * <;> simp at * <;> omega

theorem Ex.lt_trichotomy (a b : Ex) : Ex.lt a b ∨ a = b ∨ Ex.lt b a := by
  obtain ⟨⟨p, l⟩, au, pr⟩ := a
  obtain ⟨⟨p', l'⟩, au', pr'⟩ := b
  cases pr <;> cases pr' <;>
    simp only [Ex.lt, HLC.lt, HLC.mk.injEq, Ex.mk.injEq] <;> simp <;> omega

/-- T-EX: with the present bit in the order, existence merge is a semilattice join. -/
instance : StrictTotal Ex where
  lt := Ex.lt
  dec := fun _ _ => inferInstance
  irrefl := Ex.lt_irrefl
  trans := Ex.lt_trans
  trichotomy := Ex.lt_trichotomy

end Kome
