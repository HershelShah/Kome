/-
Hybrid Logical Clock, as implemented in `src/sync_engine.cpp` (`Hlc::tick`,
`Hlc::receive`, `Hlc::bump_logical`, `hlc_cmp`) and `src/engine.hpp`.

The C++ fields are `uint64_t physical` and `uint32_t logical`. We model both as
`Nat` with the fixed-width bounds stated explicitly, so that every wrap, carry
and saturation the C++ performs is a visible branch here rather than an
implicit modular overflow. Literals are used inside definitions so `omega` can
see them.

  P_MAX     = 2^64 - 1 = 18446744073709551615
  L_MAX     = 2^32 - 1 = 4294967295
  MAX_ADOPT = P_MAX - 2^32 = 18446744069414584319   (engine.hpp kMaxAdoptablePhysical)
-/
namespace Kome

structure HLC where
  physical : Nat
  logical  : Nat
deriving DecidableEq, Repr

namespace HLC

/-- The fixed-width invariant the C++ representation imposes. -/
def WF (c : HLC) : Prop := c.physical ≤ 18446744073709551615 ∧ c.logical ≤ 4294967295

/-- `{0,0}`: the reserved "no assertion" sentinel (`Entity::asserted()`). -/
def zero : HLC := ⟨0, 0⟩

/-- The saturating fixed point of `bump_logical`: no larger HLC exists. -/
def top : HLC := ⟨18446744073709551615, 4294967295⟩

/-- `hlc_cmp(a, b) < 0`: physical first, then logical. -/
def lt (a b : HLC) : Prop :=
  a.physical < b.physical ∨ (a.physical = b.physical ∧ a.logical < b.logical)

def le (a b : HLC) : Prop := lt a b ∨ a = b

instance (a b : HLC) : Decidable (lt a b) := by unfold lt; exact inferInstance
instance (a b : HLC) : Decidable (le a b) := by unfold le; exact inferInstance

theorem lt_irrefl (a : HLC) : ¬ lt a a := by
  unfold lt; omega

theorem lt_trans {a b c : HLC} (h₁ : lt a b) (h₂ : lt b c) : lt a c := by
  unfold lt at *; omega

theorem lt_asymm {a b : HLC} (h : lt a b) : ¬ lt b a := by
  unfold lt at *; omega

theorem lt_trichotomy (a b : HLC) : lt a b ∨ a = b ∨ lt b a := by
  obtain ⟨p, l⟩ := a
  obtain ⟨p', l'⟩ := b
  simp only [lt, HLC.mk.injEq]
  omega

theorem le_refl (a : HLC) : le a a := Or.inr rfl

theorem le_trans {a b c : HLC} (h₁ : le a b) (h₂ : le b c) : le a c := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (lt_trans h₁ h₂)
  · subst h₂; exact Or.inl h₁
  · subst h₁; exact Or.inl h₂
  · subst h₁; subst h₂; exact Or.inr rfl

theorem lt_of_le_of_lt {a b c : HLC} (h₁ : le a b) (h₂ : lt b c) : lt a c := by
  rcases h₁ with h₁ | h₁
  · exact lt_trans h₁ h₂
  · subst h₁; exact h₂

/-! ### bump_logical -/

/-- `Hlc::bump_logical`: `logical = base + 1`, carrying a uint32 wrap into
`physical`, and saturating (never wrapping to `{0,0}`) when the clock is
exhausted. -/
def bump (p l : Nat) : HLC :=
  if l ≠ 4294967295 then ⟨p, l + 1⟩
  else if p ≠ 18446744073709551615 then ⟨p + 1, 0⟩
  else ⟨p, 4294967295⟩

theorem bump_ne_zero (p l : Nat) : bump p l ≠ zero := by
  unfold bump zero
  split <;> (try split) <;> (intro h; simp only [HLC.mk.injEq] at h; omega)

theorem bump_phys_ge (p l : Nat) : p ≤ (bump p l).physical := by
  unfold bump
  split <;> (try split)
  all_goals first | exact Nat.le_refl _ | exact Nat.le_succ _

/-- A bump from `(p, m)` is at least `(p, l)` for any `l ≤ m`; equality only at
the saturating fixed point. -/
theorem le_bump (c : HLC) (m : Nat) (h : c.logical ≤ m) : le c (bump c.physical m) := by
  obtain ⟨p, l⟩ := c
  change l ≤ m at h
  unfold bump le lt
  split <;> (try split) <;> simp only [HLC.mk.injEq] at * <;> omega

theorem bump_wf (p l : Nat) (hp : p ≤ 18446744073709551615) (hl : l ≤ 4294967295) :
    WF (bump p l) := by
  unfold bump WF
  split <;> (try split) <;> simp only <;> omega

/-! ### tick -/

/-- `Hlc::tick(now)`: adopt the wall clock if it moved forward, else bump. -/
def tick (c : HLC) (now : Nat) : HLC :=
  if c.physical < now then ⟨now, 0⟩ else bump c.physical c.logical

/-- T-HLC-1: a ticked clock is never the `{0,0}` sentinel. -/
theorem tick_ne_zero (c : HLC) (now : Nat) : tick c now ≠ zero := by
  unfold tick
  split
  · intro h; simp only [zero, HLC.mk.injEq] at h; omega
  · exact bump_ne_zero _ _

/-- T-HLC-2: tick is strictly increasing, except at the documented saturating
fixed point `top`, where it returns the same value. -/
theorem tick_lt (c : HLC) (now : Nat) (hwf : WF c) : lt c (tick c now) ∨ c = top := by
  obtain ⟨p, l⟩ := c
  simp only [WF] at hwf
  unfold tick bump top
  split <;> (try split) <;> (try split) <;> simp only [lt, HLC.mk.injEq] at * <;> omega

theorem tick_wf (c : HLC) (now : Nat) (hwf : WF c) (hnow : now ≤ 18446744073709551615) :
    WF (tick c now) := by
  unfold tick
  split
  · unfold WF; simp only; omega
  · exact bump_wf _ _ hwf.1 hwf.2

/-- T-HLC-3: a local write after receiving `r` beats `r` under LWW on the HLC
alone, whatever the authors are -- unless the clock is exhausted. -/
theorem tick_beats (c r : HLC) (now : Nat) (hr : le r c) (hwf : WF c) (hsat : c ≠ top) :
    lt r (tick c now) :=
  lt_of_le_of_lt hr ((tick_lt c now hwf).resolve_right hsat)

/-! ### receive -/

/-- The remote physical is adopted only up to `kMaxAdoptablePhysical`. -/
def adoptPhys (c r : HLC) : Nat :=
  if c.physical < r.physical ∧ r.physical ≤ 18446744069414584319 then r.physical else c.physical

/-- ...and then the wall clock, if it is ahead of both. -/
def newPhys (c r : HLC) (now : Nat) : Nat :=
  if adoptPhys c r < now then now else adoptPhys c r

/-- `Hlc::receive(remote, now)`. -/
def receive (c r : HLC) (now : Nat) : HLC :=
  if newPhys c r now = c.physical ∧ newPhys c r now = r.physical then
    bump (newPhys c r now) (if r.logical < c.logical then c.logical else r.logical)
  else if newPhys c r now = c.physical then
    bump (newPhys c r now) c.logical
  else if newPhys c r now = r.physical then
    bump (newPhys c r now) r.logical
  else
    ⟨newPhys c r now, 0⟩

theorem adoptPhys_cases (c r : HLC) : adoptPhys c r = r.physical ∨ adoptPhys c r = c.physical := by
  unfold adoptPhys; split <;> omega

theorem adoptPhys_ge (c r : HLC) : c.physical ≤ adoptPhys c r := by
  unfold adoptPhys; split <;> omega

theorem adoptPhys_bound (c r : HLC) :
    adoptPhys c r ≤ c.physical ∨ adoptPhys c r ≤ 18446744069414584319 := by
  unfold adoptPhys; split <;> omega

theorem newPhys_cases (c r : HLC) (now : Nat) :
    newPhys c r now = adoptPhys c r ∨ (newPhys c r now = now ∧ adoptPhys c r < now) := by
  unfold newPhys; split <;> omega

theorem newPhys_ge (c r : HLC) (now : Nat) : c.physical ≤ newPhys c r now := by
  have := adoptPhys_ge c r
  unfold newPhys; split <;> omega

/-- T-HLC-4: receive never yields the `{0,0}` sentinel. -/
theorem receive_ne_zero (c r : HLC) (now : Nat) : receive c r now ≠ zero := by
  unfold receive
  split
  · exact bump_ne_zero _ _
  split
  · exact bump_ne_zero _ _
  split
  · exact bump_ne_zero _ _
  · intro h
    simp only [zero, HLC.mk.injEq] at h
    have h1 := newPhys_cases c r now
    have h2 := adoptPhys_cases c r
    omega

/-- T-HLC-5: receive never moves the clock backwards. -/
theorem le_receive (c r : HLC) (now : Nat) : le c (receive c r now) := by
  have hge := newPhys_ge c r now
  have hb1 := le_bump c (if r.logical < c.logical then c.logical else r.logical) (by split <;> omega)
  have hb2 := le_bump c c.logical (Nat.le_refl _)
  unfold receive
  split
  · next h => rw [h.1]; exact hb1
  split
  · next h => rw [h]; exact hb2
  split
  · next _ hne _ =>
    left
    unfold lt
    left
    have := bump_phys_ge (newPhys c r now) r.logical
    omega
  · next _ hne _ =>
    left
    show c.physical < newPhys c r now ∨ (c.physical = newPhys c r now ∧ c.logical < 0)
    omega

/-- T-HLC-6: the physical adopted from a peer is capped at `kMaxAdoptablePhysical`;
whatever the peer sends, the new physical is bounded by the local clock, the
wall clock, or the ceiling (plus at most one carry). -/
theorem receive_phys_bound (c r : HLC) (now : Nat) :
    (receive c r now).physical ≤ c.physical + 1 ∨
    (receive c r now).physical ≤ now + 1 ∨
    (receive c r now).physical ≤ 18446744069414584319 + 1 := by
  have h1 := newPhys_cases c r now
  have h2 := adoptPhys_bound c r
  have hb : ∀ m, (bump (newPhys c r now) m).physical ≤ newPhys c r now + 1 := by
    intro m; unfold bump; split <;> (try split) <;> simp only <;> omega
  unfold receive
  split
  · have := hb (if r.logical < c.logical then c.logical else r.logical); omega
  split
  · have := hb c.logical; omega
  split
  · have := hb r.logical; omega
  · show newPhys c r now ≤ c.physical + 1 ∨ newPhys c r now ≤ now + 1 ∨
        newPhys c r now ≤ 18446744069414584319 + 1
    omega

end HLC
end Kome
