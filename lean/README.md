# Kome: the mathematics, in Lean 4

A model of what Kome replicates and the theorems its correctness rests on.
`Kome/Frontier.lean` is the model of the redesigned engine; the other files
model the current one.
Core Lean only (no Mathlib), so it builds offline:

```bash
cd lean && lake build
```

| File | Models | Theorems |
|---|---|---|
| `Kome/HLC.lean` | `Hlc::tick`, `receive`, `bump_logical`, `hlc_cmp` with the uint64/uint32 bounds explicit | T-HLC-1..6: total order; tick and receive never yield the `{0,0}` sentinel; tick strictly increases except at the saturating fixed point; receive never goes backwards; the adoption ceiling |
| `Kome/LWW.lean` | LWW merge over any strict total order | T-LWW-1..3: idempotent, commutative, associative |
| `Kome/Cells.lean` | registers (`register_cmp`) and existence assertions | T-REG, T-EX: both orders are strict total orders |
| `Kome/State.lean` | replica state and `apply` | T-STATE-1..4, T-CONV: applies commute and absorb duplicates; same record set in any order gives the same state |
| `Kome/Equivocation.lean` | the existence order as implemented | T-EQUIV-1..2: it is not total, and its merge is order-dependent |
| `Kome/Frontier.lean` | **the redesign** (`docs/design/DESIGN.md`): records, the version order, domination, the frontier, ceiling admission | T1, T2, T2', T3 (frontier homomorphism via a sandwich lemma), T4 (convergence with GC and admission, any order, any duplication), T4', T5, T8, T9, T12, T13 |

**Status:** machine-checked. Every theorem in the table builds under Lean
4.35.0 with no `sorry`; the only axioms used are Lean's standard `propext`,
`Classical.choice` and `Quot.sound` (the two counterexample theorems in
`Equivocation.lean` use none). `./build.sh` builds it, fetching Lean from
nixpkgs when `lake` is not installed. See `docs/legacy/MATH_MODEL.md` for the model
in prose and the theorems still to state.