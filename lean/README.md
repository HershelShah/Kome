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
| `Kome/Frontier.lean` | **the redesign**, round three (`docs/design/DESIGN.md` §2–§4, §6, §7): five record kinds (`put`, `del`, per-signer `roster`, `revoke`, issuer-keyed `grant`), the version order, domination (product order on rosters), the frontier, admission under `maxceil` and `W` as functions of the held set, the discard model, tombstone expiry, and the views `root_void`, `W_eff`, `void`, `ROSTER_eff`, `del_ttl_eff`. Assumes well-formed records; certificates, capacity, the horizon's clock clamp and A7 are outside it | T1 (`StrictTotal Version`); T2/T2' (`Dom_mono`, `dominates_trans`); T3 (`frontier_hom`, `F_idem`, via the sandwich lemma `F_sandwich`); T4 (`auth_first`, `convergence_two_pass`, `convergence`); T4' (`adm_mono`, `maxCeil_F`, `isWriter_F`, `adm_F`); T5 (`cell_unique`, `rootVoid_F`, `wEff_F`, `voided_F`, `rosterEff_congr`, `rosterEff_F`, `rosterEff_present`, `delTtlEff_congr`); T8 (`chase`, `lt_iff_prefix` for D8); T9 (`adm_put_le`); T11 (`expire_none`, `expire_only_del`, `expire_frontier`, `expire_adm`, `expire_admitted`, `expire_reapply`); T12 (`data_F_auth_free`, `applyF_local`, `revoke_never_dominated`, `rootVoid_mono`, `wEff_mono_fixed`, `voided_revoke_mono`); T13 (`emitT_le`); T18 (`auth_first`) |

**Status:** machine-checked. Every theorem in the table builds under Lean
4.35.0 with no `sorry`; the only axioms used are Lean's standard `propext`,
`Classical.choice` and `Quot.sound` (the two counterexample theorems in
`Equivocation.lean` use none). `./build.sh` builds it, fetching Lean from
nixpkgs when `lake` is not installed. See `docs/legacy/MATH_MODEL.md` for the model
in prose and the theorems still to state.