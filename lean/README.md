# Kome: the mathematics, in Lean 4

`Kome/Frontier.lean` is the model of the frontier store
(`docs/design/DESIGN.md` §2–§4, §6, §7). It also contains the proofs of the
model's theorems. It uses only core Lean (no Mathlib), so it builds
offline:

```bash
./build.sh        # or: lake build
```

If `lake` is not installed, `build.sh` gets Lean from nixpkgs.
`lean-toolchain` names the version for users of `elan`.

## What the model contains

- Five record kinds: `put`, `del`, per-signer `roster`, `revoke` and
  issuer-keyed `grant`.
- The version order.
- Domination (the product order on rosters).
- The frontier.
- Admission under `maxceil` and `W`, as functions of the held set.
- The discard model.
- Tombstone expiry.
- The views `root_void`, `W_eff`, `void`, `ROSTER_eff` and `del_ttl_eff`.

Out of scope: the model assumes that records are well-formed. So it does
not model certificates, capacity (`NO_SPACE`, `AUTH_FULL`), the horizon's
clock clamp or assumption A7.

## Theorems (numbering from DESIGN.md §9)

| Theorem | Lean |
|---|---|
| T1 versions are a strict total order | `instance : StrictTotal Version` |
| T2, T2′ domination | `Dom_mono`, `dominates_trans` |
| T3 frontier homomorphism | `frontier_hom`, `F_idem`, through `F_sandwich` |
| T4 convergence | `auth_first`, `convergence_two_pass`, `convergence` |
| T4′ admission is monotone | `adm_mono`, `maxCeil_F`, `isWriter_F`, `adm_F` |
| T5 views | `cell_unique`, `rootVoid_F`, `wEff_F`, `voided_F`, `rosterEff_congr`, `rosterEff_F`, `rosterEff_present`, `delTtlEff_congr` |
| T8 chase | `chase`, `lt_iff_prefix` (D8) |
| T9 nothing admitted above the ceiling | `adm_put_le` |
| T11 expiry | `expire_none`, `expire_only_del`, `expire_frontier`, `expire_adm`, `expire_admitted`, `expire_reapply` |
| T12 revocation | `data_F_auth_free`, `applyF_local`, `revoke_never_dominated`, `rootVoid_mono`, `wEff_mono_fixed`, `voided_revoke_mono` |
| T13 bounds | `emitT_le` |
| T18 replay after compaction | `auth_first` |

**Status:** Lean machine-checks 136 theorems, with no `sorry`. The only
axioms that the proofs use are the standard Lean axioms `propext`,
`Classical.choice` and `Quot.sound`. T7 (reconciliation) is open.
