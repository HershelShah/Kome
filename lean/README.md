# Kome: the mathematics, in Lean 4

`Kome/Frontier.lean` is the model of the frontier store
(`docs/design/DESIGN.md` §2–§4, §6, §7, as changed by S2, S4, S5 and S7 of
`docs/design/SIMPLIFY.md`). It also contains the proofs of the
model's theorems. It uses only core Lean (no Mathlib), so it builds
offline:

```bash
./build.sh        # or: lake build --wfail
```

If `lake` is not installed, `build.sh` gets Lean from nixpkgs.
`lean-toolchain` names the version for users of `elan`.

The build enforces the "no `sorry`, standard axioms only" claim:

- `build.sh` runs `lake build --wfail`, so every warning fails the build.
  Lean reports a `sorry` as a warning.
- `Kome/Axioms.lean` is part of the build. Its command
  `#assert_std_axioms Kome.Frontier` collects the axioms of every
  declaration of the module and fails the build if one of them is outside
  `propext`, `Classical.choice` and `Quot.sound`. A `sorry` adds `sorryAx`,
  so it fails this check too. The check covers every theorem that the
  table below lists, and every theorem that is added later.

## What the model contains

- Five record kinds: `put`, `del`, per-signer `roster` (signer, ceiling,
  `gen`, hash; no epoch and no `del_ttl` field), `revoke` and issuer-keyed
  `grant` (with its write cap).
- The version order.
- Domination: the product order on rosters (strict in `gen`, ceiling not
  lower; two rosters of one signer at equal `gen` never dominate each
  other), on grants (greater hash, cap not lower), and on revocations of
  one `(issuer, subject)` (a lower `from_t`, or an equal `from_t` and a
  greater hash). No authorization record dominates a data record.
- The frontier.
- Admission under `maxceil`, `W` and `wcap`, as functions of the held set.
  `maxceil` and `wcap(k)` are instances of one register family `maxP p`,
  the maximum of a projection `p` that is 0 on data records and that a
  dominator never lowers.
- The discard model (`applyD`), and the store's apply (`applyH`), which
  expires at the horizon of the state it reaches.
- Tombstone expiry, at a general horizon (`expire`) and at the store's
  horizon (`expireHz`). `del_ttl` is a constant of the model (the
  parameter `delTtl`), fixed at founding. The horizon is a function of the
  state: `hz(F) = maxceil(F) − del_ttl` when `maxceil(F) ≥ del_ttl`, else
  none (`hz`); it is monotone in `F` (`hz_mono`).
- The views `deleted_at`, `exists`, `root_void`, `W_eff`, `void` and
  `ROSTER_eff` (the `(gen, h)`-maximum of the rosters whose signer is not
  root-voided). The views read the minimum `from_t` of the revocations of
  a key, which the REVOKE clause of domination does not change.
- The emitted `t` (`emitT`) and the emitted `seq` (`emitSeq`).

Out of scope: the model assumes that records are well-formed. So it does
not model certificates, capacity (`NO_SPACE`, `AUTH_FULL`) or assumption
A7.

## Theorems (numbering from DESIGN.md §9)

| Theorem | Lean |
|---|---|
| T1 versions are a strict total order | `instance : StrictTotal Version` |
| T2, T2′ domination | `Dom_mono`, `dominates_irrefl`, `dominates_trans`; per kind `dominates_roster`, `roster_same_gen`, `dominates_grant`, `dominates_revoke`, `revoke_dominates`, `auth_not_dominates_data` |
| T3 frontier homomorphism | `frontier_hom`, `F_idem`, through `F_sandwich` |
| T4 convergence | `auth_first`, `convergence_two_pass`, `convergence` |
| A16 bundles closed under admission | `auth_first_closed`; under the store's apply `auth_first_closed_H` |
| T4′ admission is monotone | `adm_mono`, `maxCeil_F`, `isWriter_F`, `wcap_F`, `adm_F`; the register family `maxP_cover`, `maxP_mono_auth` |
| T5 views | `cell_unique`, `deletedAt_congr`, `deletedAt_F`, `existsEnt_congr`, `rootVoid_F`, `wEff_F`, `voided_F`, `isMinFrom_F`, `rosterEff_congr`, `rosterEff_F`, `rosterEff_present` |
| T8 chase | `chase`, `lt_iff_prefix` (D8); seq clause `seq_emit_gt`, `seq_emit_gt_self` |
| T9 nothing admitted above the ceiling or the write cap | `adm_put_le`, `adm_put_le_wcap`; after a raise `chase_after_raise` |
| T10 equivocation | `instance : StrictTotal Version`, `equivocation_ordered`, `equivocation` (an alias of `convergence`), `convergence_empty` |
| S7 the horizon is a function of the state | `hz_F`, `hz_mono`, `isExpiredAt_hz`, `expireHz_eq`, `expireHz_no_hz`, `maxCeil_expireHz` |
| T11 expiry | at `hz`: `expireHz_none`, `expireHz_only_del`, `expireHz_frontier`, `expireHz_adm`, `expireHz_admitted`, `expireHz_reapply`; at a general horizon: `expire_none`, `expire_only_del`, `expire_frontier`, `expire_adm`, `expire_admitted`, `expire_reapply` |
| N1 a later expiry absorbs an earlier one | `expireHz_expire`, `expireHz_idem`; general horizon `expire_expire` |
| G1 expiry on arrival | `expire_applyAllH`, `expire_applyAllH_hz` (under `NoLateDom`), `applyH_clean` |
| T12 revocation | `data_F_auth_free`, `applyF_local`, `dominates_revoke`, `isMinFrom_F`, `rootVoid_mono`, `wEff_mono_fixed`, `voided_revoke_mono` |
| T13 bounds | `emitT_le` |
| T18 replay after compaction | `auth_first` |

`exists_congr` of the audit (G3) is `existsEnt_congr`: core Lean already
uses the name `exists_congr`.

**Status:** Lean machine-checks 204 theorems (202 `theorem` and 2
`instance` declarations), with no `sorry`. The only
axioms that the proofs use are the standard Lean axioms `propext`,
`Classical.choice` and `Quot.sound`; `Kome/Axioms.lean` checks this on
every build. T7 (reconciliation) is open.
