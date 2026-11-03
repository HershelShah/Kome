# Kome

A private, offline-first, serverless replication engine for records: contacts,
notes, inventories, settings, small shared lists. Each person's devices sync
directly with each other and with explicitly trusted contacts, with no central
server, end-to-end encryption, and membership that can change.

The work is design-first and proof-first:

| Layer | Where | State |
|---|---|---|
| The problem and the constraints | `docs/design/REQUIREMENTS.md` | fixed |
| The design search: eight candidates, two rounds, three adversarial judges | `docs/design/history/` | done |
| The chosen design, the **frontier store** | `docs/design/DESIGN.md` | decided |
| Its mathematics, machine-checked in Lean 4 | `lean/` | T1–T5, T8, T9, T11, T12, T13, T18 proved (136 theorems in `Frontier.lean`, no `sorry`); T7 open |
| The implementation, in SPARK, proved against the Lean model | `spark/` | 15 packages (phases 0–8 of `docs/design/IMPLEMENTATION_PLAN.md`, except `Kome.Roster`); every test passes and every package proves with 0 unproved checks (@TOTALS@); the remaining gaps are listed in the plan's Known gaps |

## The design in one paragraph

Every change is a small signed record. A replica's state is a set of
records, and merging two replicas is set union followed by dropping every
record that a newer one *dominates* under a single strict total order. That
surviving set is the *frontier*, and it is the whole state: there is no
history, no vector clock, and no per-peer bookkeeping. Deletion is a record
that dominates every field of its entity, so it frees bytes on every replica
with no membership knowledge and no clock. Everything that looks like policy
(who may write, how far into the future a clock may claim, who has been
revoked) is either a *monotone admission rule* or a *pure view* over the
frontier, never part of the merge. The one theorem that makes this work is
the frontier homomorphism `F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))`: dropping a beaten
record anywhere, at any time, never changes a future state.

## Layout

```
docs/design/          REQUIREMENTS.md, DESIGN.md, IMPLEMENTATION_PLAN.md
docs/design/history/  the design search: candidates and the judges' reports
lean/                 Lean 4 model: lean/Kome/Frontier.lean and its theorems
spark/                SPARK implementation: src/, tests/, vectors/, check.sh
third_party/          monocypher, the only cryptographic dependency
nixpkgs.pin           the pinned nixpkgs revision both toolchains come from
```

## Building and checking

Both toolchains come from the pinned nixpkgs revision (`nixpkgs.pin`) when
they are not on the path, so a machine with Nix needs nothing else.

```bash
./lean/build.sh            # machine-check every theorem (Lean 4.35.0 via lake)
./spark/check.sh all       # build, run tests, and run gnatprove on every module
./spark/check.sh frontier  # one module
PROVE=0 ./spark/check.sh all   # tests only
```

`spark/check.sh` uses GNAT 14, gprbuild, gnatprove 14 and the cvc5 and z3
provers, and fails if a module has an unproved check, except modules listed
in `PROOF_WIP`. That list is empty by default, and today no module needs
it: every module proves with 0 unproved checks. `PROOF_WIP=""` also
means no list. CI (`.github/workflows/ci.yml`) builds the Lean model and
runs `spark/check.sh <module>` for every module, as parallel jobs, on every
push.

## How the SPARK code relates to the Lean proofs

Each SPARK package refines a piece of `lean/Kome/Frontier.lean`. The Lean
file proves the theorems about *sets* of records (convergence in any order
with any duplication, the frontier homomorphism, monotone admission). The
SPARK contracts state that the bounded, in-place code implements exactly the
functions those theorems are about, and gnatprove discharges them:

Counts are from CI's clean per-module runs (gnatprove 14, `--level=3`,
cvc5 and z3): @TOTALS@. "Checks" is gnatprove's total. No package uses
`pragma Assume`, `pragma Annotate` or justified checks.

| SPARK package | Lean counterpart | What gnatprove proves | Tests | Checks | Unproved |
|---|---|---|---|---|---|
| `Kome.Byteorder` | — | Little-endian u64 encoding (D7): `To_LE_U64` and `Read_U64LE` are inverse bijections | 6 PASS | 47 | 0 |
| `Kome.Versions` | `Version`, `Version.lt`, T1 | The order is a strict total order | 11 PASS | 13 | 0 |
| `Kome.Headers` | `Record`, `dominates`, T2' | Domination: product order on rosters, GRANT keyed by (issuer, subject). It is irreflexive and transitive, and REVOKE is never dominated. `Canonical` is a property of a header | 18 PASS | 31 | 0 |
| `Kome.Registers` | `maxCeil`, `isWriter`, T4' | Both registers only grow, and writer membership is preserved | 6 PASS | 93 | 0 |
| `Kome.Frontier` | `adm`, `applyD`, `expire`, `maxCeil_F`, `isWriter_F`, T4', T11 | `Apply` keeps exactly the undominated admitted records. Each outcome (OK, Dominated, Inadmissible, No_Space, Auth_Full) is stated as an iff, and a refusal leaves the state `Unchanged`. The register cache equals maxceil(F) and W(F) (`Coherent`). `Expire` removes exactly the expired DELs | 44 PASS | 1515 | 0 |
| `Kome.Keys` | — | Key and id word records: big-endian round trips, injectivity, and `Lt`/`Id_Lt` as byte-lexicographic order | 32 PASS | 800 | 0 |
| `Kome.Crypto` | — | Monocypher binding (RFC 8032 Ed25519, X25519, BLAKE2b, ChaCha20-Poly1305) with `SPARK_Mode Off` bodies: spec-level run-time checks, data dependencies and refusal preconditions. The Posts and the BLAKE2b congruence axiom are assumed, and are checked by RFC 8032, Wycheproof and other known-answer vectors | 64 PASS | 35 | 0 |
| `Kome.Records` | T13, D1, D3, E5 | Canonical encoding, total `Decode` and both round trips. Signer certificates (`Cert_OK`) for ROSTER, REVOKE and GRANT. Decode yields only canonical headers. `Make_Put` and `Make_Del` state their headers | 172 PASS | 2622 | 0 |
| `Kome.Store` | T11, T18 (`auth_first`, tested) | `Valid` relates the index, the journal log and F. Each `Put_Frame` outcome is an iff in D11 order, and refusals change nothing. `Expire` is at `Horizon_At` (T11 (a)). `Compact` writes authorization records first. `Open_From_Log` is proved for HEADER-only logs | 109 PASS | 4504 | 0 |
| `Kome.Emit` | `chase` T8, `adm_put_le` T9, `emitT_le` T13, `lt_iff_prefix` | `Choose` picks (t, seq) without h, and the outcome is independent of h. Also: `V.T <= maxceil`, no `seq` wrap, the H8 jump, SHADOWED exactly as in §5, and an OK write is admitted and undominated | 55 PASS | 313 | 0 |
| `Kome.Views` | T5 (`rootVoid_F`, `wEff_F`, `voided_F`, `rosterEff_F`), T12 | `cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `void`, `far`, `ROSTER_eff` and `del_ttl_eff` are functions of F. Each cell has one value on every frontier | 131 PASS | 1120 | 0 |
| `Kome.Accumulator` | T6 (DESIGN.md §8) | 4096-bit `Add`/`Sub` modulo 2^4096 against an exact integer model. Commutative and associative, `Add_Sub`, the byte bijection and congruence | 30 PASS | 735 | 0 |
| `Kome.Digest` | T6 (DESIGN.md §8) | The layouts of `acc(e)` and `fp`, incremental add/remove and order independence. `Range_Sum` over D15 prefix sums is exact, with the cost formula of at most 64 Adds | 134 PASS | 967 | 0 |
| `Kome.Reconcile` | T7 (open in Lean) | Message size bounds and the OPEN/HELLO formats. The auth-then-data phases with exact root ranges. The reply kinds are pinned, the split is well founded, refusals change nothing, and `Key_Lt` is bytewise order. T7 itself is tested only | 142 PASS | 2134 | 0 |
| `Kome.Epochs` | T14 (paper) | `Derive` and the chain lemmas. Fixed-length boxes whose wrap key covers ns and the epoch, with the synthetic nonce in the Post. Segment links. Non-canonical and low-order peers are refused | 69 PASS | 220 | 0 |

What Lean proves about the functions, SPARK proves about the code; neither
tool is asked to do the other's job. The remaining pieces of the design
(`Kome.Roster`, the transports, the C ABI, extension F) follow the same
pattern, one package each, in the order given in `docs/design/DESIGN.md` §10.

## Contributing

See `CONTRIBUTING.md`: sign off every commit, and every change must keep
`lean/build.sh` and `spark/check.sh` green.

## License

See `LICENSE`.
