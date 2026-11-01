# Kome

A private, offline-first, serverless replication engine for records: contacts,
notes, inventories, settings, small shared lists. Each person's devices sync
directly with each other and with explicitly trusted contacts, with no central
server, end-to-end encryption, and membership that can change.

This repository is the ground-up rebuild. The previous C++ engine was
removed after a formal review found convergence bugs that were structural
rather than local (the history is in git; the analysis is in
`docs/legacy/`). The rebuild is design-first and proof-first:

| Layer | Where | State |
|---|---|---|
| The problem and the constraints | `docs/design/REQUIREMENTS.md` | fixed |
| The design search: eight candidates, two rounds, three adversarial judges | `docs/design/candidates/`, `docs/design/judges/` | done |
| The chosen design, the **frontier store** | `docs/design/DESIGN.md` | decided |
| Its mathematics, machine-checked in Lean 4 | `lean/` | T1–T5, T8, T9, T12, T13 proved; T7 open |
| The implementation, in SPARK, proved against the Lean model | `spark/` | 16 packages (DESIGN.md §10 phases 0–8, except `Kome.Roster`) built; all 14 test mains pass; 15 packages fully proved; `Kome.Store` has 1 of 1987 checks unproved; open design gaps listed in `docs/design/IMPLEMENTATION_PLAN.md` (Known gaps) |

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
docs/design/      requirements, candidates, judges' reports, DESIGN.md
docs/legacy/      why the previous engine was replaced (math model, bug analysis)
lean/             Lean 4 model: lean/Kome/Frontier.lean is the design's theorems
spark/            SPARK implementation: src/, tests/, vectors/, check.sh
third_party/      monocypher, the only cryptographic dependency
```

## Building and checking

Both toolchains come from nixpkgs when they are not on the path, so a machine
with Nix needs nothing else.

```bash
./lean/build.sh            # machine-check every theorem (Lean 4.35.0 via lake)
./spark/check.sh all       # build, run tests, and run gnatprove on every module
./spark/check.sh frontier  # one module
PROVE=0 ./spark/check.sh all   # tests only
```

`spark/check.sh` uses GNAT 14, gprbuild, gnatprove 14 and the cvc5 and z3
provers, and fails if a module has an unproved check, except modules listed
in `PROOF_WIP` (today only `store`, which has 1 open check: the
`St in OK | Dominated` assertion after `Frontier.Apply` in `Put_Frame`,
`kome-store.adb:1253`). CI (`.github/workflows/ci.yml`)
runs both commands on every push.

## How the SPARK code relates to the Lean proofs

Each SPARK package refines a piece of `lean/Kome/Frontier.lean`. The Lean
file proves the theorems about *sets* of records (convergence in any order
with any duplication, the frontier homomorphism, monotone admission). The
SPARK contracts state that the bounded, in-place code implements exactly the
functions those theorems are about, and gnatprove discharges them:

State as of the last full run of `spark/check.sh all` (gnatprove 14,
`--level=3`, cvc5 and z3). "Checks" is gnatprove's total; no package uses
`pragma Assume`, `pragma Annotate` or justified checks.

| SPARK package | Lean counterpart | What gnatprove proves | Tests | Checks | Unproved |
|---|---|---|---|---|---|
| `Kome.Byteorder` | — | little-endian u32/u64 store, read and bounded-buffer put/get round-trip | 74 PASS | 322 | 0 |
| `Kome.SHA256` | — | FIPS 180-4 padding and digest layout; counter bounds; incremental `Update`/`Finish` equals one-shot `Hash` (correctness of the compression function rests on known-answer vectors) | 45 PASS | 2084 | 0 |
| `Kome.Versions` | `Version`, `Version.lt`, T1 | the order is a strict total order (irreflexive, asymmetric, transitive, trichotomous) | 8 PASS | 9 | 0 |
| `Kome.Headers` | `Record`, `dominates`, T2' | domination is irreflexive and upward-closed; REVOKE is never dominated | proof only | 12 | 0 |
| `Kome.Registers` | the `maxceil` max-register and `W`, T4' | both registers only grow; writer membership is preserved | proof only | 34 | 0 |
| `Kome.Frontier` | `State`, `adm`, `keep`, `applyA` | `Apply` keeps exactly the undominated admitted records, registers only grow, the held set is always its own frontier, failures leave the state unchanged | 20 PASS | 283 | 0 |
| `Kome.Keys` | — | 256-bit keys and 128-bit ids as word records: big-endian decode/encode round trips; `Lt` is byte-lexicographic order | 16 PASS | 679 | 0 |
| `Kome.Crypto` | — | monocypher binding (bodies `SPARK_Mode Off`): spec-level run-time checks, data dependencies, refusal preconditions; the assumed Posts are checked by known-answer vectors | 47 PASS | 17 | 0 |
| `Kome.Records` | T13 | canonical encoding: length and per-byte layout, total `Decode` that leaves the record unchanged on `Malformed`, both round trips, header shape | 94 PASS | 1869 | 0 |
| `Kome.Store` | T11 (stated) | index/frontier correspondence, append-only log, refusals change nothing, `Expire`, `Compact` | 55 PASS | 1987 | **1** |
| `Kome.Emit` | `chase` T8, `adm_put_le` T9, `emitT_le` T13 | the chase, `V.T <= maxceil`, no `seq` wrap (`Seq_Exhausted`), H8 jump, SHADOWED exactly per §5, an emitted header is admitted and undominated | 42 PASS | 236 | 0 |
| `Kome.Views` | `cell_unique` T5, T12 | `cell`, `exists`, `deleted_at`, `void`, `far`, `ROSTER_eff` are deterministic functions of the frontier; one value per cell under `Canonical` | 70 PASS | 867 | 0 |
| `Kome.Accumulator` | T6 (DESIGN.md §8) | 4096-bit `Add`/`Sub` modulo 2^4096 against an exact integer model; commutative, associative, `Add_Sub`, byte bijection | 25 PASS | 716 | 0 |
| `Kome.Digest` | T6 (DESIGN.md §8) | `acc(e)` and `fp` byte layout; incremental add/remove; order independence (`Lemma_Sum_Perm`, `Lemma_Frontier_Digest_Perm`); `Range_Sum` over prefix sums | 58 PASS | 709 | 0 |
| `Kome.Reconcile` | T7 (open in Lean) | message size bounds, well-founded range split, state machine with refusals that change nothing, HELLO register join; T7 itself is tested only | 83 PASS | 1805 | 0 |
| `Kome.Epochs` | T14 (paper) | `Derive` = `Iter (K, From - To)` and the chain lemmas; fixed-length key boxes; non-canonical and low-order peers refused with a zero result | 37 PASS | 99 | 0 |

What Lean proves about the functions, SPARK proves about the code; neither
tool is asked to do the other's job. The remaining pieces of the design
(`Kome.Roster`, the transports, the C ABI, extension F) follow the same
pattern, one package each, in the order given in `docs/design/DESIGN.md` §10.

## Contributing

Commits are signed off (`git commit -s`, Developer Certificate of Origin);
CI checks it. Every SPARK module ships with a test main and must prove with
`spark/check.sh <module>` before it is merged; every Lean change must build
with `lean/build.sh` and contain no `sorry`.

## License

See `LICENSE`.
