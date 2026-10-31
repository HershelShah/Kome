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
| The implementation, in SPARK, proved against the Lean model | `spark/` | lattice core (versions, headers, registers, frontier) built, tested and fully proved |

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
provers. CI (`.github/workflows/ci.yml`) runs both commands on every push.

## How the SPARK code relates to the Lean proofs

Each SPARK package refines a piece of `lean/Kome/Frontier.lean`. The Lean
file proves the theorems about *sets* of records (convergence in any order
with any duplication, the frontier homomorphism, monotone admission). The
SPARK contracts state that the bounded, in-place code implements exactly the
functions those theorems are about, and gnatprove discharges them:

| SPARK package | Lean counterpart | What gnatprove proves |
|---|---|---|
| `Kome.Versions` | `Version`, `Version.lt`, T1 | the order is a strict total order (irreflexive, asymmetric, transitive, trichotomous) |
| `Kome.Headers` | `Record`, `dominates`, T2' | domination is irreflexive and upward-closed; REVOKE is never dominated |
| `Kome.Registers` | the `maxceil` max-register and `W`, T4' | both registers only grow; writer membership is preserved |
| `Kome.Frontier` | `State`, `adm`, `keep`, `applyA` | `Apply` keeps exactly the undominated admitted records, registers only grow, the held set is always its own frontier, failures leave the state unchanged |

What Lean proves about the functions, SPARK proves about the code; neither
tool is asked to do the other's job. The remaining pieces of the design
(records and their canonical encoding, the log, the accumulator fingerprint,
reconciliation, the transports, the C ABI) follow the same pattern, one
package each, in the order given in `docs/design/DESIGN.md` §10.

## Contributing

Commits are signed off (`git commit -s`, Developer Certificate of Origin);
CI checks it. Every SPARK module ships with a test main and must prove with
`spark/check.sh <module>` before it is merged; every Lean change must build
with `lean/build.sh` and contain no `sorry`.

## License

See `LICENSE`.
