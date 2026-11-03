# Kome

Kome is a private replication engine for records, for example contacts,
notes, inventories, settings and small shared lists. It works offline first
and needs no server. A person's devices sync directly with each other and
with contacts that the person trusts explicitly. There is no central
server, all content has end-to-end encryption, and the membership can change.

The work starts with the design and the proofs. The code comes after them:

| Layer | Where | State |
|---|---|---|
| The problem and the constraints | `docs/design/REQUIREMENTS.md` | fixed |
| The chosen design, the **frontier store** | `docs/design/DESIGN.md` | decided |
| Its mathematics, machine-checked in Lean 4 | `lean/` | T1–T5, T8, T9, T11, T12, T13, T18 proved (136 theorems in `Frontier.lean`, no `sorry`); T7 open |
| The implementation, in SPARK, proved against the Lean model | `spark/` | 15 packages (phases 0–8 of `docs/design/IMPLEMENTATION_PLAN.md`, except `Kome.Roster`). All tests pass. gnatprove proves every package with 0 unproved checks (@TOTALS@). The Known gaps section of the plan lists the remaining gaps |

## The design in one paragraph

Every change is a small signed record. A replica's state is a set of
records. To merge two replicas, take the set union, then drop every record
that a newer record *dominates* under a single strict total order. The set
that remains is the *frontier*, and it is the full state. There is no
history, no vector clock and no per-peer bookkeeping.

A deletion is a record that dominates every field of its entity. So a
deletion frees bytes on every replica, with no membership knowledge and no
clock. Some rules look like policy: who can write, how far into the future a
clock can claim to be, and who is revoked. Each of these rules is a
*monotone admission rule* or a *pure view* over the frontier. No such rule
is part of the merge.

The one theorem that makes this work is the frontier homomorphism
`F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))`. It means that if you drop a beaten record
anywhere and at any time, no future state changes.

## Layout

```
docs/design/          REQUIREMENTS.md, DESIGN.md, IMPLEMENTATION_PLAN.md
lean/                 Lean 4 model: lean/Kome/Frontier.lean and its theorems
spark/                SPARK implementation: src/, tests/, vectors/, check.sh
third_party/          monocypher, the only cryptographic dependency
nixpkgs.pin           the pinned nixpkgs revision both toolchains come from
```

## Build and check

If a toolchain is not on the path, the scripts get it from the pinned
nixpkgs revision (`nixpkgs.pin`). So a machine with Nix needs nothing else.

```bash
./lean/build.sh            # machine-check every theorem (Lean 4.35.0 with lake)
./spark/check.sh all       # build, run tests, and run gnatprove on every module
./spark/check.sh frontier  # one module
PROVE=0 ./spark/check.sh all   # tests only
```

`spark/check.sh` uses GNAT 14, gprbuild, gnatprove 14 and the cvc5 and z3
provers. It fails if a module has an unproved check, except for the modules
in the `PROOF_WIP` list. By default that list is empty. Today no module needs
it, because every module proves with 0 unproved checks. `PROOF_WIP=""` also
gives an empty list. On every push, CI (`.github/workflows/ci.yml`) builds
the Lean model. It also runs `spark/check.sh <module>` for every module, as
parallel jobs.

## How the SPARK code relates to the Lean proofs

Each SPARK package refines a part of `lean/Kome/Frontier.lean`. The Lean
file proves the theorems about *sets* of records: convergence in any order
with any duplication, the frontier homomorphism, and monotone admission. The
SPARK contracts state that the bounded, in-place code implements exactly the
functions that those theorems are about. gnatprove discharges these contracts.

The counts come from the clean per-module runs in CI (gnatprove 14,
`--level=3`, cvc5 and z3): @TOTALS@. "Checks" is the total from gnatprove.
No package uses `pragma Assume`, `pragma Annotate` or justified checks.

| SPARK package | Lean counterpart | What gnatprove proves | Tests | Checks | Unproved |
|---|---|---|---|---|---|
| `Kome.Byteorder` | — | Little-endian u64 encoding (D7): `To_LE_U64` and `Read_U64LE` are inverse bijections | 6 PASS | 47 | 0 |
| `Kome.Versions` | `Version`, `Version.lt`, T1 | The order is a strict total order | 11 PASS | 13 | 0 |
| `Kome.Headers` | `Record`, `dominates`, T2' | Domination is the product order on rosters, with GRANT keyed by (issuer, subject). Domination is irreflexive and transitive. No record dominates a REVOKE. `Canonical` is a property of a header | 18 PASS | 31 | 0 |
| `Kome.Registers` | `maxCeil`, `isWriter`, T4' | Both registers only grow, and a writer stays a writer | 6 PASS | 93 | 0 |
| `Kome.Frontier` | `adm`, `applyD`, `expire`, `maxCeil_F`, `isWriter_F`, T4', T11 | `Apply` keeps exactly the undominated admitted records. The Post states each outcome (OK, Dominated, Inadmissible, No_Space, Auth_Full) as an iff. A refusal leaves the state `Unchanged`. The register cache equals maxceil(F) and W(F) (`Coherent`). `Expire` removes exactly the expired DELs | 44 PASS | 1515 | 0 |
| `Kome.Keys` | — | Key and id word records: big-endian round trips, injectivity, and `Lt`/`Id_Lt` as byte-lexicographic order | 32 PASS | 800 | 0 |
| `Kome.Crypto` | — | Monocypher binding (RFC 8032 Ed25519, X25519, BLAKE2b, ChaCha20-Poly1305) with `SPARK_Mode Off` bodies: spec-level run-time checks, data dependencies and refusal preconditions. The Posts and the BLAKE2b congruence axiom are assumptions. RFC 8032, Wycheproof and other known-answer vectors check them | 64 PASS | 35 | 0 |
| `Kome.Records` | T13, D1, D3, E5 | Canonical encoding, total `Decode` and both round trips. Signer certificates (`Cert_OK`) for ROSTER, REVOKE and GRANT. `Decode` gives only canonical headers. `Make_Put` and `Make_Del` state their headers | 172 PASS | 2622 | 0 |
| `Kome.Store` | T11, T18 (`auth_first`, tested) | `Valid` relates the index, the journal log and F. Each outcome of `Put_Frame` is an iff in D11 order. A refusal changes nothing. `Expire` is at `Horizon_At` (T11 (a)). `Compact` writes authorization records first. gnatprove proves `Open_From_Log` for HEADER-only logs | 109 PASS | 4504 | 0 |
| `Kome.Emit` | `chase` T8, `adm_put_le` T9, `emitT_le` T13, `lt_iff_prefix` | `Choose` picks (t, seq) without h, and the outcome does not depend on h. Also: `V.T <= maxceil`, no `seq` wrap, the H8 jump, SHADOWED exactly as in §5, and an OK write is admitted and undominated | 55 PASS | 313 | 0 |
| `Kome.Views` | T5 (`rootVoid_F`, `wEff_F`, `voided_F`, `rosterEff_F`), T12 | `cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `void`, `far`, `ROSTER_eff` and `del_ttl_eff` are functions of F. Each cell has one value on every frontier | 131 PASS | 1120 | 0 |
| `Kome.Accumulator` | T6 (DESIGN.md §8) | 4096-bit `Add`/`Sub` modulo 2^4096 against an exact integer model. Commutative and associative, `Add_Sub`, the byte bijection and congruence | 30 PASS | 735 | 0 |
| `Kome.Digest` | T6 (DESIGN.md §8) | The layouts of `acc(e)` and `fp`, incremental add/remove and order independence. `Range_Sum` over D15 prefix sums is exact, with the cost formula of at most 64 Adds | 134 PASS | 967 | 0 |
| `Kome.Reconcile` | T7 (open in Lean) | Message size bounds and the OPEN/HELLO formats. The auth-then-data phases with exact root ranges. The reply kinds are pinned, and the split is well founded. A refusal changes nothing, and `Key_Lt` is bytewise order. T7 itself is tested only | 142 PASS | 2134 | 0 |
| `Kome.Epochs` | T14 (paper) | `Derive` and the chain lemmas. Fixed-length boxes whose wrap key covers ns and the epoch, with the synthetic nonce in the Post. Segment links. Non-canonical and low-order peers are refused | 69 PASS | 220 | 0 |

Lean proves the theorems about the functions. SPARK proves the same facts
about the code. Neither tool does the other's work. The remaining
parts of the design (`Kome.Roster`, the transports, the C ABI, extension F)
will use the same pattern, with one package for each part. They will come in
the order that `docs/design/DESIGN.md` §10 gives.

## Contributing

Read `CONTRIBUTING.md`. Sign off every commit. Every change must keep
`lean/build.sh` and `spark/check.sh` green.

## License

See `LICENSE`.
