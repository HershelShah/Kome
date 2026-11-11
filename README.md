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
| The chosen design, the **frontier store** | `docs/design/DESIGN.md` | decided; simplified by `docs/design/SIMPLIFY.md` (S1–S24), and `DESIGN.md` describes the result as built |
| Its mathematics, machine-checked in Lean 4 | `lean/` | T1–T3, T4 (a) and (b), T4′, T5, T8, T9, T10, T11 (a) and (b), T12, T13, T18 and T19 proved (214 theorems and 2 instances), in the scope that `DESIGN.md` §10.1 lists (no `sorry`); T4 (c) and T7 open |
| The implementation, in SPARK, proved against the Lean model | `spark/` | 17 packages (phases 0–8 of `docs/design/IMPLEMENTATION_PLAN.md`, except `Kome.Roster`). Seven of them (`Kome.Versions`, `Headers`, `Frontier`, `Records`, `Store`, `Emit`, `Views`) refine `Frontier.lean`; the others implement encodings, cryptography and protocols. The plan's Phases table holds the per-package test and proof counts, and its Known gaps section lists the remaining gaps |
| The design audit: holes, removable assumptions, residue | `docs/design/AUDIT.md` | 160 confirmed findings at 2be1260; §0 of the audit lists what is applied, and which items the simplification superseded |

## The design in one paragraph

Every change is a small signed record. A replica's state is a set of
records. To merge two replicas, take the set union, then drop every record
that a newer record *dominates* under a single strict total order. The set
that remains is the *frontier*, and it is the full state, apart from one
*ceiling cell*: the highest roster ceiling that the replica was offered
and had no room to hold. There is no history, no vector clock and no
per-peer bookkeeping.

A deletion is a record that dominates every field of its entity. So a
deletion frees bytes on every replica, with no membership knowledge and no
clock. Some rules look like policy: who can write, how far into the future a
clock can claim to be, and who is revoked. Each of these rules is a
*monotone admission rule* or a *pure view* over the frontier. No such rule
is part of the merge.

The one theorem that makes this work is the frontier homomorphism
`F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))`. It means that if you drop a beaten record
anywhere and at any time, no future state changes.

## Wire and log in brief

A collection is fixed at founding by its founding key, a salt and the
tombstone lifetime: `cid = BLAKE2b-256(root_pk ‖ salt ‖ u48(del_ttl))`,
and `ns = cid[0:16]` routes it. Every record is `tag ‖ content ‖ sig`
with `h = BLAKE2b-256(tag ‖ cid ‖ content)`, signed with Ed25519, and no
frame carries the `cid`: the verifier supplies it. The founding key
certifies the other roots (and itself). Each roster carries a fresh
collection key for its generation, boxed to each member, and the bundle
key derives from it. The log of a replica is `HEADER` (`"KOME"`, version,
`root_pk`, `salt`, `del_ttl`; 59 bytes), then `APPLY` entries (one
applied frame each), `SEQ` entries (the device's sequence counter,
written by compaction) and `CEIL` entries (a roster frame that is kept
only for its ceiling, in the ceiling cell). Tombstones expire at
`maxceil(F) − del_ttl`, a function of the state, so replay of the log
gives back the same frontier. `maxceil` does not depend on the order in
which records arrive, also when a signer's slice is full (T19).
Sync runs over Noise XK, reconciles the authorization records and then
the data records by range fingerprints, and every reply tiles the range
that it answers. `docs/design/DESIGN.md` §2, §7 and §8 give the exact
bytes.

## Layout

```
docs/design/          REQUIREMENTS.md, DESIGN.md, SIMPLIFY.md, IMPLEMENTATION_PLAN.md, AUDIT.md
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

`spark/kome_spark.gpr` has a `Mode` scenario variable. `check`, the
default, compiles with `-gnata`, so every contract, ghost call and loop
invariant runs in the tests. `release` (for example `gprbuild -P
spark/kome_spark.gpr -XMode=release`) builds without run-time contract
checks, which is the build to measure or ship; the proofs do not depend on
the mode. `spark/check.sh` documents how it selects the mode.

`spark/check.sh` uses GNAT 14, gprbuild, gnatprove 14 and the cvc5 and z3
provers (the proof switches are in `spark/kome_spark.gpr`). It fails if a
module has an unproved check, if a source uses `pragma Assume` or `pragma
Annotate`, or if a test binary links a monocypher symbol that Kome does not
bind. `spark/check.sh --list` prints the module list that CI uses. CI
(`.github/workflows/ci.yml`) runs the tests and the Lean build on every
pull request, and the full proof every night and on demand, because the
full proof takes about an hour. Before you push, run `PROVE=0
./spark/check.sh all` and the proof of each module that you changed.

## How the SPARK code relates to the Lean proofs

Seven SPARK packages refine a part of `lean/Kome/Frontier.lean`:
`Kome.Versions`, `Kome.Headers`, `Kome.Frontier`, `Kome.Records`,
`Kome.Store`, `Kome.Emit` and `Kome.Views`. The Lean file
proves the theorems about *sets* of records: convergence in any order with
any duplication, the frontier homomorphism, and monotone admission. The
SPARK contracts state that the bounded, in-place code implements exactly
the functions that those theorems are about. gnatprove discharges these
contracts. The other packages implement encodings (`Kome.Byteorder`,
`Kome.Keys`), cryptography (`Kome.Crypto`, `Kome.Epochs`) and protocols
(`Kome.Accumulator`, `Kome.Digest`, `Kome.Reconcile`, `Kome.Guard`),
`Kome.Frames` hides the frame-to-record predicate from the store's proofs,
and `Kome.Write` joins `Kome.Emit`, `Kome.Records` and `Kome.Store` into
the write path.

The per-package test and proof counts come from the clean per-module runs
in CI (gnatprove 14, `--level=3`, cvc5 and z3), and the Phases table of
`docs/design/IMPLEMENTATION_PLAN.md` records them. No package uses
`pragma Assume`, `pragma Annotate` or justified checks.

| SPARK package | Lean counterpart | What gnatprove proves |
|---|---|---|
| `Kome.Byteorder` | — | Little-endian u64 encoding (D7): `To_LE_U64` and `Read_U64LE` are inverse bijections |
| `Kome.Versions` | `Version`, `Version.lt`, T1 | The order is a strict total order |
| `Kome.Headers` | `Record`, `dominates`, T2' | The header is `(Kind, Ent, FH, V, Issuer)`. Domination is the product order on rosters (strict in gen, ceiling not lower) and on GRANTs (cap and h, keyed by (issuer, subject)), and on REVOKEs of one (issuer, subject) a lower `from_t` wins. Domination is irreflexive and transitive, and no authorization record dominates a data record. `Canonical` is a property of a header |
| `Kome.Frontier` | `adm`, `applyD`, `expire`, `maxCeil_F`, `isWriter_F`, `wcap_F`, T4', T11; `maxCeilC`, `ceilC` (T19) | `Apply` keeps exactly the undominated admitted records (`t ≤ maxceil`, `author ∈ W`, `t ≤ wcap`). The Post states each outcome (OK, Dominated, Inadmissible, No_Space, Auth_Full) as an iff. A refusal leaves the state `Unchanged`. `Max_Ceil`, `In_W` and `W_Cap` are views with `_Def` lemmas, and `Lemma_Views_Step` gives their growth. `Max_Ceil` is the larger of `Held_Ceil`, over the held rosters, and the ceiling cell, which `Raise_Ceil` writes for a roster above `Max_Ceil` without a change of the rows (`Same_Held`); `Apply` never changes the cell. Each held record carries a payload tag; an Apply changes one entity run or one signer slot. `Expire (F, Hz)` removes exactly the DELs at or below `Hz` |
| `Kome.Keys` | — | Key and id word records: big-endian round trips, injectivity, and `Lt`/`Id_Lt` as byte-lexicographic order |
| `Kome.Crypto` | — | Monocypher binding (X25519, RFC 8032 Ed25519 with SHA-512 only inside the signature, BLAKE2b, XChaCha20-Poly1305 with a 24-byte nonce) with `SPARK_Mode Off` bodies: spec-level run-time checks, data dependencies and refusal preconditions. `Verify` is the cofactored verification predicate of DESIGN.md §2 as a SPARK expression over a private `Raw_Ed25519_Check`, and it refuses small-order public keys. The Posts of the bodies, `Raw_Ed25519_Check` and the two congruence axioms `Lemma_Blake2b_Congruent` and `Lemma_X25519_Congruent` are assumptions. RFC 8032, Wycheproof and other known-answer vectors check them |
| `Kome.Records` | T13, D1, D3, E5 | Canonical encoding, total `Decode` and both round trips. Every `h` binds the `cid`. Signer certificates over the `cid` (`Cert_OK`), the founding key self-certified, for ROSTER, REVOKE and GRANT; `gen ≤ ceiling_t ≤ cert_cap`; a GRANT's header carries its issuer's cap. `Decode` gives only canonical headers. Every `Make_*` states its header |
| `Kome.Store` | T11, `applyH`, T18 (`auth_first`, tested), T19 (`maxCeil_applyHC`, `maxCeil_stepHC`: the step; the fold is Lean's) | `Valid` relates the log, the tags of F and F: every tag points at the APPLY of its record, and the tag of the ceiling cell at the CEIL of its roster. Each outcome of `Put_Frame` is an iff in D11 order, with `Log_Full` for the log bytes (`Log_Fits` is the binding's bound), and an OK apply is Lean's `applyH` with automatic expiry at `hz(F)` (T11 (a)). A refusal changes nothing. A roster that the rows refuse for room and whose ceiling is above `maxceil` is recorded in the ceiling cell (`Ceil_Only`), and `Put_Ceil` does the same for the ceiling frame of a HELLO without trying the rows; after each of the two calls, unless the log was full, `maxceil` is the old value joined with the record's ceiling (`Ceil_Step`). `seq_self` comes from the log, and the two digest states model the authorization and data rows. `Compact` writes the cell's CEIL first, then row order, retags, ends with `SEQ`, and is refused while pinned. gnatprove proves `Open_From_Log` for HEADER-only logs, and that the prefix of length `Valid_Length` replays to a `Valid` pair (T18-prefix) |
| `Kome.Frames` | — | `Frame_Is (Frame, Cid, X)`, opaque outside its body, with its definition and congruence lemmas |
| `Kome.Emit` | `chase` T8, `adm_put_le` T9, `emitT_le` T13, `lt_iff_prefix` | `Choose` picks (t, seq) without h, and the outcome does not depend on h. Also: `V.T <= min(maxceil, wcap)`, every write at `t ≥ maxceil − Cap_Lead` unless its ceiling is lower, no `seq` wrap, the H8 jump, SHADOWED and CLAMPED exactly as in §5, and an OK write is admitted and undominated |
| `Kome.Write` | `chase` T8 (through `Kome.Emit`) | The write path in one call: `Write` = Choose, Make, Sign, `Put_Frame` (T8 from `Choose`; the record's header is the target and the chosen version; seq = `Seq_Self (S) + 1`), with each outcome as an iff and SHADOWED decided before signing. `Receive` is `Put_Frame` plus the apply-side `CLONE_SUSPECTED` (H18): an own record that changes the pair sets it. `Receive` can return `Ceil_Only`; `Write` cannot. `Receive_Ceil` is the receiver side of the ceiling frame of a HELLO: it checks that the frame is a verified ROSTER, applies it with `Put_Ceil` only (`Ceil_Done`), and gives the `SUSPECT_RELAY` flag of the frame |
| `Kome.Views` | T5 (`rootVoid_F`, `wEff_F`, `voided_F`, `isMinFrom_F`, `rosterEff_F`), T12 | `cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `revoked_at`, `void`, `revoked`, `ROSTER_eff` and `Roster_Max` (by the roster key `(gen, h, signer, ceiling_t)`), `contested` and `quarantined` are functions of F (T5); none of them reads the ceiling cell. `far` and `skew` are per-replica advisories that read the local clock (`skew` also reads `maxceil`). Each cell has one value on every frontier |
| `Kome.Accumulator` | T6 (DESIGN.md §8) | 4096-bit `Add`/`Sub` modulo 2^4096 against an exact integer model. Commutative and associative, `Add_Sub`, the byte bijection and congruence |
| `Kome.Digest` | T6 (DESIGN.md §8) | The layouts of `acc(e)` (eight BLAKE2b-512 chunks) and `fp`, incremental add/remove and order independence. `Range_Sum` over D15 prefix sums is exact, with the cost formula of at most 64 Adds |
| `Kome.Reconcile` | T7 (open in Lean) | Message size bounds and the HELLO, RANGE, ELEMENTS, HAVE and ROOT formats; the HELLO carries the credential roster and the ceiling frame (the roster of the sender's ceiling cell while it is live). The gate on every call. The auth-then-data phases with ROOT bounds fixed by phase. The reply kinds are pinned, replies tile their obligation, and the split is well founded. The snapshot is sorted, distinct and has the digest of F. A refusal changes nothing, and `Key_Lt` is bytewise order. T7 itself is tested only |
| `Kome.Epochs` | T14 (paper) | The hedged per-generation key `k_g` (`Key_For_Gen`), `box_pk` from the derived `eph_sk`, fixed-length boxes whose wrap key covers the cid and the gen, with the synthetic nonce in the Post, and the bundle key. Non-canonical and low-order peers and the all-zero key are refused |
| `Kome.Guard` | — | The REVOKE-aware session gate (a member whose sign_pk is `revoked` passes no gate) and `Admits = Gate ∧ ¬ quarantined`, with the lemmas that set and clear the quarantine. No state |

Lean proves the theorems about the functions. SPARK proves the same facts
about the code. Neither tool does the other's work. The remaining
parts of the design (`Kome.Roster`, the transports, the storage binding,
the C ABI, typed fields) will use the same pattern, with one package for
each part. They will come in the order of `IMPLEMENTATION_PLAN.md`
Phases.

## Contributing

Read `CONTRIBUTING.md`. Sign off every commit. Every change must keep
`lean/build.sh` and `spark/check.sh` green.

## License

See `LICENSE`.
