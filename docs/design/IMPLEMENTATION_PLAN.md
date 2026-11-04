# Implementation plan: the frontier store in SPARK

This plan maps `DESIGN.md` onto SPARK packages. It tells which Lean theorem
each package refines, and it sets the order of the work. A package is done
when these conditions are true:

- Its test main passes.
- `spark/check.sh <name>` proves it with no unproved check.
- Its contracts name the Lean theorems that they refine.

`spark/CONVENTIONS.md` gives the rules for provable code.

## Phases

The counts come from CI. Every night, CI runs `spark/check.sh <module>`
for every module from a clean checkout (gnatprove 14, `--level=3`, cvc5 and
z3). No package uses `pragma Assume`, `pragma Annotate` or justified checks,
and `PROOF_WIP` is empty. "Proved" means 0 unproved checks. Known gaps lists
the properties that are tested and not proved.

| Phase | Packages | DESIGN.md | Lean | State |
|---|---|---|---|---|
| 0 | `Kome` (bounds, status), `Kome.Byteorder` (little-endian u64, D7) | §2 bounds, §8 | — | done. Byteorder: 6 tests, 47 checks, 0 unproved |
| 1 | `Kome.Versions`, `Kome.Headers`, `Kome.Registers`, `Kome.Frontier` (per-signer authorization slices, `Expire`) | §2, §3, §4, §7 | T1, T2', T4', T11 | done. Versions: 11 tests, 13 checks, 0 unproved. Headers: 24 tests, 33 checks, 0 unproved. Registers: 8 tests, 201 checks, 0 unproved. Frontier: 48 tests, 1,727 checks, 0 unproved |
| 2 | `Kome.Keys` (key and id encoding), `Kome.Crypto` (monocypher binding, RFC 8032 Ed25519), `Kome.Records` (canonical encoding, signer certificates, hashing, signing, well-formedness) | §2 | T13 | done. Keys: 32 tests, 800 checks, 0 unproved. Crypto: 60 tests, 35 checks, 0 unproved (spec only; the bodies are `SPARK_Mode Off`). Records: 173 tests, 2,623 checks, 0 unproved |
| 3 | `Kome.Store` (HEADER plus an APPLY/APPLY_EXPIRED/EXPIRE journal, index, `Compact` with authorization records first, expiry at `Horizon_At`) | §7 | T11, T18 | done. 109 tests, 4,511 checks, 0 unproved |
| 4 | `Kome.Emit` (`Choose` without h, chase, `seq_self` per collection, SHADOWED, SEQ_EXHAUSTED) | §5 | T8, T9, T13 | done. 61 tests, 322 checks, 0 unproved |
| 5 | `Kome.Views` (`cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `void`, `revoked`, `far`, `ROSTER_eff` by `(epoch, gen, h)`, `ROSTER_FORK`, `del_ttl_eff`) | §3, §6 | T5, T12 | done. 141 tests, 1,190 checks, 0 unproved |
| 6 | `Kome.Accumulator` (4096-bit homomorphic sum), `Kome.Digest` (fingerprint, D15 prefix sums) | §8 | T6 | done. Accumulator: 30 tests, 736 checks, 0 unproved. Digest: 134 tests, 959 checks, 0 unproved |
| 7 | `Kome.Reconcile` (OPEN, HELLO, the auth range then the data range, C8 sketch) | §8 | T7 (open) | done. 142 tests, 2,134 checks, 0 unproved |
| 8 | `Kome.Epochs` (hash-chained keys, synthetic-nonce boxes, fixed segment boundaries, segment links), `Kome.Guard` (the REVOKE-aware gate and the quarantine flag), `Kome.Roster` (certification, segments, honest-issuer rules) | §6 | T14 (paper) | Epochs done: 72 tests, 227 checks, 0 unproved. Guard done: 18 tests, 26 checks, 0 unproved. `Kome.Roster` not started |
| 9 | Transports (Noise XX, sealed bundles), C ABI | §8, §10.6 | — | not started |
| 10 | Extension F (typed fields) | §4 | F's T15–T17 | after T7 |

## Known gaps

No package has an unproved check. In this section, a gap is one of these:

- A property that is tested or reviewed, but not proved.
- A duty of a layer that is not built yet.
- An open decision.
- A missing test.

### Tested, not proved

- **Store: each entry's frame decodes to its header.** `Frame_OK`
  (`kome-store.ads`) checks the op byte, the length word and the tag. It
  does not check `Header_Of (frame) = E.H`. So `Valid` does not carry
  that fact, which is true only at the precondition of `Put_Frame`. To
  prove it, `Kome.Records` needs a `To_Header` congruence lemma for each
  record kind. (The BLAKE2b lemma, `Kome.Crypto.Lemma_Blake2b_Congruent`,
  exists.) The log-growth lemmas and the copy in `Compact` also need a
  congruence step for each entry. `Every_Frame_Matches` tests the fact after
  every `Put_Frame` and `Compact`.
- **Store: replay completeness (T18, D9).** gnatprove proves replay for
  `Open_From_Log` only for a log that holds just a HEADER. A replay that
  refused every log with entries would still meet the contract. Lean proves
  T18 over sets (`auth_first`). For the implementation, tests check it (the
  reopen scenarios in `test_store.adb`, before and after `Compact`).
- **Frontier: `Auth_Full` case (c), W full (E1, E2).** The documentation
  says that this case is unreachable on a frontier. (|W| is at most the
  number of held GRANTs, which is at most `Writers_Max`.) But the counting
  argument is not proved. `Coherent` proves that every writer has a held
  grant. It does not prove the cardinality bound.
- **Digest: the D15 call bound.** The Post of `Range_Sum` proves the cost
  formula (at most 64 Adds and 1 Sub). But only a review of the body shows
  that the out counts are equal to the calls that the body makes. An
  Accumulator call counter would close this gap. But a ghost counter makes
  `Add` stateful, so this is a design decision.
- **Reconcile** (the "Tested, not proved" list in `kome-reconcile.ads`):
  - T7 (termination and convergence; also open in Lean).
  - `Decode` accepts every ELEMENTS/HAVE that carries items.
  - The item and frame bytes inside an encoded ELEMENTS/HAVE.
  - Split balance.
  - The honest-session derivations behind `Msg_Budget`, `Range_Budget` and
    `Ship_Budget`.
- **Crypto: assumed Posts.** The bodies are `SPARK_Mode Off`, so their
  Posts and the `Lemma_Blake2b_Congruent` axiom are assumptions. Known
  answers check them: RFC 8032 §7.1 and a Wycheproof subset
  (`vectors/crypto.txt`).
- **Proved but not executed under `-gnata`.** gnatprove proves these
  `Assertion_Policy (... => Ignore)` regions, but the test mains do not run
  them. If the tests ran them, each call would cost quadratic time:
  - `kome-accumulator.adb`: four limb-loop regions (`Add`, `Sub` and their
    chain lemmas)
  - `kome-digest.adb`: four prefix-sum and state regions
  - `kome-epochs.adb`: the `Derive` loop invariant

### Duties of layers not yet built

The message formats and their checks exist. But the steps that enforce
them belong to callers that are not built yet. So D13 and E3 are closed
only as far as their formats and checks go.

- **Transport (phase 9)** (the caller duties listed in `kome-reconcile.ads`):
  - Verify and apply OPEN's founding REVOKEs (`Is_Founding_Revoke`)
    before the gate, then `Kome.Guard.Note_Open` (the quarantine flag).
  - Check the HELLO credential (`Roster_Lists_DH`), apply it,
    `Kome.Guard.Note_Credential`, and evaluate the gate
    (`Kome.Guard.Admits`: the flag and the REVOKE-aware gate). While the
    flag is set, take no sealed bundle and seal none.
  - Verify ELEMENTS/HAVE items, check each item's key and apply the items
    in key order. Report `SUSPECT_RELAY` for a peer that delivers a record
    whose author is already void (DESIGN.md §8).
  - Seal bundles with synthetic nonces, closed under admission (each
    author's GRANTs and the largest-ceiling roster first, DESIGN.md §8).
  - Flush the log to `Log_Length` before a session is Complete and before
    a bundle is acknowledged (DESIGN.md §8).
  - Choose `Log_Cap` with `Kome.Store.Log_Fits`, and compact and retry on
    `LOG_FULL` (DESIGN.md §7).
- **`Kome.Roster` (phase 8):**
  - Let only the founding key open a segment, at `Segment_Top + 1`
    (`Kome.Epochs.Segment_Start`). Choose and deliver the segment tops
    (E3).
  - Enforce the honest-issuer rules (DESIGN.md §10.3): reconcile first;
    `gen = 1 + max` over `gen ≤ 2^47`, else `STOLEN_ROOT_SUSPECTED`; the
    epoch at least the largest held; `ceiling_t ≤ now + Cap_Lead`; the
    founding reserve of 15 entries; the recovery roster's membership
    (no revoked `sign_pk`) and ceiling (`> maxceil`). Seal no box for a
    `Revoked` member.
  - Wipe the caller's ephemeral `eph_sk` (D5).
  - Give a "largest certified cap" view. Today only the per-record
    `cert_cap` check exists (`Cert_OK` in `kome-records.ads`).
- **Reconcile does not use D15 yet.** `Range_Fp` computes `Digest_Of`
  over the slice for every range. To use `Build_Prefix`/`Range_Sum`,
  `Snapshot` needs a prefix array that `Add` and `Clear` keep valid. It also
  needs a lemma that ties `Range_Sum` to `Fingerprint (Digest_Of (slice))`.
  This item is about cost, not about correctness.

### Open decisions

- **Small-order Ed25519 public keys.** `Verify` accepts them (Wycheproof
  tcIds 152-180), as RFC 8032 permits. It is not decided whether decode
  must refuse them.

### Missing tests

- **Emit:** There is no Shadowed DEL case (a DEL target at the ceiling over
  a PUT or a DEL by a higher key). There is also no test of H8 detection
  from the device's own DEL. The mutant `Own => X.K = K_Put and ...`
  passes the tests, and only the proof catches it.
- **Records:** No test decodes a PUT frame as DEL. (A test for the opposite
  direction exists.)

### Proof margin

- **Store: the Post of `Compact`** (`kome-store.ads`). z3 alone proves its
  slowest sub-goal in about 12.6 s, and the limit is 20 s at `--level=3`.
  A goal this close to the limit can fail on a slower machine or with a
  different prover release. The per-module run in CI is the reference.
