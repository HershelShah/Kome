# Implementation plan: the frontier store in SPARK

This maps `DESIGN.md` onto SPARK packages, says which Lean theorem each
package refines, and fixes the order of work. A package is done when its
test main passes, `spark/check.sh <name>` proves it with no unproved check,
and its contracts name the Lean theorems they refine. The rules for writing
provable code are in `spark/CONVENTIONS.md`.

## Phases

Counts are from CI, which runs `spark/check.sh <module>` for every module
from a clean checkout on every push (gnatprove 14, `--level=3`, cvc5 and
z3). No package uses `pragma Assume`, `pragma Annotate` or justified checks,
and `PROOF_WIP` is empty. "Proved" means 0 unproved checks; the properties
that are tested rather than proved are listed under Known gaps.

| Phase | Packages | DESIGN.md | Lean | State |
|---|---|---|---|---|
| 0 | `Kome` (bounds, status), `Kome.Byteorder` (little-endian u64, D7) | §2 bounds, §8 | — | done. Byteorder: @BYTEORDER@ |
| 1 | `Kome.Versions`, `Kome.Headers`, `Kome.Registers`, `Kome.Frontier` (per-signer authorization slices, `Expire`) | §2, §3, §4, §7 | T1, T2', T4', T11 | done. Versions: @VERSIONS@. Headers: @HEADERS@. Registers: @REGISTERS@. Frontier: @FRONTIER@ |
| 2 | `Kome.Keys` (key and id encoding), `Kome.Crypto` (monocypher binding, RFC 8032 Ed25519), `Kome.Records` (canonical encoding, signer certificates, hashing, signing, well-formedness) | §2 | T13 | done. Keys: @KEYS@. Crypto: @CRYPTO@ (spec only; the bodies are `SPARK_Mode Off`). Records: @RECORDS@ |
| 3 | `Kome.Store` (HEADER plus an APPLY/APPLY_EXPIRED/EXPIRE journal, index, `Compact` with authorization records first, expiry at `Horizon_At`) | §7 | T11, T18 | done. @STORE@ |
| 4 | `Kome.Emit` (`Choose` without h, chase, `seq_self` per collection, SHADOWED, SEQ_EXHAUSTED) | §5 | T8, T9, T13 | done. @EMIT@ |
| 5 | `Kome.Views` (`cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `void`, `far`, `ROSTER_eff`, `del_ttl_eff`) | §3, §6 | T5, T12 | done. @VIEWS@ |
| 6 | `Kome.Accumulator` (4096-bit homomorphic sum), `Kome.Digest` (fingerprint, D15 prefix sums) | §8 | T6 | done. Accumulator: @ACCUMULATOR@. Digest: @DIGEST@ |
| 7 | `Kome.Reconcile` (OPEN, HELLO, the auth range then the data range, C8 sketch) | §8 | T7 (open) | done. @RECONCILE@ |
| 8 | `Kome.Epochs` (hash-chained keys, synthetic-nonce boxes, segment links), `Kome.Roster` (certification, segments, honest-issuer rules) | §6 | T14 (paper) | Epochs done: @EPOCHS@. `Kome.Roster` not started |
| 9 | Transports (Noise XX, sealed bundles), C ABI | §8, §10.6 | — | not started |
| 10 | Extension F (typed fields) | §4 | F's T15–T17 | after T7 |

## Known gaps

No package has an unproved check. A gap here is a property that is tested
or reviewed but not proved, a duty of a layer not yet built, an open
decision, or a missing test.

### Tested, not proved

- **Store: each entry's frame decodes to its header.** `Frame_OK`
  (`kome-store.ads`) checks the op byte, the length word and the tag, but
  not `Header_Of (frame) = E.H`, so `Valid` does not carry that fact; it
  holds at `Put_Frame`'s precondition only. Proving it needs a `To_Header`
  congruence lemma per record kind in `Kome.Records` (the BLAKE2b one,
  `Kome.Crypto.Lemma_Blake2b_Congruent`, exists) and per-entry congruence
  steps in the log-growth lemmas and in `Compact`'s copy. Tested by
  `Every_Frame_Matches` after every `Put_Frame` and `Compact`.
- **Store: replay completeness (T18, D9).** `Open_From_Log` proves replay
  only for a log that holds just a HEADER; a replay that refused every log
  with entries would still meet the contract. T18 is proved over sets in
  Lean (`auth_first`); for the implementation it is tested (the reopen
  scenarios in `test_store.adb`, before and after `Compact`).
- **Frontier: `Auth_Full` case (c), W full (E1, E2).** Documented as
  unreachable on a frontier (|W| is at most the number of held GRANTs, at
  most `Writers_Max`), but the counting argument is not proved. `Coherent`
  proves that every writer has a held grant, not the cardinality bound.
- **Digest: the D15 call bound.** `Range_Sum`'s Post proves the cost
  formula (at most 64 Adds and 1 Sub); that the out counts equal the calls
  actually made rests on review of the body. An Accumulator call counter
  would close it, but a ghost counter makes `Add` stateful, so it is a
  design decision.
- **Reconcile** (the "Tested, not proved" list in `kome-reconcile.ads`):
  T7 (termination and convergence; open in Lean too), that `Decode` accepts
  every ELEMENTS/HAVE carrying items, the item and frame bytes inside an
  encoded ELEMENTS/HAVE, split balance, and the honest-session derivations
  behind `Msg_Budget`, `Range_Budget` and `Ship_Budget`.
- **Crypto: assumed Posts.** The bodies are `SPARK_Mode Off`, so their
  Posts and the `Lemma_Blake2b_Congruent` axiom are assumed. They are
  checked by known answers: RFC 8032 §7.1 and a Wycheproof subset
  (`vectors/crypto.txt`).
- **Proved but not executed under `-gnata`.** These `Assertion_Policy
  (... => Ignore)` regions are proved, but the test mains do not run them,
  because running them would cost quadratic time per call:
  - `kome-accumulator.adb`: four limb-loop regions (`Add`, `Sub` and their
    chain lemmas)
  - `kome-digest.adb`: four prefix-sum and state regions
  - `kome-epochs.adb`: the `Derive` loop invariant

### Duties of layers not yet built

The message formats and the checks for these exist; the steps that enforce
them belong to callers that are not built yet, so D13 and E3 are closed
only as far as their formats and checks go.

- **Transport (phase 9)** (the caller duties listed in `kome-reconcile.ads`):
  - Verify and apply OPEN's founding REVOKEs (`Is_Founding_Revoke`)
    before the gate.
  - Check the HELLO credential (`Roster_Lists_DH`) and evaluate the gate.
  - Verify ELEMENTS/HAVE items, check each item's key and apply the items
    in key order.
  - Seal bundles with synthetic nonces.
- **`Kome.Roster` (phase 8):**
  - Segment opening by the founding key only, and choosing and delivering
    segment tops (E3).
  - The honest-issuer gen rule (DESIGN.md §10.3).
  - Wiping the caller's ephemeral `eph_sk` (D5).
  - A "largest certified cap" view; today only the per-record `cert_cap`
    check exists (`Cert_OK` in `kome-records.ads`).
- **Reconcile does not use D15 yet.** `Range_Fp` computes `Digest_Of`
  over the slice for every range. Using `Build_Prefix`/`Range_Sum` needs a
  prefix array in `Snapshot`, kept valid by `Add` and `Clear`, and a lemma
  tying `Range_Sum` to `Fingerprint (Digest_Of (slice))`. A cost item, not
  a correctness one.

### Open decisions

- **Small-order Ed25519 public keys.** `Verify` accepts them (Wycheproof
  tcIds 152-180), as RFC 8032 permits. Whether decode should refuse them is
  undecided.

### Missing tests

- **Emit:** no Shadowed DEL case (a DEL target at the ceiling over a PUT or
  a DEL by a higher key), and no H8 detection from the device's own DEL:
  the mutant `Own => X.K = K_Put and ...` passes the tests and is caught
  only by the proof.
- **Records:** a PUT frame decoded as DEL is not tested (the opposite
  direction is).

### Proof margin

- **Store: `Compact`'s Post** (`kome-store.ads`). Its slowest sub-goal is
  proved by z3 alone in about 12.6 s against the 20 s limit at `--level=3`.
  A goal this close can fail on a slower machine or a different prover
  release; CI's per-module run is the reference.
