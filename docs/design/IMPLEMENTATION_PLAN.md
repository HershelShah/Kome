# Implementation plan: the frontier store in SPARK

This maps `DESIGN.md` onto SPARK packages, says which Lean theorem each
package refines, and fixes the order of work. The rule throughout: a
package is done when its test main passes and `spark/check.sh <name>`
proves it, and its contracts name the Lean theorems they refine.

## Phases

State as of the round-three gap pass, from a full run of
`PROOF_WIP="" spark/check.sh all` (gnatprove 14, `--level=3`, cvc5 and z3):
1 140 tests pass, 0 fail, 17 547 checks, 0 unproved, "all modules green".
`PROOF_WIP` is empty by default. Counts are gnatprove's checks per package.
No package uses `pragma Assume`, `pragma Annotate` or justified checks.
"Proved" means 0 unproved checks. It does not mean the package has no
open review findings; see Known gaps below.

| Phase | Packages | DESIGN.md | Lean | State |
|---|---|---|---|---|
| 0 | `Kome` (bounds, status), `Kome.Byteorder`, `Kome.SHA256` | §2 bounds | — | done. Byteorder: 74 tests pass, 322 checks, 0 unproved. SHA256: 49 tests, 2123 checks, 0 unproved |
| 1 | `Kome.Versions`, `Kome.Headers`, `Kome.Registers`, `Kome.Frontier` (per-signer authorization slices, `Expire`) | §2, §3, §4, §7 | T1, T2', T4', T11, `applyD`/`expire` refinement | done. Versions: 11 tests, 13 checks, 0 unproved. Headers: 18 tests, 31 checks, 0 unproved. Registers: 6 tests, 93 checks, 0 unproved. Frontier: 44 tests, 1515 checks, 0 unproved |
| 2 | `Kome.Keys` (key and id encoding), `Kome.Crypto` (monocypher binding, RFC 8032 Ed25519), `Kome.Records` (canonical encoding, signer certificates, hashing, signing, well-formedness) | §2 | T13 | done. Keys: 32 tests, 800 checks, 0 unproved. Crypto: 64 tests, 35 checks (spec only; the bodies are `SPARK_Mode Off`), 0 unproved. Records: 172 tests, 2622 checks, 0 unproved |
| 3 | `Kome.Store` (HEADER plus an APPLY/APPLY_EXPIRED/EXPIRE journal, index, `Compact` with authorization records first, expiry at `Horizon_At`) | §7 | T11, T18 (Lean `auth_first`) | done. 109 tests, 4504 checks, 0 unproved. Replay completeness and frame-to-header are tested, not proved (see gaps) |
| 4 | `Kome.Emit` (`Choose` without h, chase, `seq_self` per collection, SHADOWED, SEQ_EXHAUSTED) | §5 | T8, T9, T13 | done. 55 tests, 313 checks, 0 unproved |
| 5 | `Kome.Views` (`cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `void`, `far`, `ROSTER_eff`, `del_ttl_eff`) | §3, §6 | T5, T12 | done. 131 tests, 1120 checks, 0 unproved |
| 6 | `Kome.Accumulator` (4096-bit homomorphic sum), `Kome.Digest` (fingerprint, D15 prefix sums) | §8 | T6 | done. Accumulator: 30 tests, 735 checks, 0 unproved. Digest: 134 tests, 967 checks, 0 unproved |
| 7 | `Kome.Reconcile` (OPEN, HELLO, the auth range then the data range, module I sketch) | §8 | T7 (open in Lean) | done. 142 tests, 2134 checks, 0 unproved. T7 is tested only. Content checks are the phase-9 caller's |
| 8 | `Kome.Epochs` (hash-chained keys, synthetic-nonce boxes, segment links), `Kome.Roster` (certification, segments, honest-issuer rules) | §6 | T14 (paper) | Epochs done: 69 tests, 220 checks, 0 unproved. `Kome.Roster` not started |
| 9 | Transports (Noise XX, sealed bundles), C ABI | §8, §10.7 | — | not started |
| 10 | Extension F (typed fields) | §4 | F's T15–T17 | after T7 |

## Known gaps

These are the gaps left after round three. Each has a place in the code and
a reason. No package has an unproved check (see Phases). A gap here is a
property that is tested or reviewed but not proved, a duty that belongs to
a layer not yet built, an open decision, or a known test or documentation
gap. Line numbers are as of the round-three gap pass.

### Proved in part, the rest tested

- **Store: an entry's frame decoding to its header.**
  `Frame_OK` (`kome-store.ads:1072-1082`) checks only the op byte, the
  length word and the tag. It does not check `Header_Of (frame) = E.H`, so
  `Valid` (`:1180-1199`) does not carry that fact. It holds only at
  `Put_Frame`'s Pre (`:616`). The Crypto axiom it needs now exists
  (`Lemma_Blake2b_Congruent`, `kome-crypto.ads:173`). Still missing:
  `Kome.Records.Lemma_Header_Congruent` (one per kind), and per-entry
  congruence loops in `Lemma_Framed_Grow/Sub/Push` and in `Compact`'s copy.
  Both are cross-package and risky for a 4 504-check proof. Tested by
  `Every_Frame_Matches` (`test_store.adb:240`, `:531`, `:823`). The comment
  at `kome-store.ads:137-149` still calls the Crypto lemma "(requested)".
- **Store: replay completeness (T18, D9).** `Open_From_Log` proves replay
  only for a log that holds just a HEADER (`kome-store.ads:111-121`). A
  replay that refused every log with entries would still meet the contract.
  T18 is proved over sets in Lean (`auth_first`, `Frontier.lean:797`). For
  the implementation it is tested only (`test_store.adb:802`, `:834`,
  `:845`, `:986`, `:996`, `:1029`, `:1068`, `:1103`, `:1139`, `:1145`,
  `:1188`, `:1222`, `:1231`).
- **Frontier: `Auth_Full` case (c), W full (R5, E2).** It is documented as
  unreachable on a frontier, because |W| is at most the number of held
  GRANTs, which is at most `Writers_Max`. The counting argument is not
  proved (`kome-frontier.ads:208-212`). `Coherent` proves that every writer
  has a held grant, but not the cardinality bound.
- **Digest: the D15 call bound.** `Range_Sum`'s Post proves the cost
  formula: at most 64 Adds and 1 Sub. That the out counts equal the calls
  actually made rests on review of the body (`kome-digest.ads:84-98`). A
  body that set `Adds` without counting would still prove. One fix is an
  Accumulator call counter, either a test-only instrumented build or a
  ghost counter. A ghost counter makes `Add` stateful, so it is a design
  decision.
- **Reconcile: tested, not proved** (`kome-reconcile.ads:186-198`):
  - T7, termination and convergence; T7 is open in Lean too.
  - That `Decode` accepts every ELEMENTS/HAVE carrying items.
  - The item and frame bytes inside an encoded ELEMENTS/HAVE.
  - Split balance.
  - The honest-session derivations behind `Msg_Budget`, `Range_Budget`
    and `Ship_Budget`.
- **Crypto: assumed Posts.** The bodies are `SPARK_Mode Off`, so their
  Posts are assumed (`kome-crypto.ads:46-70`). Round three adds one axiom to
  that set, `Lemma_Blake2b_Congruent` (`:173`). The Posts are checked by
  known answers: RFC 8032 §7.1 and a Wycheproof subset
  (`vectors/crypto.txt:7-37`).
- **SHA256: no reference model of `Compress_Words`.** Correctness rests on
  NIST CAVP known answers (ShortMsg, LongMsg and Monte Carlo;
  `kome-sha256.ads:14-28`). The public ghost lemmas run under `-gnata` only
  up to about 64 KiB (`:159-172`). The proof is unaffected.
- **Proved but not executed under `-gnata`.** These `Assertion_Policy
  (... => Ignore)` regions are proved, but the test mains do not run them.
  This is the CONVENTIONS tension that was removed from Store.
  - `kome-accumulator.adb:136`, `:169`, `:305`, `:465`
  - `kome-digest.adb:457`, `:553`, `:652`, `:747`
  - `kome-epochs.adb:48`, the `Derive` invariant
  - `kome-sha256.adb:917`, the `Absorb` invariant
  - `kome-sha256.ads:527`, a private-part Post

### Duties of layers not yet built

The message formats and the checks for these exist. The steps that enforce
them belong to the caller, which does not exist yet. D13, R2, E3 and part of
the round-three minors are therefore closed only as far as their formats
and checks go.

- **Transport (phase 9)** (`kome-reconcile.ads:39-52`):
  - Verify and apply OPEN's founding REVOKEs (`Is_Founding_Revoke`)
    before the gate.
  - Check the HELLO credential (`Roster_Lists_DH`) and evaluate the gate.
  - Verify ELEMENTS/HAVE items, check each item's key and apply the items
    in key order.
  - Seal bundles with synthetic nonces.
- **`Kome.Roster` (phase 8):**
  - Segment opening by the founding key only, and choosing and delivering
    segment tops (E3, `kome-epochs.ads:76-77`).
  - The honest-issuer gen rule (R2, DESIGN.md §10.3).
  - Wiping the caller's ephemeral `eph_sk` (D5, `kome-epochs.ads:56-61`).
  - A "largest certified cap" view. Today only a per-record `cert_cap`
    check exists (`kome-records.ads:975`).
- **Reconcile does not use D15 yet.** `Range_Fp` computes `Digest_Of` over
  the slice for every range (`kome-reconcile.ads:1665-1668`), and there is
  no `Build_Prefix` or `Range_Sum` in Reconcile. Using them needs a prefix
  array in `Snapshot`, kept valid by `Add` and `Clear`, and a lemma tying
  `Range_Sum` to `Fingerprint (Digest_Of (slice))`. This is a cost item,
  not a correctness one.

### Open decisions

- **Small-order Ed25519 public keys.** `Verify` accepts them (Wycheproof
  tcIds 152-180), as RFC 8032 permits. Nobody has decided whether decode
  should refuse them (`kome-crypto.ads:22-44`).

### Tests

- **Emit:**
  - No Shadowed DEL case: a DEL target at the ceiling over a PUT or a DEL
    by a higher key.
  - No H8 detection from the device's own DEL. The mutant `Own => X.K =
    K_Put and ...` passes all 55 tests and is caught only by the proof
    (`kome-emit.adb:204`, `:245`).
  - The `Floor` comment (`kome-emit.ads:74-76`) still says Floor "reads
    only data records". It scans every held record and filters with
    `In_Floor`.

### Proof margin

- **Store: `Compact`'s Post** (`kome-store.ads:696`). Its slowest
  sub-goal is proved by z3 alone in 12.63 s; cvc5 fails at 15.1 s. The
  worst time by any prover is 17.81 s (z3, another sub-goal, which cvc5
  proves in 6.1 s). The limit is 20 s, so the margin is about 1.6x. These
  times come from reused why3 sessions. No from-scratch run has followed
  the last Store edits (`Lemma_Ends_Below` and the Post changes), so the
  4 504 / 4 504 result has not been reproduced independently.

### Documentation

- DESIGN.md §7 (about line 676) and `kome-store.ads:30-31` say the
  HEADER's capacities are those the store "was created with". In fact
  `Open_From_Log` rewrites them on reopen (`kome-store.ads:91-102`).
- DESIGN.md §10 records neither that rewrite nor the `Compact` deviation:
  no EXPIRE is written when fewer than 7 bytes remain.
- DESIGN.md §10.1 does not list T11 and T18 (`auth_first`) among the
  proved theorems. It does not mention `convergence` or
  `convergence_empty`, or the `Frontier S` / `Admitted S` hypotheses that
  `convergence` takes.

## Closed in round three

- **Store:**
  - The unproved `St in OK | Dominated` assert (`kome-store.adb:1253`) is
    gone. `Frontier.Apply`'s Post now states every outcome as an iff
    (`kome-frontier.ads:213-252`).
  - Replay to the same frontier: the registers are functions of F
    (`Coherent`), and `Compact` writes authorization records first.
  - Expired DELs are dropped by `Frontier.Expire`; the T11 (a) Post shows
    the frontier no longer wedges.
  - A dominated record is refused as `Dominated`, never `No_Space` (D11).
  - The horizon is computed from `Del_TTL_Eff` (D10).
  - No `Dynamic_Predicate`, no `Touch`, no `Assertion_Policy`
    (`Lemma_Unchanged_Refl`).
  - The `-gnatw.t` warning is gone.
- **Signer admission (D1, D1′):** Cert_OK and a founding-key certificate
  for every ROSTER, REVOKE and GRANT (`kome-records.ads:227-230`), and
  `Foreign_Root` at Store step 0.
- **Views:**
  - Only the founding key root-voids, and it is never revoked (D2).
  - Canonical headers come from decode, and roster domination is the
    product order (D3, R4).
  - `Lemma_Cell_Unique` needs only `Is_Frontier`.
  - The T12 converse tests are complete.
- **Crypto:**
  - RFC 8032 Ed25519 from monocypher-ed25519, with RFC 8032 and Wycheproof
    vectors (D4).
  - `Default_Initial_Condition`.
  - A ghost `Seed_Of`.
  - `X25519_Shared`.
  - `Always_Terminates` on `Blake2b_256` and `Wipe`.
- **Epochs:**
  - No root X25519 key (D5).
  - The wrap key covers ns and epoch, and the nonce is synthetic and in
    the Post (D6).
  - Known-answer vectors from an independent reference
    (`vectors/epochs.txt`).
  - `Step` wipes its buffers.
- **Accumulator and Digest:**
  - The byte order is recorded (D7).
  - The congruence lemmas live in Accumulator, with `Lemma_Eq_Iff_Value`.
  - The Hide_Info probe is recorded.
  - D15's extra prefix entry; any range costs at most 64 Adds and 1 Sub.
  - `Is_Perm` is opaque.
  - `D_No_Space` and the r > 32 tail are tested.
- **Emit:**
  - `Choose` takes no h, with `Lemma_Outcome_Independent_Of_H` (D8).
  - `Make_Put` and `Make_Del` state their headers.
  - `seq_self` is kept per collection.
  - `Tgt.NS` is checked.
  - The proof loops are moved into ghost lemmas.
  - The `No_Space` comment is fixed.
  - The tests for `Seq_Exhausted` after an H8 jump and for the same
    outcome under different hashes are added.
  - Superseded: the floor.t + 1 refusal, because DESIGN §5 is the spec;
    and `Clone_Suspected` stays an out flag by design.
- **Reconcile:**
  - The reply plan kinds are pinned (`Answers`).
  - `Root_OK` refuses a g = 0 HAVE and partial root RANGEs (D14).
  - `Value_Max = 40 960`, so every frame ships (D12).
  - No register crosses the wire (D13). The W′ join is superseded.
  - `Key_Lt` is proved to be bytewise order.
- **Keys:**
  - `Id128` round-trip, injectivity and order lemmas.
  - Slice lemmas.
  - A test of the length-precondition failure path.
  - The `kome.ads` comment is fixed.
- **Frontier:**
  - One data row plus a slice per signer (E1, R6).
  - `Auth_Full` on a full slice changes nothing (E2).
  - `Expire`.
  - `NS` accessor.
  - `Lemma_Unchanged_Refl`, and `Lemma_Unchanged` now runs under `-gnata`.
- **Tooling:**
  - `check.sh all` runs every module and reports all failures.
  - `PROOF_WIP=""` means no list.
  - Each run gets a private `TMPDIR`.
  - The prove step is serialized with `flock`.
  - Store's slowest goal fell from 19.18 s to 12.63 s (see Proof margin).
- **Lean:**
  - Round-three model: five record kinds, the product order, `maxceil`
    and W as functions of F, and the discard model.
  - T4 as `auth_first` / `convergence_two_pass` / `convergence`.
  - T11 (`expire_*`), T18 (`auth_first`).
  - The views `rootVoid`, `wEff`, `voided` and `rosterEff`.

## Phase 1 in detail (the lattice core)

`Kome.Versions` is `Version` and `Version.lt`, a chain of word comparisons;
the four lemmas (irreflexive, asymmetric, transitive, trichotomous) are what
every later proof uses, as in Lean where every later theorem uses only the
`StrictTotal` instance.

`Kome.Headers` is `Record` and `dominates`. A header is a record minus its
payload: the lattice never looks at a value. Every kind carries its identity
in one `Version` (a roster's is `(0, signer, gen, h)`, a revocation's is
`(from_t, subject, rev_seq, h)`), so one order serves all four kinds and
`Dominates` is a quantifier-free public definition; the lemmas are
`Lemma_Dominates_Irrefl`, `Lemma_Dominates_Trans` (T2') and
`Lemma_Revoke_Never_Dominated` (T12).

`Kome.Registers` is the pair of grow-only registers (`maxceil`, `W`),
opaque, with `Extends` (writer-set inclusion) and the lemmas that make
admission monotone.

`Kome.Frontier` is `State`, `adm`, `keep`, `applyA`. The state is the held
headers plus the registers. `Apply`'s postcondition is the refinement
statement:

- registers only grow and exactly as the record says (T4');
- every held record was held before or is the record applied (`keep` is a
  filter of `held ++ [r]`);
- every record held before is still held or is dominated by an admitted
  held record (nothing is lost except by domination);
- the held set is always its own frontier, every held record is admitted,
  and no record is held twice;
- `OK` means held, `Dominated` means beaten and not held, `Inadmissible`
  and `No_Space` mean unchanged.

Lean's `convergence` then applies to any two replicas that run `Apply` on
the same set in any order. The one deliberate divergence from the model is
that inadmissible records are refused rather than held (DESIGN.md §10.1);
the test main models the re-offer by applying a record list to a fixpoint.

## Proof hygiene learned in phase 1

The lattice core took one day of design and a day of proof engineering;
all of the second day was spent finding these four rules, now in
`spark/CONVENTIONS.md`:

- Identifiers and keys in the lattice are records of words, not byte
  arrays, so that record equality is logical equality for the prover.
  Every congruence step (`Held (S, J) = R` therefore `Dominates (Q, R)`)
  depends on it, and the byte order becomes quantifier-free.
- Public expression functions are fine when quantifier-free and harmful
  when quantified; the register set is opaque with lemmas for that reason.
- Reason about a private type through its public functions in contracts
  and asserts, and bridge each state change with an explicit equality of
  the public view before and after.
- Replace nested existentials in loop invariants with ghost witness arrays,
  and record in the same invariant every property the witnesses need later
  (the last open goal was a kept record's "not dominated", which the
  witness invariant had not carried).

Result: `Kome.Frontier.Apply` proves with 110 run-time checks, 76
assertions and 88 contract checks discharged by cvc5 and z3, no
justifications, no unproved goals, in under three minutes.

Round three added eight more rules. They are in `spark/CONVENTIONS.md`
under "Proof hygiene learned in round three": what `Hide_Info` and the
private part hide, no `Dynamic_Predicate` on state types, refusals decided
before the state changes, executable ghost lemmas, congruence axioms,
pre-state-only Posts, `Always_Terminates` and ghost secrets, and the proof
margin.
