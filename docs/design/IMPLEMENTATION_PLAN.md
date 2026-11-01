# Implementation plan: the frontier store in SPARK

This maps `DESIGN.md` onto SPARK packages, says which Lean theorem each
package refines, and fixes the order of work. The rule throughout: a
package is done when its test main passes and `spark/check.sh <name>`
proves it, and its contracts name the Lean theorems they refine.

## Phases

State as of the last full `spark/check.sh all` run (gnatprove 14,
`--level=3`, cvc5 and z3). Counts are gnatprove's checks per package; no
package uses `pragma Assume`, `pragma Annotate` or justified checks.
"Proved" means 0 unproved checks; it does not mean the package has no open
review findings (see Known gaps below).

| Phase | Packages | DESIGN.md | Lean | State |
|---|---|---|---|---|
| 0 | `Kome` (bounds, status), `Kome.Byteorder`, `Kome.SHA256` | §2 bounds | — | done. Byteorder: 74 tests pass, 322 checks, 0 unproved. SHA256: 45 tests pass, 2084 checks, 0 unproved |
| 1 | `Kome.Versions`, `Kome.Headers`, `Kome.Registers`, `Kome.Frontier` | §2, §3, §4 | T1, T2', T4', `applyA`/`keep` refinement | done. Versions: 8 tests, 9 checks, 0 unproved. Headers (proof only): 12 checks, 0 unproved. Registers (proof only): 34 checks, 0 unproved. Frontier: 20 tests, 283 checks, 0 unproved |
| 2 | `Kome.Keys` (added: key and id encoding), `Kome.Crypto` (monocypher binding), `Kome.Records` (canonical encoding, hashing, signing, well-formedness) | §2 | T13 | built. Keys: 16 tests, 679 checks, 0 unproved. Crypto: 47 tests, 17 checks (spec only; bodies `SPARK_Mode Off`), 0 unproved. Records: 94 tests, 1869 checks, 0 unproved; review blocker open (signer admission, see gaps) |
| 3 | `Kome.Store` (append-only log, index `cell → (offset, v)`, compaction = rewrite `F`), tombstone expiry | §7 | T11 (liveness, stated) | built, not accepted. 55 tests pass, 1987 checks, **1 unproved** (listed in `PROOF_WIP`); two review blockers open |
| 4 | `Kome.Emit` (chase, `seq_self`, SHADOWED, SEQ_EXHAUSTED) | §5 | T8, T9, T13 | built. 42 tests, 236 checks, 0 unproved; review major open (H-independence) |
| 5 | `Kome.Views` (`cell`, `exists`, `deleted_at`, `void`, `far`, `ROSTER_eff`) | §3, §6 | T5, T12 | built. 70 tests, 867 checks, 0 unproved; review major open (root_void) |
| 6 | `Kome.Accumulator` (4096-bit homomorphic sum, prefix sums), `Kome.Digest` | §8 | T6 | built. Accumulator: 25 tests, 716 checks, 0 unproved. Digest: 58 tests, 709 checks, 0 unproved |
| 7 | `Kome.Reconcile` (range split, HAVE round, module I sketch, register join in HELLO) | §8, §4 | T7 (open in Lean) | built. 83 tests, 1805 checks, 0 unproved; T7 tested only; review majors open |
| 8 | `Kome.Epochs` (hash-chained keys), `Kome.Roster` (members, roots, revocation) | §6 | T14 (paper) | Epochs built: 37 tests, 99 checks, 0 unproved; review major open (nonce reuse). `Kome.Roster` not started |
| 9 | Transports (Noise XX, sealed bundles), C ABI | §8, §10.7 | — | not started |
| 10 | Extension F (typed fields) | §4 | F's T15–T17 | after T7 |

## Known gaps

Every unproved check and every deviation or open finding reported by the
package authors and reviewers. "Major" and "blocker" are the reviewers'
grades.

### Unproved checks

- `Kome.Store`, 1 check, `kome-store.adb:1253`, `pragma Assert (St in OK |
  Dominated)` in `Put_Frame` after `Frontier.Apply`. `Put_Frame` refuses
  beforehand every case `Apply` would refuse, but `Frontier.Apply`'s Post
  says only `No_Space => Count (S) = Count (S'Old)`: not when `No_Space`
  happens. Needs `Apply`'s Post to state its room rule (not
  `S = S'Old`, which is false: `Apply` raises a roster's registers before
  its room check). Checked at run time by the test main under `-gnata`.

### Design decisions needed (cross-package)

- **Signer admission for ROSTER and REVOKE** (`Kome.Records`, blocker;
  touches `Kome.Frontier`, `Kome.Headers`, DESIGN.md §6 module J).
  `Well_Formed` checks authenticity under a signer named in the record, not
  the brief's root_pk, and `Signer_Listed` is self-certifying. An
  outsider-signed roster and revoke pass `Decode_Verified`; `Frontier` then
  raises maxceil to 2^48-1, adds the outsider to W and holds a permanent
  forged REVOKE. The REVOKE header has no issuer field, so `Frontier` cannot
  check signer ∈ roots_ever. Either decide module J and add signer
  admission, or restore the root_pk-only rule.
- **root_void reading** (`Kome.Views`, major). With from_t and issuer
  ignored, one compromised root can make ROSTER_eff None permanently,
  breaking module J's recovery promise for n_roots >= 2.
- **Non-canonical rosters** (`Kome.Views`). A roster with V.T > 0 lets
  `Frontier` keep a lower generation than `Gen_Lt` would choose. Needs
  `Canonical` enforced at decode and a lemma that `Gen_Lt` and `Dominates`
  agree.
- **BLAKE2b-EdDSA vs Ed25519** (`Kome.Crypto`, major). The binding signs
  with monocypher's BLAKE2b-EdDSA; DESIGN.md says Ed25519 and the brief
  asked for an RFC 8032 known answer.
- **Root X25519 key** (`Kome.Epochs`, major). DESIGN.md does not say where
  the root's X25519 key comes from.
- **Accumulator byte order** (`Kome.Accumulator`, major, DESIGN.md owner).
  §8 does not record the little-endian byte order the package uses.

### Kome.Store (not accepted)

- Blocker: reopening from the log does not replay to the same frontier.
  Registers are not saved and `Compact` keeps index order, so after a roster
  refresh plus `Compact`, a dominated-on-arrival roster that raised
  maxceil, or a roster that drops a member, replay refuses held PUTs as
  Inadmissible and loses them. The test main uses only one roster.
- Blocker: expired DELs stay held in F, so the frontier can fill and wedge,
  and its digest diverges from a reopened replica.
- Dominated records are refused with `No_Space` on a full log or index.
- No proof that an entry's frame decodes to its header.
- `Del_TTL` is caller-supplied, with one monotone horizon.
- Assigning a `Frontier.State` crashes gnatprove, so `F` cannot be restored
  after a failed `Apply`; Store's own `Dynamic_Predicate` passes the same
  crash on to clients.

### Kome.Emit

- Major: DESIGN.md §2 makes h the hash of content that includes t and seq,
  so the caller cannot supply H before `Emit_Version` picks them. The
  outcome is independent of H, but no contract says so. Needs that lemma or
  an API split.
- Deviation: the brief's refusal at floor.t + 1 is replaced by DESIGN.md's
  t_emit formula (reviewer agrees).
- `Tgt.NS` is unchecked (waits on a `Kome.Frontier` NS accessor).
- A comment says `Apply` will hold an OK write; `Apply` can still return
  `No_Space`.
- Proof-only loops in `Floor` and `Emit_Version` run as executable code.
- `Clone_Suspected` is an out Boolean, not a `Status` literal.
- With a compromised key, the H8 jump can exhaust the device-global
  seq_self in every collection.
- Two small test gaps.

### Kome.Reconcile

- Contract gap: the Posts of `Respond` and `Receive` do not constrain the
  plan kinds of a non-confirm reply. A mutant that answers every mismatched
  RANGE with an empty HAVE proves completely.
- The responder can be driven to Complete by a g = 0 HAVE or by a root
  RANGE over only part of the key space.
- Major: frames over 48 902 bytes cannot be reconciled.
- Major: HELLO register values are unauthenticated (`Join_Regs = False`
  skips the join).
- Major: the exact W' = W ∪ H.W depends on `Kome.Registers` stating
  distinct counting and a tighter `Add_Writer` bound.
- Tested, not proved: T7 (termination and convergence); that `Decode`
  accepts every ELEMENTS/HAVE carrying items; item and frame bytes inside
  an encoded ELEMENTS/HAVE; `Key_Lt` equals bytewise order on the 81-byte
  wire key; the honest-session derivations behind `Msg_Budget`,
  `Range_Budget` and `Ship_Budget`.

### Kome.Epochs

- Major: one nonce may be reused for the same member across epochs, and the
  wrap key does not cover ns or epoch, so the boxes share a keystream; a
  removed member holding k5 recovers k6 from two ROSTER boxes. Fix: hash ns
  and epoch into the wrap key.
- No known-answer vector in the repository for the box construction (an
  independent Python reference matched it).

### Kome.Views

- Deviation: `Lemma_Cell_Unique` and T12 for the Cell payload are
  conditional on `Canonical` / A2 (the unconditional form is false for the
  current `Frontier`); `Is_Void` also requires the REVOKE's ns to match.
- Test gap: no Dominated, Inadmissible or No_Space data in the T12
  converse. The Option payload looks like a real PUT header.

### Kome.Digest

- Removing a non-member (or adding twice) returns `D_OK`; only the caller's
  `Models` discipline catches it (inherent in keeping just (|R|, ACC)).
- `Range_Sum` on a one-element range at the end of a 127-element list costs
  125 additions against §8's "at most 64"; the header's "63 terms per tail
  end" understates it. Fix: store the total ACC as one more prefix entry.
  DESIGN.md §10 does not record the tail exception.
- `D_No_Space` is never exercised; the tail branch with r > 32 never runs
  under `-gnata`; some `Result` values in the test are unchecked.
- `Is_Perm` is a public quantified expression function (CONVENTIONS rule 2).
- The Accumulator congruence lemmas live in `Kome.Digest`.

### Kome.Accumulator

- Usability: the laws do not chain under Ada array `=`; clients need
  `Lemma_Value_Congruent` then `Lemma_Value_Injective`.
- Unconfirmed author claim: private-part expression functions and
  `Hide_Info` are visible to clients in gnatprove 14. Confirm before
  changing CONVENTIONS rule 2.

### Kome.Crypto

- Bodies are `SPARK_Mode Off`: the Posts are assumed and checked only by
  known-answer vectors.
- Minor: no `Default_Initial_Condition` contracts (`not Is_Valid` on a
  default key does not prove); a function returns the secret seed; the
  `Max_Data_Len` justification for store-and-forward bundles; a
  by-reference wording claim.

### Kome.SHA256

- The public ghost lemmas fail at run time under `-gnata` on large inputs:
  `Lemma_Updated_Eq` overflows the stack at 4 MiB, `Lemma_Update_Concat`
  at 1 MiB and runs over 300 s at 64 KiB. The proof is unaffected.
- Digest correctness against FIPS 180-4 rests on known-answer vectors;
  there is no reference model of `Compress_Words`.

### Kome.Keys

- `Id128` has no injectivity or order lemma (§8 will need the order).
- The test main does not exercise the length-precondition failure path.
- A comment in `kome.ads` still says `Kome.Records` does the conversion.
- Optional: a lemma converting a slice to `Key_Bytes`.

### Tooling

- `check.sh all` stops at the first failing module (`set -e`), so the
  modules after it are not run; `PROOF_WIP=""` falls back to the default
  list because of `${PROOF_WIP:-...}`.
- gnatwhy3 spins forever if `TMPDIR` names a missing directory, and two
  gnatprove runs sharing the default `/tmp` why3server socket crash with
  "failed to open semaphore". Use a private, existing `TMPDIR`.
- Several `Kome.Store` goals are close to the 20 s prover limit on a loaded
  machine.

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
