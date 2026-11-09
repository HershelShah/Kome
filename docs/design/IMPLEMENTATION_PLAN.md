# Implementation plan: the frontier store in SPARK

This plan maps `DESIGN.md` onto SPARK packages. It tells which Lean theorem
each package refines, and it sets the order of the work. A package is done
when these conditions are true:

- Its test main passes.
- `spark/check.sh <name>` proves it with no unproved check.
- Its contracts name the Lean theorem that they refine, where one exists;
  the Lean column records the status otherwise (—, paper, open).

`spark/CONVENTIONS.md` gives the rules for provable code.

## Phases

The counts come from CI. Every night, CI runs `spark/check.sh <module>`
for every module from a clean checkout (gnatprove 14, `--level=3`, cvc5 and
z3). No package uses `pragma Assume`, `pragma Annotate` or justified checks
(`spark/check.sh` fails on either), and no module is exempt from the
proof. "Proved" means 0 unproved checks. Known gaps lists the properties
that are tested and not proved, and the duties of the layers that are not
built.

| Phase | Packages | DESIGN.md | Lean | State |
|---|---|---|---|---|
| 0 | `Kome` (bounds, status), `Kome.Byteorder` (little-endian u64, D7) | §2 bounds, §8 | — | done. Byteorder: 6 tests, 47 checks, 0 unproved |
| 1 | `Kome.Versions`, `Kome.Headers`, `Kome.Registers`, `Kome.Frontier` (per-signer authorization slices, `Expire`) | §2, §3, §4, §7 | T1, T2', T4', T11 | done. Versions: 11 tests, 13 checks, 0 unproved. Headers: 24 tests, 33 checks, 0 unproved. Registers: 8 tests, 201 checks, 0 unproved. Frontier: 48 tests, 1,727 checks, 0 unproved |
| 2 | `Kome.Keys` (key and id encoding), `Kome.Crypto` (monocypher binding; `Verify` is the cofactored RFC 8032 predicate of DESIGN.md §2 as a SPARK expression over a private `Raw_Ed25519_Check`, and it refuses small-order public keys), `Kome.Records` (canonical encoding, signer certificates, hashing, signing, well-formedness; `Put_Target`/`Del_Target` constructors) | §2 | T13 | done. Keys: 32 tests, 800 checks, 0 unproved. Crypto: 60 tests, 35 checks, 0 unproved (spec only; the bodies are `SPARK_Mode Off`). Records: 173 tests, 2,623 checks, 0 unproved |
| 3 | `Kome.Store` (HEADER plus an APPLY/APPLY_EXPIRED/EXPIRE journal, index, `Compact` with authorization records first, expiry at `Horizon_At`) | §7 | T11, T18 | done. 109 tests, 4,511 checks, 0 unproved |
| 4 | `Kome.Emit` (`Choose` without h, chase, `seq_self` per collection, SHADOWED, SEQ_EXHAUSTED) | §5 | T8, T9, T13 | done. 61 tests, 322 checks, 0 unproved |
| 4 | `Kome.Write` (the write path: `Prepare` = Choose, Make, Sign; the binding persists `seq_self`; `Commit` = `Store.Put_Frame`; `Seq_Self_At_Open`, `Open_Seq` with SEQ_CORRUPT; `Receive` with the apply-side CLONE_SUSPECTED, AUDIT.md A10, H18) | §5, §7 | T8 (through `Kome.Emit`) | done. 42 tests, 123 checks, 0 unproved |
| 5 | `Kome.Views` (`cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `void`, `revoked`, `far`, `ROSTER_eff` by `(epoch, gen, h)`, `ROSTER_FORK`, `del_ttl_eff`) | §3, §6 | T5, T12 | done. 141 tests, 1,190 checks, 0 unproved |
| 6 | `Kome.Accumulator` (4096-bit homomorphic sum), `Kome.Digest` (fingerprint, D15 prefix sums) | §8 | T6 | done. Accumulator: 30 tests, 736 checks, 0 unproved. Digest: 134 tests, 959 checks, 0 unproved |
| 7 | `Kome.Reconcile` (OPEN, HELLO, the auth range then the data range; `Snapshot_Of (F)`; `Start` takes the peer's Noise key, `Receive (HELLO)` checks the credential, `Admit` has the gate as `Pre`; the obligation FIFO, D15 prefix sums in `Range_Fp`) | §8 | T7 (open) | done. 142 tests, 2,134 checks, 0 unproved |
| 8 | `Kome.Epochs` (hash-chained keys, the derived box secret `eph_sk`, synthetic-nonce boxes, fixed segment boundaries, segment links), `Kome.Guard` (the REVOKE-aware gate and the quarantine flag), `Kome.Roster` (`Build` by construction, certification, segments, recovery, honest-issuer rules) | §6 | T14 (paper) | Epochs done: 72 tests, 227 checks, 0 unproved. Guard done: 18 tests, 26 checks, 0 unproved. `Kome.Roster` not started |
| 9 | Transports (Noise XK with per-collection static keys, sealed bundles), the storage binding, C ABI | §7, §8, §10.6 | — | not started |
| 10 | Typed fields (C10) | §4, §10.7 | T15–T17 (not stated) | when an application needs them |

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
- **Store: the design's log rules that `Kome.Store` does not implement
  yet.** DESIGN.md §7 and §10.10 state them; the store today differs in
  each, and the design text is the target:
  - the replay clamp of an `EXPIRE` horizon to `Horizon_At (F, U48'Last)`
    and the `EXPIRE_NONE` entry in place of the `2^48 − 1` sentinel
    (AUDIT.md H24);
  - `Valid_Length` (the offset of the last complete entry) from
    `Open_From_Log`, and the prefix replay that the storage binding uses
    for a corrupt entry (AUDIT.md H23);
  - the store-owned compaction trigger at `2·|F| + c` entries (AUDIT.md
    H26);
  - the expire mark (the largest `t` of a `DEL` that `Expire` removed or
    an `APPLY_EXPIRED` applied), rebuilt by replay and read by
    `Kome.Emit.Choose` (AUDIT.md H28);
  - the slice as the constant `Slice_Max` with the HEADER field as a
    check, `data_cap` outside the log or in a `CAPS` entry, and a reopen
    at a smaller `data_cap` when the replay fits; today the store rewrites
    the HEADER's capacity bytes on a larger reopen and refuses a smaller
    one (AUDIT.md A11);
  - the replica statuses `Ceiling_Stale` and `Horizon_Frozen` (AUDIT.md
    N4).
- **Write: the self check of `Prepare`.** `Kome.Crypto` does not state
  `Verify (Sign (M))` (A1), so `Prepare` verifies its own signed frame at
  run time and gives `Malformed` if the check fails. With a key from
  `Key_Pair` the check never fails: `test_write.adb` checks that every
  Ready frame verifies; the `Malformed` branch is not reached in a test.
- **Emit: the `CLAMPED` and `BORN_EXPIRED` flags** of DESIGN.md §5 are not
  built. `Choose` reports `CLONE_SUSPECTED` only (AUDIT.md H22).
- **Views: `rivals (F)`** ("membership contested", DESIGN.md §3, §6) and
  the advisory `ceiling_lead` are not built (AUDIT.md A22, N3).
- **Epochs: the keyed chain.** DESIGN.md §6 defines the chain step and the
  bundle key as keyed BLAKE2b-256 (`crypto_blake2b_keyed`) under one PRF
  assumption (AUDIT.md G5). `Kome.Epochs.Step` still hashes `k ‖ "prev"`
  with the unkeyed function, `Kome.Crypto` has no keyed binding, and
  `vectors/epochs.txt` holds the unkeyed vectors. The chain lemmas treat
  `Step` as uninterpreted, so the change is local to `Step`, the bundle
  key and the vectors.
- **Headers and Views: the `AUTH_FULL` arrival-order case for `maxceil`.**
  A refused roster does not count in `maxceil`, so two replicas that
  refuse different records of one over-quota signer can hold different
  ceilings (DESIGN.md §7, §8). The fix is a reserved `CEIL (s)` cell per
  slot outside the slice (AUDIT.md H12). It is deferred; the design
  documents the case instead.
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
  - Run Noise XK with the per-collection static key `dh_sk_ns = KDF
    (device secret, ns)`, the responder's static key taken from
    `ROSTER_eff` or the enrollment credential, and `ns` in the prologue.
    Refuse a low-order peer static key (DESIGN.md §8; AUDIT.md H20, A29).
  - OPEN: as responder, wait for the initiator's OPEN and answer only
    when `ns` matches. Build the root-void set as one founding REVOKE per
    root-voided subject (the `from_t = 0` one with the least `h`), at most
    15 subjects, whatever the sender holds of that subject; send it only
    to a peer whose static key is a member `dh_pk` in some held roster,
    and `n_rv = 0` otherwise (AUDIT.md H5, A14). Verify and apply the
    peer's OPEN frames (`Is_Founding_Revoke`) before the gate, then
    `Kome.Guard.Note_Open` (the quarantine flag).
  - HELLO: drop the credential and abort, before verification, if `F`
    holds a founding REVOKE of its signer (AUDIT.md G12). Otherwise check
    it (`Roster_Lists_DH`), apply it, `Kome.Guard.Note_Credential`, and
    evaluate the gate (`Kome.Guard.Admits`: the flag and the REVOKE-aware
    gate). Evaluate the gate again at `Receive` and `Next_Phase` whenever
    the store's `Auth_Gen` moved past the session's `Gate_Gen`, and abort
    when it fails (AUDIT.md H11). While the flag is set, take no sealed
    bundle and seal none.
  - Joining (DESIGN.md §6): open a new store from the hand-off `(root_pk,
    salt, roster frame)`, and while `F` holds no non-root-voided roster
    that lists the device's own `dh_pk`, accept only a credential that
    lists both the peer's key and the device's own, and let no other
    credential change `ROSTER_eff` (AUDIT.md H10).
  - Between the auth phase and the data phase, call `Expire (Now)` if
    `del_ttl_eff` changed (AUDIT.md G18).
  - Verify ELEMENTS/HAVE items, check each item's key, and apply every
    item of kind < 3 before any item of kind ≥ 3 (D14). Report
    `SUSPECT_RELAY` for a peer that delivers a record whose author is
    already void, and report a `NO_SPACE` refusal of a peer-offered
    record as a replica status (DESIGN.md §7, §8).
  - Seal bundles as `ns ‖ nonce ‖ AEAD` with the epoch in the AD only,
    padded to fixed buckets, under `bundle_key (F)` (the key that the
    device's own entry of `ROSTER_eff` unboxes, never a key cached by
    epoch number), with synthetic nonces, closed under admission (each
    author's GRANTs and the largest-ceiling roster first). For a set
    period after an epoch change, also send an authorization-only bundle
    under the old key (DESIGN.md §6, §8; AUDIT.md A9, G11, H17).
  - Durability (AUDIT.md A21, H35): make the log durable to `Log_Length`
    before a session is Complete, before a bundle is acknowledged or
    deleted from a mailbox, before relaying an applied record, and before
    continuing after an authorization record (DESIGN.md §8).
  - Rate-limit pre-gate work and session openings per peer.
- **Storage binding (phase 9)** (DESIGN.md §7; AUDIT.md G13, H23, H26):
  - Append each entry at the `Log_Length (S)` from before the call
    (`pwrite` at that offset), so that a retry after a write error
    overwrites and never duplicates. The append preserves the prefix.
  - On any write error, discard the in-memory `(S, F)` and run
    `Open_From_Log` again; never serve a record whose entry is not on
    disk.
  - Preallocate `Log_Cap`, chosen with `Kome.Store.Log_Fits`; compact and
    retry on `LOG_FULL`.
  - Take an exclusive lock on the log for the life of the open.
  - `fsync` before a record is visible to `Reconcile` or `Emit`
    (the sync point).
  - `Compact` = write the new log, `fsync` it, rename it over the old
    one, `fsync` the directory.
  - On a torn tail, truncate to `Valid_Length` and open again; on a
    corrupt entry, open the prefix before it, report `DEGRADED`, and
    sync. Never skip an entry in the middle.
  - These duties are stated against T18: every entry-boundary prefix of a
    log that the store wrote replays OK, and the binding only ever hands
    the store such a prefix.
  - The write path (AUDIT.md A10; A5 restated): after
    `Kome.Write.Prepare`, persist `Seq_Persist` as `seq_self(ns)` durably
    (write and `fsync`) before `Kome.Write.Commit`; after `Commit`, make
    the log durable to `Log_Length` before the frame is sent or put in a
    bundle. On open, read the seq store and call `Kome.Write.Open_Seq`;
    a seq store that does not read back (torn, bad checksum) is
    `SEQ_CORRUPT`. Apply every frame from a peer with `Kome.Write.Receive`
    and show `CLONE_SUSPECTED` when its flag, the `Prepare` flag or
    `Kome.Write.Clone_View` holds (AUDIT.md H18).
- **`Kome.Roster` (phase 8):**
  - `Build (epoch key, root_pk, salt, e, signer, gen, members)` computes
    `eph_sk` and `box_pk` and seals the boxes from one secret, then wipes
    it; `Make_Roster` is private to it (AUDIT.md A6, G7). Post:
    `Box_PK = X25519_Public (eph_sk)`.
  - Let only the founding key open a segment, at `Segment_Top + 1`
    (`Kome.Epochs.Segment_Start`), on root-void, at the top of a segment,
    or in the top-leaked procedure (a new segment with no REVOKE).
    Draw and deliver the segment tops (E3); refuse an all-zero top.
  - Ceremony self-check: before a root's first roster in a segment, open
    the founding opener's link `{from_epoch = s}` with `Open_Link` from
    the received top, and refuse a top that opens none (AUDIT.md A15).
  - Issue the recovery steps in DESIGN.md §6 order (re-grants, member
    REVOKEs, re-signed revocations, then `REVOKE (R, 0)`, then the
    roster), and check the roster: no revoked `sign_pk`, `ceiling_t >
    maxceil`, `del_ttl ≥` the `del_ttl_eff` before the ceremony with the
    voided root counted (AUDIT.md H8, H16, H30, H32).
  - Enforce the honest-issuer rules (DESIGN.md §10.3): reconcile first;
    `gen = 1 + max` over `gen ≤ 2^47`, else `STOLEN_ROOT_SUSPECTED`; the
    epoch at least the largest held; re-key on divergence (AUDIT.md H9);
    the rivals union (AUDIT.md A22); a superset of `ROSTER_eff`'s members
    at the same epoch, and a sixty-fifth member refused (AUDIT.md N7);
    `ceiling_t` and `cert_cap ≤ now + Cap_Lead`, and never within `2^47`
    of `2^48 − 1` (AUDIT.md N3); the founding reserve of 15 entries; a
    REVOKE only when no held REVOKE of the subject by this issuer has a
    `from_t` at or below the new one (AUDIT.md A20); `from_t = maxceil
    (F) + 1` for a lost key and 0 for a stolen one, in the revoke API
    (AUDIT.md H33). Seal no box for a `Revoked` member.
  - Keep the ceremony log of every `Make_Cert` on the founding device,
    and read "the largest cap ever certified" from it. There is no `CERT`
    record kind, and no view of `F` can give this value (AUDIT.md G24).
    Count distinct certified keys against `Signers_Max − 1`; a renewal
    takes no slot, and a test must show that a renewal uses no slot
    (AUDIT.md G20).
  - Enrollment and rotation: the SAS/QR check over `BLAKE2b-256
    ("kome/member" ‖ ns ‖ sign_pk ‖ dh_pk)`, the join hand-off, a member's
    `dh_pk` rotation and the periodic re-keying of members (AUDIT.md N6,
    H25).
  - The generate-only key API (AUDIT.md A30).
- **Round 0 (C8 IBLT) is not built, and no phase owns it.** DESIGN.md §8
  describes it as prose; `Kome.Reconcile` has no wire tag, no
  fetch-by-hash message and no pending-weight rule for it.
- **Typed fields (phase 10)** are specified in DESIGN.md §4 and §10.7
  and not built. T15–T17 are not stated.

### Open decisions

- None. The last one, small-order Ed25519 public keys, is decided as
  "refuse": `Kome.Crypto.Verify` refuses a small-order public key (the
  eight canonical torsion encodings), and `Make_Grant`, `Make_Cert` and
  `Store.Open` refuse one as subject, signer and `root_pk`. The Wycheproof
  small-order keys (tcIds 152-180) are invalid vectors (AUDIT.md H13).

### Missing tests

- **Emit:** There is no Shadowed DEL case (a DEL target at the ceiling over
  a PUT or a DEL by a higher key). There is also no test of H8 detection
  from the device's own DEL. The mutant `Own => X.K = K_Put and ...`
  passes the tests, and only the proof catches it.
- **Records:** No test decodes a PUT frame as DEL. (A test for the opposite
  direction exists.)
