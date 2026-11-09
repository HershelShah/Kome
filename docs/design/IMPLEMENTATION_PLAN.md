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
| 2 | `Kome.Keys` (key and id encoding), `Kome.Crypto` (monocypher binding; `Verify` is the cofactored RFC 8032 predicate of DESIGN.md §2 as a SPARK expression over a private `Raw_Ed25519_Check`, and it refuses small-order public keys), `Kome.Records` (canonical encoding, signer certificates, hashing, signing, well-formedness; `Put_Target`/`Del_Target` constructors) | §2 | T13 | done. Keys: 32 tests, 800 checks, 0 unproved. Crypto: 60 tests, 35 checks, 0 unproved (spec only; the bodies are `SPARK_Mode Off`). Records: 178 tests, 2,569 checks, 0 unproved |
| 3 | `Kome.Store` (HEADER plus an APPLY/APPLY_EXPIRED/EXPIRE journal, index, `Compact` with authorization records first and `Compact_Due`, expiry at `Horizon_At` with the replay clamp, `Open_From_Log` with `Valid_Length` and `Replayed_Prefix`, the counters `Auth_Gen` and `Expire_Mark`, `Horizon_Frozen`) | §7 | T11, T18 | done. 109 tests, 4,511 checks, 0 unproved |
| 4 | `Kome.Emit` (`Choose` without h, chase, `seq_self` per collection, SHADOWED, SEQ_EXHAUSTED) | §5 | T8, T9, T13 | done. 61 tests, 322 checks, 0 unproved |
| 4 | `Kome.Write` (the write path: `Prepare` = Choose, Make, Sign; the binding persists `seq_self`; `Commit` = `Store.Put_Frame`; `Seq_Self_At_Open`, `Open_Seq` with SEQ_CORRUPT; `Receive` with the apply-side CLONE_SUSPECTED, AUDIT.md A10, H18) | §5, §7 | T8 (through `Kome.Emit`) | done. 42 tests, 123 checks, 0 unproved |
| 5 | `Kome.Views` (`cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `void`, `revoked`, `far`, `ROSTER_eff` by `(epoch, gen, h)`, `ROSTER_FORK`, `del_ttl_eff`) | §3, §6 | T5, T12 | done. 141 tests, 1,190 checks, 0 unproved |
| 6 | `Kome.Accumulator` (4096-bit homomorphic sum), `Kome.Digest` (fingerprint, D15 prefix sums) | §8 | T6 | done. Accumulator: 30 tests, 736 checks, 0 unproved. Digest: 134 tests, 959 checks, 0 unproved |
| 7 | `Kome.Reconcile` (OPEN, HELLO, the auth range then the data range. `Start` takes the peer's Noise key and prepares our OPEN, with the root-void set only for a peer that `Lists_Peer` finds in a held roster; `Select_Voids` (Post `Voids_OK`; `Lemma_Voids_Cover`) builds the set; `Receive` answers the initiator's OPEN, checks the HELLO credential and re-evaluates the gate (`Gate_Holds`) under a new `Auth_Gen`; `Admit` has the gate as `Pre`; `Next_Phase` sends the data root. `Snapshot_Of (F)` (Post `Range_Fp = Frontier_Digest`) over two `Frame_Table`s filled with `Add_Frame`; `Seal` builds the D15 `Prefix` table, and `Fingerprint_Of` reads a range from it. The obligation FIFO) | §8 | T7 (open) | done. 142 tests, 2,134 checks, 0 unproved |
| 8 | `Kome.Epochs` (the keyed BLAKE2b-256 chain step, the derived box secret `eph_sk`, synthetic-nonce boxes, fixed segment boundaries, segment links; the bundle key `k_b` is not derived here), `Kome.Guard` (the REVOKE-aware gate and the quarantine flag), `Kome.Roster` (`Build` by construction, certification, segments, recovery, honest-issuer rules) | §6 | T14 (paper) | Epochs done: 72 tests, 227 checks, 0 unproved. Guard done: 18 tests, 26 checks, 0 unproved. `Kome.Roster` not started |
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
- **Store: replay completeness (T18, D9).** gnatprove proves that
  `Open_From_Log` opens a log that holds just a HEADER with the slice of
  the open, and T18-prefix: when `Valid_Length > 0`, the result is the
  Valid replay of exactly that prefix (`Replayed_Prefix`), and on OK
  `Valid_Length − 1 = Input'Last`. It does not prove that replay accepts
  every log that a store writes. A replay that refused every log with
  entries would still meet the contract. Lean proves T18 over sets
  (`auth_first`). For the implementation, tests check it (the reopen
  scenarios in `test_store.adb`, before and after `Compact`).
- **Write: the self check of `Prepare`.** `Kome.Crypto` does not state
  `Verify (Sign (M))` (A1), so `Prepare` verifies its own signed frame at
  run time and gives `Malformed` if the check fails. With a key from
  `Key_Pair` the check never fails: `test_write.adb` checks that every
  Ready frame verifies; the `Malformed` branch is not reached in a test.
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
  - Split balance (child counts `⌊n/16⌋` or `⌈n/16⌉`), and so the
    `log₁₆` round bound and the `O(n log n)` fingerprint work.
  - The honest-session derivations behind `Msg_Budget`, `Range_Budget`,
    `Ship_Budget` and the sufficient `Oblig_Cap`.
  - That the heap sort of `Snapshot_Of` sorts (a final scan checks the
    result, so the Post holds in every case).
  - The session-wide statements "every accepted message was accepted
    while the gate held under `Gate_Gen`" and "Complete implies one full
    reply group for each obligation" (inductions over the per-call Posts
    of `Admit`, `Receive` and `Next_Phase`).
- **Crypto: assumed Posts.** The bodies are `SPARK_Mode Off`, so their
  Posts are assumptions. `Verify` is a SPARK expression, so its Post is
  proved; the assumed part of it is the private `Raw_Ed25519_Check` (no
  Post), and with it two binding axioms of the same kind,
  `Lemma_Blake2b_Congruent` and `Lemma_X25519_Congruent` (AUDIT.md A25).
  A test under `-gnata` checks each axiom. Known answers check the rest:
  RFC 8032 §7.1 and a Wycheproof subset (`vectors/crypto.txt`).
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
  - OPEN: `Start` and `Receive` send our OPEN (the responder only after a
    matching OPEN of the initiator) and build the root-void set with
    `Select_Voids` (one founding REVOKE per root-voided subject, at most
    15 subjects), sent only to a peer that `Lists_Peer` finds in a held
    roster, and `n_rv = 0` otherwise (AUDIT.md H5, A14). The caller fills
    the authorization `Frame_Table` from `Read_Frame`, entry `I` the frame
    of the `I`-th authorization record (the hypothesis of
    `Lemma_Voids_Cover`). Verify and apply the peer's OPEN frames
    (`Is_Founding_Revoke`) before the gate, then `Kome.Guard.Note_Open`
    (the quarantine flag).
  - HELLO: drop the credential and abort, before verification, if `F`
    holds a founding REVOKE of its signer (AUDIT.md G12). Otherwise check
    it (`Roster_Lists_DH`), apply it, `Kome.Guard.Note_Credential`, and
    evaluate the gate (`Kome.Guard.Admits`: the flag and the REVOKE-aware
    gate). Pass the store's current `Auth_Gen` to `Admit`, `Receive` and
    `Next_Phase`, converted from `Kome.Store.Auth_Counter` to the `U64`
    that `Kome.Reconcile` takes; those calls evaluate the gate again when
    it moved past the session's `Gate_Gen` and abort when it fails
    (AUDIT.md H11). While the flag is set, take no sealed bundle and seal
    none.
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
  - Derive the bundle key `k_b = f (k_e, "kome/bundle" ‖ ns)` with
    `Kome.Crypto.Blake2b_256_Keyed`; no SPARK package derives it yet.
    Seal bundles as `ns ‖ nonce ‖ AEAD` with the epoch in the AD only,
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
- **Storage binding (phase 9)** (DESIGN.md §7; AUDIT.md A11, G13, H23,
  H26):
  - Open every store with `Slice_Max` (`Store.Open` does not require
    it; replay refuses a HEADER with another slice), and choose `data_cap`
    at each open; a smaller one is allowed when the log replays at it.
  - Call `Compact` whenever `Compact_Due (S)` holds (more than
    `2 · Entries (S) + Compact_Slack` log entries, `Compact_Slack = 64`).
    `Put_Frame` never compacts on its own. Then replay verifies at most
    `2 · |F| + 64` signatures.
  - Append each entry at the `Log_Length (S)` from before the call
    (`pwrite` at that offset; `Put_Frame` returns it as `Off`), so that a
    retry after a write error overwrites and never duplicates. The append
    preserves the prefix.
  - On any write error, discard the in-memory `(S, F)` and run
    `Open_From_Log` again; never serve a record whose entry is not on
    disk.
  - Preallocate `Log_Cap`, chosen with `Kome.Store.Log_Fits`; compact and
    retry on `LOG_FULL`. Declare the store as
    `Store (Cap, Log_Cap, Bnd_Cap_For (Log_Cap))`: the entry boundaries
    take `Log_Cap / 6` slots (AUDIT.md G15).
  - Memory (AUDIT.md G15): a store holds about `1.7 · Log_Cap` bytes
    (the log, and `Log_Cap / 6` four-byte boundaries) beside its index.
    `Compact` takes one more buffer of `Log_Cap + 1` bytes from the
    binding and keeps no copy of the log. During `Open_From_Log` the
    input (the file, best mapped) and the store's log are both
    resident.
  - Take an exclusive lock on the log for the life of the open.
  - `fsync` before a record is visible to `Reconcile` or `Emit`
    (the sync point).
  - `Compact (S, F, Buf)` leaves the new log in `Buf`
    (`Buf (0 .. Log_Length (S) - 1)`): write it as the new file, `fsync`
    it, rename it over the old one, `fsync` the directory.
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
    `Box_PK = X25519_Public (eph_sk)`. It meets the Pres of what it calls:
    an epoch key that is not `Zero_Key` (`Box_Key`, `Seal_Link`), and
    `Sign_Key_OK` of `root_pk` and the signer (`Make_Roster`).
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

None is open. These two were decided last:

- Small-order Ed25519 public keys are decided as "refuse":
  `Kome.Crypto.Verify` refuses a small-order public key (the eight
  canonical torsion encodings). Decode refuses a small-order key, a
  non-canonical key or the key of the all-zero seed as `root_pk`,
  signer, GRANT subject, REVOKE `sign_pk` or ROSTER member `sign_pk`
  (`Kome.Records.Sign_Key_OK`). `Make_Roster`, `Make_Revoke` and
  `Make_Grant` require `Sign_Key_OK` of `root_pk` and the signer (and of
  the subject, for a GRANT or a REVOKE), `Make_Cert` and `Cert_OK` of
  the signer, and `Store.Open` of the founding key. The Wycheproof small-order keys
  (tcIds 152-180) are invalid vectors (AUDIT.md H13).
- The `EXPIRE_NONE` op of AUDIT.md H24 is declined. The `EXPIRE` entry
  encodes "no horizon" as `2^48 − 1`, a reserved value. The code decodes
  to "no horizon", which is below every bound of the replay clamp, so an
  `EXPIRE` that reads as it can only lower the horizon (DESIGN.md §7).
  This departs from REQUIREMENTS.md H6 ("no sentinel values").

### Missing tests

- **Emit:** There is no Shadowed DEL case (a DEL target at the ceiling over
  a PUT or a DEL by a higher key). There is also no test of H8 detection
  from the device's own DEL. The mutant `Own => X.K = K_Put and ...`
  passes the tests, and only the proof catches it.
- **Records:** No test decodes a PUT frame as DEL. (A test for the opposite
  direction exists.)
