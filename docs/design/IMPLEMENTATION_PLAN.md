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
| 1 | `Kome.Versions`, `Kome.Headers` (`Header (Kind, Ent, FH, V, Issuer)`; domination with the REVOKE clause, S5), `Kome.Frontier` (per-signer authorization slices, payload tags with `Run` and `Slot`, the admission views `Max_Ceil`, `In_W` and `W_Cap` with `Lemma_Views_Step`, `Expire (F, Hz)`, `Set_Tag`) | §2, §3, §4, §7 | T1, T2', T4', T11 | done. Versions: 11 tests, 13 checks, 0 unproved. Headers: 25 tests, 36 checks, 0 unproved. Frontier: 65 tests, 3,453 checks, 0 unproved |
| 2 | `Kome.Keys` (key and id encoding), `Kome.Crypto` (monocypher binding; `Verify` is the cofactored RFC 8032 predicate of DESIGN.md §2 as a SPARK expression over a private `Raw_Ed25519_Check`, and it refuses small-order public keys; `Hedge`; `Blake2b_512`), `Kome.Records` (canonical encoding, self-certified founding key and signer certificates over the `cid`, hashing, signing, well-formedness; every kind's `h`, `Well_Formed`, `Decode_Verified`, `To_Header`, `Sign` and `Make_*` take the collection context `cid = Cid_Of (root_pk, salt, del_ttl)` first, S1; `Put_Target`/`Del_Target` constructors) | §2 | T13 | done. Keys: 32 tests, 800 checks, 0 unproved. Crypto: 72 tests, 51 checks, 0 unproved (spec only; the bodies are `SPARK_Mode Off`). Records: 190 tests, 2,137 checks, 0 unproved |
| 3 | `Kome.Store` (`Store (Log_Cap)`; the log HEADER, then APPLY and SEQ entries, S15; tags `(Off, Len)` in the frontier slots and `Read_Frame`, no index, S14; `Put_Frame` with automatic expiry at `hz(F)` (`Put_Done`, `Applied_H`, Lean `applyH`); `Seq_Self` from the log, S16; `Digest_Auth`/`Digest_Data` kept by run and slot diffs, S21; `Compact` in row order with retagging, `SEQ (seq_self)` and `Busy` while `Pinned`; `Pin`/`Unpin`; `Open_From_Log` in trusted mode with `Valid_Length` and `Replayed_Prefix`; `Compact_Due`, `Log_Fits`), `Kome.Frames` (the opaque predicate `Frame_Is (Frame, Cid, X)`, so that the store's tag lemmas do not unfold the record parsers) | §7 | T11, T18 | done. Store: 50 tests, 3,049 checks, 0 unproved. Frames: 9 tests, 13 checks, 0 unproved |
| 4 | `Kome.Emit` (`Choose` without h, chase, the one lower bound `maxceil − Cap_Lead`, `seq_self` per collection, SHADOWED, SEQ_EXHAUSTED, CLAMPED) | §5 | T8, T9, T13 | done. 90 tests, 380 checks, 0 unproved |
| 4 | `Kome.Write` (the write path: `Write` = Choose, Make, Sign under `Cid (S)` and `Store.Put_Frame` in one call, S16, with the S17 outcomes; `Receive` with the apply-side CLONE_SUSPECTED; `Clone_View`, AUDIT.md H18) | §5, §7 | T8 (through `Kome.Emit`) | done. 25 tests, 108 checks, 0 unproved |
| 5 | `Kome.Views` (`cell`, `exists`, `deleted_at`, `root_void`, `W_eff`, `revoked_at`, `void`, `revoked`, `far`, `ROSTER_eff` and `Roster_Max` by the roster key `(gen, h, signer, ceiling_t)`, `contested`, `quarantined`, `skew`) | §3, §6 | T5, T12 | done. 160 tests, 1,207 checks, 0 unproved |
| 6 | `Kome.Accumulator` (4096-bit homomorphic sum), `Kome.Digest` (fingerprint with eight BLAKE2b-512 chunks per element, S20; D15 prefix sums) | §8 | T6 | done. Accumulator: 30 tests, 736 checks, 0 unproved. Digest: 134 tests, 959 checks, 0 unproved |
| 7 | `Kome.Reconcile` (no OPEN, S11: `Start (Sess, As, Cid, Peer_DH)` and the `Prologue`; HELLO with the credential check in `Receive`; `Admit` takes the two digest states and has `Gate_Open` as `Pre`; `Receive` and `Next_Phase` evaluate the gate on every call, S9; entity-major element keys, S18; RANGE with `k + 1` bounds, ELEMENTS/HAVE with `lo`, `hi` and frame-only items, ROOT, tiling replies, S19; `Snapshot_Of (F, T, S)` by source index over one frame table, built only when the digests differ, with Post `Frontier_Digest`; `Seal` builds the D15 `Prefix` table, and `Fingerprint_Of` reads a range from it; the obligation FIFO) | §8 | T7 (open) | done. 63 tests, 3,504 checks, 0 unproved |
| 8 | `Kome.Epochs` (the hedged per-gen key `Key_For_Gen`, `Eph_SK_Of`, `Box_PK_Of`, `Box_Nonce`, synthetic-nonce boxes `Box_Key`/`Unbox_Key`, `Bundle_Key_Of`; S4), `Kome.Guard` (the REVOKE-aware gate, `Admits = Gate ∧ ¬ Quarantined`, no state), `Kome.Roster` (`Build` by construction, certification, recovery, honest-issuer rules) | §6 | T14 (paper) | Epochs done: 56 tests, 152 checks, 0 unproved. Guard done: 15 tests, 63 checks, 0 unproved. `Kome.Roster` not started |
| 9 | Transports (Noise XK with per-collection static keys, sealed bundles), the storage binding, C ABI | §7, §8, §10.6 | — | not started |
| 10 | Typed fields (C10) | §4, §10.7 | T15–T17 (not stated) | when an application needs them |

## Known gaps

No package has an unproved check. In this section, a gap is one of these:

- A property that is tested or reviewed, but not proved.
- A duty of a layer that is not built yet.
- An open decision.
- A missing test.

### Tested, not proved

- **Store: replay completeness (T18, D9).** gnatprove proves that
  `Open_From_Log` opens a log that holds just a well-formed HEADER, and
  T18-prefix: when `Valid_Length > 0`, the result is the `Valid` replay of
  exactly that prefix (`Replayed_Prefix`), and on OK `Valid_Length − 1 =
  Input'Last`. It does not prove that replay accepts every log that a
  store writes and gives back its frontier. A replay that refused every
  log with entries would still meet the contract. Lean proves T18 over
  sets (`auth_first`). For the implementation, tests check it (the reopen
  scenarios in `test_store.adb`, before and after `Compact`). Replay runs
  in trusted mode (`Trusted_Frame`); the proof does not use that
  assumption, and the test main checks it on each log that it reopens.
- **Store: the copy order of `Compact`.** The Post (`Retagged`,
  `Compact_Layout`) states the HEADER bytes, that every record's APPLY
  ends before the final `SEQ (seq_self)`, and `Count + 1` entries; `Valid`
  gives that each tag holds its record's frame. That the APPLYs are
  contiguous and in row order (`Ord`) is tested only (the old
  byte-for-byte clause), and so is the fact that a compacted log never
  gets `Log_Full` (the held frames are disjoint parts of the old log; the
  check makes it a refusal).
- **Write: its own frame check.** `Kome.Crypto` does not state
  `Verify (Sign (M))` (A1), so `Write` verifies its own signed frame at
  run time and gives `Malformed` if the check fails. With a key from
  `Key_Pair` the check never fails: `test_write.adb` checks that every
  written frame verifies; the `Malformed` branch is not reached in a test.
- **Headers and Views: the `AUTH_FULL` arrival-order case for `maxceil`.**
  A refused roster does not count in `maxceil`, so two replicas that
  refuse different records of one over-quota signer can hold different
  ceilings (DESIGN.md §7, §8). The fix is a reserved `CEIL (s)` cell per
  slot outside the slice (AUDIT.md H12). It is deferred; the design
  documents the case instead.
- **Digest: the D15 call bound.** The Post of `Range_Sum` proves the cost
  formula (at most 64 Adds and 1 Sub). But only a review of the body shows
  that the out counts are equal to the calls that the body makes. An
  Accumulator call counter would close this gap. But a ghost counter makes
  `Add` stateful, so this is a design decision.
- **Reconcile** (the "Tested, not proved" list in `kome-reconcile.ads`):
  - T7 (termination and convergence; also open in Lean).
  - `Decode` accepts every RANGE and every ELEMENTS/HAVE that carries
    items (a proof shows that it accepts every ROOT and every confirm).
  - The bytes of an encoded RANGE after its `k`, and the items of an
    encoded ELEMENTS/HAVE (the Posts state the head; a test checks the
    round trip).
  - Split balance (child counts `⌊n/16⌋` or `⌈n/16⌉`) and the cuts on
    multiples of 64 for a window of at least 1 024 elements, and so the
    `log₁₆` round bound and the `O(n log n)` fingerprint work.
  - The honest-session derivations behind `Msg_Budget`, `Range_Budget`,
    `Ship_Budget` and the sufficient `Oblig_Cap`.
  - The session-wide statements "every accepted message was accepted
    while `Gate_Open` held at each call" and "Complete implies one tiling
    answer for each obligation" (inductions over the per-call Posts of
    `Admit`, `Receive` and `Next_Phase`).
- **Crypto: assumed Posts.** The bodies are `SPARK_Mode Off`, so their
  Posts are assumptions: among them `Hedge` (keyed BLAKE2b-256 under the
  signing seed) and `Blake2b_512`, which has no Post (its known answers
  come through `vectors/digest.txt`). `Verify` is a SPARK expression, so
  its Post is proved; the assumed part of it is the private
  `Raw_Ed25519_Check` (no Post), and with it two binding axioms of the
  same kind, `Lemma_Blake2b_Congruent` and `Lemma_X25519_Congruent`
  (AUDIT.md A25). A test under `-gnata` checks each axiom. Known answers
  check the rest: RFC 8032 §7.1 and a Wycheproof subset
  (`vectors/crypto.txt`), and the hedge lines of the same file.
- **Proved but not executed under `-gnata`.** gnatprove proves these
  `Assertion_Policy (... => Ignore)` regions, but the test mains do not run
  them. If the tests ran them, each call would cost quadratic time or
  worse (`spark/CONVENTIONS.md`):
  - `kome-accumulator.adb`: four limb-loop regions (`Assert` and
    `Loop_Invariant` in `Lemma_Add_Chain`, `Lemma_Sub_Chain`,
    `Lemma_Value_Bounds`, `Lemma_Limbs_Bytes`).
  - `kome-digest.adb`: four prefix-sum and state regions (`Loop_Invariant`,
    `Assert` and `Ghost` in `Digest_Of`, `State_Of`, `Build_Prefix`, and
    also `Pre` and `Post` in `Range_Sum`).
  - `kome-frontier.adb`: `Pre => Ignore` around `Lemma_Item`,
    `Lemma_Distinct_Held` and `Lemma_Tag_Of_P`; `Loop_Invariant` and
    `Assert` in `Lemma_All_Flat`, `Lemma_Classify`, `Lemma_Step_Flat`,
    `Lemma_Step_Tags`, `Lemma_Distinct_Held` and `Lemma_Data_Flat`;
    `Loop_Invariant` in
    `Lemma_Off_Mono`, `Find_Held`, `Max_Ceil_Impl`, `W_Cap_Impl`,
    `Lemma_Retag_Data` and `Lemma_Retag_Flat`.
  - `kome-store.adb`: `Loop_Invariant` in `Lemma_Tags_Kept`,
    `Lemma_Tags_Same`, `Lemma_Tags_Apply`, `Lemma_Tags_Expire`,
    `Lemma_Self_Tags`, `Lemma_Copied_Kept`, `Copy_Frames`,
    `Lemma_Rest_Same`, `Lemma_Hashes_Same`, `Lemma_Offs_Step`,
    `Lemma_Slot_Flat`, `Lemma_Auth_Flat`, `Lemma_Expire_Flat`,
    `Lemma_Seq_Apply`, `Lemma_Seq_Sub`, `Lemma_Applied_H` and
    `Lemma_Digest_Split`; `Loop_Invariant`, `Assert` and `Ghost` in
    `Data_Range_Sum` and `Auth_Range_Sum`.
  - `kome-write.adb`: `Loop_Invariant` in `Lemma_Seq_Base`.
  - `kome-reconcile.adb`: `Loop_Invariant`, `Assert`, `Ghost`, `Pre` and
    `Post` inside `Snapshot_Of` (the insertions would be cubic, because
    `Valid` is pairwise); the Post of `Snapshot_Of` itself executes.

  Building with `-XMode=release` turns every contract check off, not only
  these regions (`spark/kome_spark.gpr`).

### Duties of layers not yet built

The message formats and their checks exist. But the steps that enforce
them belong to callers that are not built yet. So D13 is closed only as
far as its formats and checks go.

- **Transport (phase 9)** (the caller duties listed in `kome-reconcile.ads`):
  - Run Noise XK with the per-collection static key `dh_sk_ns = KDF
    (device secret, ns)`, the responder's static key taken from
    `ROSTER_eff` or the enrollment credential, and
    `Kome.Reconcile.Prologue (Cid)` (`"kome/1" ‖ ns ‖ 01`) as the
    prologue. Refuse a low-order peer static key (DESIGN.md §8; AUDIT.md
    H20, A29).
  - HELLO: `Receive` refuses a credential that is not a roster that lists
    the peer's key, or whose signer is root-voided (AUDIT.md G12, A13).
    Otherwise decode, verify and apply the credential, decode the record
    of `ROSTER_eff`, and call `Admit` when `Gate_Open` holds, with the
    store's `Digest_Auth (S)` and `Digest_Data (S)`. This is also how a
    quarantined replica takes the recovery roster (S11).
  - The gate on every call: pass the decoded record of `ROSTER_eff` of
    the current `F` to every `Receive` and `Next_Phase`; they evaluate
    `Gate_Open` and abort when it fails (S9). While
    `Kome.Views.Quarantined` holds, take no sealed bundle and seal none.
  - The snapshot (S21): when the session enters `Auth`, call
    `Kome.Store.Pin`, fill the frame table from `Read_Frame (S, Tag_Off
    (Tag (F, I)))` in the flat order of `F` (entry `I` the frame of
    `Held (F, I)`), call `Snapshot_Of` and `Seal`, pass the snapshot to
    every later call, and `Unpin` when the session ends, whatever its end.
  - Joining (DESIGN.md §6): open a new store from the hand-off `(root_pk,
    salt, del_ttl, roster frame)`, and while `F` holds no non-root-voided
    roster that lists the device's own `dh_pk`, accept only a credential
    that lists both the peer's key and the device's own, and let no other
    credential change `ROSTER_eff` (AUDIT.md H10).
  - Verify ELEMENTS/HAVE items, pass each item's key, and apply the
    delivered frames in element-key order (the one ordering rule, D14).
    Report `SUSPECT_RELAY` for a peer that delivers a record whose author
    is already void, and report a `NO_SPACE` refusal of a peer-offered
    record as a replica status (DESIGN.md §7, §8).
  - Bundles: derive `bundle_key (F)` with `Kome.Epochs.Bundle_Key_Of`
    from the `k_g` that the device's own entry of `ROSTER_eff` unboxes
    (never a key cached by `gen`). Seal bundles as `ns ‖ nonce ‖ AEAD`
    with `cid ‖ u48 (gen)` in the AD only, padded to fixed buckets, with
    synthetic nonces, closed under admission (each author's GRANTs and the
    largest-ceiling roster first). For a set period after `ROSTER_eff`
    changes, keep the previous key and also send an authorization-only
    bundle under it (DESIGN.md §6, §8; AUDIT.md A9, G11, H17).
  - Durability (AUDIT.md A21, H35): make the log durable to `Log_Length`
    before a session is Complete, before an own frame is sent, before a
    bundle is acknowledged or deleted from a mailbox, before relaying an
    applied record, and before continuing after an authorization record
    (DESIGN.md §8).
  - Rate-limit session openings per peer.
- **Storage binding (phase 9)** (DESIGN.md §7; AUDIT.md G13, H23, H26):
  - Choose the data capacity (`Cap` of `F`) at each open; a smaller one is
    allowed when the log replays at it. `Slice_Max` is a constant, so
    there is no slice to choose.
  - Call `Compact` whenever `Compact_Due (S, F)` holds (more than
    `2 · Count (F) + Compact_Slack` log entries, `Compact_Slack = 64`) and
    no session pins the store; on `Busy`, compact after the session.
    `Put_Frame` never compacts on its own.
  - Append each entry at the `Log_Length (S)` from before the call
    (`pwrite` at that offset; `Put_Frame` returns it as `Off`), so that a
    retry after a write error overwrites and never duplicates. The append
    preserves the prefix.
  - On any write error, discard the in-memory `(S, F)` and run
    `Open_From_Log` again; never serve a record whose entry is not on
    disk.
  - Preallocate `Log_Cap`, chosen with `Kome.Store.Log_Fits (Cap,
    Log_Cap)`; compact and retry on `LOG_FULL`. Declare the store as
    `Store (Log_Cap)`.
  - Memory: a store holds its log and the two digest states; the tags are
    in the frontier's slots. `Compact` takes one more buffer of `Log_Cap +
    1` bytes from the binding and keeps no copy of the log. During
    `Open_From_Log` the input (the file, best mapped) and the store's log
    are both resident.
  - Take an exclusive lock on the log for the life of the open.
  - `fsync` before a record is visible to `Reconcile` or `Emit`
    (the sync point).
  - `Compact (S, F, Buf, Result)` leaves the new log in `Buf`
    (`Buf (0 .. Log_Length (S) - 1)`): write it as the new file, `fsync`
    it, rename it over the old one, `fsync` the directory.
  - On a torn tail, truncate to `Valid_Length` and open again; on a
    corrupt entry, open the prefix before it, report `DEGRADED`, and
    sync. Never skip an entry in the middle. The log's integrity is the
    host's: replay does not verify signatures (S15).
  - These duties are stated against T18: every entry-boundary prefix of a
    log that the store wrote replays OK, and the binding only ever hands
    the store such a prefix.
  - The write path (S16): write with `Kome.Write.Write`; make the log
    durable to `Log_Length` before the frame is sent or put in a bundle
    (A5, A21). Apply every frame from a peer with `Kome.Write.Receive`
    and show `CLONE_SUSPECTED` when its flag or `Kome.Write.Clone_View`
    holds (AUDIT.md H18).
- **`Kome.Roster` (phase 8):**
  - `Build (k_g, cid, signer, gen, members)` computes `eph_sk` and
    `box_pk` and seals the boxes from one secret, then wipes it;
    `Make_Roster` is private to it (AUDIT.md A6, G7). Post: `Box_PK =
    X25519_Public (eph_sk)`. It meets the Pres of what it calls: a `k_g`
    that is not `Zero_Key` (`Box_Key`), and `Sign_Key_OK` of the signer
    (`Make_Roster`).
  - Draw `rnd` for each roster and derive `k_g` with
    `Kome.Epochs.Key_For_Gen`; draw again if it is `Zero_Key`.
  - The founding ceremony: `Make_Cert (root_sk, cid, root_pk,
    Founding_Cap)`, the self-certificate that every founding-key record
    carries.
  - Issue the recovery steps in DESIGN.md §6 order (re-grants, member
    REVOKEs, re-signed revocations, then `REVOKE (R, 0)`, then the
    recovery roster at a `gen` above every held roster), and check the
    result: no revoked `sign_pk`, `ceiling_t > maxceil`, and the recovery
    roster is `Roster_Max` and `ROSTER_eff` (AUDIT.md H8, H16, H30, H32).
  - Enforce the honest-issuer rules (DESIGN.md §10.3): reconcile first;
    `gen = 1 + max` over `gen ≤ 2^47`, else `STOLEN_ROOT_SUSPECTED`; on
    `contested`, a `gen` above every held roster with the confirmed union
    of the members (AUDIT.md A22, S12); a sixty-fifth member refused
    (AUDIT.md N7); `ceiling_t` and `cert_cap ≤ now + Cap_Lead`, and never
    within `2^47` of `2^48 − 1` (AUDIT.md N3); the founding reserve of 15
    entries; `from_t = maxceil (F) + 1` for a lost key and 0 for a stolen
    one, in the revoke API (AUDIT.md H33). Seal no box for a `Revoked`
    member.
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
- **Round 0 (C8 IBLT) is an optional extension** (DESIGN.md §10.8, S23):
  not built, and no phase owns it.
- **Typed fields (phase 10)** are specified in DESIGN.md §4 and §10.7
  and not built. T15–T17 are not stated.

### Open decisions

None is open. These were decided last:

- Small-order Ed25519 public keys are decided as "refuse":
  `Kome.Crypto.Verify` refuses a small-order public key (the eight
  canonical torsion encodings). Decode refuses a small-order key, a
  non-canonical key or the key of the all-zero seed as `root_pk`,
  signer, GRANT subject, REVOKE `sign_pk` or ROSTER member `sign_pk`
  (`Kome.Records.Sign_Key_OK`). `Make_Roster`, `Make_Revoke` and
  `Make_Grant` require `Sign_Key_OK` of the signer (and of the subject,
  for a GRANT or a REVOKE), `Make_Cert` of the signer, `Cert_OK` of
  `root_pk` and the signer, and `Store.Open` of the founding key. The
  Wycheproof small-order keys (tcIds 152-180) are invalid vectors
  (AUDIT.md H13).
- The "no horizon" code `2^48 − 1` and its exception to REQUIREMENTS.md
  H6 are gone: the horizon is a function of `F` and the log has no expiry
  entry (SIMPLIFY.md S7).
- The authorization element key is `tag ‖ 0^17 ‖ signer ‖ h`: the zero
  bytes come before the signer so that both key layouts keep their fields
  at the same places (SIMPLIFY.md, "As built").
- `Snapshot_Of` insertion-sorts the authorization slots, which are kept
  in arrival order; a linear merge would need the frontier to keep its
  slots ordered by signer (DESIGN.md §10.11).

### Missing tests

- **Emit:** There is no Shadowed DEL case (a DEL target at the ceiling over
  a PUT or a DEL by a higher key). There is also no test of H8 detection
  from the device's own DEL. The mutant `Own => X.K = K_Put and ...`
  passes the tests, and only the proof catches it.
- **Records:** No test decodes a PUT frame as DEL. (A test for the opposite
  direction exists.)
- **Views:** `test_views` no longer fills a slice, so it does not test
  `Auth_Full` (that takes 512 records); `test_frontier` fills one slice to
  `Slice_Max`.
