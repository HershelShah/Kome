# Data-layer TODO

Tracking the remaining data-part work (CRDT model, storage, encoding/access).
P0 (message chunking) and P1 (LWW-existence + tombstone GC + codec v3) are being
implemented now; this file holds the rest. See `docs/DATA_MODEL.md` and
`docs/STORAGE.md` for the design rationale behind these.

## P2 — Performance (profiling-identified; the machinery already exists)

- **Parallel signature verification on load.** Reopen re-verifies every record
  serially (~6.5 s for ~40k records; verify is 151 µs each). The reconcile path
  already has a parallel batch verifier (`apply_records`, `kParallelVerifyMin` in
  `reconcile.cpp`); point storage load at the same pool to cut startup ~N-cores×.
- **Batched fsync on bulk apply.** A sync that ingests N records does N
  `begin/commit` = N fsyncs (~1 ms each), so bootstrapping from a peer is
  fsync-throttled. Wrap a whole reconcile batch in one storage transaction (one
  staged frame, one fsync). The append-only log makes this trivial. Pre-existing
  (SQLite had per-mutation tx too).

## P3 — Data access / ergonomics

- **Namespace entity-scan read primitive.** List a collection without exporting
  everything — prefix iteration over the sorted map. New public read API.
- **Typed-value convention in bindings.** A 1-byte type tag (bytes / utf8 / int /
  counter) for friendlier Python/WASM APIs; the core stays opaque bytes.
- **Optional PN-counter value type.** For shared quantities/tallies that must sum
  across concurrent offline edits (LWW can't). Per-actor map, O(actors) metadata.
  Add only when the use case needs it. Self-contained new value-kind.

## P4 — Security feature (unlocked by the log format)

- **At-rest encryption.** Whole-file or per-record; straightforward now that we
  own the format (SQLite would have needed SQLCipher). The log holds the identity
  seed in plaintext today (chmod 0600). Likely an XChaCha20-Poly1305 wrapper over
  each frame keyed from a passphrase/OS keystore.

## P4b — Deletion follow-up (design only — protocol rev)

- **Signed per-record `expires_at` (engine-level TTL).** Today ephemeral data
  is app-level: the app stores a TTL field, hides expired records at read
  time, and each member's sweep runs the erase → tombstone → compact recipe
  (`docs/STORAGE.md`). The designed next step is a record-level, author-signed
  `expires_at`: every replica drops the record at the deadline *without* a
  cooperative sweep, and the relay can drop expired envelopes server-side
  (which needs the expiry visible on the envelope — authenticated but outside
  the sealed payload, a deliberate metadata leak to trade off). This is a
  protocol rev — codec/signing-content change plus a relay wire change — NOT
  additive; do not implement until the codec is due a version bump.

## P5 — Backlog / tuning / docs

- **Per-namespace HLC clock domains.** Fixes the documented engine-global-clock
  cross-namespace degradation (a far-future write in one namespace lowers the
  wall-clock quality of conflict resolution in others). Design-level; see
  SECURITY.md.
- **Compaction dead-fraction trigger.** Today's trigger is size-only
  (`file > max(64 KiB, 2× last-compacted)`), so an all-live growing dataset gets
  rewritten more than necessary (amortized O(log n) extra writes). Track a live
  byte estimate and compact on dead-fraction instead. Negligible at personal
  scale.
- **"Collections-as-entities" app-author guidance.** The #1 modeling rule: model
  a collection as entities (one per item), never an array stuffed in one value
  (which loses concurrent edits). Pure docs — add to README/quickstart.
- **Adversarial decoder sweep.** Finish the audit class beyond varints (huge
  length prefixes, deep inputs, OOM). Mostly covered by `fuzz_storage` /
  `fuzz_change_decode`; worth a deliberate pass.
- **ORSWOT existence (held in reserve).** If true add-wins under untrusted or
  high-concurrency writes ever becomes a requirement, replace LWW-existence with
  an observed-remove set with per-actor dots (`docs/DATA_MODEL.md` §4). Not
  needed for the current use case.
