# Decisions

One line of rationale per non-obvious choice, newest last.

## M1 — Convergent core

- **`SYNC_SITE_ID_LEN = 32` from the start** (plan widens 16→32 in M2). Building
  fresh, so adopting the final width immediately avoids a pointless ABI churn;
  in M4 a site_id is the BLAKE2b-256 of a signing public key (32 bytes).
- **Digest = SHA-256 over the sorted full state** (existence counters + every
  field register, including those hidden under a tombstone). Sorting comes free
  from `std::map`, making the digest order-independent; it is the convergence
  oracle, so it must reflect *all* state, not just visible state.
- **Vendored SHA-256** (compact FIPS-180-4 implementation) rather than a crypto
  dependency: the M1 digest needs only a deterministic, collision-resistant
  hash, and this keeps M1 dependency-free. Real crypto (BLAKE2b/Ed25519/X25519)
  arrives with monocypher in M4.
- **In-memory state via `std::map`** keyed by binary `std::string` (NUL-safe).
  Ordered iteration gives deterministic export/digest; full in-RAM working set
  is acceptable for v1 per the plan.
- **Local `set` always wins for its cell** by assigning a freshly ticked HLC
  register directly. A fresh tick is strictly greater than the engine's last
  HLC, and the engine's clock is bumped past any received remote on `apply`, so
  a local write can never be silently older than current state.
- **SQLite is vendored under `third_party/sqlite/`** (moved from `vendor/`) to
  match the plan's target layout. Built now so M2 only adds the storage layer.

## M2 — Durable storage

- **Persistence is a layer *under* M1**: a `ke::Storage` wrapper loads all state
  on open and write-throughs every mutation inside a transaction. The merge
  code in `sync_engine.cpp` is unchanged — it just calls `tx_*` helpers when a
  store is attached. In-memory engines (`sync_engine_create`) pass `store==null`
  and skip all of it.
- **ns/entity/field stored as BLOB** (not TEXT) so binary keys with embedded
  NULs round-trip losslessly.
- **WAL + `synchronous=NORMAL` + `busy_timeout=5000`**: WAL gives crash-atomic
  single-writer durability (committed transactions survive SIGKILL; partial
  ones roll back on reopen), NORMAL is the safe WAL durability/speed point, and
  busy_timeout lets a concurrent connection wait rather than fail.
- **Per-mutation transaction (not batched)**: simplest correct write-through.
  The plan says batch only after a benchmark shows it is needed; tests pass at
  this granularity, so no batching yet.
- **Persisted identity wins on reopen**: `site_id` is stored in `meta` on first
  open; later opens load it and ignore the passed-in id. A replica's identity is
  a property of its file.
- **Schema guard**: `meta.schema_version` is checked on open; an
  unknown/newer version returns `SYNC_ERR_INVALID` and `sync_engine_open`
  yields NULL — no migration, no corruption.

## M3 — Incremental sync (range-based reconciliation)

- **Codec is hand-rolled little-endian + LEB128 varints**, 1-byte format
  version at the head of every record. No struct memcpy, no MessagePack
  dependency — the format is fully specified by codec.cpp and pinned by an
  inline golden vector in reconcile_test.cpp (committed bytes guard against
  endianness/format drift, satisfying T3.2).
- **Combinable fingerprint = SHA256(count_LE || Σ SHA256(record))**, where the
  sum is 256-bit little-endian modular addition. A prefix-sum array over the
  sorted snapshot makes any sub-range's fingerprint an O(1) delta, so splitting
  a range never rehashes siblings.
- **No version vector / oplog.** Range reconciliation finds the set difference
  without peer history, exactly as the plan directs; a VV fast-path is
  explicitly deferred.
- **Protocol modes FP / LEAF / HAVE.** FP recurses (split into 16 buckets);
  LEAF ships a side's full content for a small range; HAVE is the terminal
  reply with the records the peer still lacks. This three-step finish (FP →
  LEAF → HAVE) guarantees termination while exchanging records both ways.
- **Sessions snapshot their own state at begin.** Fingerprints are computed
  over the immutable snapshot; incoming records are applied to the engine (for
  convergence) but do not perturb protocol math. Final state = union of both
  snapshots, which equals the full-state oracle.
- **Self-contained descriptors (explicit lo+hi bounds).** Combined with
  idempotent merge, this makes the protocol converge under reordered and
  duplicated messages (T3.7), tested with a lossy queue-based driver — a
  stronger guarantee than the reliable-channel assumption requires.
- **Tuning: 16 buckets, leaf threshold 2** (reconcile.h). Gives ~log16(n)
  round-trips and a few records per differing leaf.

## M4 — Secure transport, identity, authorization (in progress)

- **Crypto dependency: monocypher 4.0.2** (vendored, BSD-2/CC0, single file under
  `third_party/monocypher/`). Provides X25519, BLAKE2b, ChaCha20-Poly1305 AEAD,
  and EdDSA. The optional SHA-512 Ed25519 module is unneeded: monocypher core
  EdDSA is BLAKE2b-based and self-contained. We do not interoperate with
  external Ed25519, so this is fine; SHA-256 (ours) covers the Noise hash.
- **Identity derived deterministically from a 32-byte seed**: two sub-seeds
  (BLAKE2b of seed||0x01 / ||0x02) yield the EdDSA signing pair and the X25519
  agreement pair. `site_id = BLAKE2b-256(signing pubkey)` per T4.4.
- **T4.2 via primitive KATs**: published vectors for SHA-256, HMAC-SHA256
  (RFC 4231), X25519 (RFC 7748), BLAKE2b (RFC 7693); round-trip + tamper for
  EdDSA and the AEAD. monocypher AEAD is XChaCha20-Poly1305 (24-byte nonce), so
  the channel adapts Noise XX to that cipher rather than RFC8439 ChaChaPoly.
