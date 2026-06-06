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
