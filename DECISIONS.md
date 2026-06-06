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
