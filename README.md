# P2P Replication Engine

A private, distributed, offline-first sync engine that runs over today's
internet. At its heart is a convergent (CRDT) data core; around it, an
incremental sync protocol, an encrypted/authenticated transport, and NAT
traversal — built inside-out, milestone by milestone, each gated on its own
test suite.

This is a ground-up rebuild following [the implementation plan](#milestones).

## Status

| Milestone | What | State |
|-----------|------|-------|
| **M1** | Convergent core (HLC, LWW register, causal-length set, export/apply, digest) | ✅ done |
| **M2** | Durable storage (SQLite, single file) | ✅ done |
| **M3** | Incremental sync (range-based set reconciliation) | ✅ done |
| **M4** | Secure transport, identity, capabilities (Noise XX) | ✅ done |
| M5 | Real connectivity (STUN, hole punching, relay) | next |
| M6 | Hardening (fuzz, sanitizers, bindings) | — |

## Build

```bash
cmake -B build
cmake --build build
ctest --test-dir build --output-on-failure
```

With a sanitizer:

```bash
cmake -B build-asan -DSYNC_SANITIZER=address
cmake --build build-asan
ctest --test-dir build-asan
```

## Usage (C, M1)

```c
#include "sync_engine.h"

uint8_t site_id[SYNC_SITE_ID_LEN] = { /* this replica's identity */ };
sync_engine *e = sync_engine_create(site_id);

sync_engine_set(e, (const uint8_t*)"people", 6,
                   (const uint8_t*)"alice", 5,
                   (const uint8_t*)"name", 4,
                   (const uint8_t*)"Alice", 5);

/* Full-state replication baseline (the oracle the optimized sync is checked
 * against): export records, apply them into a peer. */
sync_change *recs; size_t n;
sync_engine_export(e, &recs, &n);
/* ... ship recs to a peer, who calls sync_engine_apply on each ... */
sync_changes_free(recs, n);

sync_engine_destroy(e);
```

See `examples/example.c` for a complete two-replica convergence demo.

## Design

- **Convergence is the law.** Every value type's merge is a semilattice join
  (commutative, associative, idempotent). The merge of two replicas does not
  depend on message order or duplication.
  - **Hybrid Logical Clock** orders events causally without trusting wall clocks.
  - **LWW register** per field, resolved by a total order on
    `(hlc.physical, hlc.logical, site_id, value)`.
  - **Causal-length set** per entity for existence/deletion: odd = present,
    merge takes the max — so create/delete/re-create all converge.
- **The full-state `export`/`apply` path is the oracle.** Later milestones'
  optimized sync is verified against it; it is never removed.
- **Incremental sync without peer history.** `sync_session_*` reconciles two
  replicas by recursively comparing range fingerprints and exchanging only the
  differing records — O(log n) round-trips, transfer proportional to the
  difference — checked against the full-state oracle. No version vectors.
- **C ABI safety.** No C++ exception crosses the boundary; memory ownership is
  documented per function; the suite is sanitizer-clean.

Non-obvious choices are recorded in [`DECISIONS.md`](DECISIONS.md).

## Dependencies

Vendored, permissively licensed:
- **SQLite** (public domain) — single-file durable storage (M2).
- **monocypher 4.0.2** (BSD-2 / CC0) — X25519, BLAKE2b, ChaCha20-Poly1305,
  EdDSA for identity, signatures, capabilities, and the Noise channel (M4).
- **GoogleTest** — fetched at build time, tests only.

## License

Engine code: MIT or Apache-2.0 (TBD before 1.0). Spec/docs: CC0/CC-BY.
