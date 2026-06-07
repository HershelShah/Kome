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
| **M5** | Real connectivity (UDP, STUN, hole punching, relay) | ✅ subset (T5.1–T5.8; IPv6/kernel-NAT need a real network) |
| **M6** | Hardening (fuzz, sanitizers, threading, Python binding) | ✅ done |

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

## Two-node end-to-end demo

A real two-process demo: two nodes, two SQLite files, syncing over UDP through
the full stack (Noise XX encryption → reliability layer → range
reconciliation). Each writes records offline, then they connect and converge.

```bash
cmake -B build && cmake --build build --target node
examples/demo.sh
```

Expected: both nodes print the **same** post-sync digest and each ends up with
all 6 records (its own 3 plus the peer's 3). Because the databases are durable,
reopening one afterward (even from another language) shows the synced data
persisted:

```bash
SYNC_ENGINE_LIB=build/libsync_engine.so PYTHONPATH=bindings/python \
  python3 -c "import sync_engine as se; e=se.Engine(b'\x01'*32, path='a.db'); \
              print(e.get(b'contacts', b'B-0', b'name'))"
```

## Multi-node mesh demo

`examples/meshnode` is a gossip daemon: one UDP socket, multiple peers, a Noise
channel per peer, and a fresh reconciliation cycle every ~300 ms (so newly
learned data propagates onward). `examples/mesh_demo.sh` launches N of them in a
ring where each node talks only to its two neighbours:

```bash
cmake --build build --target meshnode
examples/mesh_demo.sh 8 8      # 8 processes, 8 seconds
```

Each node starts with one local record and ends knowing all N — data travels
multi-hop around the ring across separate processes — and all report a single
identical digest. The in-process `multinode_test` pushes the same anti-entropy
to far larger N (verified to 250 nodes / 125k records) over ring, star, and
random-mesh topologies.

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

## Threading contract

A single `sync_engine` (or `sync_session`) is **not** internally synchronized:
use one engine from one thread at a time, or guard it with your own lock.
Distinct engines are fully independent — the library holds no global mutable
state (validated under ThreadSanitizer in `threading_test`).

## Fuzzing

`tests/fuzz/` has libFuzzer targets for `sync_change_decode`,
`sync_capability_decode`, and the reconciliation message parser. Build them
with a clang that ships the fuzzer runtime:

```bash
cmake -B build-fuzz -DSYNC_FUZZ=ON -DCMAKE_CXX_COMPILER=clang++
cmake --build build-fuzz
./build-fuzz/fuzz_change_decode -runs=1000000
```

`hardening_test` exercises the same parsers with tens of thousands of random
and mutated inputs under AddressSanitizer, so the no-crash property is checked
in CI even without the libFuzzer runtime.

## Python binding

```bash
SYNC_ENGINE_LIB=build/libsync_engine.so python3 -m pytest bindings/python
```

The ctypes wrapper (`bindings/python/sync_engine.py`) mirrors the C ABI; the
smoke test reproduces `examples/example.c` (write → export → apply → read →
digest match).

## Dependencies

Vendored, permissively licensed:
- **SQLite** (public domain) — single-file durable storage (M2).
- **monocypher 4.0.2** (BSD-2 / CC0) — X25519, BLAKE2b, ChaCha20-Poly1305,
  EdDSA for identity, signatures, capabilities, and the Noise channel (M4).
- **GoogleTest** — fetched at build time, tests only.

## License

Engine code: MIT or Apache-2.0 (TBD before 1.0). Spec/docs: CC0/CC-BY.
