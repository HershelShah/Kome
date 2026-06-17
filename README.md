# P2P Replication Engine

A private, distributed, offline-first sync engine that runs over today's
internet. At its heart is a convergent (CRDT) data core; around it, an
incremental sync protocol, an encrypted/authenticated transport, and NAT
traversal — built inside-out, milestone by milestone, each gated on its own
test suite.

**What it's for:** apps where each user owns their data and syncs it directly —
across their own devices and with explicitly-trusted contacts — with **no central
server**, end-to-end encryption, and per-namespace access control. Think
encrypted contacts, notes, inventories, settings, small shared lists.

**What it's not:** a collaborative rich-text/document editor (Google-Docs-style
character-by-character merge) — that's [Yjs](https://github.com/yjs/yjs) /
[Automerge](https://automerge.org) territory. Kome resolves conflicts per field
by last-writer-wins, which is right for *records*, not co-edited prose. The
single dependency is [monocypher](https://monocypher.org) (one vendored file);
storage is a dependency-free append-only log.

This is a ground-up rebuild following [the implementation plan](#milestones).

## Status

| Milestone | What | State |
|-----------|------|-------|
| **M1** | Convergent core (HLC, LWW register, LWW-existence, export/apply, digest) | ✅ done |
| **M2** | Durable storage (append-only log, single file) | ✅ done |
| **M3** | Incremental sync (range-based set reconciliation) | ✅ done |
| **M4** | Secure transport, identity, capabilities (Noise XX) | ✅ done |
| **M5** | Real connectivity (UDP, STUN, hole punching, relay) | ✅ subset (T5.1–T5.8; IPv6/kernel-NAT need a real network) |
| **M6** | Hardening (fuzz, sanitizers, threading, Python binding) | ✅ done |

## Build

```bash
cmake -B build                 # defaults to a Release build
cmake --build build
ctest --test-dir build --output-on-failure
```

With a sanitizer:

```bash
cmake -B build-asan -DSYNC_SANITIZER=address
cmake --build build-asan
ctest --test-dir build-asan
```

## Quickstart (Python)

```python
import sync_engine as se

# Two devices, each with its own identity (a 32-byte seed). `path=` makes the
# engine durable (an append-only log on disk); omit it for in-memory.
phone  = se.Engine(b"\x01" * 32, path="phone.db")
laptop = se.Engine(b"\x02" * 32, path="laptop.db")

# Write locally — offline-first, no server needed.
phone.set(b"contacts", b"alice", b"phone", b"555-1234")
laptop.set(b"contacts", b"bob",   b"email", b"bob@example.com")

# Sync. Shown here in-process; over a network this is the secure
# connect_and_sync path (Noise XX + identity proof + range reconciliation).
phone.replicate_into(laptop)
laptop.replicate_into(phone)

assert phone.get(b"contacts", b"bob", b"email") == b"bob@example.com"
assert phone.digest() == laptop.digest()   # converged to identical state
```

```bash
cmake -B build && cmake --build build --target sync_engine   # builds libsync_engine.so
SYNC_ENGINE_LIB=build/libsync_engine.so PYTHONPATH=bindings/python python3 quickstart.py
```

For a real two-process network demo (UDP + the full secure stack), see
[Two-node end-to-end demo](#two-node-end-to-end-demo) below.

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

A real two-process demo: two nodes, two log-backed databases, syncing over UDP through
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

## Real-network testing

`node`/`meshnode` are localhost demos. For cross-host validation, **`netnode`**
is a deployable node that drives the production path (`connect_and_sync` — Noise
XX + identity proof + capability-scoped reconcile + authenticated reliability)
and, for NATed peers, `ConnectionManager` (rendezvous → direct/hole-punch →
relay fallback), alongside the `relayd`/`rendezvousd` daemons. For mesh-scale
validation across many hosts, **`netmesh`** drives that same secure path to N
peers at once over one socket (the deployable counterpart to localhost-only
`meshnode`); `examples/netmesh_demo.sh` runs a secure ring of them. The runbook
for two real hosts (LAN direct, NAT + relay, hole-punch, reconnection), the
secure mesh at scale, and a single-box network-namespace rig are in
[`docs/REAL_NETWORK_TESTING.md`](docs/REAL_NETWORK_TESTING.md). (IPv6 is not yet
supported — the UDP layer is IPv4-only.)

## Design

- **Convergence is the law.** Every value type's merge is a semilattice join
  (commutative, associative, idempotent). The merge of two replicas does not
  depend on message order or duplication.
  - **Hybrid Logical Clock** orders events causally without trusting wall clocks.
  - **LWW register** per field, resolved by a total order on
    `(hlc.physical, hlc.logical, site_id, value)`.
  - **LWW presence register** per entity for existence/deletion: present/absent
    decided by the latest `(hlc, author)` assertion — so create/delete/re-create
    all converge under the same LWW rule as fields (no counter to saturate).
- **The full-state `export`/`apply` path is the oracle.** Later milestones'
  optimized sync is verified against it; it is never removed.
- **Incremental sync without peer history.** `sync_session_*` reconciles two
  replicas by recursively comparing range fingerprints and exchanging only the
  differing records — O(log n) round-trips, transfer proportional to the
  difference — checked against the full-state oracle. No version vectors.
- **C ABI safety.** No C++ exception crosses the boundary; memory ownership is
  documented per function; the suite is sanitizer-clean.

Non-obvious choices are recorded in [`DECISIONS.md`](DECISIONS.md).

## Transport independence

The sync stack is transport-agnostic: the engine, reconciliation session, Noise
channel, reliability layer, and `connect_and_sync` all work on opaque bytes via
a `send`/`recv` seam, so the library runs over **any** connection — UDP, TCP,
BLE, WebSocket, a pipe. `transport_parity_test` runs the same scenarios over
**UDP, TCP, and WebSocket** (`src/transport/{tcp,ws}.*`) with identical
assertions, TSan- and ASan-clean. The WebSocket layer (RFC 6455 handshake +
masked framing) is browser-compatible — verified by an RFC handshake
known-answer test — so a browser can connect to a node's WS endpoint (and a
WASM build of the engine would make the browser a full node). One boundary: the UDP adapter sends
each message as a datagram (~64 KB cap); large payloads need a stream transport
like TCP (`TransportTcp.LargeMessages` syncs a 256 KB value over TCP).

## Threading contract

A single `sync_engine` (or `sync_session`) is **not** internally synchronized:
use one engine from one thread at a time, or guard it with your own lock.
Distinct engines are fully independent — the library holds no global mutable
state (validated under ThreadSanitizer in `threading_test`).

## Security

The threat model, guarantees, and known limitations are in
[`SECURITY.md`](SECURITY.md): per-record Ed25519 signatures (authenticity is
independent of the transport), an identity-bound Noise XX channel with
capability read/write scoping, an authenticated reliability layer, hardened
relay/rendezvous, and bounded resource use throughout — validated by sanitizers,
fuzzers, and a regression test per fix. Report vulnerabilities privately (see
`SECURITY.md`).

## Fuzzing

`tests/fuzz/` has coverage-guided libFuzzer targets over **every place the
library parses externally-controlled bytes**:

| Target | Surface |
|--------|---------|
| `fuzz_change_decode` | record codec |
| `fuzz_capability_decode` | capability codec |
| `fuzz_session` | reconciliation message parser |
| `fuzz_apply` | decode → signature-verify → merge |
| `fuzz_storage` | on-disk load (corrupt log file) |
| `fuzz_noise` | Noise XX handshake parser |
| `fuzz_stun` | STUN request/response parser |
| `fuzz_reliable` | reliability-layer datagram framing |
| `fuzz_ws` | WebSocket frame parser |
| `fuzz_invite` | invite codec |

```bash
sudo apt-get install -y clang libclang-rt-18-dev    # provides libclang_rt.fuzzer
cmake -B build-fuzz -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
      -DSYNC_FUZZ=ON -DSYNC_BUILD_TESTS=OFF
cmake --build build-fuzz
./build-fuzz/fuzz_change_decode corpus_change/      # runs until stopped
```

`.github/workflows/fuzz.yml` runs **all ten targets in parallel nightly**,
each for the full runner window, with each corpus cached so coverage compounds
night over night. Smoke runs found zero crashes/OOB/leaks/UB. `hardening_test`
is the always-on ASan surrogate for regular per-PR CI (random/mutated inputs
through the same parsers) where the libFuzzer runtime isn't installed.

## Coverage

```bash
sudo apt-get install -y lcov
tools/coverage.sh          # builds with gcov, runs the suite, writes the report
```

Produces `coverage-html/` (browsable) and refreshes [`docs/COVERAGE.md`](docs/COVERAGE.md)
— a per-file table committed to the repo. Current engine-code coverage is
**~94% lines / ~98% functions** (third_party, tests, and GoogleTest excluded).
`.github/workflows/coverage.yml` regenerates it on each push and uploads the
HTML as an artifact. (Coverage already paid off: it flagged dead code and an
untested HMAC branch + missing `sync_strerror` cases, all since fixed.)

## Benchmarks & profiling

```bash
cmake -B build -DCMAKE_BUILD_TYPE=Release -DSYNC_BENCH=ON   # fetches GoogleBenchmark
cmake --build build --target bench
./build/bench                       # microbenchmarks over the hot paths

tools/profile.sh 'BM_ApplyRegister' 3000   # callgrind per-function attribution
```

`bench/bench_main.cpp` covers the crypto primitives, codec, engine ops, and
range reconciliation (with `Range()`+`Complexity()` big-O for the scaling
cases). The committed baseline and the data-driven optimization backlog live in
[`docs/PERF.md`](docs/PERF.md). Headline: signature work (Ed25519
sign/verify) dominates every write and every reconciled record — that's where
the optimization story starts.

## Python binding

```bash
SYNC_ENGINE_LIB=build/libsync_engine.so python3 -m pytest bindings/python
```

The ctypes wrapper (`bindings/python/sync_engine.py`) mirrors the C ABI; the
smoke test reproduces `examples/example.c` (write → export → apply → read →
digest match).

## WebAssembly (browser as a full node)

The engine compiles to WASM so a browser tab is a real replica, driving the
transport-agnostic reconciliation session over its native WebSocket:

```bash
sudo apt-get install -y emscripten
tools/wasm_build.sh                       # -> build-wasm/sync_engine.{js,wasm}
node bindings/wasm/parity.cjs             # same scenarios as UDP/TCP/WS, in WASM

tools/wasm_tests.sh                       # the actual gtest suites, compiled
                                          # to WASM and run under Node via ctest
```

The WASM target isn't checked by a hand-written subset — the **literal**
GoogleTest suites compile to WebAssembly and run under Node, so every
transport-agnostic scenario test passes on WASM exactly as it does on
UDP/TCP/WS. `tools/wasm_tests.sh` configures the build with `emcmake` (which
points ctest at `node`) and runs `convergence`, `reconcile`, `crypto`,
`security`, `relay`, `multinode`, `resilience`, `scenario`, and `defensive` as
`.wasm`. Native-only suites (real sockets, `fork`, threads, linker `--wrap`)
are gated out under `if(NOT EMSCRIPTEN)`; their engine logic is still covered on
WASM through the suites above (e.g. durability via `resilience_test`).

`bindings/wasm/sync_engine.cjs` is the JS binding (mirrors the Python one);
`examples/web/index.html` is an in-page browser demo. A browser node reaches
other nodes via a WebSocket-speaking peer/relay (the native `src/transport/ws.*`
side). Verified in CI by `.github/workflows/wasm.yml`.

## Continuous integration

| Workflow | When | What |
|----------|------|------|
| `ci.yml` | every push / PR | build + full suite across Release/Debug + ASan/UBSan/TSan (`-Werror`) |
| `coverage.yml` | push / PR | lcov report (artifact) + refreshes `docs/COVERAGE.md` |
| `wasm.yml` | push / PR | build WASM + parity battery + the full gtest scenario suites compiled to WASM, in Node |
| `fuzz.yml` | nightly | whole-surface coverage-guided fuzzing, compounding corpora |
| `nightly.yml` | nightly | **everything**: full suite incl. opt-in OOM + multi-process chaos, all sanitizers, N=250 scale, WASM parity, coverage |

So every path — the engine, all transports (UDP/TCP/WS), WASM, the services,
chaos/resilience, and OOM/defensive — is exercised either per-PR or overnight.

## Dependencies

Vendored, permissively licensed:
- (storage is a dependency-free append-only log; SQLite was removed.)
- **monocypher 4.0.2** (BSD-2 / CC0) — X25519, BLAKE2b, ChaCha20-Poly1305,
  EdDSA for identity, signatures, capabilities, and the Noise channel (M4).
- **GoogleTest** — fetched at build time, tests only.

## License

Engine code: MIT or Apache-2.0 (TBD before 1.0). Spec/docs: CC0/CC-BY.
