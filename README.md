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
| **M7** | Packaging (pip wheel, npm/WASM, single-file amalgamation) | ✅ engineering done — all three channels landed; first publish pending registry setup ([docs/PACKAGING.md](docs/PACKAGING.md)) |

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
import kome as se

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
pip install .          # builds a self-contained wheel from this checkout
                       # (`pip install kome-sync` once 0.1.0 is on PyPI)
python3 quickstart.py  # = the snippet above, saved as quickstart.py
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
  python3 -c "import kome as se; e=se.Engine(b'\x01'*32, path='a.db'); \
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

`netnode`/`netmesh` are for validating the wire path itself; **`komed`**
(`services/komed`) is the generic, config-driven, always-on peer daemon meant
to actually be deployed — no app semantics, just an identity, a durable
database, and a `key=value` config (`db=`, `peer=<pubkey>@host:port`,
`rendezvous=`, `relay=`, `interval_ms=`, `cap_file=` for delegated read-scoped
serving) that it syncs on a cadence over the same production secure path,
alongside the `relayd`/`rendezvousd` daemons. It answers inbound connections
from any peer that dials it — even with zero configured `peer=` lines, the way
`relayd`/`rendezvousd` passively answer requests — so a bare `komed` pointed at
a shared database is "the always-on member of your circles" any application
can stand up standalone. `komed --identity` prints its pubkey for wiring into
peers' configs, `--once` runs a single cron-friendly sync cycle, and
`tests/komed_test.sh` is the end-to-end check (two `komed`s, direct UDP, full
convergence, clean `SIGTERM` shutdown).

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

## Python package

```bash
pip install .            # self-contained wheel from this checkout; import kome
```

The binding (`bindings/python/kome/`) is a ctypes wrapper mirroring the C ABI —
no `Python.h`, so wheels are `py3-none-<platform>`: one wheel per platform
covers every Python ≥ 3.8. scikit-build-core drives the same CMakeLists and
bundles `libsync_engine` inside the package (`kome/_lib/`), so installing needs
no toolchain knowledge and importing needs no environment variables. PyPI
distribution name: **`kome-sync`** (`kome` is squatted); import name: `kome`.
Windows wheels are deferred — storage/transport are POSIX (see
[docs/PACKAGING.md](docs/PACKAGING.md)).

`.github/workflows/wheels.yml` builds Linux (manylinux2014 x86_64/aarch64) and
macOS (x86_64/arm64) wheels + the sdist on every push, then installs each into
a clean venv and runs the binding tests from outside the repo — the gate tests
the packaged artifact, not the build tree. `release.yml` re-gates and publishes
to PyPI (Trusted Publishing) on version tags.

Dev flow without installing (the ctypes layer falls back to the build tree):

```bash
SYNC_ENGINE_LIB=build/libsync_engine.so PYTHONPATH=bindings/python \
  python3 -m pytest bindings/python
```

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

The JS binding ships as the npm package **`kome-sync`** (`bindings/wasm/`;
built by `tools/npm_build.sh`): CJS + ESM entries with TypeScript
declarations, a `kome-sync/embedded` single-file variant (wasm
base64-embedded — no asset pipeline, ~33% larger), and bundler support via
the `browser` condition (vite/webpack 5 emit the `.wasm` asset
automatically). `.github/workflows/npm.yml` gates the packed tarball on the
parity battery, ESM/embedded smokes, a strict `tsc` check, and a vite build
loaded in headless Chromium; `release.yml` publishes with npm provenance on
version tags. The repo dev flow is unchanged (`sync_engine.cjs` over
`build-wasm/`; the API core is shared in `binding.cjs`).
`examples/web/index.html` is an in-page browser demo. A browser node reaches
other nodes via a WebSocket-speaking peer/relay (the native `src/transport/ws.*`
side). Verified in CI by `.github/workflows/wasm.yml`. `bindings/wasm-runtime/`
(`kome-sync-runtime`, a sibling npm package) turns the binding's manual
session pump into a running gossip loop — a browser/Node `SyncClient` and a
Node `SyncHub` — over that same one-frame-per-message WebSocket wire; see its
own README for usage, the wire protocol, and its trust-model caveat.

## Single-file amalgamation

SQLite-style two-file distribution: the whole engine as `kome.h` (the public
C API — `sync_engine.h` under the distribution name) + `kome.cpp` (every TU
concatenated, monocypher included). No build system, no dependencies — any
project with a C++17 compiler links it, including plain-C codebases calling
through the pure-C header:

```bash
python3 tools/amalgamate.py -o dist    # or download kome-<v>-amalgamation.zip
                                       # from a GitHub Release
c++ -std=c++17 -O2 -c dist/kome.cpp    # one object file
cc  -std=c99 -I dist -c your_app.c     # your C program against kome.h
c++ your_app.o kome.o -o your_app
```

`-DKOME_NO_TRANSPORT` yields the portable core (engine, storage, crypto,
reconciliation, Noise, capabilities — the same subset the WASM build proves
out); the default includes the POSIX transports. The release zip also carries
a `sync_engine.h` alias (identical to `kome.h`, same include guard), so code
written against the repo header compiles unchanged. The amalgamation is
generated, never committed: `.github/workflows/amalgamation.yml` regenerates
it on every push and runs the **entire** gtest suite against it (gcc + clang,
`-Werror`), plus the two-file drop-in gate — `examples/example.c` compiled as
C99, linked against `kome.o`, demo converging — and portable-core/WASM
compile variants.

## Continuous integration

| Workflow | When | What |
|----------|------|------|
| `ci.yml` | every push / PR | build + full suite across Release/Debug + ASan/UBSan/TSan (`-Werror`) |
| `coverage.yml` | push / PR | lcov report (artifact) + refreshes `docs/COVERAGE.md` |
| `wasm.yml` | push / PR | build WASM + parity battery + the full gtest scenario suites compiled to WASM, in Node |
| `wheels.yml` | push / PR | Linux/macOS wheels + sdist; each installed into a clean venv and tested as the packaged artifact |
| `npm.yml` | push / PR | npm tarball installed into a fresh project: parity battery, ESM/embedded smokes, strict tsc, vite + headless-Chromium browser gate |
| `amalgamation.yml` | push / PR | regenerate kome.h/kome.cpp; full suite against it (gcc + clang, -Werror) + C99 drop-in demo + portable-core/WASM compiles |
| `release.yml` | `v*` tag | re-gate all channels via the same workflows; publish PyPI (Trusted Publishing) + npm (provenance) + amalgamation zip on the GitHub Release |
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

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). Every commit must be signed off
under the [Developer Certificate of Origin](https://developercertificate.org/)
(`git commit -s`); CI enforces this on pull requests.

## License

Engine code: [MIT](LICENSE). Spec/docs: CC0/CC-BY.
