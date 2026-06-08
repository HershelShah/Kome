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

## M4 — Secure transport, identity, authorization

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

- **Per-record EdDSA signatures.** Every change record (existence and
  register) carries `author` (signing pubkey) + `signature` over its canonical
  content; `apply` verifies before touching state (`SYNC_ERR_BADSIG`). Codec
  bumped to v2; the LWW total order is now (hlc, author, value); existence
  merges by (causal_length, author) max. The digest feeds author, not the
  signature (deterministic and redundant).
- **Identity from a 32-byte seed.** `sync_engine_create/open` take a seed that
  derives the EdDSA + X25519 keypair; `sync_engine_identity` returns the signing
  pubkey, `sync_engine_site_id` its BLAKE2b-256. The seed is persisted (schema
  v2) so identity survives reopen.
- **Capabilities are single signed statements** (issuer, subject, ns, access,
  expiry, sig); chains are reconstructed by graph search from the namespace
  root at authorize time, narrowing access per hop. Enforcement is opt-in:
  a namespace is enforced only once a root for it is granted; otherwise open.
  `grant` checks only the signature so expired-but-signed caps can be held but
  fail authorization. Capabilities are in-memory (not yet persisted).
- **Read scoping filters before fingerprinting.** `sync_session_begin_scoped`
  drops records the peer cannot read from the snapshot, so out-of-scope
  namespaces never enter a fingerprint or leak their existence.

- **Noise XX channel adapted to XChaCha20-Poly1305.** `src/noise.{h,cpp}`
  implements Noise_XX (X25519 / SHA-256) using monocypher's XChaCha20-Poly1305
  AEAD instead of RFC 8439 ChaChaPoly, so it is not wire-compatible with
  standard Noise (recorded as a deliberate trade for the single-dependency
  invariant). It yields a mutually authenticated, forward-secret channel that
  the M3 session runs inside (T4.1, T4.3). HKDF/HMAC-SHA256 are built on our
  SHA-256; ephemeral keys come from /dev/urandom.
- **Channel authenticates the X25519 static, not yet the EdDSA identity.** Both
  derive from one seed, so for honest peers they correspond; binding the DH
  static to the signing identity (a signed proof over the handshake hash) is a
  follow-up. Read-scoping currently trusts the caller-supplied peer pubkey.

## M5 — Real connectivity (in-container subset)

- **Pump-style reliability layer (stop-and-wait).** `transport/reliable.{h,cpp}`
  turns a lossy/reordering/duplicating datagram link into a reliable ordered
  stream with seq/ack/retransmit. Stop-and-wait suffices because the
  reconciliation protocol already keeps one message in flight; no callbacks
  (matches the engine's pump style).
- **UDP transport is non-blocking BSD sockets** (`transport/udp.{h,cpp}`),
  IPv4. STUN (`transport/stun.{h,cpp}`) is a minimal RFC 5389 Binding
  client + server helpers (XOR-MAPPED-ADDRESS), tested against a local server.
- **Relay is a blind, in-process store-and-forward core** (`transport/relay.
  {h,cpp}`): forwards opaque blobs by destination pubkey, queues for offline
  peers, and has no key material or decrypt path (privacy invariant by
  construction). A network service would wrap this core.
- **NAT traversal is verified with a userspace NAT simulator** (the plan allows
  a simulator in place of Linux netns, which this sandbox lacks: no
  `ip`/`iptables`). It models full-cone vs symmetric mapping + inbound
  filtering and a STUN-reflexive lookup, so full-cone peers punch through
  (T5.3) while symmetric peers fail and fall back to the relay (T5.4).
- **Environment limits.** T5.9 (IPv6 preference) is not runnable here — this
  container cannot bind IPv6 (`::1` fails). Kernel-level NAT (netns) hole
  punching isn't runnable either; the simulator covers the traversal logic.
  These need a real multi-network host to exercise end to end.

## Post-M6 — Security follow-ups

- **Channel bound to the EdDSA identity.** After the Noise handshake each side
  signs the unique final transcript hash with its signing key and sends
  `signing_pubkey || signature` (`NoiseChannel::make/verify_identity_proof`).
  A valid proof shows the signing-key holder ran *this* handshake with *this*
  X25519 static — closing the earlier gap where the channel only authenticated
  the DH static. It can't be replayed across sessions (the transcript hash
  differs) or by a MITM (each leg has a different hash). Read-scoped sessions
  can now feed the *bound* peer pubkey instead of a claimed one.
- **Capabilities are persisted.** A `capability` table (added `IF NOT EXISTS`,
  so v2 files stay compatible — no schema bump) stores granted caps as wire
  blobs; `sync_engine_grant` write-throughs and `load` re-adds them
  (re-verifying each signature). Enforcement now survives reopen. Internal
  `cap_encode`/`cap_decode` are shared by the public ABI and storage.

- **Capabilities are exchanged during sync.** Each reconciliation message now
  carries a capability section (delegations the sender holds), sent once per
  session; the receiver ingests them before applying records, so an authorized
  peer's records are accepted without any prior out-of-band `grant`. Safety: a
  **root is never trusted over the wire** (`cap_ingest_delegations` skips roots
  and re-verifies signatures) — authorization always roots chains at a
  locally-established owner, so a peer cannot inject a fake owner for a
  namespace you own. Ingested delegations are in-memory only (not persisted);
  gossip re-propagates them. Duplicate caps are de-duplicated by signature.

## M6 — Hardening & productionization

- **Fuzzing is dual-track.** Real libFuzzer targets live in `tests/fuzz/`
  (built with `-DSYNC_FUZZ=ON` on a clang with the fuzzer runtime). Because this
  environment lacks that runtime, `hardening_test` runs the same parser entry
  points (`sync_change_decode`, `sync_capability_decode`, `sync_session_step`)
  over ~30k random and mutated-valid inputs under ASan — the no-crash/no-OOB
  property is enforced in CI regardless.
- **Threading contract: caller-serialized, no shared global state.** The engine
  has no internal mutex; the value is that distinct engines never interfere.
  `threading_test` drives 8 independent engine pairs concurrently and is
  TSan-clean, validating the no-global-state invariant.
- **Version negotiation** is checked both on the wire (unknown/old codec
  `format_version` → `SYNC_ERR_INVALID`) and on disk (T2.4 schema guard).
- **Python binding** is a thin ctypes wrapper over a new `libsync_engine.so`
  shared target. The smoke test mirrors `example.c`. Memory safety of the
  underlying C is covered by the ASan suite; running CPython itself under ASan
  needs an `LD_PRELOAD` of the runtime (environment-specific) so is not wired
  into CI.
- **T6.1 sanitizers/Valgrind.** The full 9-suite test set passes under ASan and
  UBSan with zero errors; Valgrind reports zero leaks on the example and the
  deterministic convergence tests (the randomized 300-trial tests are
  leak-covered by ASan's LeakSanitizer, which is far faster).

## Resilience scenarios (real-life operational tests)

- **resilience_test** exercises combined failure/recovery situations, not just
  the unit-level primitives: a network partition that diverges with a
  conflicting edit then heals (deterministic LWW winner, all non-conflicting
  edits survive); a node that drops offline — missing peers' edits and making
  its own — then rejoins and catches up both ways; a durable node that crashes,
  restarts from its file with no data loss, and rejoins; and 40 rounds of
  random churn (nodes independently up/down + writing) that converges with
  every record present on every node (no data loss). All in-process and
  deterministic.

## Multi-process chaos + connection self-healing

- **meshnode survives peer restarts.** When a peer is SIGKILL'd and comes back,
  its Noise channel and reliability state reset but the survivor's don't, which
  would deadlock the edge. Each peer connection now tracks last-progress
  (a delivered message or a valid ack, reported by `ReliableLink::on_datagram`);
  after `kResetMs` (2s) with no progress it tears down and re-handshakes. Acks
  count as progress, so healthy idle connections (initiator's periodic FP gets
  acked) are never reset, while a silent/restarted peer is detected on both the
  initiator and responder side.
- **A node announces its record once, not per restart.** Re-writing identical
  data on every restart only bumped its HLC (churn that delays digest
  convergence); meshnode now writes its self-record only on a fresh DB.
- **tests/chaos_test.sh**: launches N real `meshnode` processes in a ring,
  SIGKILLs + restarts random nodes for a chaos window, then settles and
  verifies (via the Python binding) that every durable DB reopens cleanly,
  holds every node's record (no data loss), and all converge to one digest.
  Wired into ctest behind `-DSYNC_CHAOS=ON` (slow/timing-heavy; off by default).

## Fuzzing — real coverage-guided run

- **libFuzzer requires the compiler-rt fuzzer runtime** (`libclang_rt.fuzzer`),
  which is shipped by `libclang-rt-18-dev`, not by clang alone. With it
  installed, `-DSYNC_FUZZ=ON` (clang) builds the three targets and a budget run
  executed ~34M inputs through `sync_change_decode` / `sync_capability_decode`
  and reached 857 edges in the reconciliation message parser (`fuzz_session`)
  with zero crashes/OOB/leaks/UB. `.github/workflows/fuzz.yml` runs this nightly
  (installs the runtime, caches corpora, uploads any crash artifacts).
- `hardening_test` remains the always-on surrogate for regular CI (random +
  mutated inputs under ASan) where the fuzzer runtime isn't installed.

## Fuzzing — whole-surface, overnight, compounding corpus

- **Eight targets cover every untrusted-input boundary**, not just the codecs:
  record decode, capability decode, reconciliation message parser, decode+apply
  (signature verify + merge), on-disk storage load (corrupt SQLite), Noise XX
  handshake parser, STUN parser, and reliability-layer framing.
- **No token budget for the nightly run.** `.github/workflows/fuzz.yml` runs
  each target on its own runner in parallel for the full window (default 5h,
  the 6h runner cap leaving margin) and caches each corpus so coverage
  accumulates night over night — real, growing coverage rather than a fixed
  budget. Crashing inputs are uploaded as artifacts (and become regression
  seeds).
- Smoke runs of all eight (15-30s each here) executed tens of millions of
  inputs total with zero findings.

## M5 doables — services, invites, connection manager (§4/§7 too)

- **LICENSE/§7**: MIT for engine code, CC0 for docs, vendored deps keep theirs.
- **Logging/§4**: per-engine `sync_engine_set_logger` (off by default); messages
  are generic (apply-rejection reasons) and never include values/keys/namespaces.
- **Invites**: `sync_invite_encode/decode` carry peer pubkey + rendezvous address
  + optional capability (no public DHT).
- **Relay/rendezvous daemons**: the blind relay and a rendezvous registry now
  have UDP request/reply protocols and standalone daemons (`relayd`,
  `rendezvousd`); loopback tests cover store-and-forward and register/lookup.
- **Connection manager**: `connect_and_sync` runs Noise + reliability + reconcile
  over a pluggable `PeerTransport` (Direct UDP or Relay), and `ConnectionManager`
  tries direct then falls back to relay. For a *one-shot* sync, "done" means
  **quiesced** (handshake complete, session started, reliable link drained, no
  activity) — not "produced an empty reply", which would hang the side that
  sends the terminal records (its last output is non-empty and the settled peer
  stops pumping it). On a reliable link a lull only occurs once the exchange is
  complete, so this can't settle mid-protocol.
- **Still environment-bound**: T5.9 IPv6, real kernel-NAT hole punching, and a
  true cross-network run need a real multi-host setup; the components above are
  validated on localhost.

## Transport independence (TCP parity)

- **The sync stack is transport-agnostic.** Engine, reconcile session, Noise
  channel, reliability layer, and `connect_and_sync` operate on opaque bytes via
  the `PeerTransport` (`send`/`recv`) seam. UDP is one adapter; TCP is another.
- **`src/transport/tcp.{h,cpp}`** adds a loopback-TCP stream with length-prefix
  framing + reassembly (the one TCP-specific bit: a stream isn't message-
  delimited). It presents the same datagram-shaped interface, so the existing
  stack runs over it unchanged. `transport_parity_test` runs six scenarios
  (basic converge, conflict, delete-vs-edit, binary value, many entities,
  empty-vs-full) over **both UDP and TCP** with identical assertions —
  TSan- and ASan-clean — proving every transport-agnostic path works over TCP.
- **Known boundary the exercise surfaced:** the UDP adapter sends each reconcile
  message as a single datagram, so it is capped at the ~64 KB UDP limit. A large
  value or a big empty-vs-full `HAVE` batch exceeds that and only works over a
  stream transport (TCP). `TransportTcp.LargeMessages` syncs a 256 KB value +
  1500 records over TCP to demonstrate this. Lifting the UDP cap would require
  message fragmentation in the reliability layer (not built; TCP is the answer
  for large payloads). Over a reliable transport `ReliableLink` is redundant but
  harmless (no loss ⇒ no retransmits), which the parity tests also confirm.

## WebSocket transport (browser-facing)

- **`src/transport/ws.{h,cpp}`** implements RFC 6455: the HTTP Upgrade
  handshake (`Sec-WebSocket-Accept = base64(SHA1(key + GUID))`, with a small
  internal SHA-1 + base64), and binary framing with client-masking /
  server-unmasking, fragmentation reassembly, and ping/close control frames.
  Both server and client sides are implemented so nodes can talk WS to each
  other and a browser can connect to a node's WS endpoint.
- **Browser compatibility is proven without a browser** by `WebSocket.
  AcceptKeyVector` (the RFC 6455 example key → accept), plus the full parity
  suite running all six scenarios over WS (`"ws"` in the `TEST_P` matrix) with
  real masking, TSan- and ASan-clean.
- **For a browser to be a full *node*** (not just connect), the engine would be
  compiled to WASM and driven over the browser's native WebSocket — the C++ WS
  transport here is for native nodes and for a relay/server that speaks WS to
  such browser nodes. A WASM build is the natural next step for in-browser
  replicas.

## WebAssembly build (browser as a full node)

- **`tools/wasm_build.sh`** compiles the engine core (no transport/sockets) to
  `build-wasm/sync_engine.{js,wasm}` with Emscripten, exporting the public C
  ABI. The browser does I/O with its native `WebSocket` and drives the
  transport-agnostic reconciliation **session** through the exported ABI, so a
  browser tab is a real replica — not just a client.
- `.c` deps (sqlite, monocypher) are compiled with `emcc` (C); `em++` would
  treat `.c` as C++. sqlite is built `SQLITE_THREADSAFE=0` (single-threaded
  WASM); in-memory engines don't touch it, and durable storage in-browser
  (IDBFS/OPFS) is a later step.
- **`bindings/wasm/sync_engine.cjs`** mirrors the Python binding over the WASM
  heap; **`bindings/wasm/parity.cjs`** runs in Node (identical to a browser for
  the compute) and verifies two engines converge via the session + a
  conflict resolves — wired into `.github/workflows/wasm.yml`. `examples/web/`
  is an in-page browser demo with the WebSocket pump sketched.
- Node 22 exposes a global `fetch`, which trips Emscripten 3.1.6 into the web
  load path; the binding passes `wasmBinary` explicitly to avoid it.

## WASM parity (storage + capabilities)

- WASM is at **full engine parity**, not just in-memory sync: `bindings/wasm/
  parity.cjs` runs the six transport scenarios *plus* durable storage
  (reopen-identity and two-durable-engine convergence over SQLite) and
  capability enforcement (authorized writer accepted via gossiped cap, stranger
  rejected) — covering M1-M4 in WASM.
- The build uses `-sWASM_BIGINT` (capability expiry is `uint64_t`; the only i64
  in the ABI). Storage runs on Emscripten's in-memory MEMFS; a browser would
  mount **IDBFS/OPFS** for persistence across page reloads — the engine/SQLite
  logic is identical, only the FS backing differs.
- Intentionally **not** in WASM: the native socket transports (UDP/TCP/WS),
  STUN, and the relay/rendezvous daemons — a browser uses its own WebSocket and
  reaches those as native server/relay peers, so they aren't a WASM concern.

## WASM runs the actual gtest suites (not a hand-written subset)

- "All transports pass all the scenarios" is taken literally: the **real**
  GoogleTest binaries compile to WebAssembly and run under Node, so the WASM
  target passes the same scenario suites as the native UDP/TCP/WS builds rather
  than a parallel battery (`bindings/wasm/parity.cjs` stays as the binding-level
  smoke test). `tools/wasm_tests.sh` drives it: `emcmake cmake` sets
  `CMAKE_CROSSCOMPILING_EMULATOR=node`, so `ctest` runs each `<test>.js`.
- Built for WASM (pure in-process compute): `convergence`, `reconcile`,
  `crypto`, `security`, `relay`, `multinode`, `resilience`, `scenario`,
  `defensive`. Gated out under `if(NOT EMSCRIPTEN)`: `storage` (fork),
  `network`/`connection`/`transport_parity`/`service` (real sockets/threads),
  `hardening` (fork), `threading` (pthreads), `oom` (linker `--wrap`), and the
  multi-process chaos test. Their engine logic is still exercised on WASM by the
  built suites (durability via `resilience_test`, transport semantics via the
  reconciliation session in `multinode`/`scenario`), so no scenario goes
  unverified on the WASM target.
- Three Emscripten-specific build details, all isolated to `if(EMSCRIPTEN)` so
  the native build is untouched:
  - `-fstack-protector-strong` is dropped (Emscripten's libc has no
    `__stack_chk_guard`).
  - The link flags target Node: `-sENVIRONMENT=node -sNODERAWFS=1`
    (real FS for the durability tests' temp DBs), `-sWASM_BIGINT`,
    `-sEXIT_RUNTIME=1` (process exits with gtest's code so ctest sees
    pass/fail), `-sALLOW_MEMORY_GROWTH`/roomy `TOTAL_STACK`/`INITIAL_MEMORY`
    for the larger in-process multinode runs, and `-sWASM_ASYNC_COMPILATION=0`
    so `main()` runs (and flushes output) during load.
  - A `--pre-js` (`tools/wasm_node_prejs.js`) hides Node 22's global `fetch`,
    which this toolchain's loader otherwise tries to use on a bare `.wasm`
    filesystem path (same root cause as the binding's `wasmBinary` workaround).
  - **`main()` plumbing** (`tests/wasm_gtest_main.cpp`): Emscripten emits the
    `callMain` that runs the program only when it sees `main()` among its
    *direct* link inputs — a `main()` inside the `gtest_main` archive is
    invisible, so the binary would load and exit 0 having run nothing. And this
    version wires `callMain` to the `main`/`__main_void` symbol (`int
    main(void)`), not `__main_argc_argv` (`int main(int, char**)`). So we
    compile our own no-arg `main()` directly into each WASM test and link plain
    `gtest`; the native build still uses upstream `gtest_main`.

## Code style: .editorconfig + advisory clang-tidy, no enforced clang-format

- We anchor style with **`.editorconfig`** (indent, charset, LF, final newline,
  80-col) and an **advisory `.clang-tidy`** (bug-finding + safe modernization;
  not a CI gate). We deliberately do **not** enforce `clang-format`: the
  hand-tuned layout — aligned `switch` returns, aligned trailing assignments,
  and compact one-line guard blocks (`if (!ok) { rollback(); return false; }`)
  — reads better than any `clang-format` config can reproduce, and forcing one
  would churn ~200 lines per core file while degrading readability. New code
  should match the surrounding style by hand.
- clang-tidy mutes a few checks that fight deliberate choices at the C ABI
  boundary (C arrays and C-style casts on the `extern "C"` surface, byte<->char
  `reinterpret_cast`, magic-number literals).

## Defensive hardening (audit pass)

- `tcp.cpp` now fails `TcpListener::open` if `setsockopt(SO_REUSEADDR)` errors
  (was ignored); `stun.cpp` zero-initializes the `in_addr` and tolerates a bad
  `inet_pton` instead of reading uninitialized memory; `connect_and_sync` bails
  cleanly if `sync_session_begin` returns null (OOM) rather than driving a null
  session. None changed observable behavior on the happy path.
- Fixed-length crypto constants (`SYNC_PUBKEY_LEN`/`SYNC_SIG_LEN`) replace bare
  `32`/`64` literals in `capability.cpp` (and the peer-key copy in
  `connection.cpp`), matching the `(long)SYNC_PUBKEY_LEN` idiom already used in
  `codec.cpp`.

## Shared low-level primitives (audit pass)

- **`src/byteorder.h`** is the single home for fixed-width little-endian
  (de)serialization (`put_/store_/read_/get_*u32le/u64le`). It replaces the
  hand-rolled byte loops that had been copied into the codec, the engine's
  digest, the reconciliation fingerprint, and the capability codec. Big-endian
  network framing stays with the transports (different concern, different file).
- **`dup_field` / `free_change_fields`** (codec) own the four malloc'd byte
  fields of a `sync_change`; both `export`/`sync_changes_free` and
  `decode`/`free_decoded` now go through them instead of repeating the
  malloc-copy-or-NULL and four-field-free dance. `dup_field` only ever *sets*
  its `*oom` flag, so a caller can run several dups and test once.
- **`sign_existence`** (engine) factors the identical existence-assertion
  build+sign block that `set` and `delete` each had inline; **`serialize_key`**
  (reconcile) factors the cell-key serialization that `process_desc` built
  twice; **`key_bytes`** (engine.hpp) renders a `PubKey` as a map/set key in one
  place. Pure deduplication — wire formats and digests are byte-identical
  (verified against the unchanged convergence/fuzz oracles and WASM parity).

## Test helper consolidation (audit pass)

- The three durability suites (storage/hardening/resilience) each carried a
  near-identical self-cleaning temp-directory struct; they now share
  **`tests/tempdir.hpp`** (`synctest::TempDir`, prefix-configurable). POSIX-only,
  which is fine — those suites are native-only.
- The trivial `B()` byte-cast and the "spread" `seed_from(uint32_t)` helper were
  copy-pasted into ~11 test files; they now come from `cluster.hpp`
  (`using cluster::B; using cluster::seed_from;`). The "fill" `seed_from(uint8_t)`
  variant (all bytes = v) is a *different* mapping, so those files keep their
  local one — both produce distinct per-seed identities, and the tests only rely
  on distinctness + convergence, so neither choice affects results.
- Added **`EXPECT_SYNC_OK` / `ASSERT_SYNC_OK`** macros (in cluster.hpp) for the
  60+ `EXPECT_EQ(call, SYNC_OK)` sites; adopted in cluster.hpp itself.
- Deliberately left each suite's richer local helpers (per-file `digest`/`put`/
  `populate`/session-pump variants, and the two `baseline_union`s) in place:
  they diverge in small but real ways (ASSERT vs EXPECT, return types, custom
  drive loops), so folding them risked behavior changes for little gain. The
  goal was no-regression dedup, not maximal sharing.

## Transport framing tidy (audit pass)

- The reliability layer and TCP framing now serialize their seq/length prefixes
  through `byteorder.h` (`put_u32le`/`read_u32le`) instead of open-coded byte
  loops — same wire bytes, less duplication.
- Magic recv-buffer/handshake sizes are named: `kRecvChunk` (TCP),
  `kDatagramMax` (UDP), `kMaxHandshakeBytes` (WS).
- `connect_and_sync` factors the repeated "step session -> encrypt -> send onto
  the link" into one `pump()` helper used by both the kickoff and the per-message
  path; relies on `sync_free(nullptr)` being a no-op to drop the `if (o)` guards.
- Deliberately deferred: the WebSocket frame parser's `goto`-based header read
  and a `FileDescriptor` RAII wrapper. Both are localized, tested, and working;
  refactoring them adds risk to the socket path for little gain. STUN's BE
  `put16`/`get16` stay local (STUN-specific, tiny). TSan-clean across
  network/connection/relay/transport_parity.

## Build system tidy (audit pass)

- The engine sources compile once into an **OBJECT library** (`sync_engine_obj`)
  that the STATIC (`sync_engine`) and SHARED (`sync_engine_shared`) libs reuse —
  no double compile, no repeated include/link config. The object library now
  carries sqlite3/monocypher (and pthread/dl) as **PUBLIC** deps, which is
  correct for a static library: consumers must link the transitive deps. That in
  turn made the per-test `target_link_libraries(... monocypher/sqlite3)` and
  `target_include_directories(... third_party/...)` lines redundant — they're
  gone; `sync_add_test` now takes an optional `LIBS` only for non-engine deps
  (Threads::Threads).
- `CMAKE_BUILD_TYPE` defaults to Release for a bare `cmake -B build` (single-
  config generators) so it isn't a surprise unoptimized build.
- `tools/coverage.sh` no longer swallows a failing `ctest` with `|| true`
  (coverage from a red suite is misleading) and uses the same `nproc` fallback
  as the other scripts.
- Deferred: factoring the five CI workflows' shared checkout/configure steps
  into a composite action. It's pure cosmetic dedup with no functional gain, and
  can't be verified locally — left for a CI-side change where it can be tested in
  a PR run.

## Performance measurement (optimization story, chapter 1)

- Benchmarks use **GoogleBenchmark** (fetched via FetchContent like GoogleTest,
  dev-only, behind `-DSYNC_BENCH=ON` so normal builds don't fetch it). Chosen
  over a hand-rolled harness for statistical sampling, `DoNotOptimize`, and
  `Range()`+`Complexity()` big-O sweeps — which matter for an optimization story.
- Profiling is **callgrind** (`tools/profile.sh`), not `perf`: the sandbox/CI
  containers don't grant `perf_event` access, and callgrind counts instructions
  so attribution is deterministic run-to-run.
- Baseline + the prioritized, data-driven optimization backlog live in
  `docs/PERF.md`. Finding: Ed25519 sign/verify (monocypher `fe_mul`/`fe_sq`)
  is >99% of convergence/apply cost; the codec/maps/digest are noise beside it.
  Top lever (next chapter): verify a record's signature only if it would change
  state, so losing/duplicate records cost nothing.

## verify-on-win: authenticate only state-changing records (optimization ch.2)

- `sync_engine_apply` now does the LWW/existence merge comparison *before* the
  EdDSA signature check, and verifies only when the record would be accepted.
  Verification is ~100x everything else (docs/PERF.md), so dropping it for
  records that lose LWW or that we already hold is the single biggest win.
- **Why it's safe.** A dominated record reaches no state — and we look it up
  with `find()` (not `operator[]`), so it inserts no entity and does not even
  advance the HLC clock (a dominated record's HLC is provably <= ours, since our
  current value's HLC is already folded into the clock). A record forged to
  *win* the comparison is still verified and rejected (BADSIG), so no forged data
  is ever accepted. An attacker can still make us spend a verify by sending a
  high-HLC record, but that was already true (we verified everything before).
- **Behavior change:** previously *any* invalid-signature record returned
  SYNC_ERR_BADSIG; now a forged record that would lose returns SYNC_OK (it's
  silently ignored, exactly as a validly-signed loser is). Both halves are
  pinned by `Defensive.VerifyOnlyWhenRecordWouldChangeState`. Convergence,
  capability enforcement, and order-independence are unchanged (the accepted set
  is identical; the clock only ever needed to track records we adopt).

## Cached reconciliation snapshot (optimization ch.3)

- `session_begin` no longer rebuilds the sorted/hashed element set every time.
  The engine caches it in `std::shared_ptr<const ReconSnapshot>`, rebuilt lazily
  only when `state_gen` (bumped on every write/delete/accepted-apply) shows it's
  stale. A session takes a `shared_ptr` to the snapshot at begin, so it observes
  a stable point-in-time view even though records it applies mid-sync bump
  `state_gen` and cause the *next* begin to build a fresh one — the in-flight
  session keeps the old via the refcount (no copy, no dangling).
- `ReconSnapshot`/`Element`/`SortKey` moved out of reconcile.cpp's anonymous
  namespace into named `ke` so the engine can hold a `shared_ptr<const
  ReconSnapshot>` without tripping `-Wsubobject-linkage` under `-Werror`.
- Effect: the gossip steady state (repeated sync without writes) drops from
  O(N log N) to O(1) — `session_begin` 2.5 ms → 15 ns and in-sync converge
  5.2 ms → 1 µs at N=1024 (docs/PERF.md). Write→sync→write is unchanged (one
  rebuild per write). Invalidation pinned by
  `Reconcile.SnapshotCacheInvalidatesOnWrite`; scoped (per-peer read-filtered)
  sessions still build their own snapshot (not cached).

## Parallel batch verification (optimization ch.4)

- Bulk transfer is the one path still irreducibly verify-bound (every new record
  must be verified once; ch.2/ch.3 only removed *avoidable* verifies). True batch
  Ed25519 needs group-op primitives monocypher doesn't expose, and hand-rolling
  EdDSA is a security non-starter — so reconcile's `apply_records` verifies a
  large received batch across worker threads (`std::thread`), then applies the
  valid records serially with `apply_change(..., already_verified=true)`.
- **Correctness/safety:** every record is still signature-checked and the merge
  still decides acceptance, so a forged record is dropped and cannot suppress a
  legitimate record in the same batch (we verify all, then apply only the valid
  — no "pick one candidate per cell" shortcut that a forgery could exploit). The
  parallel region reads only const decoded records and writes per-index results,
  so it is data-race-free (TSan-clean). monocypher verify is pure/stateless.
- **Scope:** engages only at/above 16 records (small gossip-diff batches stay on
  the serial verify-on-win path; thread-spawn would cost more than it saves) and
  is `#ifndef __EMSCRIPTEN__` (WASM is single-threaded → serial). This keeps the
  "one engine, one thread at a time" caller contract: the workers live and join
  within a single `sync_session_step`, touch no engine state, and add no global
  mutable state.
- `sync_engine_apply` is now a thin wrapper over internal
  `ke::apply_change(e, c, already_verified)`; `already_verified=true` skips only
  the EdDSA check (the cheap state-change gate from ch.2 still runs).
- Effect (4 cores): full-transfer convergence ~3.5× faster, scaling with core
  count (docs/PERF.md). all-conflict is unchanged (its batches are ≤2 records,
  below the threshold). Per-record verify cost is unchanged — we just run them
  concurrently.

## Allocation & code-level cleanups (optimization ch.5)

- Profiling the cold snapshot build showed ~55% malloc/free/memset/memcpy: it
  round-tripped through `sync_engine_export` (callocs an N array + four
  `dup_field` mallocs per record, freed right after). `build_snapshot` now
  iterates the engine's `ns`/`fields` maps directly and encodes each element in
  place, borrowing the maps' strings — export array and 4×N field copies/frees
  gone. Output is byte-identical (reconcile/convergence oracle unchanged), and
  reconciliation no longer depends on the public export path.
- `encode_record` reserves its buffer once (no per-append regrowth).
- `add256`/`sub256` operate on four 64-bit limbs instead of 32 bytes, via the
  little-endian byte helpers so they stay endianness-independent (the compiler
  lowers read/store_u64le to a single load/store on LE, a bswap on BE) and
  byte-identical. Avoided `unsigned __int128` (it trips `-Wpedantic`/`-Werror`);
  carry/borrow are detected with the standard `s < a` overflow test.
- Effect: cold `session_begin` ~12% faster at N=4096 and much less allocator
  churn; the cached gossip path (ch.3) is unchanged. Recorded a follow-up in
  docs/PERF.md: the per-element SHA-256 (~35% of the cold build) could move to
  BLAKE2b (~4×), but that shifts the on-wire fingerprint and needs versioning.

## Security S1: bind the live channel to identity + enforce read scoping

- The Noise XX handshake authenticates only the X25519 static key. The EdDSA
  identity-proof machinery (`make/verify_identity_proof`, signing the handshake
  transcript) existed but was only exercised in tests — `connect_and_sync` used
  the **unscoped** `sync_session_begin` and never verified the peer. Result: a
  peer that completed a handshake received *every* namespace, so capability read
  scoping was silently dead on the live path, and the far end's identity was
  unbound.
- `connect_and_sync` now, immediately after the handshake completes, sends its
  signed identity proof as the first encrypted message and requires the peer's
  proof as the first message it receives; a bad/absent proof aborts the sync
  (fail-closed — the session is never created, so it can't settle). The proof is
  bound to the unique transcript, so a relay-MITM can't forward A's proof onto
  its own channel to B. The verified peer signing key then drives
  `sync_session_begin_scoped`, so a peer only receives namespaces it may read.
- Covered by `Connection.ReadScopingEnforcedOverTransport` (an authenticated
  peer with no read delegation gets the open namespace but not the owned one);
  the proof construction/rejection itself is covered by security_test.
- Scope: the library path (`connect_and_sync`). The `meshnode`/`node` *demo*
  binaries hand-roll their own Noise loop and remain demo-only.

## Security S2: re-verify record signatures on storage load

- `Storage::load` trusted entity/field rows because they were on disk — it
  copied `author`/`sig`/`value` straight into engine state with no signature
  check (the capability load already re-verified via `cap_sig_valid`). A
  crafted/swapped/shared DB file could thus inject forged records that bypass
  the signature gate the network path enforces, and those rows were then
  re-emitted into the reconcile snapshot and gossiped as authentic.
- Load now re-verifies every signed row through `record_sig_ok` (rebuild the
  canonical signing bytes, `verify` against the stored author/sig) and drops
  any that fail — existence assertions when `causal_length>0`, every field
  register. `cl==0` entity rows carry no signed assertion (and are never emitted
  as existence elements), so they need no check. Same fail-closed posture as the
  capability load.
- Covered by `Storage.ForgedRowRejectedOnLoad` (a zeroed field sig → field
  dropped but existence intact; a zeroed existence sig → entity not present;
  legit rows survive).

## Security S3: bound network frame sizes

- WebSocket `recv_frame` honored a peer-controlled 64-bit frame length: the
  `hdr+masklen+len` "is it all buffered yet?" check overflowed `size_t`, passed,
  then `std::string payload(ptr, len)` allocated ~2^64 → remote crash/over-read.
  And fragmented-message reassembly (`assembling_ += payload`) was unbounded.
  Both now cap at `kMaxMessageBytes` (64 MiB) and drop the connection on
  violation (rejecting *before* the size math, so it can't overflow).
- TCP `extract` honored a 32-bit length up to 4 GiB, letting one prefix make us
  buffer unbounded bytes; now capped at `kMaxFrameBytes` (64 MiB) → drop.
- 64 MiB is far above any real reconcile message (the LargeMessages test is
  256 KB; the UDP path is a single ~64 KB datagram). Follow-up noted: the WS
  frame parser and `sync_invite_decode` still lack fuzz targets.

## Security S4: DoS-hardening batch

Three contained fixes against remote denial-of-service:

- **Unbounded wire counts.** `decode_message`/`decode_desc` read a varint
  count (caps, descriptors, leaf records) up to 2^63 and `emplace_back` per
  entry, so a few KB of zero-length entries allocated thousands of objects.
  Each entry needs >=1 byte, so the count is now rejected if it exceeds the
  remaining buffer — before any allocation. (We still don't `reserve()` on the
  count, keeping the existing grow-as-bytes-permit guard.)
- **Parallel-verify worker exception.** `change_sig_ok` -> `encode_signing` can
  throw `bad_alloc`; an exception escaping a `std::thread` calls
  `std::terminate`. The worker loop is now wrapped in try/catch (any failure ->
  not-verified, fail-closed), so a large batch under memory pressure can't crash
  the process.
- **Noise receive-nonce desync.** The transport `decrypt` advanced
  `recv_nonce_` before the auth check, so a single forged/corrupt frame
  permanently desynced the channel (every later legit frame then failed). It now
  advances the counter only on a successful decrypt — covered by
  `Security.ForgedFrameDoesNotDesync`.

## Security S5: capability DoS hardening

- `CapStore::authorized` re-scanned every held capability at each chain hop —
  O(N^2) per write once a peer gossips many delegations. It now indexes the
  usable delegations for the namespace by issuer in one pass, so the chain
  search is O(N). Same authorization result (covered by the existing chain/ring
  capability tests + multinode enforced ring).
- `cap_ingest_delegations` now stops adding once the store reaches
  `kMaxIngestedCaps` (4096): a peer can sign unlimited junk delegations from
  throwaway keys, so the gossip path must be bounded. Locally granted caps
  (`sync_engine_grant`) are a trust decision and aren't subject to the cap.
- Documented the `sync_engine_grant` contract (#4): it is the *local* trust API
  and deliberately accepts roots (unlike the wire path, which never does);
  callers must not pipe untrusted/network capabilities into it.

## Security S7: hardening tail

- **Reconcile DoS bounds.** A `sync_session` now counts processed messages and
  gives up cleanly after `kMaxSessionSteps` (so a non-terminating peer can't run
  it forever even without a caller deadline), and per step it stops producing
  reply descriptors once they exceed `~kBuckets * (own element count)` — a legit
  round never reaches that, but a peer flooding whole-range fingerprints can't
  amplify beyond the receiver's own scale (its excess descriptors are dropped).
- **Strict-length record decode.** `apply_records` and the LEAF diff now require
  `decode_record` to consume the *entire* blob; trailing bytes would let a peer
  craft distinct wire records that decode to the same logical record (evading
  dedup, churning the fingerprint).
- **Identity-at-rest hygiene.** The transient seed copy is `secure_wipe`d after
  deriving the keypair; the DB file is `chmod 0600` best-effort. The seed is
  still persisted (reopen re-derives the identity) — the DB *is* this node's
  private key, like an SSH key; FS-level protection / at-rest encryption is the
  embedder's responsibility (documented in load()).
- **random_bytes** now wipes the buffer and returns false on a short read, so a
  partial/weak buffer can't be used as key material.

## Security S8: fuzz coverage for the WS parser + invite codec

- The WebSocket frame parser (where the S3 length-overflow lived) had no fuzz
  target because it was embedded in `WsStream::recv_frame` (socket-coupled,
  stateful). Extracted the frame decode into a pure `ke::ws_parse_frame(buf, len,
  ...)` (returns ready/need-more/error) — `recv_frame` now drives it, and
  `fuzz_ws` exercises it directly. Behavior-preserving (transport_parity green).
- Added `fuzz_invite` for `sync_invite_decode` (parses an untrusted pubkey +
  address string + optional embedded capability), which had no target.
- Both run 200k iterations locally with zero crashes; wired into fuzz.yml's
  nightly matrix (now ten targets) and the README table.

## Security S6a: relay resource caps + return-routability

- The blind relay accepted SENDs from anyone into an unbounded `mailbox_` with
  no expiry, and FETCH delivered the whole queue to the (spoofable) UDP source.
  So a peer could OOM the relay, or use it as a reflection/amplification weapon
  (store a big queue for a key, then FETCH with a spoofed source = victim).
- The mailbox is now bounded: per-destination blob count + byte caps (oldest
  evicted), a global byte budget, a distinct-key cap, and oversized/empty blobs
  dropped. Relay blindness is unchanged (content stays Noise-encrypted).
- FETCH is now a two-step return-routability handshake: the relay answers a
  FETCH with a random nonce sent to the requester's claimed address, and only
  delivers on a follow-up that echoes that nonce from the same endpoint. A
  spoofed-source requester never receives the nonce, so it can't trigger a
  delivery — the only reflected packet is the 16-byte challenge. The pending-
  challenge set is bounded. Covered by `Relay.MemoryCapsBoundQueue` and
  `Relay.FetchChallengeReturnRoutability`.

## Security S6b: rendezvous key-ownership proof

- `REGISTER` recorded any key -> endpoint with no proof of ownership, so an
  attacker could bind a victim's key to an arbitrary endpoint (denial-of-
  discovery; S1's identity proof then blocks actual impersonation, but the
  victim is delisted).
- Registration is now a challenge/response: the server replies to `REGISTER`
  with a random nonce; the client must return a `REGISTER-AUTH` carrying a
  signature of that nonce by the key's signing secret. The server records the
  mapping only if the signature verifies under the registered key AND the nonce
  matches the one it sent to that endpoint — so only the key's owner, at its
  claimed address, can register it. `rendezvous_register` now takes the KeyPair.
- Also fixed the `get_endpoint` `l+2` length-overflow (attacker varint).
- Covered by `Service.RendezvousLoopback` (real keypairs) and
  `Service.RendezvousRejectsForgedRegistration`.

## Security S6c: authenticate the reliability layer

- The reliability framing ([type][seq]) rode *outside* Noise in cleartext and
  was processed before decryption, so a forged DATA (at the live recv seq) or
  ACK (at the live send seq) desynced the link — one injected datagram could
  permanently wedge a connection.
- Frames now carry an optional HMAC-SHA256 tag keyed by `reliability_key()` — a
  symmetric key both peers derive from the shared handshake transcript hash.
  `connect_and_sync` calls `link.enable_mac()` once the handshake completes, so
  the proof exchange and all reconcile traffic are authenticated. The MAC is
  opt-in (`enable_mac`), so the Noise-less drive paths (network/relay tests) are
  unchanged.
- Boundary handling: the handshake messages themselves are unauthenticated
  (Noise authenticates them) since no session key exists yet, and the keying is
  asymmetric (the initiator keys a step before the responder). To avoid wedging
  at the transition, a keyed receiver rejects an unauthenticated frame only when
  it would *change state* (advance recv_seq_ or clear the in-flight send); stale
  plain handshake duplicates are still accepted and re-acked, so the last
  handshake frames settle across the boundary. A forged frame at the live
  sequence is rejected. Covered by `Reliable.MacRejectsForgedFrameOnceKeyed`.

## Real-network testing harness (netnode)

- `node`/`meshnode` are localhost demos that hand-roll the pre-security channel
  (no S1 identity proof, no S6c MAC) and bind 127.0.0.1 — unsuitable for real
  cross-host testing. Added **`examples/netnode.cpp`**, a deployable node on the
  *production* path: `connect_and_sync` (Noise XX + transcript-bound identity
  proof + capability-scoped reconcile + authenticated reliability) for a known
  endpoint (`--peer`), and `ConnectionManager` (rendezvous discovery → direct/
  hole-punch → relay fallback) for NATed peers (`--rendezvous`/`--relay`/
  `--peer-key`). Binds a configurable address.
- Validated on loopback over real UDP: direct converges; managed converges via
  relay fallback; rendezvous register(+S6b proof)/lookup discovers the peer.
  Cross-host / real-NAT / IPv6 can't run in the sandbox.
- `docs/REAL_NETWORK_TESTING.md` is the two-host runbook (per M5 scenario, with
  pass criteria); `tools/netns_real_net_test.sh` is a single-box network-
  namespace rig (real kernel stack; needs a real host with iproute2).
- Flagged honestly: the UDP layer is **IPv4-only** (`AF_INET`), so IPv6 (T5.9)
  needs `AF_INET6` support in `UdpSocket` before it can be validated.
