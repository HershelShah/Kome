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
  only when `content_gen` (bumped on every write/delete/accepted-apply; at the
  time of this decision a single `state_gen`, since split in two — see the
  Gen-split entry below) shows it's stale. A session takes a `shared_ptr` to
  the snapshot at begin, so it observes a stable point-in-time view even though
  records it applies mid-sync bump `content_gen` and cause the *next* begin to
  build a fresh one — the in-flight session keeps the old via the refcount (no
  copy, no dangling).
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
  Both now cap at `kMaxWsMessageBytes` (64 MiB) and drop the connection on
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

## Backlog: IPv6 (deferred), and the powers-of-two scaling sweep

- **IPv6 (T5.9) is explicitly backlogged**, not abandoned. The work is bounded:
  add `AF_INET6`/`sockaddr_in6` to `UdpSocket` (dual-stack or a parallel path),
  extend `netnode`'s `ip:port` parser for `[v6]:port`, and validate T5.9 on a
  v6-capable network. Deferred because it's a feature gap that doesn't block the
  IPv4 real-network validation (M5 T5.1–T5.8) that comes first.
- **Multi-node scaling is now in the automated suite**, not just the runbook.
  Added a parameterized sweep `PowersOfTwo/MultiNodeScale` in
  `tests/multinode_test.cpp` at **N = 2, 4, 8, 16, 32, 64** — one independently
  reported case per network size. Each N drives convergence across all three
  topologies (ring = worst-case diameter, star = hub fan-out, random connected
  mesh) plus the **enforced-namespace** case, where every node holds the root
  and its own write delegation and authorization for every peer's `n*n` records
  must arrive purely via capabilities gossiped during sync (asserted present).
  Runs natively and under WASM/Node (same scenarios both targets). The inline
  star/mesh edge builders were factored into `star_edges`/`mesh_edges` helpers
  shared with the existing `StarTopology`/`RandomMesh` cases. N=64 dominates
  runtime (~26 s native / ~12 s WASM); kept in-suite since the sweep is the
  multi-node acceptance gate.

## Wire-cost measurement: bytes/rounds vs. divergence (and a relay-cap bug)

Instrumented the convergence pump to report `rounds`, `wire_bytes`, `max_msg`,
`relay_cap_frac` (= max_msg / 64 KiB S6a cap), and `amplification`
(wire_bytes / raw-diff payload). Measured (Release, 4 vCPU):

- **In-sync poll is constant**: 37 bytes, 1 round, *flat from N=64 to N=16384*.
  The fingerprint short-circuit works — a no-op sync costs a fixed 37 B no
  matter the dataset. Round-trips to converge stay bounded (~3 RTT / 6 messages)
  for *any* divergence, so latency is O(1)-ish, not O(N) or O(log N).
- **Bandwidth tracks the diff, not the dataset** (the headline claim, confirmed):
  at fixed N=4096, wire grows with D (changed records): D=1 → 3.1 KB, D=16 →
  27 KB, D=256 → 274 KB, D=4096 → 2.0 MB. A 4096-record node syncing one change
  sends ~3 KB, not 1 MB. Amplification falls from ~24× at D=1 (fixed
  fingerprint-tree descent overhead dominates a tiny diff) to ~3.9× at D=N.
- **BUG — reconcile messages are not chunked, so `max_msg` blows past the
  64 KiB relay blob cap (S6a `kMaxBlobBytes`).** A single HAVE/transfer message
  packs *all* differing records, growing unboundedly: max_msg hits 64 KiB at
  **~90 changed records per sync** and reaches ~1.1 MB at D=4096 (17× the cap).
  Consequence: **relay-routed sync silently fails once two peers diverge by more
  than ~90 records**, while direct sync still works — and the relay path is
  exactly the NAT-fallback the real-network testing targets. It also forces
  massive UDP fragmentation (a ~1 MB message is 700+ fragments under a 1400 B
  MTU; one lost fragment loses the datagram, and the reliability layer is
  stop-and-wait). Full-transfer max_msg ≈ wire_bytes confirms it's essentially
  one giant message.
- **Fix direction**: cap a single reconcile/transfer message below the relay
  blob limit (and ideally near the UDP MTU), emitting the diff as a bounded,
  pipelined sequence of messages instead of one blob. No data model change —
  a session-layer framing change. Tracked as the top pre-ship item; it gates
  the relay fallback path at any non-trivial scale.

## Data-model audit (loop): findings

- **Iteration 1 — HLC far-future / clock poisoning.** No engine bug: clock.receive
  runs only after signature + capability checks, so a rejected far-future record
  can't advance the engine clock. Locked in by
  `Security.UnauthorizedFutureWriteDoesNotPoisonClock`. The authorized far-future
  case (physical pinned, honest writes recover via logical) is an intentional,
  pre-existing tradeoff (`Convergence.HlcReceiveMonotonicity`). Engine-global
  clock blast radius documented in SECURITY.md.
- **Iteration 2 — non-canonical varints (FIXED).** `get_varint` accepted
  non-minimal encodings, so a peer could craft non-canonical wire records that
  apply to the right logical state but mismatch the raw-bytes fingerprint
  (`reconcile.cpp:453`) → forced re-transmission (bandwidth amplification). Made
  `get_varint` strictly minimal (+ reject 10th-byte overflow bits). Regression:
  `Reconcile.VarintsAreCanonical`.
- **Iteration 3 — causal-length saturation (documented, design-level).** A peer
  can pin entity presence with `causal_length≈UINT64_MAX`; honest deletes (`+=1`)
  wrap and lose the merge, so the entity is permanently undeletable and
  resurrects on sync. No-auth in open namespaces; WRITE-delegate-vs-owner in
  enforced ones. Convergence-safe rejection isn't possible (clock/history-free
  max-counter), so documented in SECURITY.md with the design-level fix
  (history-validated existence / OR-Set tags). Confirmed empirically.

## Storage: SQLite → append-only log

- **Replaced the SQLite persistence layer with a dependency-free append-only
  log** (`storage.cpp`). SQLite was used only as a durable KV store (full state
  in RAM; load-on-open + write-through), never as a query engine — so a ~250K-LOC
  (9.3 MB vendored) SQL B-tree was overkill in the trusted path. The log is a
  single file of length-prefixed, SHA-checksummed frames; one mutation is one
  fsync'd frame; a crash leaves at most a torn trailing frame, detected by its
  checksum and truncated on reopen. Replay merges each record by the engine's own
  LWW/existence rule, so it is order-independent and idempotent — a duplicated or
  partially-written tail cannot corrupt state (the same property that makes a CRDT
  converge makes log replay safe).
- **Why:** smallest possible TCB for a security engine, smaller WASM/mobile
  binary, one encoding for disk and wire, and straightforward at-rest encryption.
  It also sets up compaction-as-GC (rewrite the log as one record per live cell),
  which pairs with the proposed LWW-existence model (see `docs/DATA_MODEL.md`).
- The `Storage` class API is unchanged, so the engine/capability code did not
  change; only `storage.{h,cpp}` and the two format-level storage tests
  (forged-sig rejection, version guard — now corrupt the log + recompute frame
  checksums). Builds native + WASM (Emscripten's POSIX layer covers
  open/fsync/ftruncate); 16/16 native + WASM suites green. **Compaction is the
  immediate follow-up** (the log currently grows until rewritten).

## Storage: log compaction (Bitcask "merge")

- **Compaction completes the append-only-log store.** Without it the log grew
  with the number of writes; `Storage::compact` rewrites it to one record per
  live cell (a meta frame + one frame per entity + a capability frame), bounding
  the file to O(state) and keeping reopen O(state). Triggered from the write
  path (`maybe_compact`) on a doubling threshold — compact when the log exceeds
  max(64 KiB, 2× its size at the last compaction) — giving amortized O(1) write
  amplification; also runs once at load if an existing log is >2× its live image.
- **Atomicity:** compaction writes a full image to `<path>.tmp`, fsyncs it,
  `rename()`s over the log (atomic), reopens, and fsyncs the directory. A crash
  during compaction leaves the original log untouched (the rename is the commit
  point), so it can never lose data. Serializing the in-RAM state reproduces the
  exact current state, so the digest is unchanged across a compaction.
- **Identity seed:** the store now retains the 32-byte seed (wiped in its
  destructor) so it can re-persist identity on each rewrite. The file already
  holds the seed in plaintext (chmod 0600), so this is not new exposure.
- This is also where tombstone GC plugs in once the LWW-existence model lands
  (drop tombstones past their TTL during the rewrite). Tested by
  `Storage.CompactionBoundsLog` (5000 writes to one cell → file stays <256 KiB,
  digest preserved across reopen); native + WASM + ASan clean, full suite green.

## P1 landed: LWW-existence + tombstone GC

- **LWW-existence implemented** (codec v3, storage v2): entity presence is an LWW
  register (present:bool by latest (hlc, author)), replacing the causal-length
  counter. Removes the saturation attack and unifies the model to one LWW rule.
  Format break (signatures cover the new content); pre-1.0, no migration.
- **Tombstone GC** runs during compaction (`gc_tombstones`): an asserted absence
  older than `kTombstoneTtlMs` (30 days) is dropped with its hidden fields,
  bounding delete-heavy growth. Live entities, unasserted shells, and fresh
  tombstones are kept. Best-effort by design — a peer offline past the horizon
  may resurrect a delete (the Earthstar bound). Tested by
  `Storage.TombstoneGcOnCompaction`.
- All oracle tests (convergence/scenario/multinode) pass unchanged: the merge is
  still SEC, order-independent, idempotent. Native 16/16 + WASM + ASan green.

## T3: at-rest encryption

- **`sync_engine_open_encrypted(path, seed, key)`** seals the append-only log at
  rest. Each frame is `[len][nonce:24][ciphertext][mac:16]` under
  XChaCha20-Poly1305 with a random per-frame nonce; the AEAD tag both
  authenticates and detects torn writes, so it replaces the SHA checksum. The
  encrypted file uses a distinct magic (`KOMEENC1`) plus a header **key-check**
  (a fixed plaintext sealed under the key) so a wrong key fails the open up front
  rather than being mistaken for a torn frame and truncating data. Compaction
  re-seals; the digest is unchanged across encrypt/reopen/compact.
- The engine takes a raw 32-byte key, not a passphrase — key derivation
  (Argon2/scrypt) or an OS keystore is the embedder's choice, keeping the core
  minimal. The key is wiped from memory on destroy. Plaintext logs are unchanged
  (`sync_engine_open`); the two modes are mutually exclusive (mode mismatch fails
  cleanly). Tested by `Storage.AtRestEncryption` (round-trip, wrong-key/mode
  rejection, no plaintext leak, encrypted compaction). Native 16/16 + WASM + ASan.

## Secure mesh daemon (netmesh) + SecurePeerSession

- The secure per-peer state machine (Noise XX handshake → transcript-bound
  identity proof → capability-scoped reconcile) was extracted out of
  `connect_and_sync`'s blocking loop into a reusable, non-blocking
  **`SecurePeerSession`** (consumes/emits opaque datagrams; the caller routes
  them). `connect_and_sync` is now a thin blocking driver over one such session
  with `gossip_interval_ms == 0` (one cycle, then quiesce) — behaviour and ABI
  unchanged, verified by the existing `connection`/`network`/`transport_parity`/
  `relay` suites. One knob (`gossip_interval_ms > 0`) turns it into a repeating
  gossip session (initiator re-snapshots and re-kicks each interval; responder
  re-snapshots per cycle), which is what multi-hop propagation needs.
- **`netmesh`** (examples/) is the deployable, real-network counterpart to the
  localhost-only `meshnode`: one UDP socket, N peers, a `SecurePeerSession` each,
  inbound demuxed by sender address. Unlike `meshnode` (raw `NoiseChannel`, no
  identity proof, no read-scoping) it drives the **production secure path** at
  mesh scale. Initiator per edge is decided by identity-key compare (strict order
  → exactly one initiator per edge); a silence detector re-handshakes a restarted
  peer (`reset()`). Time-bounded report mode and a long-running `--daemon` mode.
- **Scope:** flat reachable substrate only (Tailscale/VMs/LAN) — demux-by-sender
  assumes no NAT rewriting between peers. NAT traversal (hole-punch/relay) stays
  validated pairwise by `netnode`; folding relay into the mesh would need inbound
  demux (relay fetch carries no sender tag) and is deferred.
- Tested in-process (no sockets → CI + WASM) by `securemesh_test`: ring +
  full-mesh convergence, read-scoping enforced, no-sync-without-authentication,
  and restart/`reset()` re-convergence. End-to-end over real sockets by
  `examples/netmesh_demo.sh` (secure ring) + `tools/netmesh_verify.sh`. Native
  17/17 + ASan green; `connect_and_sync` path TSan-clean.

## M7 — Packaging (phase 1: pip wheel)

- **Distribution name `kome-sync`, import name `kome`.** `kome` on PyPI is
  squatted (an empty 0.1.0, no description). The import name carries the
  brand; distribution/import names are independent in Python packaging, and
  the only collision — co-installing the squatter's package — isn't worth
  engineering around.
- **License stays MIT.** The plan's "decide MIT vs dual" prerequisite
  dissolved on contact with `LICENSE`, which already declares MIT (engine) +
  CC0 (docs); the README's "TBD before 1.0" line was stale and is now fixed.
- **ctypes + `py3-none-<platform>` wheels via scikit-build-core.** No
  `Python.h` anywhere means no per-interpreter ABI: one wheel per platform
  covers every Python ≥ 3.8, and the existing CMakeLists stays the only build
  system (`build.targets = [sync_engine_shared]`, install component `python`
  → `kome/_lib/` inside the wheel).
- **`SYNC_ENGINE_LIB` beats the bundled library and fails loudly if wrong.**
  Previously a nonexistent path in the env var was silently skipped; an
  explicit override that is silently ignored is worse than an error. Wheel
  users never set it; dev flows want it to win.
- **The wheel gate copies tests to a temp dir before running them.** pytest
  prepends a test file's directory to `sys.path`, so testing in-place would
  import the repo's `bindings/python/kome` instead of the installed wheel —
  exactly the "works in my build tree" failure the gate exists to catch.
- **Windows wheels deferred, stated in README.** `storage.cpp` (POSIX
  open/fsync) and `src/transport/*` (BSD sockets) need a port; that's engine
  work (an M8 candidate), not packaging, and pretending otherwise would gate
  the whole channel on it.

## M7 — Packaging (phase 2: npm/WASM)

- **`kome-sync` on npm too** — `kome` is squatted on both registries, so the
  fallback becomes a feature: one package name everywhere (PyPI, npm).
- **One API implementation, five entries.** The Binding class lives in
  `binding.cjs`; index.cjs/index.mjs, embedded.cjs/embedded.mjs, and the repo
  dev shim (`sync_engine.cjs` over build-wasm/) all wrap it. Shared emcc
  source list/ABI/flags moved to `tools/wasm_flags.sh`, sourced by both
  wasm_build.sh and npm_build.sh — same no-drift move as the reusable CI
  workflows.
- **Node always runs the CJS engine build, even via the ESM entry.** The
  distro emscripten (3.1.6)'s EXPORT_ES6 output references `__dirname` on its
  Node path — a ReferenceError in ES modules. The ES6 builds serve
  browsers/bundlers only, where that path is dead code; index.mjs branches on
  the environment. Static `new URL("./dist/kome.wasm", import.meta.url)` in
  index.mjs is what lets vite/webpack emit the wasm asset.
- **Distro-pinned emscripten, not emsdk.** The plan said pin emsdk; wasm.yml
  has always used apt's emscripten, and the npm build uses the same toolchain
  so the package is built by exactly what the gtest-suites-in-WASM gate runs.
  Revisit if a distro bump changes codegen in a way the parity gate catches.
- **Gate scripts are copied into the temp project before running** — ESM
  resolves imports relative to the script file, so running them from the repo
  would miss the gate project's node_modules (the same in-place trap as the
  pytest sys.path one in phase 1, with the same fix).
- **npm publish is tags-only.** npm has no TestPyPI; the manual-dispatch
  dry-run stops at the fully-gated tarball artifact instead of publishing
  anything.
- **Review round (phase 2) — the packaged-artifact gate had the same in-place
  trap a third way**: run from inside `bindings/wasm/`, Node's *package
  self-reference* resolves `require("kome-sync")` back to the repo checkout
  (its package.json bears that name), so the parity gate silently re-tested
  the repo, never the tarball. parity.cjs is now copied into the gate project
  like every other gate script. Related fixes from the same review: ES6
  engine builds are now `-sENVIRONMENT=web,worker` (the __dirname landmine is
  out of the artifact, not just routed around); per-condition `types` with
  `.d.mts` re-exports (a lone CJS-flavored d.ts made `import kome from
  "kome-sync"` type-check while failing at runtime — the tsc gate now checks
  both flavors plus that negative case); the two release publish jobs gate on
  each other so registries can't diverge; npm.yml builds once and fans out
  (kills the `matrix.node == 22` upload condition); LICENSE ships in the
  tarball; open() validates seed length; identity/exists/digest check return
  codes; sync() can't leak sessions on a throwing step. Deliberately
  deferred: dist/ ships ~400KB of duplicate engine bytes (kome.wasm ≈
  kome.cjs.wasm, two embedded builds) — correctness first at 0.1.0, size
  dedup is follow-up.

## M7 — Packaging (phase 3: single-file amalgamation)

- **The generator is pure concatenation plus include surgery.** Internal
  (quote-form) includes are dropped because emission order — a topo sort over
  the actual include graph — satisfies them; nothing else is rewritten, and
  unknown includes or core→transport edges are hard errors. Unity-build
  symbol collisions are fixed in src/ by renaming (`storage.cpp`
  get_bytes→get_blob, `rendezvous.cpp` kChallenge/kAck/endpoint_key→kRz*/rz_*,
  `ws.cpp` kMaxMessageBytes→kMaxWsMessageBytes), never patched in the
  generator, so the normal build keeps compiling the same code the
  amalgamation ships.
- **kome.h IS sync_engine.h** — same content, same include guard, plus a
  provenance banner. A C consumer can `#include` either name; the drop-in CI
  gate compiles examples/example.c (C99) against it unmodified.
- **`SYNC_AMALGAMATION=ON` swaps the engine's TU, not the build.** The OBJECT
  library builds from generated kome.cpp; monocypher's include path is still
  exported but its static lib isn't linked (the definitions are inside the
  TU), and the four demos that link monocypher directly are gated off. The
  full suite, sync_engine_shared, and the services all build unchanged.
- **`KOME_NO_TRANSPORT` = the WASM subset.** The guard excludes exactly the
  POSIX-socket transports, mirroring what tools/wasm_flags.sh compiles — one
  boundary, two consumers.
- **clang joins the gate.** The single-TU view surfaced dead code per-TU gcc
  builds can't see (three unused crypto.h constants, deleted); amalgamation
  CI runs gcc and clang where per-PR CI is gcc-only.
- **Generated, never committed** — CI regenerates per push; releases attach
  kome-<version>-amalgamation.zip (kome.h, kome.cpp, LICENSE, SHA256SUMS) to
  the GitHub Release, and all three channels' publishes gate on each other.

## Blind TCP store-and-forward relay (issue #49)

- **Mailbox = a dedicated EdDSA keypair's public key, per-circle.** One
  broadcast is one POST instead of N; the relay learns only "holder of the
  mailbox capability posted/polled", never the recipient set or its size. A
  per-member mailbox is just a mailbox whose keypair belongs to one member,
  so the model subsumes per-member without the relay knowing which an app
  chose. Revocation is circle re-key + new mailbox keypair — standard E2EE
  group semantics; the old mailbox ages out via TTL/LRU.
- **Retained log, not drain-on-fetch.** A shared circle mailbox can't be
  drained by the first member to poll it (everyone must see the same
  broadcast), so FETCH takes a client-held cursor (`since_seq`) and is
  non-destructive; removal is by TTL/caps only, echoing `evicted_up_to` so a
  client below it knows it missed data.
- **One global monotonic seq counter, seeded from wall-clock at startup**
  (not per-mailbox). A per-mailbox counter restarting at 1 after eviction or
  a relay restart would silently strand every cursor a client saved against
  the old incarnation; a shared, wall-clock-seeded counter always hands out
  seqs above any prior cursor. Coarsens the seq into a global-post-volume
  leak, and `seq >> 20` discloses the relay's boot time to an authorized
  poster; both are relay operational metadata (not client content, identity,
  or key material — outside the plaintext/key blindness invariant), accepted
  and documented at the `next_seq_` seed in tcp_relay.cpp.
- **Per-operation challenge signatures, not a one-shot ATTACH or capability
  chains.** Every op is individually signed against the connection's HELLO
  challenge (`server_pk`, `nonce`) with a strictly-increasing per-mailbox
  `ctr`, so a forwarded/relayed frame is worth exactly one operation to
  whoever relays it (not forwardable into a session). Presenting the
  existing `Capability` chains instead was rejected: it would hand the relay
  issuer/subject pubkeys and the delegation graph — strictly more metadata
  than "holder of this one mailbox key" — so chains stay client-side.
- **Fetch-driven LRU, POST does not touch it.** A write-only junk spray
  never refreshes its own mailboxes, so when the mailbox-count or global-byte
  cap forces whole-mailbox eviction, victims are reader-less mailboxes first
  — the retained-log analogue of the UDP relay's F6 LRU-admits-new-peers
  fix, adapted for "refresh on read" instead of "refresh on any access".
  Combined with a real TTL (a retained log must drain by time too, or steady
  state becomes "every post evicts someone's data").
- **Opaque per-mailbox push-wake handles, not raw APNs/FCM tokens.** A raw
  device token is stable and device-global, so registering it directly would
  let the relay link every circle sharing that device. The app's push
  gateway maps handle→token instead, so the relay learns only
  mailbox↔handle and the gateway only handle↔token — neither party alone
  links a device to its circles. Wakes carry only the handle (no mailbox id,
  sender, size, or content), debounced per-handle (30s) so a blob flood
  can't become a ping flood.
- **Single-threaded poll loop, server-owned raw I/O — no `TcpStream` on the
  server side.** Reading tcp.cpp closely rules out the convenience calls for
  a server fielding untrusted persistent connections: `send_all` loops on
  EAGAIN with no deadline (one never-reading client freezes the whole
  loop), and `recv_frame` buffers up to 64 MiB per connection with idle and
  EOF both reported as plain `false`. `TcpRelayServer` instead owns
  nonblocking `::recv`/`::send` directly with per-connection RX/TX buffers,
  a 68 KiB client-frame cap enforced at the length prefix, a 2 MiB TX cap,
  and independent idle-timeout / mid-frame-progress / TX-stall deadlines —
  no threads, no locks, TSan-clean by construction, and `TcpListener`
  gained an `fd()` accessor + `set_nonblock` in `open()` + backlog 128 so it
  can join that same poll set without ever blocking `::accept`.
- **Per-IP token-bucket table, not per-connection.** Reconnecting must not
  reset a budget (bounded LRU-expired table instead), and buckets are
  charged before any signature verification — garbage frames cost no EdDSA,
  bounding CPU under a spoofed-source-free flood regardless of validity.
  The op bucket is charged at the very top of `process_frame`, *before*
  parsing, so a flood of tiny malformed frames is throttled like real ops
  (not just the well-formed ones); and a per-connection protocol-error count
  drops a connection past a small budget (mirroring the auth-failure drop),
  so a pure-garbage connection is reaped rather than served `ERR` replies
  forever — without this, a stream of 4-byte frames bought unthrottled
  ERR-reply work from the single-threaded loop (adversarial-review finding).
- **`MailboxLog::store` can return false for a reason other than "policy
  drop".** The UDP relay's `Relay::send` is `void` (a silent-drop contract
  the plan explicitly does not carry over): POST must acknowledge only
  actual storage, so `store` reports the assigned seq or failure and the
  server replies `ERR 5`, never a lying `OK`. In practice, with the per-
  mailbox cap (1 MiB) far below the global cap (64 MiB) and the global-cap
  eviction discipline evicting every other LRU mailbox before giving up,
  genuine capacity exhaustion is not reachable within a sane test byte
  budget — `MailboxLog` exposes a test-only global-cap override
  (`set_total_bytes_cap_for_test`) so the `ERR 5` path is still exercised
  deterministically rather than left unverified.
- **Client helpers live in the same file as the server, behind a clearly
  marked section.** The plan's blindness invariant ("no call site of
  `sign`/`x25519`/`aead_decrypt`" in the server implementation) and the
  plan's file list (client helpers, which must sign, inside
  `tcp_relay.cpp`) both hold: `tcp_relay_test.cpp`'s source-level check
  scopes its grep to everything above the `/* ---- client helpers` marker,
  so the invariant is enforced automatically without splitting a small
  internal file in two.

## Storage — open is read-only (nightly komed_test flake)

- **`Storage::load` no longer truncates a torn tail (or compacts a bloated
  log) at open; both are deferred to the writer's first append/mutation.**
  Open-time `ftruncate` made merely opening a database destructive: a
  concurrent read-only open (a monitoring tool, `komed --identity`, a test
  poller) that raced the owner's append classified the in-flight — or even
  fully committed — trailing frame as a torn tail and chopped it. The owner's
  in-memory state kept the change and never re-appended it, so the record was
  silently gone from disk with nothing to heal it (reconcile compares live
  in-memory state, which still matched). This was the ~1% nightly komed_test
  "DIGEST MISMATCH with all records present" flake. Crash recovery semantics
  are unchanged — the owner still drops a genuinely torn tail before its
  first write — and `Storage.OpenLeavesFileUntouched` pins the new contract:
  open + read + close leaves the file byte-identical.

## Deletion & erasure ABI (upstreamed from Circles)

- **The privacy-deletion recipe moved from app code into the public ABI.**
  Circles (the first real embedder) shipped ephemeral posts by combining four
  fragile facts about the engine from the app side: an empty-value `set` is
  the only replicating "unset"; fields must be zeroed BEFORE tombstoning
  (a `set` on a tombstoned entity resurrects it); `sync_blob_delete` only
  tombstones, so it walked the manifest's binary layout in Kotlin to zero
  chunk payloads by hand; and physical erasure needed `ke::Storage::compact`
  via a shim into an internal class. Each was an engine invariant an app had
  no right to depend on — the manifest-layout coupling especially: a layout
  change would have silently stopped image bytes from being erased, a privacy
  failure with no error signal. All four are now engine guarantees:
  `sync_engine_compact` (the internal Bitcask merge made callable),
  `sync_blob_erase` (zero chunk payloads with fresh-HLC LWW overwrites so the
  erasure replicates, then tombstone chunks + manifest), and
  `sync_engine_erase_field` (the empty overwrite that *refuses* a tombstoned
  entity instead of resurrecting it — the ordering invariant enforced at the
  API instead of documented at the call site). Additive C ABI only — no wire,
  codec, or `kTombstoneTtlMs` change.
- **Erase never creates or resurrects state.** `sync_engine_erase_field`
  returns NOTFOUND for an absent/tombstoned entity or absent field;
  `sync_blob_erase` skips chunks the replica never received and cannot reach
  payloads already hidden under a prior plain delete (tombstone GC covers
  those). A corrupt manifest gets its entity tombstoned ("erase what exists")
  and reports SYNC_ERR_CORRUPT so the caller knows chunk payloads may
  survive. No chunk refcounting (documented; same shared-chunk caveat as
  delete).
- **Proof retained from the app's verification:** the storage suite now pins
  that after `sync_blob_erase` + `sync_engine_compact` the *encrypted* log
  file is smaller than it was while it held the payload (Circles measured
  34368 → 27512 bytes on-device). `docs/STORAGE.md` documents the
  erase → tombstone → compact recipe, the 30-day tombstone interplay, and the
  cooperative-deletion limits; the designed next step (signed per-record
  `expires_at`, a protocol rev) is parked in `docs/DATA_TODO.md`.

## Gen-split: `state_gen` → `content_gen` + `scope_gen` (improvement 1)

- **The single invalidation counter is now two.** `state_gen` bumped on every
  mutation — writes, applies, tombstone GC, *and* capability grants/revokes/
  ingest — so a grant or revoke discarded a perfectly valid O(N) unscoped RBSR
  snapshot (`recon_cache`) even though the element set it encodes had not
  changed by a byte. The engine now keeps `content_gen` (the element set
  changed: set/delete/accepted-apply/tombstone GC) and `scope_gen` (who may
  read/write changed: grant/revoke/wire ingest). The unscoped snapshot is a
  pure function of `ns`, so `ensure_cache` and the snapshot stamp key on
  `content_gen` alone; the per-peer scoped cache is keyed on the pair
  (`ke::GenPair`, `sync_engine::scoped_cache_gens`), because a scope-only
  change must still drop every cached per-peer view — a fully-open peer then
  cheaply re-aliases the still-valid unscoped snapshot instead of rebuilding.
- **`state_gen` is deleted, not aliased — that is the mechanism.** Every one
  of the old read/write sites fails to compile until its author classifies the
  invalidation as content or scope, and any future `e->state_gen++` from an
  unrebased branch is a compile error rather than a silently mis-keyed cache.
  `ReconSnapshot::gen` stays a bare content-only `uint64_t` (documented at the
  field); scoped validity lives on the engine, not the snapshot object.
- **`SecurePeerSession` copies the gens as two loose `uint64_t`s
  (`sess_content_gen_`/`sess_scope_gen_`), not a `ke::GenPair`.** Naming
  `GenPair` in `transport/connection.h` would require including `engine.hpp`,
  and that header deliberately keeps `sync_engine` opaque — it is included by
  komed, the examples, and the transport test suites, so the include would
  silently widen the dependency surface for all of them. Two plain counters
  compared with `||` at the responder's cycle boundary reproduce the exact
  "either changed" semantics with zero new includes.
- **External consumers must migrate.** Anything reading `e->state_gen`
  directly through the internal headers (the Circles app shim did) no longer
  compiles; the replacement is `gens()` (or the individual counters) with the
  content/scope classification made explicit at the call site.

## Element-hash cache: cache per-cell reconciliation hashes (improvement 2)

- **Each cell now carries its own reconciliation-element hash.** `Register`
  gets `Hash256 elem_hash{}`, `Entity` gets `Hash256 ex_hash{}` (`Hash256 =
  std::array<uint8_t,32>`, promoted into `ke` in `engine.hpp`) — the SHA-256
  of the cell's canonical `encode_record` bytes (`encode_signing` bytes + the
  raw 64 B signature), computed once at every mutation point that installs or
  replaces a cell. `build_snapshot`'s `emit_element` now copies the stored
  hash instead of re-hashing the record, so the cold rebuild that dominated
  post-write sync drops from a SHA-256-per-element pass to a pure encode+copy
  pass. Wire bytes, RBSR fingerprints, and the on-disk frame format are all
  byte-identical; `sync_engine_digest` is deliberately **not** rewired to this
  cache (its preimage excludes signatures, a different hash over different
  bytes); the cache itself is RAM-only and rebuilt during the load-verify pass
  at open, so there is no schema bump.
- **Compute-then-commit: every hash is computed before the first byte of the
  state it describes is mutated — a standing invariant for future mutation
  points, not just this one.** `element_hash` allocates (`encode_record`
  appends into a `std::string`) and can throw `std::bad_alloc`. Computing it
  *after* installing the cell — the naive shape — would let a throw there
  strand an already-committed cell with a stale/zero hash and no invalidation
  signal: silent, permanent fingerprint divergence in Release, since nothing
  ever re-hashes a live cell from its bytes again. Every insertion point
  (`sign_existence`, `sync_engine_set`'s register path, both branches of
  `apply_change`) now computes the hash into a local alongside the signature,
  then assigns everything into the entity/register together as the last,
  non-throwing step, so a throw anywhere in the sequence leaves engine state
  exactly as untouched as before this change. Any future code that installs
  or replaces a `Register`/`Entity` must keep this shape: compute every
  allocating/throwing derived value — hash included — into locals first, then
  commit them as one non-throwing block.
- **The two hot local paths hash the buffer they already built, instead of
  re-encoding.** `author_sign`/`verify_change` already construct a `signing`
  string for the Ed25519 call and used to discard it; it is now threaded out
  to a streaming `element_hash(signing_bytes, sig, out)` overload
  (`Sha256.update(signing).update(sig, 64).finish()`), byte-equivalent to the
  one-shot form because `encode_record` is exactly `encode_signing` followed
  by an unprefixed signature append. Only `apply_change`'s
  `already_verified=true` path (no pre-built `signing` buffer available)
  still one-shot-encodes; that call still obeys the compute-then-commit rule
  above. `Storage::verify_range`'s parallel load-verify pass hashes the same
  way, writing a disjoint `hashes[i]` slot per index alongside the existing
  `ok[i]` verify result, unconditionally — identical code on the threaded and
  serial-fallback branches.
- **`merge_record`'s `try_emplace` closes the default-inserted-Register tie
  structurally, not just by test.** The promoted (out of the anonymous
  namespace) `ke::merge_record(sync_engine*, const DecodedChange&, const
  Hash256&)` uses `try_emplace` on the register map to observe insertion
  explicitly: on a `register_cmp` win, the incoming record's hash installs
  together with the record; on `inserted && !won` — the map just
  default-constructed a `Register` nobody described — that cell's hash is
  computed from its *own* canonical encoding via the shared
  `change_from_register` helper. Either branch leaves the map with a hash
  that actually describes what is stored under it; there is no path that
  leaves a default-constructed cell with a zero or stale hash.
- **One shared construction, not five hand-written encodings.**
  `change_from_entity`/`change_from_register` are factored out of
  `build_snapshot` and reused by `merge_record`'s degenerate-insert path and
  by the cross-path oracle test, so "the hash covers exactly what
  `build_snapshot` re-encodes" is a structural property of one code path
  instead of an argument repeated by hand at every call site.
- **Measured** (`docs/PERF.md` chapter 6): `BM_SessionBeginCold` at N=64 (the
  plan's headline case) goes 220.4 µs → 80.1 µs (2.75×, matching the plan's
  ~2.7× claim) and at N=4096, 13.43 ms → 2.00 ms (6.72×, 85.1% of the cold
  rebuild removed — SHA-256's share of the cold build grows with N, not flat
  at the ~63%/~35% figures either earlier chapter claimed; see PERF.md's
  reconciliation). Write-path cost: `BM_SetNewCell` (two hashes: presence +
  register) regresses 104.4 µs → 107.3 µs (+2.76%) against the ~86 µs
  Ed25519 double-sign that already dominates that path; `BM_SetOverwrite`
  and `BM_ApplyRegister` (one hash each) come out *faster* (−9.31%, −19.45%)
  from reusing the signing buffer instead of paying a separate re-encode.

## Batch-blob writes: nesting-safe batches with mandatory sub-frame flushing (improvement 3)

- **`Storage::batch_maybe_flush` fires from the engine's own write path — the
  in-batch branches of `tx_entity`/`tx_entity_field` — never left as a
  caller-optional call, because the naive shape (stage the whole batch,
  fsync once at commit) was reviewed and rejected on memory, not just
  correctness. §3.3's design-review hazard table measured a naive 8 MiB
  blob put at **+41.7 MB** peak VmHWM against the mandatory-flush design's
  **~+17.9 MB** — roughly **2.3× worse** — because an unbounded staging
  buffer holds the *entire* put (256 32 KiB chunks plus framing) in RAM
  simultaneously before its one fsync. `kBatchFlushBytes` (2 MiB; 256 KiB
  under `__EMSCRIPTEN__`, since the WASM heap only grows) caps staging at
  one threshold's worth regardless of batch size, and `Storage.
  BlobPutFrameBounded` pins the resulting cost on the fsync counter (not
  frame count — `atomic_replace`'s multi-frame rewrite still costs one
  fsync pair): 4 mandatory sub-frames + 1 outermost-commit frame + 1
  compaction rewrite for an 8 MiB put. The corrected memory claim (avoids
  the regression, restores roughly today's baseline peak, does not improve
  on it until Phase 4's streaming compactor replaces `serialize_state`'s
  full-image allocation) is recorded in `docs/PERF.md` chapter 7, not
  asserted in CI — process-global RSS isn't a CI assertion here.
- **Every sub-frame carries its own copy of the three clock-meta entries**
  (`hlc_physical`/`hlc_logical`/`db_clock`, via the new `Storage::
  stamp_clock_meta` helper shared by `batch_maybe_flush` and the outermost
  `batch_commit`), so a crash between sub-frames can never leave a durable
  record whose HLC exceeds the persisted clock — the same "any durable
  frame with records also carries a covering clock" invariant the log
  already upheld per-commit, now upheld per-sub-frame. The original
  `MidBatchCrashPrefix` design was reviewed as vacuous (`Hlc::tick`'s
  wall-clock branch would make the parent's post-reopen write dominate
  either way) and was respecified: the child `apply()`s signed remote
  records carrying a *future* HLC — forcing `clock.receive` to push the
  engine clock ahead of wall time — inside an open batch, until two
  sub-frame flushes have fired, then `_exit(0)` with the batch still open
  (no commit, no unwind). `Storage.MidBatchCrashPrefix` then asserts, on
  reopen, that the clock replayed to the *future* stamp (not a wall-clock
  fallback) and that a fresh local write only wins LWW because of it —
  the one assertion that actually fails without the per-sub-frame stamp.
  Fork-based, so native-only (WASM has no `fork`).
- **Capability writes stay outside the batch entirely.** `put_capability`/
  `put_revocation` (`src/capability.cpp`) bypass `emit()` and call
  `write_frame` directly, `in_batch()` or not, so `sync_engine_grant`/
  `sync_engine_revoke` keep today's synchronous fsync durability
  unconditionally — spec §3.3 point 5. The alternative (wire them into
  `batch_maybe_flush` like everything else) would let `sync_engine_revoke`
  return `SYNC_OK` for a revocation a later `batch_abort` can silently
  discard: a real security regression, since a revocation is how a
  compromised device gets cut off and the caller has already been told the
  cut-off happened. Pinned by two tests, not one: `Defensive.
  RevokeInsideBatchSurvivesAbort` (grant/revoke inside an open batch cost
  their own fsyncs while a sibling staged mutation costs none, and only
  the staged mutation is gone after `batch_abort`) and the fork-based
  `Defensive.RevokeInsideBatchSurvivesCrash` — the abort variant alone
  can't pin the property because `sync_engine_destroy` commits an open
  batch on the way out, so only killing the process before any destroy or
  abort proves the revocation was already durable on its own frame at the
  moment `sync_engine_revoke` returned.
- **Per-sub-frame fsync shipped over single-fsync-at-commit — the one open
  design fork the spec left for the maintainer, resolved to the
  conservative option as specified.** A single fsync at the outermost
  commit would save fsyncs on a huge batch, but it downgrades the
  erase-before-tombstone durable-prefix argument (`EraseTombstonePrefixInvariant`)
  from unconditional to "holds only if replay stops at the first bad
  frame" — a torn write during the one giant fsync could otherwise land a
  tombstone durably while its preceding zero-overwrite is lost, the exact
  resurrection-of-erased-content ordering bug the whole erase → tombstone
  recipe exists to prevent. Per-sub-frame fsync keeps every durable frame
  independently self-consistent (checksum-verified, append-order,
  clock-stamped), so the existing torn-tail argument at `load()` covers
  the multi-sub-frame case with no new reasoning.

## Stream compaction: bounding the compaction transient to O(one frame) (improvement 4)

- **`serialize_state` had to go: it built the whole compacted image as one
  `std::string` before `atomic_replace` ever touched disk, and that transient
  was measured, not assumed.** The data-structure review's design-review pass
  compacted 50k entities (17 MB log, ~30 MB live RSS) and measured a **+29.1
  MB VmHWM transient (48.5→77.6 MB)** — ~1.7× process memory — extrapolating
  to an estimated 100–300 MB at 200–500k records, which is exactly the
  Android low-memory-kill window (`docs/DATA_STRUCTURE_REVIEW.md` §3.1). A
  full-image allocation at compaction time was therefore a correctness risk
  on the platform the library is explicitly sized for, not just a memory
  nicety.
- **The bounded-sink design streams frames straight to `<path>.tmp` instead
  of into RAM.** `Storage::rewrite_log_streamed` replaces `serialize_state` +
  `atomic_replace` together: a `FrameSink` buffer pinned at `kCompactBufSize`
  = 256 KiB for the entire run (`append` flushes *before* copying, and
  anything ≥ the buffer size writes straight through, bypassing it — a
  threshold checked only *after* copying would let one oversized append grow
  the buffer geometrically and `std::string` never shrinks it back on
  `clear()`) accepts header + sealed frames one at a time; `sink.ok` gates
  both loop conditions, not just a single post-loop check, so a mid-stream
  write failure (ENOSPC/EIO) aborts immediately instead of falling back to
  building, sealing, and buffering every remaining entity — which would
  silently re-open the exact full-image transient this change exists to
  remove, on the failure path.
- **The honest bound is the capability/revocation frame, not an entity
  frame.** A frame is AEAD-sealed as a unit and can't be streamed away, so
  the peak is set by the *largest single frame* — and at `kMaxIngestedCaps`/
  `kMaxIngestedRevs` = 4096, the entire granted-capability set serializes as
  one ~598 KB frame body, whose encrypted-path `seal_frame` (`full`+`ct`+
  `framed`) costs **~1.8 MB** of transients, not the ~33 KiB an entity-only
  estimate would predict — roughly 50× the original claim. The corrected,
  tested bound is `kCompactBufSize` + 3× that largest frame = **2,056,336 B**
  (~2.0 MiB); `compact_stream_test` compacts an engine holding capabilities
  *and* a revocation specifically so this branch is exercised (no prior
  compaction test held any capability state at all). Measured
  (`docs/PERF.md` chapter 8): largest single allocation **262,145 B** on
  both plaintext and encrypted paths — essentially just the `FrameSink`
  buffer — against a 27.2/28.8 MB compacted image, over 100× smaller; VmHWM
  compaction-transient delta at 50k entities × 3 fields drops 34.1 MB→0.33 MB
  plaintext (−99.0%), 1.8 MB→0.26 MB encrypted (−85.9%, smaller because the
  cap/rev frame is the residual cost the bound above accounts for).
- **A mandatory final `ftruncate(tmp.fd, sink.total)` guards against a size
  misprediction, even though it's a no-op today.** `compacted_image_size`
  computes the exact byte count arithmetically for the open-time heuristic
  (mirrors the streamed frames entry-for-entry; cross-checked by a
  `#ifndef NDEBUG assert(sink.total == compacted_image_size(e))` live on
  every Debug/ASan/TSan/UBSan compaction), and the temp file is opened
  `O_TRUNC` and only ever appended to, so the truncate changes nothing on
  the path that ships. It exists for the path that doesn't yet: if the temp
  file is ever pre-sized with `ftruncate(tmp.fd, compacted_image_size(e))`
  to give WASM's MEMFS a one-shot allocation instead of `expandFileStorage`'s
  geometric growth, a size misprediction between the estimate and the actual
  stream could otherwise commit a rename'd log with trailing zero bytes —
  the final truncate to the *streamed* total forecloses that before it can
  ever happen, independent of whether pre-sizing ships.
- **The epilogue-ordering fix closes a latent bug the rewrite exposed rather
  than caused.** The pre-existing `atomic_replace` renamed successfully,
  then on a failed reopen returned `false` with `file_size_` still holding
  the *old* (larger) size while the on-disk file was already the new,
  smaller one — every subsequent `write_frame` would then `lseek` against a
  stale offset. `rewrite_log_streamed` sets `file_size_`/`tail_torn_`/
  `open_compact_pending_` to the new truth **immediately after the rename,
  before attempting the reopen** — the rename is the commit point, so the
  bookkeeping should reflect it the instant it happens, not after a second
  syscall that can independently fail.
- **The Phase-3 fsync counter keeps counting at the same accessor, on
  purpose.** `atomic_replace`'s two `storage_fsync_count()` bumps (temp-file
  fsync before rename, best-effort directory fsync after it) move to
  `rewrite_log_streamed` unchanged in count — same two calls, same counter —
  so `Storage.BlobPutFrameBounded`'s Phase-3 arithmetic (one compaction
  rewrite costs exactly 2 counted fsyncs, chapter 7 of `docs/PERF.md`)
  needed no update: the counter instruments *what a compaction rewrite costs
  in fsyncs*, and that cost is identical whether the bytes behind it were
  streamed or built as one string.
- **The directory fsync moved ahead of the reopen** (the one ordering change
  inside the epilogue). Both sit after the rename, so the old order only
  mattered on the reopen-failure path — where it skipped the directory fsync
  entirely, leaving the commit that had *already happened* un-hardened
  against a crash, and costing 1 counted fsync instead of 2 for that
  compaction. Durability of the commit point does not depend on this handle
  keeping a usable fd, so the fsync goes first and the reopen failure now
  costs only this handle its descriptor. The same edit fixes a latent
  edge case inherited from `atomic_replace`: a log at the filesystem root
  (`/x.db`) has its only slash at index 0, and `substr(0, 0)` asked to fsync
  `""` — a directory that never opens — so root-level logs silently got no
  directory fsync at all. It resolves to `/` now.
- **Everything the rewrite must not disturb, didn't:** rename stays the sole
  commit point (a crash or write failure mid-stream leaves the original log
  byte-identical, plus at most an orphan `<path>.tmp` that `open()` never
  reads and the next compaction `O_TRUNC`s); the digest is unchanged across
  compaction (the streamed bytes are the same bytes `serialize_state` used
  to build, just not materialized all at once); F2 holds structurally —
  `seal_frame`'s empty return is checked before any append, so a zero-nonce
  frame from an RNG failure never reaches even the temp file; and the
  erase→tombstone→compact shrink proofs (`CompactAbiShrinksPlaintextLog`,
  `BlobEraseThenCompactShrinksEncryptedLog`) pass unmodified, because the
  rewrite changes how the image is assembled, not which frames survive it.
  `CompactionIsDeterministicByteForByte` was respecified from a
  self-comparison (compact twice, diff the outputs — vacuous against a
  writer that drops the same frame both times) to a structural check via
  the Phase-3 frame walker: exactly one meta frame + one frame per entity in
  byte-lexicographic order + optional cap/rev frames, each entity frame's
  entry count matching its field count.

## Scoped-range-views: deadline-cached read-scoped snapshots (improvement 5)

- **Why the never-cache branch existed, and what replaced it.** A peer whose
  read scope depended on a finite-expiry capability used to be excluded from
  the per-peer snapshot cache entirely — `ensure_scoped_cache` returned an
  uncached `build_filtered` result every single time — because the existing
  cache had no notion of expiring an entry when nothing else moved: every
  invalidation the engine tracked was a generation bump, and a capability's
  expiry isn't one. That made every gossip cycle for such a peer, including an
  idle, converged one, pay a full O(N_visible) re-encode (`docs/PERF.md`
  chapter 9: 253.7 µs–4741.5 µs per cycle depending on shape). The replacement
  is `ReconView`: an immutable set of half-open base-index ranges over a
  `ReconSnapshot`, plus prefix sums over those ranges, cached per peer in the
  new `sync_engine::scoped_view_cache` under a wall-clock deadline
  (`valid_until_ms`) in addition to the existing `GenPair` guard. A cache hit
  is one map lookup plus one deadline compare — 1762×–32254× faster than the
  uncached rebuild it replaces, flat in both N and visible fraction.
- **Security fix — the cache deadline is the minimum expiry over every
  namespace scanned, denied ones included, not only readable/time-bound
  ones.** `CapStore::owned()` ignores expiry, so an *owned* namespace whose
  only root capability carries a finite expiry silently becomes *open*
  (world-readable — no usable root means unowned) the instant that root
  lapses, with no grant/revoke/write to bump a generation counter. Computing
  `valid_until_ms` only for the readable, time-bound case — the original
  shape — would cache that denial past the moment it flips to world-readable.
  `CapStore::authorized` (`capability.cpp`) now sets its `valid_until_ms`
  out-parameter whenever the namespace has a usable root and anything in it
  carries a finite expiry, for the denied case exactly as for the allowed
  one; `ensure_scoped_source`'s pre-scan (`reconcile.cpp`) takes the minimum
  over every namespace it visits, with no early exit on the first denial.
  Pinned by `ScopedView.DenialDeadlineSurvivesRootExpiry` and by
  denial-case assertions added to `Security.ReadScopeTimeBoundFlag`.
- **Security fix — `cap_authorize_read`'s `now` is now a required parameter;
  the `now == 0 → now_ms()` sentinel is gone.** With `now == 0`, `usable()`'s
  `c.expiry == 0 || now <= c.expiry` check treats *every* finite-expiry
  capability as usable — an uninitialized or defaulted `now` was a fail-open
  planted directly in the read-scope enforcement path, and the Debug
  cross-check couldn't catch it because the cross-check was handed that same
  `now`. `now` is required at both `cap_authorize_read` call sites now, with
  no in-function fallback and no default argument; `begin_session` reads the
  clock exactly once per session and threads that single instant through the
  scope pre-scan, the range-view build, the filtered build, and the Debug
  cross-check, so all four classify against the same point in time. Two
  separate clock reads could otherwise classify a peer as time-independent
  and then, a microsecond later, silently cache a set narrower than that
  classification assumed, as if it were permanent.
- **Privatization that makes a missed raw-base access a compile error, not a
  discipline.** `sync_session`'s snapshot/view members (`ss_`/`vw_`) are
  private, written exactly once by `set_source()` (asserted write-once, and
  asserted mutually exclusive — a session reconciles over one source, never
  both). Every other member is expressed in visible-index space (`size()`,
  `elem()`, `lower_index()`, `fingerprint()`), so `s->ss->snap[i]`-style raw
  base indexing — which would silently ignore read scope — no longer
  compiles from anywhere in the file. The original design privatized only the
  *accessors*, leaving `ss`/`vw` themselves public and directly assignable,
  so its "a missed access is a compile error" claim did not actually hold;
  this closes it structurally instead of by convention.
- **Read scoping now rests on index arithmetic over a shared base, not
  physical absence — accepted, and deliberately layered.** When cheap (see
  the gating decision below), a view ranges over the engine's *shared*,
  unfiltered snapshot instead of a per-peer snapshot with denied records
  physically removed, so correctness depends on the range/index arithmetic
  (`ReconView::base_index`/`elem`/`vsum`, each bounds-asserted —
  `assert(v < visible)`, since the unguarded mapping at `v == visible` is
  valid-but-wrong and invisible to UBSan) rather than on denied bytes never
  having been copied in the first place. Three independent mitigations, not
  one: the Debug cross-check (every view build compared element-for-element
  and prefix-sum-for-prefix-sum against a from-scratch, genuinely-filtered
  `build_filtered`, live on all four sanitizer CI legs since they all build
  Debug), the accessor privatization above, and an adversarial test that
  drives crafted out-of-range and malformed reconcile-message bounds at a
  scoped session and asserts that no byte, count, or fingerprint of a denied
  namespace escapes into the reply
  (`ScopedView.MaliciousBoundsCannotLeakDeniedBytes`) — built on a new
  minimal wire-message encoder with its own encode/decode round-trip guard
  (`tests/recon_wire.hpp`, its discriminating power separately pinned by
  `ScopedView.WireVehicleGuardIsDiscriminating`), since the production
  message encoders have internal linkage and no reconcile-message builder
  existed to reuse. See `SECURITY.md`'s residual-risk entries for the
  deployed framing.
- **Measured crossover: gate on "is the base already paid for," not a
  visible-fraction threshold.** Ranging over the shared base costs an O(N)
  snapshot build where the old filtered path cost only O(N_visible); forcing
  `build_view`'s gate to `share_base = true` unconditionally to measure the
  ungated path directly (`docs/PERF.md` chapter 9) showed a 6.67×–15.65×
  write-active regression at small visible fractions (1/100, 1/10) — and the
  ungated path stayed 1.88×–2.42× regressive even at the *largest* visible
  fraction measured (1/2); the ratio only approaches 1.0× in the limit as the
  peer's visible fraction approaches "reads everything," where filtering and
  sharing converge to the same work. No fraction short of that limit is safe
  to treat as "close enough" to share for free. `build_view` therefore ships
  gated on `share_base = base_is_current(e) || fully_open` — share the
  already-built, current unscoped snapshot, or share it when the peer may
  read all of it anyway; otherwise build the peer's own filtered snapshot,
  exactly as the pre-phase path did — rather than on a visible-fraction or
  multi-consumer heuristic. Gated, write-active cost lands at parity with the
  pre-phase filtered rebuild (ratios 0.92–1.01 across the measured shapes);
  the idle/converged case this phase exists for keeps its full 1762×–32254×
  win, since gating only chooses which base a view is built over, never
  whether the deadline cache applies.

## Integration: the five improvements on one head

- **The rebase was mechanical, as the plan predicted.** P5 was developed off
  P2 (the reconcile track) and had never met P3/P4 until integration.
  Replaying it onto P4 conflicted in `DECISIONS.md` and `docs/PERF.md` only —
  both the "two phases appended at the same place" kind — while every source
  file merged clean, including `reconcile.cpp`, which P2 and P5 both edit.
  Resolution kept both sides and renumbered P5's PERF chapter 7 → 9 (7 and 8
  were taken by P3 and P4).
- **Cross-phase review found no correctness or security defect**, which is
  the claim worth recording precisely: each phase had been reviewed only
  against its own base, so the seams — P4's streamed compaction against P2's
  cached element hashes, P3's batching against P4's `maybe_compact`, P5's
  view cache against P1's generation bumps — were unexamined until here. They
  were verified by repro and by mutation, plus a ~13k-op randomized soak
  across 13 build/encryption configurations with the P2 hash assert, the P4
  size-exactness assert and the P5 view cross-check all live.
- **It did find a coverage gap, and the gap hid a real leak path.** Reaching
  the `ReconView` path requires a delegation with a *finite* expiry; every
  test that created one used an in-memory engine, and every test that
  compacted or batched used expiry 0. So nothing pinned the P5 × P3 and
  P5 × P4 seams. The behaviour was correct, but the protection was
  accidental: neutering `gc_tombstones`' `content_gen++` leaks a GC'd
  tombstone to a peer through a stale scoped view, and no permanent test
  noticed. `ScopedView.TombstoneGcEvictsCachedViewOnStoreBackedEngine` and
  `ScopedView.RevokeInsideOpenBatchEvictsCachedViewImmediately` close it on
  store-backed engines; the first is mutation-proofed against exactly that
  neutering, the second pins that a revoke inside an open batch cuts a cached
  view *immediately* (capability writes bypass batching, so waiting for the
  commit would keep serving a revoked peer).
- **Also fixed here:** documentation that had drifted out of step with the
  code — `engine.hpp`'s `scoped_cache_gens` contract still named
  `ensure_scoped_cache` (P5 renamed it `ensure_scoped_source`), PERF chapter
  7 still described compaction going through `atomic_replace` in the present
  tense (P4 deleted it), and the plan's Phase-5 gate text still described the
  visible-fraction heuristic it *anticipated* rather than the
  `base_is_current || fully_open` gate that measurement actually produced.

## Zero-HLC existence records: `{0,0}` is a reserved sentinel (bug fix)

- **`sync_engine_digest` changes value for any engine holding an unasserted
  entity.** Stated first because it is the headline: the digest is the
  documented convergence oracle. A *healthy, converged* replica holds no
  unasserted entity (`sync_engine_set` emits the presence assertion and the
  register together), so no healthy digest moves. What moves is an engine
  holding an entity key that carries no reconciliation element: a register that
  arrived before its existence record, a shell left by the compute-then-commit
  `bad_alloc` path, or a replica poisoned by the bug below. Wire bytes, RBSR
  fingerprints and the on-disk frame format are untouched; no golden digest
  vector exists anywhere in the repo (every digest assertion in the suite is
  engine-to-engine within one run). The real exposure is a mixed-version fleet
  comparing digests mid-sync across a field-before-existence transient.
- **The bug.** `Entity::asserted()` *derives* "does this entity carry a presence
  assertion?" from `presence_hlc != {0,0}` instead of storing a bit. But
  `apply_change`'s EXISTENCE branch compared `(hlc, author)` against a
  synthesised `{0,0}` + `kZeroAuthor` tuple for an absent cell, so an incoming
  record stamped `{0,0}` *tied* on HLC and *won* the `memcmp` tie-break for any
  real public key. It then committed `present_v`/`ex_author`/`ex_sig` onto a
  cell that `asserted()` still reported unasserted. Four subsystems disagreed
  about one cell: `exists` said 1, `digest` moved, `build_snapshot` advertised
  no element, and `Storage::apply_entry` re-derived `asserted()` at load and
  discarded the presence bit, author and signature. Reachable from the wire by
  any peer with namespace write access — and reachable *by accident*, because
  the public header still documented the pre-LWW contract (`hlc` marked
  "REGISTER only", "unused" for EXISTENCE), so `memset`-then-fill — the natural
  way to hand-build a `sync_change` — produced exactly this record.
- **Why the digest fix is not optional.** The entity-key set is not the element
  set, and RBSR can only ever equalise the element set — so *any* entity key
  carrying zero elements is permanently un-reconcilable and permanently
  digest-visible. Two replicas that reconciliation reports as fully converged
  held permanently different digests, with no route to repair: `gc_tombstones`
  deliberately keeps unasserted shells and `rewrite_log_streamed` re-emits every
  entity unconditionally, so a shell survives both GC and compaction forever.
  Rejecting `{0,0}` at apply closes only one of three shell producers; the
  second is `apply_entry`'s unasserted branch and the third is the `bad_alloc`
  shell that compute-then-commit *deliberately blesses* (`engine.hpp`). The
  third cannot be closed at the source without abandoning that invariant, so the
  digest itself has to be shell-immune. `docs/DATA_STRUCTURE_REVIEW.md` predicted
  this for a hypothetical incremental digest; it was already true of the O(N) one.
- **This restores the digest's documented contract rather than changing it.**
  `DECISIONS.md` promises the digest reflects *all state* — it still hashes every
  tombstone and every register hidden under one; what it stops hashing is the
  *absence* of an assertion, a constant tuple (`present=0`, `hlc {0,0}`, zero
  author) whose only information is "this key is in the map", which is precisely
  what RBSR does not replicate. Three written promises were false before this
  fix and are true after it: the header's "two engines that have merged the same
  set of records produce identical digests", "digest preserved across reopen",
  and "the digest is unchanged across a compaction".
- **Rejected: an explicit stored `asserted` bit.** It is the honest
  representation, and the wire would *not* need to change (a record on the wire
  is always an assertion; there is no "no assertion" record to encode). But the
  in-memory `Entity` and the on-disk `kEntity` entry would, and `Storage::load`
  rejects an unknown schema version outright — so it costs a format bump plus a
  migration. What that buys is the ability to represent an assertion from a peer
  whose clock reads exactly `{0,0}`: a record that loses LWW to every other
  assertion in existence, and which that same peer's next tick would emit
  correctly as `{0,1}`. A format break to preserve a degenerate case.
- **`{0,0}` is therefore reserved by rule, not by accident**, and that is the
  lasting cost of keeping the derived predicate: a future maintainer who
  introduces a legitimate zero-HLC producer will have their data dropped. It is
  documented at `Entity::asserted()`, at `sync_change` in the public header, and
  enforced in both apply paths. `Hlc::tick` cannot return `{0,0}`, both local
  existence producers go through it, and `build_snapshot` only ever advertises
  `asserted()` cells — so no honest writer can emit `{0,0}`, and the rejection
  can never refuse an honest peer's record.
- **That last claim was not true when first written, and adversarial review
  caught it.** `Hlc::logical` is `uint32_t` and both increment sites were a bare
  `+= 1`, so a clock at `{p, UINT32_MAX}` wrapped to `{p, 0}` — and at `p == 0`
  (a host whose `now_ms()` is stuck at the epoch: no RTC, which is exactly the
  embedded/WASM case) that is the sentinel itself. `Hlc::carry_logical_overflow`
  now carries the wrap into `physical`, which keeps the result strictly greater
  than the pre-tick value (`{p,MAX} < {p+1,0}`) and makes "a ticked clock is
  never `{0,0}`" a *total* invariant rather than an overwhelmingly likely one.
  A latent HLC overflow independent of this bug, fixed here because the whole
  rejection rests on it. `docs/DATA_MODEL.md`'s planned v2→v3 migration had the
  same defect from the other direction — it synthesized `hlc = {0, C}`, mapping
  a legacy `causal_length = 0` onto the sentinel — and is respecified to
  `{0, C + 1}`.
- **The first attempt at that carry was itself wrong, in two ways, and a second
  review round caught both.** It decided the carry from `logical == 0` *after*
  the increment, which cannot distinguish a wrap from `receive`'s fourth branch
  — where `logical = 0` is a deliberate reset because the wall clock advanced
  past both sides — so every ordinary apply pushed `physical` one millisecond
  past `now`, breaking `receive`'s own `physical <= max(local, remote, now)`
  bound. And its `physical += 1` was unguarded, so at `physical == UINT64_MAX`
  it wrapped to `0` with `logical` already `0`: the sentinel again, reached from
  the other end. That one was *remote-triggerable* — `receive` adopts a peer's
  physical with no clamp on future timestamps, so a single signed record at
  `{UINT64_MAX, UINT32_MAX-1}` plus one local write minted `{0,0}` and silently
  lost the local write. Strictly worse than the hole it was closing.
  `Hlc::bump_logical` decides the carry from the *pre-increment* counter, so
  only a real wrap carries, and saturates at `{UINT64_MAX, UINT32_MAX}` instead
  of wrapping: a repeated timestamp costs only progress (LWW ties on author and
  the later write is dropped), where wrapping mints a phantom. Recorded because
  the pattern generalises — "detect the overflow from the post-state" is the
  bug, and the carry itself needed its own overflow guard.
- `reconcile` ignores
  `apply_change`'s return value, so a rejection drops one record rather than
  aborting a session: no DoS, no stall.
- **`present()` now means `asserted() && present_v`.** A no-op after the above,
  kept so that a future path re-introducing present-without-assertion is caught
  by construction rather than by a repro.
