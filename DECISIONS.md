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
