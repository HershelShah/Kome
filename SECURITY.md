# Security

This document is the threat model and security posture for the engine. It
describes what the system protects, against whom, the guarantees and their
limits, and the residual risks we know about. It reflects the codebase as of
the S1–S8 security pass (see `DECISIONS.md` for the per-change rationale).

> **Status: research / pre-1.0, not independently audited.** The design has had
> an internal adversarial review and is exercised by sanitizers and fuzzers
> (below), but it has not had a third-party audit. Don't deploy it to protect
> anything you can't afford to lose without your own review.

## Reporting a vulnerability

Please report suspected vulnerabilities privately to the maintainer rather than
opening a public issue. Include a description, affected component, and a
reproducer if you have one. We'll acknowledge and work a fix on a branch before
any public disclosure.

## What the system is

A peer-to-peer, offline-first replication engine. Replicas exchange signed
change-records and converge (CRDT). It runs over untrusted networks via an
encrypted, mutually-authenticated channel (Noise XX), with optional capability-
based access control per namespace, and optional relay/rendezvous infrastructure
for connectivity.

## Identities and trust

- A replica's **identity** is an Ed25519 signing keypair. The **site id** is
  `BLAKE2b-256(signing_public_key)`. The same seed also derives an X25519
  keypair for the channel.
- **Every change-record is individually signed** by its author over a canonical
  encoding (`encode_signing`: version, kind, ns, entity, field, value, HLC,
  causal-length, author). Authenticity of data does **not** depend on the
  transport — a record is trusted because its signature verifies, wherever it
  came from (network, relay, disk).
- **Capabilities** are signed delegation chains rooted at a namespace owner. A
  namespace becomes access-controlled ("owned") once a root capability for it is
  locally granted; otherwise it is open. `sync_engine_grant` is the **local
  trust API** (the embedder decides which roots/delegations to install); the
  network path (`cap_ingest`) never accepts roots and only extends chains
  anchored at a locally-trusted root.

## Guarantees

Under the threat model below, the engine aims to provide:

1. **Data integrity & authenticity.** A record can only be accepted if its
   signature verifies against its declared author. A forged or tampered record
   is rejected — over the network, from a relay, *and* when loaded from disk
   (S2). Verification is skipped only for records that would not change state
   (they reach no state and don't perturb the clock); a record forged to *win*
   the merge is still verified and rejected (verify-on-win).
2. **Write authorization.** On an owned namespace, a record is applied only if
   its author holds a valid capability chain granting write access.
3. **Channel confidentiality & peer authentication.** Sessions run inside a
   Noise XX channel (forward-secret, mutually authenticating the X25519 static
   keys) that is additionally **bound to the peer's Ed25519 identity** by a
   signed proof over the unique handshake transcript (S1) — so a relay/MITM
   cannot impersonate or interpose. The reliability framing under the channel is
   authenticated too (S6c).
4. **Read scoping.** A peer only receives records from namespaces it is
   authorized to read; the live transport reconciles a capability-scoped
   snapshot keyed to the authenticated peer (S1).
5. **Convergence safety.** Merges are commutative/associative/idempotent;
   message reorder/loss/duplication cannot corrupt state or diverge two honest
   replicas.

## Threat model

**In scope — a network adversary** who can observe, drop, reorder, duplicate,
inject, and spoof source addresses on the wire, connect to nodes, relays, and
rendezvous servers, and author/sign their own records and capabilities (from
keys they control). Defenses:

| Attack | Defense |
|--------|---------|
| Forge/tamper a record | per-record Ed25519 signature; rejected on apply and on storage load |
| Impersonate a peer / MITM the channel | Noise XX + transcript-bound Ed25519 identity proof (S1); a proof can't be replayed onto another handshake |
| Read a restricted namespace by connecting | capability read-scoping on the authenticated peer (S1) |
| Inject/forge a record via a relay | relay carries only ciphertext (blind); records still signature-checked |
| Forge reliability seq/ack to wedge a link | reliability frames HMAC-authenticated with a handshake-derived key (S6c) |
| Replay an old valid record | dominated by current state (monotonic causal-length / LWW order) → no effect |
| Parser exploits (malformed frames/records/caps/invites) | bounds-checked, fuzzed; WS frame length capped before the size math (S3) |

**Resource / denial-of-service.** A network adversary can always make a node
spend a signature verification (this was true before and after the perf work).
We bound the amplification:

| Vector | Bound |
|--------|-------|
| Oversized WS/TCP frame → crash/OOM | 64 MiB frame cap, reject before overflow (S3) |
| Unbounded wire counts (descriptors/caps/records) | rejected if count > remaining bytes (S4) |
| Reconcile descriptor amplification / non-termination | reply capped at ~`kBuckets × own element count`; per-session step cap (S7) |
| Gossiped-capability flood | `CapStore` bounded; chain check O(N) not O(N²) (S5) |
| Relay mailbox OOM | per-key + global byte caps, oldest-evicted; oversized blobs dropped (S6a) |
| Relay spoofed-source reflection/amplification | return-routability cookie on FETCH (S6a) |
| Rendezvous registry flood / victim-key redirection | key-ownership proof + bounded pending set (S6b) |
| Parallel verify worker exception → `std::terminate` | worker wrapped, fail-closed (S4) |

**Out of scope.** Endpoint compromise (an attacker who can read process memory
or the on-disk database has the node's identity — see Limitations); traffic
analysis / metadata (sizes, timing, who-talks-to-whom are not hidden); a
malicious *authorized* writer within its granted scope; physical/side-channel
attacks; availability of third-party relay/rendezvous infrastructure itself.

## Component posture

- **Crypto (`crypto.cpp`, monocypher 4.0.2):** Ed25519 (BLAKE2b-based) signing,
  X25519, XChaCha20-Poly1305 AEAD, BLAKE2b, HMAC/HKDF-SHA256. `random_bytes`
  fails closed (wipes + returns false on short read) so a partial buffer is
  never used as key material.
- **Codec / reconcile (`codec.cpp`, `reconcile.cpp`):** length-prefixed,
  versioned, canonical encodings; fuzzed; strict-length decode on received
  records (no trailing-byte ambiguity); reconciliation checked against the
  full-state oracle.
- **Capabilities (`capability.cpp`):** signed chains, cycle-guarded DFS, opt-in
  enforcement; bounded store; roots never trusted from the wire.
- **Channel (`noise.cpp`):** Noise XX with the AEAD swapped for XChaCha20-
  Poly1305 (so **not wire-compatible with standard Noise**), identity binding,
  receive-nonce advanced only on successful auth (S4).
- **Transport (`udp/tcp/ws/reliable/stun/relay/rendezvous`):** bounded buffers,
  authenticated reliability, hardened relay/rendezvous (above).
- **Storage (`storage.cpp`, SQLite WAL):** all queries parameterized (no
  injection); rows re-verified on load; identity-bearing DB chmod'd `0600`
  best-effort.

## Hardening & testing

- **Sanitizers:** the full suite runs under ASan, UBSan, and TSan in CI;
  `-Werror` on the per-PR matrix.
- **Fuzzing:** ten coverage-guided libFuzzer targets over every external-byte
  parser (record/capability/session/apply/storage/noise/stun/reliable/ws/
  invite), run nightly with compounding corpora.
- **Regression tests:** each security fix above is pinned by a test (e.g.
  `Connection.ReadScopingEnforcedOverTransport`, `Storage.ForgedRowRejectedOnLoad`,
  `Security.ForgedFrameDoesNotDesync`, `Relay.FetchChallengeReturnRoutability`,
  `Service.RendezvousRejectsForgedRegistration`, `Reliable.MacRejectsForgedFrameOnceKeyed`,
  `Defensive.VerifyOnlyWhenRecordWouldChangeState`).

## Known limitations & residual risks

- **Identity secret at rest.** A durable node stores its seed (its private
  identity) in the database so reopen re-derives the same identity — like an SSH
  private key on disk. We wipe transient copies in memory and set `0600`, but
  there is no at-rest encryption: protect the DB file with filesystem
  permissions / full-disk or filesystem encryption. Anyone who can read the file
  controls the identity.
- **Additive set-fingerprint.** The reconciliation range fingerprint is an
  additive sum of per-element hashes, which is not collision-resistant against
  an adversary who can get chosen signed records accepted into a namespace.
  Worst case is *silent divergence / data suppression* for a range (not data
  forgery — signatures still gate writes). A collision-resistant multiset hash
  (LtHash/ECMH) is the planned fix; it is a wire-protocol change.
- **Low-order / non-canonical keys.** Author public keys are not screened for
  low-order points. This does not grant access on an owned namespace (the key
  holds no capability), but such keys should be rejected for defense in depth.
- **HLC from a valid writer.** An authorized writer (or a compromised key) can
  push the HLC far into the future; future writes then lose merges until wall
  time catches up. Bounding accepted skew is a planned hardening.
- **Handshake-phase reliability frames** are unauthenticated (no session key
  exists yet); they are the Noise handshake itself, which Noise authenticates,
  so the worst case is a handshake-time DoS, not a compromise.
- **No wire-protocol version negotiation yet.** Cross-version peers are not
  guaranteed to interoperate or fail gracefully; this is tracked separately.
- **M5 connectivity is a subset.** IPv6 preference and kernel-NAT hole punching
  are validated by an in-process simulator, not a real multi-host network.
- **DoS is bounded, not eliminated.** Verification is the dominant cost and an
  unauthenticated peer can always make a node verify; the bounds above cap
  amplification but a determined attacker with bandwidth can still degrade
  service. Rate-limiting at the deployment layer is recommended.

## Deployment guidance

- Treat the database file as a private key: restrictive permissions, encrypted
  storage, backups protected accordingly.
- Run relay/rendezvous behind your own rate limiting; they are resource-bounded
  but not a substitute for network-layer DoS protection.
- Enable capability enforcement for any namespace whose writes/reads must be
  restricted (unowned namespaces are open by design).
- Keep the per-record signature path: do not feed network-received capabilities
  into `sync_engine_grant` (that is the local-trust API; use the sync path).
