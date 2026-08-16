# Android binding & AAR (implementation plan)

The fourth distribution channel, following M7's three (pip wheel, npm/WASM,
amalgamation — `docs/PACKAGING.md`). Motivation is in
`docs/GO_TO_MARKET.md` §2: "no mobile SDK packaging" is the last
High-severity buyer gap without an engineering answer, the warmest customer
list (stranded Realm refugees) is mobile-first, and the ATAK plugin track
requires an Android artifact before anything else can happen.

The engine itself needs no porting: Android is Linux, the NDK provides POSIX
sockets and C++17, and monocypher is portable C99. This is packaging plus one
deliberate ABI addition (phase 3), not engine work. As with M7, every phase is
gated on CI proving the *packaged artifact* — the AAR a user would download —
not the build tree.

| Deliverable | User experience |
|-------------|-----------------|
| `kome-sync` AAR on Maven Central | `implementation("io.github.hershelshah:kome-sync:0.x")` → the README quickstart runs in Kotlin, zero NDK required |

## D0 — Decisions up front (small diffs, blocking)

- **D0a — Binding mechanics: hand-written JNI in C++, Kotlin-first public
  API.** No JNA/JNR (they'd be the project's second dependency and cost a
  reflective call per op); no SWIG/djinni codegen (the C ABI is ~50 functions
  — generator machinery costs more than it saves, and the ctypes binding
  proves the surface is small enough to mirror by hand). One `kome_jni.cpp`,
  one Kotlin module.
- **D0b — Names.** Maven Central coordinates `io.github.hershelshah:kome-sync`
  (the `io.github.<user>` namespace is verified by a GitHub repo challenge —
  start the Central portal registration in week 1, it's the long pole for
  publishing, same lesson as PyPI/npm squat-checking in P7.0b). Kotlin package
  `io.github.hershelshah.kome`, entry class `Engine`. C symbols stay `sync_*`,
  the library stays `libsync_engine.so` (P7.0b's reasoning: renaming is churn).
- **D0c — ABIs: `arm64-v8a`, `armeabi-v7a`, `x86_64`.** arm64 is the fleet,
  v7a is cheap insurance for low-end field-ops hardware (the target vertical),
  x86_64 is the emulator/CI. No x86-32. Build with NDK r28+, and align ELF
  segments to 16 KiB — Google Play requires 16 KB page-size support for
  everything targeting Android 15+, and a misaligned .so is a hard reject.
  CI checks alignment with `readelf` per ABI, not by hope.
- **D0d — minSdk 21.** Nothing in the engine needs newer; 21 is the NDK
  floor anyway and covers effectively every device in the target verticals.
- **D0e — Build from the repo CMake tree, not the amalgamation.** The
  amalgamation ships only the public C API, but phase 3's network shim and
  the JNI layer want the same access komed has (internal C++ headers, one
  source snapshot, no ABI drift risk because everything ships together).
  The existing `CMakeLists.txt` builds `libsync_engine` unchanged under the
  NDK toolchain file; the JNI TU is one more target in the same build.
- **D0f — Threading: honor the caller-serialized contract in Kotlin, don't
  re-litigate it in C.** The engine's documented contract is "one engine, one
  thread at a time; no shared global state" (DECISIONS.md, M6). The Kotlin
  `Engine` owns a single-thread dispatcher; every call hops through it.
  Public API is `suspend` functions plus blocking variants for Java callers.
  No mutex added to the C side — the JVM wrapper is the serialization point,
  exactly as the Python GIL is today.

## Phase 1 — cross-compile + artifact hygiene gate

Prove `libsync_engine.so` builds and is well-formed for every ABI before any
Java exists.

- `android.yml` workflow: matrix over the three ABIs,
  `cmake -DCMAKE_TOOLCHAIN_FILE=$NDK/build/cmake/android.toolchain.cmake
  -DANDROID_ABI=... -DANDROID_PLATFORM=android-21 -DANDROID_STL=c++_static`,
  plus `-Wl,-z,max-page-size=16384`.
- Gate per ABI: links with no missing symbols (`llvm-readelf -d`, no
  `NEEDED` beyond libc/libm/liblog), 16 KiB `LOAD` alignment verified,
  exported surface is exactly the `sync_*` C ABI (`llvm-nm -D` diffed against
  the header — same spirit as the amalgamation's symbol discipline).
- The full gtest suite already runs on linux-x86_64 in `ci.yml`; phase 1
  adds no on-device testing. Cross-compile + ELF checks are the whole gate.

## Phase 2 — JNI + Kotlin core binding (parity with Python/WASM surface)

Bind the entire public C ABI — the same surface the ctypes binding and the
WASM binding wrap, no more, no less:

- Engine lifecycle: `create(seed)`, `open(path, seed)`,
  `openEncrypted(path, seed, key)`, `flush()`, `close()`
  (`AutoCloseable`, plus a `java.lang.ref.Cleaner` safety net so a leaked
  handle never leaks native memory).
- Data: `set/get/delete/exists`, `scan` (cursor pagination surfaced as a
  Kotlin `Sequence<ScanEntry>`), blobs (`blobPut/blobGet/blobStat/blobDelete`),
  `exportChanges/applyChange` with a `Change` data class mirroring
  `sync_change` field-for-field, `digest()`.
- Sync: `sessionBegin`/`sessionBeginScoped`/`sessionStep`/`sessionEnd` — the
  transport-agnostic pump, so any Kotlin transport can drive reconciliation
  (this is what makes phase 3b possible at all).
- Authz: capabilities (root/delegate/encode/decode/grant/revoke/isRevoked),
  invites (encode/decode).
- Misc: identity/siteId, logger callback (JNI → a Kotlin `(level, msg)`
  lambda; the C contract already guarantees no secrets in messages),
  `strerror`, `abiVersion` (checked at load, refuse to run on mismatch —
  same as `_ffi.py`).

Conventions, all inherited from the Python binding so the three bindings
stay teachable as one API: keys/values are `ByteArray` (typed values remain
a future, cross-binding decision — DATA_TODO P3); `NOTFOUND` maps to `null`,
every other error to `KomeException(code)`; buffers returned by the engine
are copied into JVM arrays and `sync_free`d before the JNI call returns, so
no native pointer ever crosses into Kotlin.

**The cheap gate (no emulator): host-JVM tests.** Build the ordinary
linux-x86_64 `libsync_engine.so` + `libkome_jni.so`, run the full Kotlin
test suite on the desktop JVM with `-Djava.library.path`. This is the
wheels.yml trick — test the binding logic at native speed on every push —
and it means the emulator only ever has to prove "same behavior on
Android", not carry the whole suite. Port the parity battery (the
README-quickstart convergence scenario the npm package gates on) as the
canonical test.

## Phase 3 — networked sync

The gap this phase closes: the production network path (`connect_and_sync`,
`SecurePeerSession` — Noise XX, STUN, hole punch, relay) is C++-internal.
Examples and komed use it; no binding can. Two lanes, in order:

- **3a — a minimal networked-sync C ABI, then JNI it.** New public surface,
  deliberately tiny (this is a stable-ABI commitment; keep it one concept):
  roughly `sync_net_config` (bind/rendezvous/relay addresses),
  `sync_net_connect_and_sync(engine, peer_pubkey, invite/addr, config,
  timeout_ms)` → error code, plus a cancel handle so a Kotlin coroutine can
  abort a stuck attempt. Implemented in the repo tree where the internals
  are visible; exposed in `sync_engine.h`; **the Python binding gets it in
  the same PR** — the README's "over a network this is the secure
  connect_and_sync path" note finally becomes a callable line of Python,
  and the ABI addition pays for itself across every binding at once.
  Bump `SYNC_ABI_VERSION`.
- **3b — Kotlin WebSocket runtime (follow-up, optional).** A `SyncClient`
  mirroring `kome-sync-runtime`'s TS loop (dial, gossip interval, reconnect,
  converge) over OkHttp, for networks where UDP is blocked and for talking
  to the same WS hubs the browser clients use. It drives the phase-2
  session pump; no native changes. Ship it as a separate module so the core
  AAR keeps zero dependencies.

Gate for 3a: an end-to-end CI scenario — x86_64 emulator app converges with
a host-side komed over the emulator's `10.0.2.2` host alias (UDP, full
secure stack). Hole punching through real NATs stays out of CI scope, same
caveat as M5 ("needs a real network"); the netnode/relay scenarios already
cover the protocol logic on the host.

## Phase 4 — Android platform integration (samples and docs, not SDK code)

Keep the AAR dependency-free; the opinionated Android-lifecycle code goes in
a sample app and a recipe doc, the same honest-scoping move as "records, not
queries":

- **Storage**: engine file under `context.filesDir`; at-rest key as a random
  32 bytes wrapped by an Android Keystore AES key → `openEncrypted` (the
  KOMEENC1 path — the seed never sits in plaintext on a phone).
- **Sync scheduling recipe**: foreground service for live sync, WorkManager
  periodic reconcile for background, connectivity-callback trigger, Doze
  notes. The relay's push-wake design (opaque per-mailbox handles,
  DECISIONS.md) is the future FCM hook; document the seam, don't build it.
- **Sample app**: the two-device offline-first inventory demo from the GTM
  plan, which doubles as the flagship-demo work item and the ATAK-plugin
  starting point.

## Phase 5 — AAR packaging, CI, Maven Central

- AAR assembly: Kotlin classes + per-ABI `jniLibs` + consumer R8 rules
  (keep JNI-referenced names), prefab headers optionally exported for NDK
  consumers who want the C API directly.
- `android.yml` end state: ABI matrix build + ELF checks (phase 1), host-JVM
  suite (phase 2), one Gradle-managed-device x86_64 instrumented run of the
  parity battery + the komed convergence scenario (phase 3), then the
  assembled AAR installed into a fresh sample project and smoke-tested — the
  npm.yml "test the artifact, not the tree" pattern.
- Publishing: Sonatype Central portal, signed artifacts, version
  single-sourced from `project(sync_engine VERSION ...)` exactly as P7.0c
  does for pip/npm; `release.yml` grows a fourth channel that refuses to
  publish on tag/version disagreement.
- Docs: Kotlin quickstart in the README, this file updated to "landed"
  status per phase, Realm-migration guide gains the Android section it was
  missing.

## Sequencing & risks

Rough solo-effort shape: phase 1 ≈ 1–2 days, phase 2 ≈ 3–5 days, phase 3a
≈ 3–4 days (most of it ABI design care, not code), phase 5 ≈ 2–3 days,
phase 4 ≈ 2 days. Phases 1→2→3a are strictly ordered; 4 and 5 overlap them.

- **Central namespace verification is the long pole** for the publish step —
  register in week 1 (D0b), publish whenever ready.
- **New public ABI (3a) is a forever commitment** — keep it to the one
  connect-and-sync entry point + cancel; resist config sprawl (everything
  else can arrive later without breaking anyone).
- **16 KiB pages and 32-bit v7a** are the two silent-breakage risks; both
  are mechanical CI checks (readelf; the existing suite compiled `-m32`
  already runs in the sanitizer matrix's spirit — add a v7a-shaped host gate
  only if a real bug ever appears).
- **Emulator CI can't prove NAT traversal** — inherited M5 caveat, already
  documented; the on-device gate proves the secure stack end-to-end, which
  is what buyers ask about.
