# Android-bindings plan — validation report

## Verdict summary

The research+verification pass confirms six plan-level defects in `docs/ANDROID.md` (four high severity, two medium) and validates five existing decisions as sound. Three of the confirmed defects are correctness-breaking rather than stylistic: the Phase 2 leaked-handle safety net (`java.lang.ref.Cleaner`) crashes every device below API 33 while both CI gates are structurally blind to it; the proposed networked-sync ABI's `peer_pubkey` parameter implies identity pinning that `SecurePeerSession`/`ConnectionManager` never perform, so `sync_net_connect_and_sync` would silently sync with an unauthenticated third party; and the same ABI omits the initiator/responder role and peer-liveness precondition that a one-shot blocking Noise handshake requires. A fourth high-severity finding is empirical: the Phase 1 "exported surface is exactly the `sync_*` C ABI" gate fails today against a freshly built `libsync_engine.so` (418 dynamic exports, only 44 are `sync_*`), contradicting D0e's "unchanged" framing. Two medium findings round out the set: the plan is silent on `sync_session`'s raw-pointer dependency on its parent `sync_engine` (a real use-after-free ordering hazard once Session gets its own Cleaner-style handle), and surfacing `scan` as a lazy Kotlin `Sequence` fights both the suspend/blocking split in D0f and the header's documented `""`-entity cursor caveat. None of the six were refuted; all required only precision corrections, which are folded into the revisions below. Five other claims — the dispatcher/threading model, hand-written JNI, cancel-handle feasibility, the single-entry-point network cut, and the cross-compile/16KiB/host-JVM-gate mechanics — were checked and hold as written.

---

## Confirmed findings

### 1. `java.lang.ref.Cleaner` is unavailable below API 33 — both CI gates are blind to it

**Plan says** (`docs/ANDROID.md:77-80`): Engine lifecycle is `AutoCloseable`, "plus a `java.lang.ref.Cleaner` safety net so a leaked handle never leaks native memory." D0d (`:40-41`) sets minSdk 21.

**Code/evidence shows**: `Cleaner` was added to Android at API 33 and is not in the core-library-desugaring set. Every device on API 21–32 hits `NoClassDefFoundError` — at Engine class init if `Cleaner` is held in a `static final` field, otherwise at first execution of the referencing instruction (i.e. effectively every Engine construction). Neither gate can catch it: the Phase 2 "cheap gate" (`:102-109`) runs on a desktop JVM, where `Cleaner` has existed since Java 9; neither the Phase 3 emulator gate (`:135-136`) nor the Phase 5 Gradle-managed-device run (`:163-165`) names an API level at all, so the minSdk 21 floor is never exercised by anything in the plan.

**Revision**: Replace the Engine safety net with a `PhantomReference` + `ReferenceQueue` registry (the `NativeAllocationRegistry` pattern — that class itself is hidden API, so it can't be used directly) instead of `Cleaner`. Close the gate gap two ways, not one:
- Add Android Lint's `NewApi` check (`abortOnError`) to `android.yml` — catches this and any future API-level regression at build time for free.
- Add at least one low-API (API 21 or 26) instrumented boot test so the declared floor is actually run somewhere in CI.

### 2. Proposed networked-sync ABI implies identity pinning the internals don't perform

**Plan says** (`docs/ANDROID.md:119-122`): `sync_net_connect_and_sync(engine, peer_pubkey, invite/addr, config, timeout_ms)` — the name and parameter imply "sync with this specific peer."

**Code/evidence shows**: `verify_identity_proof` (`src/noise.cpp:244-253`) is a pure output — it `memcpy`s whatever pubkey the peer proves possession of, with no expected-key input. `begin_cycle_` (`src/transport/connection.cpp:130-142`) starts capability-scoped reconciliation immediately with whoever authenticates. `ConnectionManager::sync_with` (`connection.cpp:274-293`) uses `peer_pk` only for relay addressing, never as a comparison target, and `DirectTransport::recv` (`connection.h:109-112`) discards the sender address entirely.

**Revision** (applying the verdict's correction): the fix must cover more than "any third party holding a valid capability" and more than "the direct endpoint." Because unowned namespaces are world-readable/writable, a stranger with *zero* capabilities can complete the handshake, converge over every open namespace, push writes into them, and the caller gets a success return believing it synced with the named peer — and because `DirectTransport::recv` ignores source address, any host that can land a UDP datagram on the socket can race the real peer, not just something answering at `direct_ep`. The relay path is not exempt either — mailbox fetch is guarded only by a stateless return-routability cookie, not proof of key possession. Add an optional expected-pk comparison inside `SecurePeerSession`, checked at the verify site (`connection.cpp:134`) *before* `begin_cycle_()` — checking only when `authenticated()` first flips from an outer loop is too late, since the initiator's first scoped fingerprint is already queued for transmission by the time control returns there. This single change also covers komed/netmesh and the relay path.

### 3. Proposed ABI omits initiator/responder role and the peer-liveness precondition

**Plan says** (`docs/ANDROID.md:119-122, 135-139`): `sync_net_connect_and_sync(...)` has no role parameter; Phase 4 (`:154`) proposes a two-device demo with no stated precondition.

**Code/evidence shows**: only the initiator sends the first handshake datagram (`connection.cpp:102-109`); `connect_and_sync` is a deadline-bounded loop that fails if the peer doesn't dial within the timeout — Noise XX is interactive and the relay's store-and-forward does not relax this. komed derives role via `memcmp(my_pk, peer_pk, 32) < 0` (`komed_main.cpp:595-604`) plus a flipped-role retry against pure responders (`:653-658`) and sticky self-promotion in daemon mode (`:532-547`); this convention is already recorded repo-wide in `DECISIONS.md:961`. netnode's `--role` flag (`examples/netnode.cpp:79`) defaults to responder rather than strictly requiring the flag.

**Revision**: adopt komed's derived-role convention (the ABI already has both keys) *plus* a flipped-role retry within `timeout_ms` — derivation alone is insufficient for a one-shot call against a pure responder. State the deployment precondition explicitly in the plan: the named peer must concurrently be inside its own connect/serve loop (komed in **daemon mode**, netmesh, or a second phone also calling the ABI) — a one-shot call against `komed --once` will not converge. The Phase 3a gate text should say which komed mode CI runs, since the plan currently doesn't specify.

### 4. Phase 1's symbol-surface gate fails against the current build

**Plan says** (`docs/ANDROID.md:65-68`): "exported surface is exactly the `sync_*` C ABI (`llvm-nm -D` diffed against the header)." D0e (`:46-47`): "The existing `CMakeLists.txt` builds `libsync_engine` unchanged under the NDK toolchain file."

**Code/evidence shows**: a fresh build of `sync_engine_shared` exports 418 dynamic symbols — 44 match the header's `sync_*` functions exactly, but 374 do not: 329 mangled C++ internals (`sync_engine_detail::Sha256`, `ke::MailboxLog`, `SecurePeerSession`, etc.) plus 45 vendored monocypher `crypto_*` symbols. No `-fvisibility=hidden`, version script, or visibility attribute exists anywhere in the repo (`CMakeLists.txt:24-28,164-166`; `include/sync_engine.h:27` is bare `extern "C"`). `ANDROID_STL=c++_static` only excludes libc++/libunwind archive symbols, not the project's own.

**Revision**: this is a real build-configuration change, cheaper than "visibility work" suggests — a link-time version script scoped to `sync_engine_shared` alone, not a header-wide `-fvisibility=hidden` attribute pass:
```
# sync_engine.ver
{ global: sync_*; local: *; };
```
applied via `target_link_options` on `sync_engine_shared`, which subsumes the monocypher problem too (making `-Wl,--exclude-libs,ALL` optional rather than required). Note the interposition risk is specifically against another vendored copy of monocypher in-process (names don't collide with libsodium's), not "monocypher/libsodium-family" broadly. Phase 1 should name this version-script file explicitly rather than let D0e's "unchanged" silently paper over it.

### 5. `sync_session`'s lifetime dependency on its engine is undocumented

**Plan says**: Phase 2 lists per-type API surface (`docs/ANDROID.md:77-93`) with a Cleaner safety net on Engine but no cross-handle lifetime rule.

**Code/evidence shows**: `struct sync_session` embeds a raw `sync_engine *` (`src/reconcile.cpp:321-322`, assigned at `:733`) and dereferences it throughout stepping (`apply_records`, `cap_ingest_delegations`, `s->engine->caps->export_blobs`). If Session gets its own independent Cleaner-style safety net, cleanup order among simultaneously-unreachable objects is unspecified — `sync_engine_destroy` can run before a further `sync_session_step`, producing a use-after-free.

**Revision** (scope narrowed per the verdict's correction — this applies to exactly one child type, not three: `Capability` is a pure value struct that safely outlives its engine, and scan returns an owned array, not a handle): state explicitly in Phase 2 that Kotlin `Session` holds a strong reference to its `Engine`, every session call is dispatched on that engine's single-thread dispatcher, `Engine.close()` ends live sessions (or refuses while any are open), and `Session` gets **no independent Cleaner** that could outrun the engine's. Worth mirroring as a doc-comment addition on `sync_session_begin` in `include/sync_engine.h`, which is silent on this today. Note `sync_session_end` is just `delete s` and doesn't touch the engine — the hazard is specifically destroy-then-step, not destroy-then-end.

### 6. `scan` as a lazy `Sequence<ScanEntry>` fights the suspend/blocking split and the cursor's `""`-entity caveat

**Plan says** (`docs/ANDROID.md:81-82`): `scan` surfaced as `Sequence<ScanEntry>`; D0f (`:48-54`) commits to "suspend functions plus blocking variants."

**Code/evidence shows**: `include/sync_engine.h:196-214` documents that `start_after=""` is indistinguishable from "start from the beginning," so an entity literally named `""` cannot be used as a cursor; a lazy `Sequence` must block-hop each page fetch onto the single-thread dispatcher on whatever thread the consumer iterates, and iteration can outlive `Engine.close()` (`engine.use { it.scan(ns) }.toList()` compiles and would call into a destroyed handle).

**Revision** (per the verdict's corrections): D0f's blocking-variant lane legitimately covers a synchronous `Sequence`, so this isn't a flat D0f contradiction — the actual gap is that `Sequence` is offered as the *only* scan shape, leaving the suspend lane with no counterpart. Add a `Flow`-based (or eager-page) suspend variant, and add a handle-validity guard on every native entry point so a `Sequence` outliving `use{}` fails cleanly instead of touching freed memory. On the cursor caveat: page size ≥ 2 is *not* sufficient — a namespace whose only remaining live entity is `""` returns `[""]` regardless of page size, and the loop restarts from the beginning forever. Special-case the empty-named entity explicitly, or terminate when a page comes back shorter than the requested limit (the pattern `tests/scan_test.cpp:99-113` already uses).

---

## Checked and holds

- **D0f dispatcher model** — single-thread-dispatcher-per-Engine correctly realizes the caller-serialized contract; document two caveats: the logger lambda fires on the dispatcher thread (no blocking Engine calls from it), and no `AttachCurrentThread` machinery is needed since `engine_log` only ever fires on the calling thread.
- **D0a hand-written JNI** — correct given `sync_change`'s asymmetric-ownership struct layout and malloc'd double-pointer out-params; generator overhead would exceed hand-JNI cost here.
- **Cancel handle for `connect_and_sync`** — feasible with an atomic flag (~20ms latency, safe off-thread), but `rendezvous_register`/`rendezvous_lookup` are uncancellable multi-second blocking calls that must be shortened or looped to bound total cancel latency.
- **Single-entry-point network cut (`sync_with`)** — `ConnectionManager` already packages the right semantics; `netnode.cpp:123-157` is nearly the shim's body; D0e's repo-tree build choice makes the "Python binding in the same PR" claim realistic with zero extra build changes.
- **Phase 1/2 build mechanics** — NDK cross-compile is clean (only `MSG_NOSIGNAL` and `fopen("/dev/urandom")`, both bionic-API-21-safe); 16KiB page-size guidance is accurate; the host-JVM test gate correctly mirrors the proven `wheels.yml` pattern.

## Claims that did not survive verification

None — all findings raised were confirmed as real (with precision corrections applied above); no claim was refuted.