# M7 — Packaging & Distribution (implementation plan)

The engine works; getting it *into people's hands* doesn't. Today the only way
to try Kome is `cmake -B build` — a C++ toolchain, CMake ≥ 3.16, and for the
browser story an Emscripten install. The precedent from libraries in the same
shape is unambiguous: DuckDB and PyNaCl are C/C++ cores whose adoption happened
almost entirely through `pip install` / `npm install`, not through people
building the amalgamated source — and SQLite's two-file amalgamation is why it
is *in* everything. Bindings and zero-build packages are where adoption
happens; the C ABI (`include/sync_engine.h`), the ctypes binding
(`bindings/python/sync_engine.py`), and the WASM binding
(`bindings/wasm/sync_engine.cjs`) already exist and are CI-verified, so M7 is
packaging work, not engine work.

Three channels, one engine, in leverage order:

| Channel | Deliverable | User experience |
|---------|-------------|-----------------|
| **A. PyPI** | self-contained wheel | `pip install kome-sync` → the README quickstart runs, zero toolchain |
| **B. npm** | WASM package (Node + browser + bundlers) | `npm install kome-sync` → two engines converge in a 10-line script |
| **C. Amalgamation** | `kome.h` + `kome.cpp`, one download | drop two files into any C/C++ project, `c++ -c kome.cpp`, done |

Everything below is gated the same way the engine milestones were: a task isn't
done until CI proves the *packaged artifact* (not the build tree) passes its
suite.

## P7.0 — Prerequisites (blocking decisions, small diffs)

- **P7.0a — License.** ✅ resolved: `LICENSE` already declares **MIT** for the
  engine + CC0 for docs — the README's "MIT or Apache-2.0 (TBD)" line was
  stale, not an open decision. Packages ship as MIT; README/LICENSE cleaned
  up in phase 1.
- **P7.0b — Names.** ✅ resolved for PyPI: `kome` is squatted (an empty
  0.1.0), so the distribution name is **`kome-sync`** — the import name stays
  **`kome`** (distribution/import names are independent). npm's `kome` gets
  checked in phase 2 — ✅ resolved: squatted there too, so **`kome-sync`** on
  both registries (one name to remember). C symbols stay `sync_*` and
  the shared library stays `libsync_engine` — the ABI is stable and tested
  under that name; renaming symbols is churn with no user benefit.
- **P7.0c — Version single-sourcing.** `project(sync_engine VERSION 0.1.0)` in
  CMakeLists.txt is the one source of truth. The Python build reads it via
  scikit-build-core's regex metadata provider; the npm build script injects it
  into `package.json`; the release workflow refuses to publish if the git tag
  (`v0.1.0`) disagrees with it.

## Workstream A — `pip install kome-sync` (self-contained wheel)

**Status: landed** (A1–A5 + the release workflow skeleton; publishing awaits
the PyPI Trusted Publisher being configured for `kome-sync` and a `v0.1.0`
tag, with a TestPyPI dry-run via `release.yml`'s manual dispatch first).

**Approach.** Keep the ctypes binding — that's the PyNaCl lesson inverted:
because there is no compiled *extension module* (no `Python.h` anywhere), the
wheel has no per-interpreter ABI. One `py3-none-<platform>` wheel per platform
covers every Python ≥ 3.8, forever, with no abi3 gymnastics. The wheel is just
the pure-Python wrapper plus `libsync_engine.{so,dylib}` built by the existing
CMake, bundled inside the package. Build backend: **scikit-build-core** (it
drives the CMakeLists we already have; no second build system).

- **A1 — Package layout.** New `bindings/python/kome/` package:
  `kome/__init__.py` (public API — the current `Engine` class and constants),
  `kome/_ffi.py` (the ctypes layer, today's `sync_engine.py`), and
  `kome/_lib/` (destination for the shared library inside the wheel).
  `_find_lib()` search order becomes: `SYNC_ENGINE_LIB` env (explicit dev
  override — wins everywhere and fails loudly if wrong) → `kome/_lib/`
  (installed wheel) → the existing build-tree candidates (repo dev flow,
  unchanged). `bindings/python/sync_engine.py`
  becomes a thin `from kome import *` shim for one release, then dies.
- **A2 — Build config.** `pyproject.toml` at the repo root with
  `build-backend = "scikit_build_core.build"`, `wheel.py-api = "py3"`
  (produces the py3-none-platform tag), and CMake args
  `-DSYNC_BUILD_TESTS=OFF`. Add an `install(TARGETS sync_engine_shared ...)`
  rule (component `python`) so scikit-build-core places the library in
  `kome/_lib/`. Version via the regex provider pointed at CMakeLists.txt
  (P7.0c).
- **A3 — Self-contained sdist.** `pip install` from the sdist must need only a
  C++17 compiler and CMake — it already does: monocypher is vendored and
  GoogleTest's FetchContent is gated behind `SYNC_BUILD_TESTS` (OFF here).
  Gate: build the sdist, install it in a network-restricted container, run the
  smoke test.
- **A4 — Wheel matrix.** GitHub Actions with cibuildwheel: **manylinux2014
  x86_64 + aarch64** (auditwheel repair; the engine's only runtime deps are
  libstdc++/libm, which auditwheel policies handle), **macOS x86_64 + arm64**
  (delocate; `MACOSX_DEPLOYMENT_TARGET=11`). One CPython per platform
  (`CIBW_BUILD="cp312-*"`) since the output is interpreter-agnostic. **Windows
  is explicitly out of scope for M7**: `src/storage.cpp` uses POSIX
  `open/fsync` and `src/transport/*` uses BSD sockets; a winsock/Win32 port is
  its own milestone (M8 candidate), not a packaging task. Document WSL as the
  interim answer.
- **A5 — Packaged-artifact test gate.** New CI job per platform: build the
  wheel, install it into a **clean venv**, run `bindings/python/test_smoke.py`
  plus a new test that exercises the README quickstart verbatim (durable
  `path=` engines, replicate, digest match) — against the installed package,
  with `SYNC_ENGINE_LIB` deliberately unset. This is the gate that catches
  "works in my build tree" bugs.
- **A6 — Publish.** `release.yml` on tag: build sdist + all wheels → publish
  via **PyPI Trusted Publishing** (OIDC, no long-lived token). First release
  goes through TestPyPI end-to-end (install from TestPyPI in a clean container,
  run the quickstart) before the real index.

**Exit gate:** on a machine with no compiler, `pip install kome-sync` then the
README Python quickstart runs unmodified. README's build-first instructions
get replaced by that one line.

*Deliberately out of scope:* widening the Python API to sessions /
capabilities / invites / networking. The wheel ships the API that exists; a
richer `kome.connect()` story is follow-up work (tracked separately) and must
not block distribution of what's already tested.

## Workstream B — npm / WASM package

**Status: landed** (B1–B6; publishing awaits the npm Trusted Publisher being
configured for `kome-sync` on npmjs.com and a `v*` tag — the manual-dispatch
dry-run stops at the fully-gated tarball artifact, since npm has no TestPyPI
equivalent). Two notes from implementation: the API core lives once in
`binding.cjs` and every entry (CJS/ESM × split/embedded, plus the repo dev
shim) wraps it; and in Node the ESM entry loads the *CJS* engine build,
because the distro emscripten's `EXPORT_ES6` output references `__dirname`
on its Node path — the ES6 build serves browsers/bundlers, where that path
is dead.

**Approach.** `tools/wasm_build.sh` already produces a modularized
Emscripten build (`-sMODULARIZE -sEXPORT_NAME=createSyncEngine
-sENVIRONMENT=web,node`), and `bindings/wasm/sync_engine.cjs` is the
high-level wrapper. Packaging means: proper `package.json` with a conditional
`exports` map, an ESM entry alongside CJS, TypeScript declarations, and a CI
gate that tests the **packed tarball**, not the repo layout.

- **B1 — Package layout.** `bindings/wasm/` grows into the npm package root:
  `package.json` (`name: "kome-sync"`, `exports` with `import`/`require`/`browser`
  conditions, `files` allowlist), `index.cjs` (today's wrapper),
  `index.mjs` (ESM), `index.d.ts`. Build emits two Emscripten outputs into the
  package: the current CJS/web one and an `-sEXPORT_ES6` ESM one; the `.wasm`
  file ships alongside. Loading order stays "wrapper wraps factory", so the
  wrapper API is identical across entries.
- **B2 — Embedded single-file variant.** A second entry point
  `kome-sync/embedded` built with `-sSINGLE_FILE=1` (wasm base64-embedded in the
  JS). ~33% size overhead, but zero asset-pipeline configuration — the
  path of least resistance for bundler users who hit "where does the .wasm
  go" friction. Document the tradeoff; default entry stays split-file.
- **B3 — Types + API.** Hand-written `index.d.ts` covering the wrapper
  (Engine lifecycle, set/get/delete/exists, export/apply, digest, session
  begin/step/end, capabilities, invites — everything `EXPORTS` in
  wasm_build.sh already exposes). CI type-checks it with `tsc` and runs a
  small consumer snippet under `--strict`.
- **B4 — Persistence note, not feature.** Default filesystem is MEMFS;
  document (in the package README) mounting IDBFS/OPFS in browsers and that
  Node users who want durability on real disk should prefer the native
  path for now. No new persistence code in M7.
- **B5 — Packaged-artifact test gate.** A reusable `npm.yml` (the wheels.yml
  pattern — release.yml invokes it, so the release can't drift from CI):
  build the package, `npm pack`, install the tarball into a fresh temp
  project, then (1) run `parity.cjs` re-pointed at the installed package —
  the same scenario battery that gates the WASM build today, (2) ESM +
  embedded `import`/`require` smoke tests, (3) a strict `tsc` check of the
  declarations, and (4) a browser app built by a stock bundler (vite) against
  the installed package, loaded headlessly in Chromium — proving the
  `browser` condition and `.wasm` asset story actually work. Node LTS matrix
  (20/22).
- **B6 — Publish.** `npm publish --provenance` from `release.yml` (OIDC via
  npm Trusted Publishing; tags only). Toolchain reproducibility: the build
  uses the distro-pinned apt emscripten — the same toolchain wasm.yml has
  always used — rather than a separately-pinned emsdk; revisit if the distro
  bump ever changes codegen in a way the parity gate catches.

**Exit gate:** `npm install kome-sync`, a 10-line Node script converges two
engines and matches digests; the same package builds into the browser demo
with vite, unconfigured.

## Workstream C — single-file amalgamation

**Approach.** SQLite's play: one header, one implementation file, no build
system. Ours is C++ under a C API, so the pair is **`kome.h`** (the public C
header — `sync_engine.h` re-emitted with a provenance banner) and
**`kome.cpp`** (every `src/*.cpp` + `src/transport/*.cpp` + monocypher
concatenated). Any project with a C++ toolchain — including plain-C
codebases, which call through the pure-C header and just link the one extra
object — integrates with `c++ -c kome.cpp`. Set that expectation explicitly
in docs: it's a `.cpp`, not a `.c`, and that's fine for the same reason
linking libstdc++ is fine.

- **C1 — Generator.** `tools/amalgamate.py`: resolves internal `#include`s in
  dependency order, strips their guards, hoists and dedupes system includes,
  wraps `monocypher.c` in `extern "C"`, stamps a banner (version, commit,
  regeneration command), defines `KOME_AMALGAMATION 1`. No source rewriting
  beyond include surgery — if two TUs collide (file-local `static` helpers or
  anonymous-namespace names shadowing across TUs, the classic unity-build
  failure), **fix the collision in `src/` by renaming**, so the amalgamation
  stays a pure concatenation and the normal build keeps compiling the same
  code.
- **C2 — Full-suite gate.** CMake option `SYNC_AMALGAMATION=ON`: build
  `sync_engine` from the generated pair instead of `SYNC_SOURCES`, then run
  the **entire** ctest suite against it, `-Wall -Wextra -Wpedantic -Werror`,
  gcc and clang. Also compile it single-TU under emcc (the WASM build should
  work from the amalgamation too — that's the "one file, every target"
  promise). New CI job on every push/PR.
- **C3 — No committed copy.** The amalgamation is **generated, never
  committed** — a checked-in copy goes stale the day after it lands. CI
  regenerates and gates it on every push (C2); `release.yml` attaches
  `kome-<version>-amalgamation.zip` (`kome.h`, `kome.cpp`, `LICENSE`,
  SHA-256 sums) to each GitHub Release. That's the download URL the README
  points at.
- **C4 — Transport toggle.** The transports drag in POSIX headers, which
  kills the amalgamation on non-POSIX targets. Guard them with
  `#ifndef KOME_NO_TRANSPORT` in the generated file so
  `-DKOME_NO_TRANSPORT` yields the portable core (engine, storage, crypto,
  reconciliation, Noise, capabilities) — the same subset the WASM build
  already proves out. Default keeps transports in.

**Exit gate:** download two files from a release, `c++ -c kome.cpp` on a
stock Linux/macOS box, link against `examples/example.c` compiled as C, demo
converges; CI runs the full gtest suite against the generated pair on every
push.

## Release pipeline (ties the three together)

New `release.yml`, triggered by `v*` tags:

1. Check tag == CMake `project(VERSION)` (P7.0c); abort on mismatch.
2. Fan out: sdist + wheel matrix (A4) / npm tarball (B5) / amalgamation zip (C3)
   — each job re-runs its packaged-artifact gate before anything publishes.
3. Publish: PyPI (Trusted Publishing) + npm (`--provenance`) + GitHub Release
   assets. All OIDC; zero long-lived secrets in the repo.

## Order of work

| Phase | What | Why first |
|-------|------|-----------|
| 1 | P7.0 + Workstream A | pip is the highest-leverage channel per the DuckDB/PyNaCl evidence, and A has the least new machinery (the binding and CMake already exist) |
| 2 | Workstream B | wasm.yml already proves the artifact; this is repackaging + types + the tarball gate |
| 3 | Workstream C + release.yml | amalgamation needs the unity-build cleanup pass (C1) and the release workflow wants all three artifact jobs to exist |

Each phase lands as its own PR, gated on its packaged-artifact CI job. After
phase 1 ships, the README leads with `pip install kome-sync`.

## Risks & mitigations

- **Name availability** — check PyPI/npm for `kome` first (P7.0b); fallbacks
  chosen up front so a squatted name doesn't stall the workstream.
- **manylinux compliance** — build inside the manylinux2014 image via
  cibuildwheel; auditwheel is the arbiter, not our guess about glibc.
- **Windows demand** — explicitly deferred (A4); the ask is a storage/
  transport port, not packaging. Saying so in the README beats implying it.
- **Emscripten drift** — pin emsdk in CI (B6); a wasm artifact that changes
  under an unpinned toolchain is a supply-chain smell.
- **Unity-build symbol collisions** — surfaced deterministically by the C2
  gate; fixed in source, never patched in the generator.
- **Dual-package hazard (npm)** — CJS and ESM entries wrap the *same* factory
  but a consumer importing both gets two module instances; engines don't share
  global state (validated by threading_test's no-global-state contract), so
  this is a docs note, not a bug to engineer around.
