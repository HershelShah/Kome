#!/usr/bin/env bash
# Build the npm package artifacts (M7 workstream B, docs/PACKAGING.md).
#
#   tools/npm_build.sh   ->   bindings/wasm/dist/
#     kome.cjs.js + kome.cjs.wasm     CommonJS entry's engine (Node require)
#     kome.mjs    + kome.wasm         ES module engine (Node import + bundlers)
#     kome.embedded.cjs.js            single-file variants (wasm base64-embedded,
#     kome.embedded.mjs               no asset pipeline; ~33% larger)
#
# Also stamps bindings/wasm/package.json's version from CMake's
# project(VERSION) — the single source of truth (P7.0c).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
source tools/wasm_flags.sh

DIST=bindings/wasm/dist
mkdir -p "$DIST"
MONO="$(mktemp -d)/monocypher.o"

wasm_build_monocypher "$MONO"
wasm_link "$MONO" "$DIST/kome.cjs.js"
wasm_link "$MONO" "$DIST/kome.embedded.cjs.js" -sSINGLE_FILE=1
# ES6 builds are browser/worker-only: the entry points route Node to the CJS
# builds (see index.mjs), and web,worker keeps emscripten's ESM-hostile Node
# glue out of the artifact entirely.
WASM_ENV=web,worker wasm_link "$MONO" "$DIST/kome.mjs"          -sEXPORT_ES6=1
WASM_ENV=web,worker wasm_link "$MONO" "$DIST/kome.embedded.mjs" -sEXPORT_ES6=1 -sSINGLE_FILE=1
rm -rf "$(dirname "$MONO")"

# The MIT license text must ship inside the tarball (npm only auto-includes a
# LICENSE at the package root, and the package root is bindings/wasm/).
cp LICENSE bindings/wasm/LICENSE

VERSION="$(sed -n 's/^project(sync_engine VERSION \([0-9.]*\).*/\1/p' CMakeLists.txt)"
(cd bindings/wasm && npm pkg set version="$VERSION")

ls -la "$DIST"
echo "built npm artifacts in $DIST (kome-sync $VERSION)"
