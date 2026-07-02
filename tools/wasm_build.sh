#!/usr/bin/env bash
# Compile the engine core to WebAssembly so a browser can be a full node.
# Shared source list / ABI / flags live in tools/wasm_flags.sh (also used by
# tools/npm_build.sh for the npm package artifacts).
#
#   tools/wasm_build.sh   ->   build-wasm/sync_engine.{js,wasm}
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
source tools/wasm_flags.sh

OUT=build-wasm
mkdir -p "$OUT"

wasm_build_monocypher "$OUT/monocypher.o"
wasm_link "$OUT/monocypher.o" "$OUT/sync_engine.js"

ls -la "$OUT"/sync_engine.js "$OUT"/sync_engine.wasm
echo "built $OUT/sync_engine.{js,wasm}"
