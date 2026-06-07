#!/usr/bin/env bash
# Compile the transport-agnostic GoogleTest suites to WebAssembly and run them
# under Node — so the WASM target literally passes the same scenario tests as
# the native UDP/TCP/WS builds, not just a hand-written subset.
#
# emcmake points CMake at the Emscripten toolchain and sets
# CMAKE_CROSSCOMPILING_EMULATOR=node, so each gtest binary builds to a .js/.wasm
# pair and `ctest` invokes it as `node <test>.js`. Native-only suites (real
# sockets, fork, threads, --wrap) are gated out in CMakeLists.txt under
# `if(NOT EMSCRIPTEN)`.
#
#   tools/wasm_tests.sh            # build-emtest/, run all WASM gtest suites
#   tools/wasm_tests.sh -R crypto  # extra args are forwarded to ctest
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BUILD=build-emtest

command -v emcmake >/dev/null || { echo "emcmake not found (install emscripten)"; exit 1; }
command -v node    >/dev/null || { echo "node not found"; exit 1; }

emcmake cmake -B "$BUILD" -DSYNC_BUILD_TESTS=ON -DCMAKE_BUILD_TYPE=Release
cmake --build "$BUILD" -j"$(nproc 2>/dev/null || echo 4)"

# Emscripten sets CMAKE_CROSSCOMPILING_EMULATOR=node, so ctest runs node <t>.js.
ctest --test-dir "$BUILD" --output-on-failure "$@"
