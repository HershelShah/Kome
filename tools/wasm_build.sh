#!/usr/bin/env bash
# Compile the engine core to WebAssembly so a browser can be a full node.
# Transport (sockets) is excluded — the browser does I/O via its native
# WebSocket and drives the reconciliation session through the exported ABI.
#
#   tools/wasm_build.sh   ->   build-wasm/sync_engine.{js,wasm}
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT=build-wasm
mkdir -p "$OUT"

# C deps compiled as C (em++ would treat .c as C++).
emcc -O2 -w -DSQLITE_THREADSAFE=0 -DSQLITE_OMIT_LOAD_EXTENSION \
     -Ithird_party/sqlite -c third_party/sqlite/sqlite3.c -o "$OUT/sqlite3.o"
emcc -O2 -w -Ithird_party/monocypher -c third_party/monocypher/monocypher.c \
     -o "$OUT/monocypher.o"

CPP="src/sync_engine.cpp src/sha256.cpp src/storage.cpp src/codec.cpp \
     src/reconcile.cpp src/crypto.cpp src/capability.cpp src/invite.cpp \
     src/noise.cpp"

EXPORTS='["_sync_engine_create","_sync_engine_open","_sync_engine_destroy",
"_sync_engine_flush","_sync_engine_identity","_sync_engine_site_id",
"_sync_engine_set","_sync_engine_delete","_sync_engine_get","_sync_engine_exists",
"_sync_engine_export","_sync_changes_free","_sync_engine_apply","_sync_engine_digest",
"_sync_free","_sync_strerror","_sync_abi_version","_sync_change_encode",
"_sync_change_decode","_sync_change_free_decoded","_sync_change_sign",
"_sync_session_begin","_sync_session_begin_scoped","_sync_session_step",
"_sync_session_end","_sync_capability_root","_sync_capability_delegate",
"_sync_capability_encode","_sync_capability_decode","_sync_capability_subject",
"_sync_engine_grant","_sync_capability_free","_sync_invite_encode",
"_sync_invite_decode","_sync_engine_set_logger","_malloc","_free"]'

em++ -O2 -std=c++17 -w \
  -Iinclude -Isrc -Ithird_party/sqlite -Ithird_party/monocypher \
  $CPP "$OUT/sqlite3.o" "$OUT/monocypher.o" \
  -sMODULARIZE=1 -sEXPORT_NAME=createSyncEngine -sENVIRONMENT=web,node \
  -sALLOW_MEMORY_GROWTH=1 -sEXPORTED_FUNCTIONS="$(echo "$EXPORTS" | tr -d '\n ')" \
  -sEXPORTED_RUNTIME_METHODS='["ccall","cwrap","getValue","setValue","UTF8ToString","HEAPU8","HEAPU32"]' \
  -o "$OUT/sync_engine.js"

ls -la "$OUT"/sync_engine.js "$OUT"/sync_engine.wasm
echo "built $OUT/sync_engine.{js,wasm}"
