# Shared definitions for the WASM builds — sourced by tools/wasm_build.sh
# (dev/CI build into build-wasm/) and tools/npm_build.sh (npm package
# artifacts), so the source list, exported ABI, and compiler flags cannot
# drift between the two.
#
# Transport (sockets) is excluded: a browser node does I/O via its native
# WebSocket and drives the reconciliation session through the exported ABI.

WASM_CPP="src/sync_engine.cpp src/sha256.cpp src/storage.cpp src/codec.cpp \
     src/reconcile.cpp src/crypto.cpp src/capability.cpp src/invite.cpp \
     src/noise.cpp"

WASM_EXPORTS='["_sync_engine_create","_sync_engine_open","_sync_engine_destroy",
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

# Compile the vendored C dep as C (em++ would treat .c as C++).
#   $1 = output object path
wasm_build_monocypher() {
    emcc -O2 -w -Ithird_party/monocypher \
         -c third_party/monocypher/monocypher.c -o "$1"
}

# Link the engine to a modularized WASM module.
#   $1 = monocypher object, $2 = output (.js or .mjs), rest = extra emcc flags
#   (e.g. -sEXPORT_ES6=1 for an ES module, -sSINGLE_FILE=1 to embed the wasm)
# WASM_ENV overrides the target environments (default web,node); the ES6
# builds use web,worker so emscripten's Node path — which references
# __dirname, a ReferenceError in ES modules on this emscripten version —
# isn't in the artifact at all.
wasm_link() {
    local mono="$1" out="$2"
    shift 2
    em++ -O2 -std=c++17 -w \
        -Iinclude -Isrc -Ithird_party/monocypher \
        $WASM_CPP "$mono" \
        -sMODULARIZE=1 -sEXPORT_NAME=createSyncEngine \
        -sENVIRONMENT="${WASM_ENV:-web,node}" \
        -sALLOW_MEMORY_GROWTH=1 -sWASM_BIGINT \
        -sEXPORTED_FUNCTIONS="$(echo "$WASM_EXPORTS" | tr -d '\n ')" \
        -sEXPORTED_RUNTIME_METHODS='["ccall","cwrap","getValue","setValue","UTF8ToString","HEAPU8","HEAPU32"]' \
        "$@" -o "$out"
}
