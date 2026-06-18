cmake_minimum_required(VERSION 3.16)
project(sync_engine VERSION 0.1.0 LANGUAGES C CXX)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# Default to an optimized build so a bare `cmake -B build` isn't a surprise
# debug build. CI sets the type explicitly where it matters.
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

# --- Options ---------------------------------------------------------------
option(SYNC_SANITIZER "Enable a sanitizer (address, thread, undefined)" "")
option(SYNC_BUILD_TESTS "Build the test suite" ON)
option(SYNC_COVERAGE "Build with gcov instrumentation (use tools/coverage.sh)" OFF)

# --- Compiler flags --------------------------------------------------------
add_compile_options(-Wall -Wextra -Wpedantic)
# Stack protector needs __stack_chk_guard, which Emscripten's libc doesn't ship.
if(NOT EMSCRIPTEN)
    add_compile_options(-fstack-protector-strong)
endif()

if(SYNC_SANITIZER)
    add_compile_options(-fsanitize=${SYNC_SANITIZER} -fno-omit-frame-pointer -g)
    add_link_options(-fsanitize=${SYNC_SANITIZER})
endif()

if(SYNC_COVERAGE)
    # Instrument our code (third_party/gtest are filtered out in the report).
    # Atomic counters keep the threading test's coverage sound.
    add_compile_options(-O0 -g --coverage -fprofile-update=atomic)
    add_link_options(--coverage)
endif()

# --- Emscripten / WASM ------------------------------------------------------
# When configured with emcmake, build the engine + the transport-agnostic test
# suites to WebAssembly and run them under Node (CMAKE_CROSSCOMPILING_EMULATOR
# is set to node by emcmake, so ctest invokes `node <test>.js`). This is how we
# prove the WASM target literally passes the same scenario tests as UDP/TCP/WS.
if(EMSCRIPTEN)
    # Each gtest binary is a Node-run .js module. Real FS (NODERAWFS) lets the
    # storage/durability tests use /tmp; EXIT_RUNTIME makes the process exit
    # with gtest's return code so ctest sees pass/fail; a roomy stack + memory
    # growth keep the larger in-process multinode/scale runs happy.
    add_link_options(
        -sENVIRONMENT=node
        -sNODERAWFS=1
        -sALLOW_MEMORY_GROWTH=1
        -sWASM_BIGINT
        -sEXIT_RUNTIME=1
        -sTOTAL_STACK=4194304
        -sINITIAL_MEMORY=134217728
        # Node 22 exposes a global fetch() that Emscripten's loader tries (and
        # fails) to use on a bare .wasm filesystem path; this pre-js hides it so
        # the loader reads the wasm via fs.readFileSync instead. Synchronous
        # compilation then runs main() during load (so gtest output is flushed
        # before the process exits, instead of in a deferred promise).
        -sWASM_ASYNC_COMPILATION=0
        --pre-js ${CMAKE_SOURCE_DIR}/tools/wasm_node_prejs.js
    )
endif()


# --- Vendored monocypher (M4) ----------------------------------------------
add_library(monocypher STATIC third_party/monocypher/monocypher.c)
set_target_properties(monocypher PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_include_directories(monocypher PUBLIC third_party/monocypher)
target_compile_options(monocypher PRIVATE -w)

# --- sync_engine library ---------------------------------------------------
set(SYNC_SOURCES
    src/sync_engine.cpp
    src/sha256.cpp
    src/storage.cpp
    src/codec.cpp
    src/reconcile.cpp
    src/crypto.cpp
    src/capability.cpp
    src/invite.cpp
    src/noise.cpp
    src/transport/reliable.cpp
    src/transport/udp.cpp
    src/transport/stun.cpp
    src/transport/relay.cpp
    src/transport/rendezvous.cpp
    src/transport/connection.cpp
    src/transport/tcp.cpp
    src/transport/ws.cpp
)

# Compile the sources once into an OBJECT library; the static and shared libs
# both reuse it (no double compile, no repeated include/link config).
add_library(sync_engine_obj OBJECT ${SYNC_SOURCES})
set_target_properties(sync_engine_obj PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_include_directories(sync_engine_obj
    PUBLIC  ${CMAKE_SOURCE_DIR}/include
    PRIVATE ${CMAKE_SOURCE_DIR}/src
            ${CMAKE_SOURCE_DIR}/third_party/monocypher
)
target_link_libraries(sync_engine_obj PUBLIC monocypher)
if(UNIX AND NOT APPLE)
    target_link_libraries(sync_engine_obj PUBLIC pthread dl)
endif()

add_library(sync_engine STATIC)
target_link_libraries(sync_engine PUBLIC sync_engine_obj)

# Native-only artifacts: the shared library (language bindings) and the
# socket/fork-using example + daemon programs. These don't apply to the WASM
# target (a browser node does I/O via its WebSocket and the exported ABI), so
# skip them under Emscripten — only the engine library + gtest suites build.
if(NOT EMSCRIPTEN)
    # Shared library for language bindings (Python, M6).
    add_library(sync_engine_shared SHARED)
    set_target_properties(sync_engine_shared PROPERTIES OUTPUT_NAME sync_engine)
    target_link_libraries(sync_engine_shared PUBLIC sync_engine_obj)

    # --- Example -----------------------------------------------------------
    add_executable(example examples/example.c)
    target_link_libraries(example PRIVATE sync_engine)

    # Two-process end-to-end demo node (uses internal transport/crypto headers).
    add_executable(node examples/node.cpp)
    target_link_libraries(node PRIVATE sync_engine monocypher)
    target_include_directories(node PRIVATE
        ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/third_party/monocypher)

    # Multi-peer gossip daemon for the multi-process mesh demo.
    add_executable(meshnode examples/meshnode.cpp)
    target_link_libraries(meshnode PRIVATE sync_engine monocypher)
    target_include_directories(meshnode PRIVATE
        ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/third_party/monocypher)

    # Deployable node for real-network testing: the production connect_and_sync
    # path + ConnectionManager (rendezvous -> direct/punch -> relay fallback).
    add_executable(netnode examples/netnode.cpp)
    target_link_libraries(netnode PRIVATE sync_engine monocypher)
    target_include_directories(netnode PRIVATE
        ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/third_party/monocypher)

    # Secure multi-peer mesh daemon for real-network scale testing: drives N
    # SecurePeerSession links (Noise XX + identity proof + cap-scoped reconcile)
    # over one socket, gossiping to convergence. Real-network counterpart to the
    # localhost-only meshnode.
    add_executable(netmesh examples/netmesh.cpp)
    target_link_libraries(netmesh PRIVATE sync_engine monocypher)
    target_include_directories(netmesh PRIVATE
        ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/third_party/monocypher)

    # Infrastructure daemons (M5): blind relay + endpoint-broker rendezvous.
    add_executable(relayd services/relay/relay_main.cpp)
    target_link_libraries(relayd PRIVATE sync_engine)
    target_include_directories(relayd PRIVATE ${CMAKE_SOURCE_DIR}/src)
    add_executable(rendezvousd services/rendezvous/rendezvous_main.cpp)
    target_link_libraries(rendezvousd PRIVATE sync_engine)
    target_include_directories(rendezvousd PRIVATE ${CMAKE_SOURCE_DIR}/src)

    # Real-internet STUN interop smoke test: drives the engine's STUN client
    # against a public RFC 5389 server and prints the reflexive endpoint. A
    # one-command check that UDP egress + reflexive discovery work from a host.
    add_executable(stun_interop tools/stun_interop.cpp)
    target_link_libraries(stun_interop PRIVATE sync_engine)
    target_include_directories(stun_interop PRIVATE ${CMAKE_SOURCE_DIR}/src)
endif()

# --- Tests -----------------------------------------------------------------
if(SYNC_BUILD_TESTS)
    include(FetchContent)
    FetchContent_Declare(
        googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG        v1.14.0
    )
    set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(googletest)

    enable_testing()

    # sync_add_test(name src [LIBS lib...]) — a gtest binary linked against the
    # engine. Extra LIBS (e.g. Threads::Threads) are for deps the engine doesn't
    # already expose; sqlite3/monocypher and the third_party include paths come
    # transitively from sync_engine (its deps are PUBLIC), so tests no longer
    # repeat them. On Emscripten we compile our own main() (see
    # tests/wasm_gtest_main.cpp) and link plain gtest; ctest runs the .js node.
    function(sync_add_test name src)
        cmake_parse_arguments(T "" "" "LIBS" ${ARGN})
        if(EMSCRIPTEN)
            add_executable(${name} ${src}
                           ${CMAKE_SOURCE_DIR}/tests/wasm_gtest_main.cpp)
            target_link_libraries(${name} PRIVATE sync_engine gtest ${T_LIBS})
        else()
            add_executable(${name} ${src})
            target_link_libraries(${name} PRIVATE sync_engine gtest_main ${T_LIBS})
        endif()
        target_include_directories(${name} PRIVATE ${CMAKE_SOURCE_DIR}/src)
        add_test(NAME ${name} COMMAND ${name})
    endfunction()

    # --- Transport-agnostic suites: built natively AND for WASM ------------
    # These exercise the engine purely in-process (CRDT core, reconciliation
    # session, storage reopen, in-process Noise + multinode/relay over a sim
    # net, scenarios, capability enforcement) — no real sockets, fork, threads,
    # or --wrap. Under Emscripten they compile to .js/.wasm and run under Node,
    # so the WASM target passes the same scenarios as the UDP/TCP/WS builds.
    sync_add_test(convergence_test tests/convergence_test.cpp)
    sync_add_test(reconcile_test tests/reconcile_test.cpp)
    sync_add_test(crypto_test tests/crypto_test.cpp)
    sync_add_test(security_test tests/security_test.cpp)
    sync_add_test(relay_test tests/relay_test.cpp)
    sync_add_test(multinode_test tests/multinode_test.cpp)
    sync_add_test(resilience_test tests/resilience_test.cpp)
    sync_add_test(scenario_test tests/scenario_test.cpp)
    sync_add_test(defensive_test tests/defensive_test.cpp)
    sync_add_test(securemesh_test tests/securemesh_test.cpp)
    sync_add_test(circles_test tests/circles_test.cpp)
    sync_add_test(messaging_test tests/messaging_test.cpp)

    # Opt-in adversarial / large-scale stress suite (slow; in-process). OFF by
    # default so it stays out of the normal/CI run; enable with -DSYNC_STRESS=ON.
    option(SYNC_STRESS "Build the stress-test suite" OFF)
    if(SYNC_STRESS)
        sync_add_test(stress_test tests/stress_test.cpp)
        set_tests_properties(stress_test PROPERTIES TIMEOUT 600)
    endif()

    # --- Native-only suites ------------------------------------------------
    # These depend on host facilities WASM doesn't provide: real sockets
    # (network/connection/transport_parity/service), fork (storage durability
    # /hardening crash-recovery), pthreads (threading), or linker --wrap (oom).
    # The WASM build covers the same engine logic through the suites above
    # (durability via resilience_test, transport semantics via the session in
    # multinode/scenario), so gating these out leaves no scenario unverified.
    if(NOT EMSCRIPTEN)
        find_package(Threads REQUIRED)

        sync_add_test(storage_test tests/storage_test.cpp)
        sync_add_test(network_test tests/network_test.cpp)
        sync_add_test(hardening_test tests/hardening_test.cpp)
        sync_add_test(threading_test tests/threading_test.cpp LIBS Threads::Threads)
        sync_add_test(service_test tests/service_test.cpp)
        sync_add_test(connection_test tests/connection_test.cpp)
        sync_add_test(transport_parity_test tests/transport_parity_test.cpp
                      LIBS Threads::Threads)

        # OOM fault-injection test (allocation-failure paths). Off by default
        # and out of the sanitizer matrix, where --wrap conflicts with ASan's
        # allocator.
        option(SYNC_OOM_TEST "Build the OOM fault-injection test" OFF)
        if(SYNC_OOM_TEST)
            sync_add_test(oom_test tests/oom_test.cpp)
            target_link_options(oom_test PRIVATE
                -Wl,--wrap=malloc -Wl,--wrap=calloc)
        endif()
    endif()
endif()

# --- Multi-process chaos integration test (slow; opt in) -------------------
option(SYNC_CHAOS "Enable the multi-process chaos integration test" OFF)
if(SYNC_CHAOS)
    add_test(NAME chaos_test
             COMMAND bash ${CMAKE_SOURCE_DIR}/tests/chaos_test.sh 6 12 12)
    set_tests_properties(chaos_test PROPERTIES
        ENVIRONMENT
          "MESHNODE_BIN=$<TARGET_FILE:meshnode>;SYNC_ENGINE_LIB=$<TARGET_FILE:sync_engine_shared>"
        TIMEOUT 120)
endif()

# --- Benchmarks (optimization story) ---------------------------------------
# GoogleBenchmark microbenchmarks over the hot paths (fetched like GoogleTest,
# dev-only). For the truest numbers configure the whole tree Release so the
# engine itself is optimized. Profile with tools/profile.sh (callgrind).
option(SYNC_BENCH "Build the microbenchmark harness (fetches GoogleBenchmark)" OFF)
if(SYNC_BENCH)
    include(FetchContent)
    set(BENCHMARK_ENABLE_TESTING OFF CACHE BOOL "" FORCE)
    set(BENCHMARK_ENABLE_GTEST_TESTS OFF CACHE BOOL "" FORCE)
    set(BENCHMARK_ENABLE_INSTALL OFF CACHE BOOL "" FORCE)
    FetchContent_Declare(
        googlebenchmark
        GIT_REPOSITORY https://github.com/google/benchmark.git
        GIT_TAG        v1.8.3
    )
    FetchContent_MakeAvailable(googlebenchmark)

    add_executable(bench bench/bench_main.cpp)
    target_link_libraries(bench PRIVATE sync_engine benchmark::benchmark_main)
    target_include_directories(bench PRIVATE ${CMAKE_SOURCE_DIR}/src)
    # Always optimize the bench TU; for an honest baseline configure Release so
    # the engine library is optimized too.
    target_compile_options(bench PRIVATE -O2 -g -DNDEBUG -fno-omit-frame-pointer)
endif()

# --- Fuzz targets (libFuzzer; needs a clang with the fuzzer runtime) -------
option(SYNC_FUZZ "Build libFuzzer targets (requires clang + fuzzer runtime)" OFF)
if(SYNC_FUZZ)
    foreach(fz change_decode capability_decode session apply storage noise stun reliable ws invite)
        add_executable(fuzz_${fz} tests/fuzz/fuzz_${fz}.cc ${SYNC_SOURCES})
        target_include_directories(fuzz_${fz} PRIVATE
            ${CMAKE_SOURCE_DIR}/include ${CMAKE_SOURCE_DIR}/src
            ${CMAKE_SOURCE_DIR}/third_party/monocypher)
        target_link_libraries(fuzz_${fz} PRIVATE monocypher)
        target_compile_options(fuzz_${fz} PRIVATE -fsanitize=fuzzer,address)
        target_link_options(fuzz_${fz} PRIVATE -fsanitize=fuzzer,address)
    endforeach()
endif()
