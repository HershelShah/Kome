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
option(SYNC_AMALGAMATION
       "Build the engine from the generated single-file amalgamation (M7)" OFF)

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
    src/blob.cpp
    src/transport/reliable.cpp
    src/transport/udp.cpp
    src/transport/stun.cpp
    src/transport/cookie.cpp
    src/transport/relay.cpp
    src/transport/rendezvous.cpp
    src/transport/connection.cpp
    src/transport/tcp.cpp
    src/transport/tcp_relay.cpp
    src/transport/ws.cpp
)

# Compile the sources once into an OBJECT library; the static and shared libs
# both reuse it (no double compile, no repeated include/link config).
#
# With SYNC_AMALGAMATION=ON the engine is instead built from the generated
# single-file amalgamation (tools/amalgamate.py) — the same suite then gates
# the two-file artifact releases ship. monocypher is inside kome.cpp, so the
# separate static lib must not also be linked (duplicate definitions).
if(SYNC_AMALGAMATION)
    # The fuzzers compile the per-file sources and the chaos test runs the
    # (amalgamation-excluded) meshnode demo — combining either with the
    # amalgamated engine would silently test the wrong artifact.
    if(SYNC_FUZZ OR SYNC_CHAOS)
        message(FATAL_ERROR "SYNC_AMALGAMATION is incompatible with "
                            "SYNC_FUZZ/SYNC_CHAOS (they build the per-file "
                            "sources / the excluded demo daemons)")
    endif()
    message(STATUS "SYNC_AMALGAMATION: engine built from generated kome.cpp; "
                   "monocypher-linking demos (node/meshnode/netnode/netmesh) "
                   "are excluded")
    find_package(Python3 REQUIRED COMPONENTS Interpreter)
    set(SYNC_AMALG_DIR ${CMAKE_BINARY_DIR}/amalgamation)
    file(GLOB_RECURSE SYNC_AMALG_INPUTS CONFIGURE_DEPENDS
         ${CMAKE_SOURCE_DIR}/src/*.cpp
         ${CMAKE_SOURCE_DIR}/src/*.h
         ${CMAKE_SOURCE_DIR}/src/*.hpp)
    add_custom_command(
        OUTPUT ${SYNC_AMALG_DIR}/kome.cpp ${SYNC_AMALG_DIR}/kome.h
        COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/tools/amalgamate.py
                -o ${SYNC_AMALG_DIR}
        DEPENDS ${CMAKE_SOURCE_DIR}/tools/amalgamate.py
                ${SYNC_AMALG_INPUTS}
                ${CMAKE_SOURCE_DIR}/include/sync_engine.h
                ${CMAKE_SOURCE_DIR}/third_party/monocypher/monocypher.c
                ${CMAKE_SOURCE_DIR}/third_party/monocypher/monocypher.h
        COMMENT "Generating single-file amalgamation (tools/amalgamate.py)")
    add_library(sync_engine_obj OBJECT ${SYNC_AMALG_DIR}/kome.cpp)
    # monocypher's definitions live inside kome.cpp; consumers (tests) still
    # include its header, so export the include path without the library.
    target_include_directories(sync_engine_obj
        PUBLIC ${CMAKE_SOURCE_DIR}/third_party/monocypher)
else()
    add_library(sync_engine_obj OBJECT ${SYNC_SOURCES})
    target_link_libraries(sync_engine_obj PUBLIC monocypher)
endif()
set_target_properties(sync_engine_obj PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_include_directories(sync_engine_obj
    PUBLIC  ${CMAKE_SOURCE_DIR}/include
    PRIVATE ${CMAKE_SOURCE_DIR}/src
            ${CMAKE_SOURCE_DIR}/third_party/monocypher
)
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

    # Wheel packaging (M7, pyproject.toml): when driven by scikit-build-core
    # (which defines SKBUILD), install the shared library inside the Python
    # package so the wheel is self-contained. Gated so a plain
    # `cmake --install` doesn't scatter a Python-package layout into the
    # prefix for C/C++ consumers.
    if(SKBUILD)
        install(TARGETS sync_engine_shared
                LIBRARY DESTINATION kome/_lib
                COMPONENT python)
    endif()

    # --- Example -----------------------------------------------------------
    add_executable(example examples/example.c)
    target_link_libraries(example PRIVATE sync_engine)

    # Demo/test daemons that link the monocypher static lib directly (they
    # use crypto internals) — incompatible with the amalgamated engine, which
    # already carries monocypher's definitions.
    if(NOT SYNC_AMALGAMATION)
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

        # komed: the generic, config-driven, always-on peer daemon. Drives the
        # same secure production path as netnode/netmesh (Noise XX + identity
        # proof + capability-scoped reconcile), so it needs monocypher linked
        # directly like they do (incompatible with the amalgamated engine).
        add_executable(komed services/komed/komed_main.cpp)
        target_link_libraries(komed PRIVATE sync_engine monocypher)
        target_include_directories(komed PRIVATE
            ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/third_party/monocypher)
    endif() # NOT SYNC_AMALGAMATION

    # Infrastructure daemons (M5): blind relay + endpoint-broker rendezvous.
    add_executable(relayd services/relay/relay_main.cpp)
    target_link_libraries(relayd PRIVATE sync_engine)
    target_include_directories(relayd PRIVATE ${CMAKE_SOURCE_DIR}/src)
    add_executable(rendezvousd services/rendezvous/rendezvous_main.cpp)
    target_link_libraries(rendezvousd PRIVATE sync_engine)
    target_include_directories(rendezvousd PRIVATE ${CMAKE_SOURCE_DIR}/src)

    # Blind TCP store-and-forward relay (issue #49): persistent-connection
    # counterpart to relayd for NATed/CGNAT clients that can't receive UDP.
    add_executable(tcp-relayd services/tcp_relay/tcp_relay_main.cpp)
    target_link_libraries(tcp-relayd PRIVATE sync_engine)
    target_include_directories(tcp-relayd PRIVATE ${CMAKE_SOURCE_DIR}/src)

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
    sync_add_test(scan_test tests/scan_test.cpp)
    sync_add_test(blob_test tests/blob_test.cpp)

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

        # Blind TCP relay (issue #49): in-process logic/auth/caps suite, plus
        # a real-sockets suite (background server thread, service_test's
        # pattern) covering the wire protocol and the offline-convergence e2e.
        sync_add_test(tcp_relay_test tests/tcp_relay_test.cpp)
        sync_add_test(tcp_relay_service_test tests/tcp_relay_service_test.cpp
                      LIBS Threads::Threads)

        # komed E2E test: two standalone komed processes, two durable SQLite
        # databases, syncing over real UDP through the production secure
        # path. Only registered where the komed target itself is built (it
        # is skipped, like komed, under SYNC_AMALGAMATION).
        #
        # It loads libsync_engine.so a second time via Python ctypes (the
        # test's verification steps use the Python binding directly, outside
        # the komed processes). Under an active ASan/TSan build that second,
        # non-LD_PRELOADed load of the sanitizer-instrumented .so fails
        # ("ASan runtime does not come first in initial library list" /
        # "libtsan.so.2: cannot allocate memory in static TLS block") — not a
        # real product bug, so pass the active sanitizer through and have the
        # script skip (exit 77, wired to SKIP_RETURN_CODE below) rather than
        # report a false failure. UBSan has no such runtime-preload
        # requirement and still runs the test.
        if(TARGET komed)
            add_test(NAME komed_test
                     COMMAND bash ${CMAKE_SOURCE_DIR}/tests/komed_test.sh)
            set_tests_properties(komed_test PROPERTIES
                ENVIRONMENT
                  "KOMED_BIN=$<TARGET_FILE:komed>;SYNC_ENGINE_LIB=$<TARGET_FILE:sync_engine_shared>;KOMED_TEST_SANITIZER=${SYNC_SANITIZER}"
                TIMEOUT 180
                SKIP_RETURN_CODE 77)
        endif()

        # tcp-relayd E2E test (issue #49): a small signed client binary
        # (tests/tcp_relay_probe.cpp) drives a real tcp-relayd process over a
        # loopback socket. Guarded on tcp-relayd existing, mirroring the
        # komed_test guard above, so a build configuration that ever excludes
        # the native daemons doesn't register a shell test with nothing to
        # drive it.
        if(TARGET tcp-relayd)
            add_executable(tcp_relay_probe tests/tcp_relay_probe.cpp)
            target_link_libraries(tcp_relay_probe PRIVATE sync_engine)
            target_include_directories(tcp_relay_probe PRIVATE ${CMAKE_SOURCE_DIR}/src)

            add_test(NAME tcp_relayd_test
                     COMMAND bash ${CMAKE_SOURCE_DIR}/tests/tcp_relayd_test.sh)
            set_tests_properties(tcp_relayd_test PROPERTIES
                ENVIRONMENT
                  "TCP_RELAYD_BIN=$<TARGET_FILE:tcp-relayd>;TCP_RELAY_PROBE_BIN=$<TARGET_FILE:tcp_relay_probe>;TCP_RELAYD_TEST_SANITIZER=${SYNC_SANITIZER}"
                TIMEOUT 120
                SKIP_RETURN_CODE 77)
        endif()

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
