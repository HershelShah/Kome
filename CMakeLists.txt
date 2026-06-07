cmake_minimum_required(VERSION 3.16)
project(sync_engine VERSION 0.1.0 LANGUAGES C CXX)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# --- Options ---------------------------------------------------------------
option(SYNC_SANITIZER "Enable a sanitizer (address, thread, undefined)" "")
option(SYNC_BUILD_TESTS "Build the test suite" ON)

# --- Compiler flags --------------------------------------------------------
add_compile_options(-Wall -Wextra -Wpedantic -fstack-protector-strong)

if(SYNC_SANITIZER)
    add_compile_options(-fsanitize=${SYNC_SANITIZER} -fno-omit-frame-pointer -g)
    add_link_options(-fsanitize=${SYNC_SANITIZER})
endif()

# --- Vendored SQLite (M2) --------------------------------------------------
add_library(sqlite3 STATIC third_party/sqlite/sqlite3.c)
set_target_properties(sqlite3 PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_include_directories(sqlite3 PUBLIC third_party/sqlite)
target_compile_definitions(sqlite3 PRIVATE
    SQLITE_THREADSAFE=1
    SQLITE_DEFAULT_WAL_SYNCHRONOUS=1
    SQLITE_OMIT_LOAD_EXTENSION
)
target_compile_options(sqlite3 PRIVATE -w)

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
    src/noise.cpp
    src/transport/reliable.cpp
    src/transport/udp.cpp
    src/transport/stun.cpp
    src/transport/relay.cpp
)

add_library(sync_engine STATIC ${SYNC_SOURCES})
target_include_directories(sync_engine
    PUBLIC  ${CMAKE_SOURCE_DIR}/include
    PRIVATE ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/third_party/sqlite
            ${CMAKE_SOURCE_DIR}/third_party/monocypher
)
target_link_libraries(sync_engine PRIVATE sqlite3 monocypher)
if(UNIX AND NOT APPLE)
    target_link_libraries(sync_engine PRIVATE pthread dl)
endif()

# Shared library for language bindings (Python, M6).
add_library(sync_engine_shared SHARED ${SYNC_SOURCES})
set_target_properties(sync_engine_shared PROPERTIES OUTPUT_NAME sync_engine)
target_include_directories(sync_engine_shared
    PUBLIC  ${CMAKE_SOURCE_DIR}/include
    PRIVATE ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/third_party/sqlite
            ${CMAKE_SOURCE_DIR}/third_party/monocypher
)
target_link_libraries(sync_engine_shared PRIVATE sqlite3 monocypher)
if(UNIX AND NOT APPLE)
    target_link_libraries(sync_engine_shared PRIVATE pthread dl)
endif()

# --- Example ---------------------------------------------------------------
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

    function(sync_add_test name src)
        add_executable(${name} ${src})
        target_link_libraries(${name} PRIVATE sync_engine gtest_main)
        target_include_directories(${name} PRIVATE ${CMAKE_SOURCE_DIR}/src)
        add_test(NAME ${name} COMMAND ${name})
    endfunction()

    sync_add_test(convergence_test tests/convergence_test.cpp)
    sync_add_test(storage_test tests/storage_test.cpp)
    target_link_libraries(storage_test PRIVATE sqlite3)
    target_include_directories(storage_test PRIVATE
        ${CMAKE_SOURCE_DIR}/third_party/sqlite)

    sync_add_test(reconcile_test tests/reconcile_test.cpp)

    sync_add_test(crypto_test tests/crypto_test.cpp)
    target_link_libraries(crypto_test PRIVATE monocypher)
    target_include_directories(crypto_test PRIVATE
        ${CMAKE_SOURCE_DIR}/third_party/monocypher)

    sync_add_test(security_test tests/security_test.cpp)
    target_link_libraries(security_test PRIVATE monocypher)
    target_include_directories(security_test PRIVATE
        ${CMAKE_SOURCE_DIR}/third_party/monocypher)

    sync_add_test(network_test tests/network_test.cpp)

    sync_add_test(relay_test tests/relay_test.cpp)
    target_link_libraries(relay_test PRIVATE monocypher)
    target_include_directories(relay_test PRIVATE
        ${CMAKE_SOURCE_DIR}/third_party/monocypher)

    sync_add_test(hardening_test tests/hardening_test.cpp)

    sync_add_test(threading_test tests/threading_test.cpp)
    find_package(Threads REQUIRED)
    target_link_libraries(threading_test PRIVATE Threads::Threads)

    sync_add_test(multinode_test tests/multinode_test.cpp)

    sync_add_test(resilience_test tests/resilience_test.cpp)

    sync_add_test(scenario_test tests/scenario_test.cpp)
endif()

# --- Fuzz targets (libFuzzer; needs a clang with the fuzzer runtime) -------
option(SYNC_FUZZ "Build libFuzzer targets (requires clang + fuzzer runtime)" OFF)
if(SYNC_FUZZ)
    foreach(fz change_decode capability_decode session)
        add_executable(fuzz_${fz} tests/fuzz/fuzz_${fz}.cc ${SYNC_SOURCES})
        target_include_directories(fuzz_${fz} PRIVATE
            ${CMAKE_SOURCE_DIR}/include ${CMAKE_SOURCE_DIR}/src
            ${CMAKE_SOURCE_DIR}/third_party/sqlite
            ${CMAKE_SOURCE_DIR}/third_party/monocypher)
        target_link_libraries(fuzz_${fz} PRIVATE sqlite3 monocypher)
        target_compile_options(fuzz_${fz} PRIVATE -fsanitize=fuzzer,address)
        target_link_options(fuzz_${fz} PRIVATE -fsanitize=fuzzer,address)
    endforeach()
endif()
