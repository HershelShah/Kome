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

# --- sync_engine library ---------------------------------------------------
set(SYNC_SOURCES
    src/sync_engine.cpp
    src/sha256.cpp
    src/storage.cpp
)

add_library(sync_engine STATIC ${SYNC_SOURCES})
target_include_directories(sync_engine
    PUBLIC  ${CMAKE_SOURCE_DIR}/include
    PRIVATE ${CMAKE_SOURCE_DIR}/src ${CMAKE_SOURCE_DIR}/third_party/sqlite
)
target_link_libraries(sync_engine PRIVATE sqlite3)
if(UNIX AND NOT APPLE)
    target_link_libraries(sync_engine PRIVATE pthread dl)
endif()

# --- Example ---------------------------------------------------------------
add_executable(example examples/example.c)
target_link_libraries(example PRIVATE sync_engine)

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
endif()
