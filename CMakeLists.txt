cmake_minimum_required(VERSION 3.16)
project(Kome VERSION 0.0.1 LANGUAGES C CXX)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# --- Options ---------------------------------------------------------------
option(KOME_SANITIZER "Enable sanitizer (address, thread, undefined)" "")
option(KOME_USE_SQLCIPHER "Use SQLCipher instead of vendored SQLite for encrypted database support" OFF)

# --- Compiler flags --------------------------------------------------------
add_compile_options(-Wall -Wextra -Wpedantic -fstack-protector-strong)
add_compile_definitions($<$<NOT:$<CONFIG:Debug>>:_FORTIFY_SOURCE=2>)

# Linker hardening (non-Apple Unix)
if(UNIX AND NOT APPLE)
    add_link_options(-Wl,-z,relro -Wl,-z,now -Wl,-z,noexecstack)
endif()

if(KOME_SANITIZER)
    add_compile_options(-fsanitize=${KOME_SANITIZER} -fno-omit-frame-pointer)
    add_link_options(-fsanitize=${KOME_SANITIZER})
endif()

# --- SQLite backend --------------------------------------------------------
if(KOME_USE_SQLCIPHER)
    # Use system SQLCipher (drop-in SQLite replacement with encryption).
    # Requires libsqlcipher to be installed (e.g. apt install libsqlcipher-dev).
    find_package(PkgConfig REQUIRED)
    pkg_check_modules(SQLCIPHER REQUIRED IMPORTED_TARGET sqlcipher)
    add_library(sqlite3 ALIAS PkgConfig::SQLCIPHER)
else()
    # Vendored plain SQLite — PRAGMA key is a no-op (no encryption).
    add_library(sqlite3 STATIC vendor/sqlite3.c)
    set_target_properties(sqlite3 PROPERTIES POSITION_INDEPENDENT_CODE ON)
    target_include_directories(sqlite3 PUBLIC vendor)
    target_compile_definitions(sqlite3 PRIVATE
        SQLITE_THREADSAFE=1
        SQLITE_DEFAULT_WAL_SYNCHRONOUS=1
        SQLITE_OMIT_LOAD_EXTENSION
    )
    # Suppress warnings in vendored code
    target_compile_options(sqlite3 PRIVATE -w)
endif()

# --- Vendored CWPack -------------------------------------------------------
add_library(cwpack STATIC vendor/cwpack.c)
set_target_properties(cwpack PROPERTIES POSITION_INDEPENDENT_CODE ON)
target_include_directories(cwpack PUBLIC vendor)
target_compile_options(cwpack PRIVATE -w)

# --- Kome library ----------------------------------------------------------
set(KOME_SOURCES
    src/kome_engine.cpp
    src/kome_log.cpp
    src/kome_util.cpp
    src/kome_wire.cpp
    src/kome_conflict.cpp
    src/kome_sync.cpp
    src/kome_relay_transport.cpp
    src/kome_easy.cpp
)

add_library(kome SHARED ${KOME_SOURCES})
target_include_directories(kome
    PUBLIC  $<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/include>
    PRIVATE ${CMAKE_SOURCE_DIR}/src
            ${CMAKE_SOURCE_DIR}/vendor
)
target_link_libraries(kome PRIVATE sqlite3 cwpack)
target_compile_definitions(kome PRIVATE KOME_BUILDING)
set_target_properties(kome PROPERTIES
    C_VISIBILITY_PRESET hidden
    CXX_VISIBILITY_PRESET hidden
    VISIBILITY_INLINES_HIDDEN ON
)

add_library(kome_static STATIC ${KOME_SOURCES})
target_include_directories(kome_static
    PUBLIC  $<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/include>
    PRIVATE ${CMAKE_SOURCE_DIR}/src
            ${CMAKE_SOURCE_DIR}/vendor
)
target_link_libraries(kome_static PRIVATE sqlite3 cwpack)
target_compile_definitions(kome_static PRIVATE KOME_BUILDING)

# Link pthreads and dl on Linux
if(UNIX AND NOT APPLE)
    target_link_libraries(kome PRIVATE pthread dl)
    target_link_libraries(kome_static PRIVATE pthread dl)
endif()

# --- Tests -----------------------------------------------------------------
include(FetchContent)
FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG        v1.14.0
)
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

enable_testing()

function(kome_add_test name src)
    add_executable(${name} ${src})
    target_link_libraries(${name} PRIVATE kome_static gtest_main)
    target_include_directories(${name} PRIVATE
        ${CMAKE_SOURCE_DIR}/src
        ${CMAKE_SOURCE_DIR}/vendor
    )
    add_test(NAME ${name} COMMAND ${name})
endfunction()

kome_add_test(test_engine   tests/gtest_engine.cpp)
kome_add_test(test_wire     tests/gtest_wire.cpp)
kome_add_test(test_conflict tests/gtest_conflict.cpp)
kome_add_test(test_sync     tests/gtest_sync.cpp)
kome_add_test(test_replication tests/gtest_replication.cpp)
kome_add_test(test_edge_cases tests/gtest_edge_cases.cpp)
kome_add_test(test_namespace_config tests/gtest_namespace_config.cpp)
kome_add_test(test_encryption tests/gtest_encryption.cpp)
kome_add_test(test_easy_and_relay tests/gtest_easy_and_relay.cpp)

# --- Install rules ---------------------------------------------------------
include(GNUInstallDirs)
include(CMakePackageConfigHelpers)

install(TARGETS kome
    EXPORT KomeTargets
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
)
install(TARGETS kome_static
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
)
install(FILES
    include/kome.h
    src/kome_easy.h
    src/kome_relay_transport.h
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

# pkg-config
configure_file(kome.pc.in kome.pc @ONLY)
install(FILES ${CMAKE_BINARY_DIR}/kome.pc
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/pkgconfig)

# CMake find_package support
install(EXPORT KomeTargets
    FILE KomeTargets.cmake
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Kome)

configure_package_config_file(
    cmake/KomeConfig.cmake.in
    ${CMAKE_BINARY_DIR}/KomeConfig.cmake
    INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Kome
)
write_basic_package_version_file(
    ${CMAKE_BINARY_DIR}/KomeConfigVersion.cmake
    COMPATIBILITY SameMajorVersion
)
install(FILES
    ${CMAKE_BINARY_DIR}/KomeConfig.cmake
    ${CMAKE_BINARY_DIR}/KomeConfigVersion.cmake
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Kome
)
