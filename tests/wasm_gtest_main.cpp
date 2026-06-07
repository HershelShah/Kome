// A GoogleTest entry point compiled directly into each WASM test executable.
//
// Two Emscripten quirks make this necessary (instead of linking gtest_main):
//
//  1. Emscripten emits the callMain that actually runs the program only when it
//     sees main() among its *direct* link inputs. A main() living solely inside
//     the gtest_main static archive is invisible to that scan, so the test
//     would load and exit 0 without running a single case.
//
//  2. This toolchain version wires callMain to the `main`/`__main_void` symbol
//     (emitted by `int main(void)`), not to `__main_argc_argv` (emitted by
//     `int main(int, char**)`). So the entry point must take no arguments.
//
// We don't forward command-line args to gtest on the WASM run — ctest invokes
// each binary with no filter, running the whole suite, which is exactly what
// "all transports pass all the scenarios" requires. Used only for EMSCRIPTEN;
// the native build keeps upstream gtest_main.
#include "gtest/gtest.h"

int main() {
  int argc = 1;
  char arg0[] = "wasm_test";
  char *argv[] = {arg0, nullptr};
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
