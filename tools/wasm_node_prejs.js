// Injected via --pre-js into every WASM gtest binary so it runs under Node.
//
// Emscripten's loader (this toolchain version) reaches for a global fetch()
// whenever one exists and tries to fetch() the .wasm by filesystem path. Node
// 22 exposes such a global fetch, which then fails on a bare path. Hiding it
// makes the loader fall back to its ArrayBuffer path (fs.readFileSync), which
// is what we want for a local Node test run.
if (typeof globalThis !== "undefined") {
  globalThis.fetch = undefined;
}
