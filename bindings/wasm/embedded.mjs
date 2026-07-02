/* kome-sync/embedded — ES module entry over the single-file build (the wasm
 * is base64-embedded in the JS: no asset pipeline, ~33% larger download).
 *
 * Same environment split as index.mjs: Node loads the CommonJS single-file
 * build (the ES6 output's Node path is broken on this emscripten version);
 * browsers/bundlers get the ES6 single-file build via dynamic import. */
import bindingCjs from "./binding.cjs";

const { Binding } = bindingCjs;

const isNode =
  typeof process !== "undefined" && !!(process.versions && process.versions.node);

async function load() {
  let createSyncEngine;
  if (isNode) {
    const { createRequire } = await import("node:module");
    createSyncEngine = createRequire(import.meta.url)("./dist/kome.embedded.cjs.js");
  } else {
    ({ default: createSyncEngine } = await import("./dist/kome.embedded.mjs"));
  }
  const M = await createSyncEngine();
  return new Binding(M);
}

export { load, Binding };
