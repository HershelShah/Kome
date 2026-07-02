/* kome-sync/embedded — CommonJS entry over the single-file build (the wasm is
 * base64-embedded in the JS: no asset pipeline, ~33% larger download). */
"use strict";
const { Binding } = require("./binding.cjs");

async function load() {
  // Literal relative require: resolves against this file's directory and
  // stays statically analyzable for bundlers consuming the CJS entry.
  const createSyncEngine = require("./dist/kome.embedded.cjs.js");
  const M = await createSyncEngine();
  return new Binding(M);
}

module.exports = { load, Binding };
