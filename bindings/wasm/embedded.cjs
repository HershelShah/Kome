/* kome-sync/embedded — CommonJS entry over the single-file build (the wasm is
 * base64-embedded in the JS: no asset pipeline, ~33% larger download). */
"use strict";
const path = require("path");
const { Binding } = require("./binding.cjs");

async function load() {
  const createSyncEngine = require(path.join(__dirname, "dist", "kome.embedded.cjs.js"));
  const M = await createSyncEngine();
  return new Binding(M);
}

module.exports = { load, Binding };
