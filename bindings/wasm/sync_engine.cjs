/* sync_engine.cjs — repo dev-flow binding over the build-wasm/ output.
 *
 * The API implementation lives in binding.cjs (shared with the npm package
 * entries, index.cjs / index.mjs). This shim only supplies the dev default:
 * the module tools/wasm_build.sh puts in build-wasm/.
 *
 *   tools/wasm_build.sh && node bindings/wasm/parity.cjs
 */
"use strict";
const path = require("path");
const { Binding, loadCjs } = require("./binding.cjs");

async function load(modulePath) {
  const jsPath = modulePath || path.join(__dirname, "../../build-wasm/sync_engine.js");
  return loadCjs(jsPath);
}

module.exports = { load, Binding };
