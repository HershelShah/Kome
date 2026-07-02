/* kome-sync — ES module entry (Node import, and what bundlers/browsers get
 * via the "browser"/"import" conditions).
 *
 * Node uses the CommonJS engine build: this emscripten version's EXPORT_ES6
 * output references __dirname on its Node path, which doesn't exist in ES
 * modules. Browsers/bundlers get the ES6 engine build via dynamic import —
 * the Node-only code in it is dead there. */
import bindingCjs from "./binding.cjs";

const { Binding } = bindingCjs;

// Static `new URL(..., import.meta.url)` so bundlers (vite, webpack 5) emit
// the wasm as an asset and rewrite the URL.
const wasmUrl = new URL("./dist/kome.wasm", import.meta.url);

const isNode =
  typeof process !== "undefined" && !!(process.versions && process.versions.node);

async function load() {
  if (isNode) {
    const { fileURLToPath } = await import("node:url");
    return bindingCjs.loadCjs(
      fileURLToPath(new URL("./dist/kome.cjs.js", import.meta.url)));
  }
  const { default: createSyncEngine } = await import("./dist/kome.mjs");
  const M = await createSyncEngine({
    locateFile: (f) => (f.endsWith(".wasm") ? wasmUrl.href : f),
  });
  return new Binding(M);
}

export { load, Binding };
