/* kome-sync — CommonJS entry (Node require). Browsers and bundlers resolve
 * the "browser"/"import" conditions to index.mjs instead. */
"use strict";
const path = require("path");
const { Binding, loadCjs } = require("./binding.cjs");

async function load() {
  return loadCjs(path.join(__dirname, "dist", "kome.cjs.js"));
}

module.exports = { load, Binding };
