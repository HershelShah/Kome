/* CJS smoke for the kome-sync/embedded entry (single-file build). Copy into
 * a project with kome-sync installed, then run. */
"use strict";
const { load } = require("kome-sync/embedded");

(async () => {
  const k = await load();
  const a = k.create(new Uint8Array(32).fill(3));
  const b = k.create(new Uint8Array(32).fill(4));
  k.set(a, "ns", "x", "f", "y");
  k.sync(a, b);
  if (!k.exists(b, "ns", "x")) throw new Error("embedded CJS smoke failed");
  console.log("embedded CJS smoke: OK");
})().catch((e) => { console.error(e); process.exit(1); });
