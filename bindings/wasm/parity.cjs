/* parity.cjs — run the SAME scenarios as tests/transport_parity_test.cpp, but
 * with the engine compiled to WASM, so we know it works in WASM in every case
 * the native UDP/TCP/WS paths do. The reconciliation runs through the session
 * (the transport-agnostic message pump a browser drives over its WebSocket).
 *
 *   tools/wasm_build.sh && node bindings/wasm/parity.cjs
 */
"use strict";
const path = require("path");
const { load } = require("./sync_engine.cjs");

const enc = (s) => new TextEncoder().encode(s);
const eqBytes = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);

let failed = 0;
function check(name, cond, msg) {
  if (cond) { console.log("  ok   " + name); }
  else { console.log("  FAIL " + name + (msg ? " — " + msg : "")); failed++; }
}

(async () => {
  const k = await load(path.join(__dirname, "../../build-wasm/sync_engine.js"));
  const seed = (v) => new Uint8Array(32).fill(v);
  let s = 1;
  const eng = () => k.create(seed(s++));

  console.log("ABI " + k.abiVersion());
  check("abi-version", k.abiVersion() === 4);

  // BasicConverge: independent writes on both sides converge.
  {
    const a = eng(), b = eng();
    for (let i = 0; i < 30; i++) {
      k.set(a, "ns", "a" + i, "f", "v" + i);
      k.set(b, "ns", "b" + i, "f", "v" + i);
    }
    k.sync(a, b);
    let all = eqBytes(k.digest(a), k.digest(b));
    for (let i = 0; i < 30; i++)
      all = all && k.exists(a, "ns", "b" + i) && k.exists(b, "ns", "a" + i);
    check("BasicConverge", all);
    k.destroy(a); k.destroy(b);
  }

  // Conflict: same-cell writes resolve to one deterministic winner.
  {
    const a = eng(), b = eng();
    k.set(a, "ns", "cell", "f", "from-A");
    k.set(b, "ns", "cell", "f", "from-B");
    k.sync(a, b);
    check("Conflict",
          eqBytes(k.get(a, "ns", "cell", "f"), k.get(b, "ns", "cell", "f")) &&
          eqBytes(k.digest(a), k.digest(b)));
    k.destroy(a); k.destroy(b);
  }

  // DeleteVsEdit: delete dominates a concurrent edit.
  {
    const a = eng(), b = eng();
    k.set(a, "ns", "e", "f1", "init");
    k.sync(a, b);                 // shared base
    k.del(a, "ns", "e");
    k.set(b, "ns", "e", "f2", "edit");
    k.sync(a, b);
    check("DeleteVsEdit",
          !k.exists(a, "ns", "e") && !k.exists(b, "ns", "e") &&
          eqBytes(k.digest(a), k.digest(b)));
    k.destroy(a); k.destroy(b);
  }

  // BinaryValue: NUL-containing value round-trips.
  {
    const a = eng(), b = eng();
    const bin = new Uint8Array([0, 1, 2, 0, 255, ...new Array(2000).fill(0xab)]);
    k.set(a, "ns", "bin", "f", bin);
    k.sync(a, b);
    check("BinaryValue",
          eqBytes(k.get(b, "ns", "bin", "f"), bin) &&
          eqBytes(k.digest(a), k.digest(b)));
    k.destroy(a); k.destroy(b);
  }

  // ManyEntities: 100 + 100 distinct converge to the union.
  {
    const a = eng(), b = eng();
    for (let i = 0; i < 100; i++) {
      k.set(a, "ns", "a" + i, "f", "x");
      k.set(b, "ns", "b" + i, "f", "y");
    }
    k.sync(a, b);
    let all = eqBytes(k.digest(a), k.digest(b));
    for (let i = 0; i < 100; i++)
      all = all && k.exists(b, "ns", "a" + i) && k.exists(a, "ns", "b" + i);
    check("ManyEntities", all);
    k.destroy(a); k.destroy(b);
  }

  // EmptyVsFull: an empty side bootstraps from the other.
  {
    const a = eng(), b = eng();
    for (let i = 0; i < 60; i++) k.set(a, "ns", "e" + i, "f", "v");
    k.sync(a, b);
    let all = eqBytes(k.digest(a), k.digest(b));
    for (let i = 0; i < 60; i++) all = all && k.exists(b, "ns", "e" + i);
    check("EmptyVsFull", all);
    k.destroy(a); k.destroy(b);
  }

  console.log(failed ? `\nWASM PARITY FAILED (${failed})` : "\nWASM PARITY OK (all scenarios converge in WASM)");
  process.exit(failed ? 1 : 0);
})().catch((e) => { console.error(e); process.exit(1); });
