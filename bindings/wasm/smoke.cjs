/* smoke.cjs — runs the WASM engine in Node (same code a browser runs) and
 * verifies two engines converge via the reconciliation session.
 *
 *   tools/wasm_build.sh && node bindings/wasm/smoke.cjs
 */
"use strict";
const path = require("path");
const { load } = require("./sync_engine.cjs");

function seed(v) { return new Uint8Array(32).fill(v); }
function eq(a, b) { return a.length === b.length && a.every((x, i) => x === b[i]); }
function assert(c, m) { if (!c) { console.error("FAIL:", m); process.exit(1); } }

(async () => {
  const k = await load(path.join(__dirname, "../../build-wasm/sync_engine.js"));
  assert(k.abiVersion() === 4, "ABI version");

  const a = k.create(seed(1)), b = k.create(seed(2));

  // Independent offline writes.
  k.set(a, "people", "alice", "name", "Alice");
  k.set(b, "people", "bob", "name", "Bob");

  // Reconcile via the session (what a browser pumps over its WebSocket).
  k.sync(a, b);

  // Each side sees the other's record, and digests match.
  assert(eq(k.get(a, "people", "bob", "name"), new TextEncoder().encode("Bob")),
         "A learned bob");
  assert(eq(k.get(b, "people", "alice", "name"), new TextEncoder().encode("Alice")),
         "B learned alice");
  assert(eq(k.digest(a), k.digest(b)), "digests converged");

  // Conflict: concurrent same-cell writes resolve to one deterministic winner.
  const c = k.create(seed(10)), d = k.create(seed(11));
  k.set(c, "ns", "cell", "f", "from-C");
  k.set(d, "ns", "cell", "f", "from-D");
  k.sync(c, d);
  assert(eq(k.get(c, "ns", "cell", "f"), k.get(d, "ns", "cell", "f")),
         "conflict winner agrees");
  assert(eq(k.digest(c), k.digest(d)), "conflict converged");

  [a, b, c, d].forEach((e) => k.destroy(e));
  console.log("wasm smoke test: OK (engine + reconciliation session run in WASM)");
})().catch((e) => { console.error(e); process.exit(1); });
