/* parity.cjs — run the SAME scenarios as tests/transport_parity_test.cpp, but
 * with the engine compiled to WASM, so we know it works in WASM in every case
 * the native UDP/TCP/WS paths do. The reconciliation runs through the session
 * (the transport-agnostic message pump a browser drives over its WebSocket).
 *
 *   tools/wasm_build.sh && node bindings/wasm/parity.cjs
 */
"use strict";
// KOME_PKG re-points the battery at an installed package (the npm tarball
// gate in npm.yml); default is the repo dev flow over build-wasm/. NOTE:
// with KOME_PKG this file must be COPIED into the consuming project first —
// run in place, Node's package self-reference resolves "kome-sync" to this
// very directory (bindings/wasm has that name in its package.json), so the
// gate would silently re-test the repo instead of the installed tarball.
const { load } = require(process.env.KOME_PKG || "./sync_engine.cjs");

const enc = (s) => new TextEncoder().encode(s);
const eqBytes = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);

let failed = 0;
function check(name, cond, msg) {
  if (cond) { console.log("  ok   " + name); }
  else { console.log("  FAIL " + name + (msg ? " — " + msg : "")); failed++; }
}

(async () => {
  const k = await load(); // dev default: build-wasm/sync_engine.js
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

  const READ = 1, WRITE = 2;

  // StorageReopenIdentity: a durable engine survives close/reopen (M2). Storage
  // is SQLite over MEMFS here; a browser mounts IDBFS/OPFS for cross-reload
  // persistence, but the engine logic is the same.
  {
    const e = k.open("/p1.db", seed(s++));
    for (let i = 0; i < 5; i++) k.set(e, "ns", "e" + i, "f", "v" + i);
    const d1 = k.digest(e);
    k.destroy(e);
    const e2 = k.open("/p1.db", seed(0)); // existing file -> persisted identity
    let ok = eqBytes(k.digest(e2), d1);
    for (let i = 0; i < 5; i++) ok = ok && k.exists(e2, "ns", "e" + i);
    check("StorageReopenIdentity", ok);
    k.destroy(e2);
  }

  // StorageDurableConverge: two durable engines sync, then both reopen to the
  // same converged state.
  {
    const a = k.open("/da.db", seed(s++)), b = k.open("/db.db", seed(s++));
    k.set(a, "ns", "x", "f", "X");
    k.set(b, "ns", "y", "f", "Y");
    k.sync(a, b);
    const conv = k.digest(a);
    const ok1 = eqBytes(conv, k.digest(b));
    k.destroy(a); k.destroy(b);
    const a2 = k.open("/da.db", seed(0)), b2 = k.open("/db.db", seed(0));
    const ok2 = eqBytes(k.digest(a2), conv) && eqBytes(k.digest(b2), conv) &&
                k.exists(a2, "ns", "y") && k.exists(b2, "ns", "x");
    check("StorageDurableConverge", ok1 && ok2);
    k.destroy(a2); k.destroy(b2);
  }

  // CapabilityEnforcement: an enforcing node accepts an authorized writer's
  // records (capability gossiped during sync) and drops a stranger's (M4).
  {
    const owner = eng(), writer = eng(), stranger = eng(), v = eng();
    const wpk = k.identity(writer);
    const root = k.capRoot(owner, "nsA", READ | WRITE);
    const deleg = k.capDelegate(owner, root, wpk, WRITE, 0);
    check("cap-grant-root", k.grant(v, root) === 0);
    check("cap-grant-deleg", k.grant(writer, deleg) === 0);

    k.set(writer, "nsA", "w1", "f", "hi");
    k.sync(writer, v);
    check("CapAuthorizedAccepted", k.exists(v, "nsA", "w1"));

    k.set(stranger, "nsA", "s1", "f", "no");
    k.sync(stranger, v);
    check("CapUnauthorizedRejected", !k.exists(v, "nsA", "s1"));

    k.capFree(root); k.capFree(deleg);
    [owner, writer, stranger, v].forEach((e) => k.destroy(e));
  }

  console.log(failed ? `\nWASM PARITY FAILED (${failed})` : "\nWASM PARITY OK (sync, storage + reopen, and capability enforcement all in WASM)");
  process.exit(failed ? 1 : 0);
})().catch((e) => { console.error(e); process.exit(1); });
