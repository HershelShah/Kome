import { load } from "kome-sync";

const results = [];
function record(name, ok, detail) {
  results.push(`${ok ? "PASS" : "FAIL"} ${name}${detail ? " — " + detail : ""}`);
  return ok;
}

try {
  // Baseline convergence (unchanged from before the WASM parity work).
  const k = await load();
  const a = k.create(new Uint8Array(32).fill(1));
  const b = k.create(new Uint8Array(32).fill(2));
  k.set(a, "contacts", "alice", "phone", "555-1234");
  k.set(b, "contacts", "bob", "email", "bob@example.com");
  k.sync(a, b);
  const got = new TextDecoder().decode(k.get(a, "contacts", "bob", "email"));
  const da = k.digest(a), db = k.digest(b);
  const converged = got === "bob@example.com" &&
    k.abiVersion() === 4 && da.length === 32 && da.every((x, i) => x === db[i]);
  record("convergence", converged);

  // New exports reachable from the browser (ES6) build too: scan + blob.
  k.set(a, "sc", "e1", "f", "v");
  k.set(a, "sc", "e2", "f", "v");
  const scanned = k.scan(a, "sc", null, 0).map((u) => new TextDecoder().decode(u)).sort();
  record("scan", scanned.length === 2 && scanned[0] === "e1" && scanned[1] === "e2");

  const blobData = new Uint8Array(70000).fill(7); // > 2 chunks (32768/chunk)
  const blobId = k.blobPut(a, "blobs", blobData);
  const blobBack = k.blobGet(a, "blobs", blobId);
  record("blob-roundtrip", blobBack.length === blobData.length &&
    blobBack.every((x, i) => x === blobData[i]));

  k.destroy(a); k.destroy(b);

  // Browser-only persistence: mountIdbfs + syncFs over IndexedDB. Simulate a
  // reload by loading a second, independent Emscripten module instance (its
  // own fresh MEMFS) against the *same* IndexedDB-backed directory, rather
  // than actually reloading the page.
  const dir = "/persisted";
  const dbPath = dir + "/store.db";
  const seed = new Uint8Array(32).fill(9);

  const k1 = await load();
  k1.mountIdbfs(dir);
  await k1.syncFs(true); // pull whatever's already there (nothing, first run)
  const e1 = k1.open(dbPath, seed);
  k1.set(e1, "ns", "durable", "f", "persisted-value");
  const digestBeforeReload = k1.digest(e1);
  k1.destroy(e1);
  await k1.syncFs(false); // push MEMFS writes out to IndexedDB

  const k2 = await load(); // fresh module instance == fresh MEMFS
  k2.mountIdbfs(dir);
  await k2.syncFs(true); // pull the persisted state back in
  const e2 = k2.open(dbPath, new Uint8Array(32)); // existing file: seed ignored, persisted identity wins
  const persistedOk = record("idbfs-persistence",
    e2 !== 0 &&
    new TextDecoder().decode(k2.get(e2, "ns", "durable", "f")) === "persisted-value" &&
    k2.digest(e2).every((x, i) => x === digestBeforeReload[i]));
  k2.destroy(e2);

  const ok = converged && results.every((r) => r.startsWith("PASS"));
  document.getElementById("out").textContent = results.join("\n");
  document.title = ok ? "KOME_OK" : "KOME_FAIL";
} catch (e) {
  document.getElementById("out").textContent =
    results.join("\n") + "\n" + String((e && e.stack) || e);
  document.title = "KOME_FAIL";
}
