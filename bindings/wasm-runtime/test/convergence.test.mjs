import { test } from "node:test";
import assert from "node:assert/strict";
import { SyncClient, SyncHub } from "../dist/index.js";
import { getBinding, nextSeed, nextPort, eqBytes, waitUntil } from "./helpers.mjs";

test("two SyncClients + one SyncHub converge to identical digests over real localhost ws", async () => {
  const k = await getBinding();

  const hubEngine = k.create(nextSeed());
  const aEngine = k.create(nextSeed());
  const bEngine = k.create(nextSeed());

  // Each client writes distinct records on its own in-memory engine, BEFORE connecting.
  for (let i = 0; i < 20; i++) k.set(aEngine, "ns", `a${i}`, "f", `va${i}`);
  for (let i = 0; i < 20; i++) k.set(bEngine, "ns", `b${i}`, "f", `vb${i}`);

  const port = nextPort();
  const hub = new SyncHub({ engine: hubEngine, binding: k, port, scoped: false });
  await hub.start();

  const clientA = new SyncClient({ engine: aEngine, binding: k, url: `ws://127.0.0.1:${port}`, scoped: false, intervalMs: 300 });
  const clientB = new SyncClient({ engine: bEngine, binding: k, url: `ws://127.0.0.1:${port}`, scoped: false, intervalMs: 300 });

  const errors = [];
  clientA.onError((e) => errors.push(["A", e]));
  clientB.onError((e) => errors.push(["B", e]));
  hub.onError((e) => errors.push(["hub", e]));

  try {
    clientA.connect();
    clientB.connect();

    const allPresent = () => {
      for (let i = 0; i < 20; i++) {
        if (!k.exists(hubEngine, "ns", `a${i}`)) return false;
        if (!k.exists(hubEngine, "ns", `b${i}`)) return false;
        if (!k.exists(aEngine, "ns", `a${i}`)) return false;
        if (!k.exists(aEngine, "ns", `b${i}`)) return false;
        if (!k.exists(bEngine, "ns", `a${i}`)) return false;
        if (!k.exists(bEngine, "ns", `b${i}`)) return false;
      }
      return true;
    };

    const start = Date.now();
    await waitUntil(
      () =>
        allPresent() &&
        eqBytes(k.digest(hubEngine), k.digest(aEngine)) &&
        eqBytes(k.digest(hubEngine), k.digest(bEngine)),
      { timeoutMs: 20000, label: "hub+clientA+clientB convergence" },
    );
    const convergeMs = Date.now() - start;
    console.log(`  [convergence] converged in ${convergeMs}ms`);

    assert.equal(errors.length, 0, `unexpected errors: ${JSON.stringify(errors.map((e) => String(e[1])))}`);
    assert.ok(eqBytes(k.digest(hubEngine), k.digest(aEngine)));
    assert.ok(eqBytes(k.digest(hubEngine), k.digest(bEngine)));
    assert.ok(eqBytes(k.digest(aEngine), k.digest(bEngine)));
  } finally {
    clientA.stop();
    clientB.stop();
    await hub.stop();
    k.destroy(hubEngine);
    k.destroy(aEngine);
    k.destroy(bEngine);
  }
});
