import { test } from "node:test";
import assert from "node:assert/strict";
import { SyncClient, SyncHub } from "../dist/index.js";
import { getBinding, nextSeed, nextPort, eqBytes, waitUntil, sleep } from "./helpers.mjs";

test("client reconnects with backoff after the hub is killed and restarted, re-converging including a record written while disconnected", async () => {
  const k = await getBinding();

  const hubEngine = k.create(nextSeed());
  const clientEngine = k.create(nextSeed());
  k.set(clientEngine, "ns", "before", "f", "v1");

  const port = nextPort();
  let hub = new SyncHub({ engine: hubEngine, binding: k, port, scoped: false });
  await hub.start();

  const client = new SyncClient({
    engine: clientEngine,
    binding: k,
    url: `ws://127.0.0.1:${port}`,
    scoped: false,
    intervalMs: 250,
  });
  const states = [];
  client.onStateChange((s) => states.push(s));
  client.onError(() => {}); // reconnect attempts against a dead hub are expected to error; swallow
  client.connect();

  try {
    await waitUntil(() => k.exists(hubEngine, "ns", "before"), { timeoutMs: 10000, label: "initial converge" });
    assert.ok(eqBytes(k.digest(hubEngine), k.digest(clientEngine)));

    // Kill the hub mid-run.
    await hub.stop();
    states.length = 0;
    await waitUntil(() => states.includes("closed"), { timeoutMs: 5000, label: "client to notice the hub died" });

    // Write a record while disconnected — must ship once reconnected.
    k.set(clientEngine, "ns", "during-outage", "f", "v2");

    // Give the client a couple of failed reconnect attempts against the dead port.
    await sleep(600);

    // Restart the hub on the SAME port.
    hub = new SyncHub({ engine: hubEngine, binding: k, port, scoped: false });
    const restartStart = Date.now();
    await hub.start();

    await waitUntil(() => states.includes("open"), { timeoutMs: 15000, label: "client reconnect" });
    const reconnectMs = Date.now() - restartStart;
    console.log(`  [reconnect] client reconnected ${reconnectMs}ms after hub restart`);

    await waitUntil(
      () => k.exists(hubEngine, "ns", "during-outage") && eqBytes(k.digest(hubEngine), k.digest(clientEngine)),
      { timeoutMs: 10000, label: "post-reconnect re-convergence" },
    );

    assert.ok(k.exists(hubEngine, "ns", "before"));
    assert.ok(k.exists(hubEngine, "ns", "during-outage"));
    assert.ok(eqBytes(k.digest(hubEngine), k.digest(clientEngine)));
  } finally {
    client.stop();
    await hub.stop();
    k.destroy(hubEngine);
    k.destroy(clientEngine);
  }
});
