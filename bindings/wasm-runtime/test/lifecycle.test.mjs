import { test } from "node:test";
import assert from "node:assert/strict";
import { SyncClient, SyncHub } from "../dist/index.js";
import { getBinding, nextSeed, nextPort, waitUntil } from "./helpers.mjs";

test("SyncClient.stop() is idempotent and aborts an in-flight cycle cleanly", async () => {
  const k = await getBinding();
  const hubEngine = k.create(nextSeed());
  const clientEngine = k.create(nextSeed());
  for (let i = 0; i < 50; i++) k.set(clientEngine, "ns", `e${i}`, "f", `v${i}`);

  const port = nextPort();
  const hub = new SyncHub({ engine: hubEngine, binding: k, port, scoped: false });
  await hub.start();

  const client = new SyncClient({
    engine: clientEngine,
    binding: k,
    url: `ws://127.0.0.1:${port}`,
    scoped: false,
    intervalMs: 200,
  });
  client.onError(() => {});
  let state = "connecting";
  client.onStateChange((s) => { state = s; });
  client.connect();

  try {
    // Wait until the socket is genuinely open (proves the connect path ran —
    // the old `liveSessions >= 0` guard was trivially true), then stop
    // repeatedly. Whether or not a cycle happens to be live at this instant,
    // liveSessions must settle to 0 and stay there. (Deterministic mid-cycle
    // abort — sessionEnd on forced drop — is proven in leak.test.mjs.)
    await waitUntil(() => state === "open", { timeoutMs: 5000, label: "client to open" });
    client.stop();
    client.stop();
    client.stop();
    assert.equal(client.liveSessions, 0, "stop() must end any in-flight session, and stay idempotent");
  } finally {
    await hub.stop();
    k.destroy(hubEngine);
    k.destroy(clientEngine);
  }
});

test("SyncHub.stop() is idempotent, ends every connection's session, and releases the port for a second start()", async () => {
  const k = await getBinding();
  const hubEngine = k.create(nextSeed());
  const clientEngine = k.create(nextSeed());
  k.set(clientEngine, "ns", "a", "f", "v");

  const port = nextPort();
  const hub = new SyncHub({ engine: hubEngine, binding: k, port, scoped: false });
  await hub.start();

  const client = new SyncClient({
    engine: clientEngine,
    binding: k,
    url: `ws://127.0.0.1:${port}`,
    scoped: false,
    intervalMs: 150,
  });
  client.onError(() => {});
  client.connect();

  try {
    await waitUntil(() => hub.connectionCount >= 1, { timeoutMs: 5000, label: "client to connect to the hub" });

    await hub.stop();
    await hub.stop(); // idempotent
    assert.equal(hub.liveSessions, 0);
    assert.equal(hub.connectionCount, 0);

    // The port must be free: a second SyncHub can bind the same port right away.
    const hub2 = new SyncHub({ engine: hubEngine, binding: k, port, scoped: false });
    await hub2.start();
    await hub2.stop();
  } finally {
    client.stop();
    await hub.stop();
    k.destroy(hubEngine);
    k.destroy(clientEngine);
  }
});
