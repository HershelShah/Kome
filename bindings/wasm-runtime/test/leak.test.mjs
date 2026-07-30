import { test } from "node:test";
import assert from "node:assert/strict";
import { SyncClient, SyncHub } from "../dist/index.js";
import { getBinding, nextSeed, nextPort, waitUntil } from "./helpers.mjs";

test("200 gossip cycles leave zero live sessions and no unhandled errors; stop() is clean", async () => {
  const k = await getBinding();

  const hubEngine = k.create(nextSeed());
  const clientEngine = k.create(nextSeed());

  const port = nextPort();
  const hub = new SyncHub({ engine: hubEngine, binding: k, port, scoped: false });
  await hub.start();

  const client = new SyncClient({
    engine: clientEngine,
    binding: k,
    url: `ws://127.0.0.1:${port}`,
    scoped: false,
    intervalMs: 15, // fast, to get 200 cycles quickly
  });

  const errors = [];
  client.onError((e) => errors.push(e));

  let cycles = 0;
  client.onSync(() => {
    cycles++;
    // Between cycles (the GossipPeer's cycle is fully torn down — busy=false
    // — before the next periodic tick fires), there must never be more than
    // one live SessionHandle on this connection.
    assert.ok(client.liveSessions <= 1, `liveSessions grew to ${client.liveSessions} mid-run`);
  });

  try {
    client.connect();
    await waitUntil(() => cycles >= 200, { timeoutMs: 30000, label: "200 gossip cycles" });

    assert.equal(errors.length, 0, `unexpected errors during the run: ${errors.map(String).join("; ")}`);
    assert.equal(client.liveSessions, 0, "client has a live session between cycles");
    assert.equal(hub.liveSessions, 0, "hub has a live session between cycles");
  } finally {
    client.stop();
    assert.equal(client.liveSessions, 0, "stop() must end any in-flight session");
    await hub.stop();
    assert.equal(hub.liveSessions, 0, "hub.stop() must end all sessions");
    k.destroy(hubEngine);
    k.destroy(clientEngine);
  }
});
