import { test } from "node:test";
import assert from "node:assert/strict";
import { SyncClient, SyncHub } from "../dist/index.js";
import { getBinding, nextSeed, nextPort, waitUntil, sleep } from "./helpers.mjs";

const READ = 1;
const WRITE = 2;

test("hub read-scopes a namespace by the pubkey a client presents; an unauthorized client gets none of it", async () => {
  const k = await getBinding();

  const hubEngine = k.create(nextSeed());
  const authorizedEngine = k.create(nextSeed());
  const unauthorizedEngine = k.create(nextSeed());

  // A restricted namespace the hub owns, plus an open one as a control.
  k.set(hubEngine, "secret", "s1", "f", "topsecret");
  k.set(hubEngine, "public", "p1", "f", "hello");

  const rootCap = k.capRoot(hubEngine, "secret", READ | WRITE);
  assert.equal(k.grant(hubEngine, rootCap), 0, "granting the root into the hub itself must succeed");

  const authorizedPubkey = k.identity(authorizedEngine);
  const delegCap = k.capDelegate(hubEngine, rootCap, authorizedPubkey, READ, 0);
  assert.equal(k.grant(hubEngine, delegCap), 0, "delegating READ to the authorized client must succeed");

  const port = nextPort();
  const hub = new SyncHub({ engine: hubEngine, binding: k, port, scoped: true });
  await hub.start();

  const authorizedClient = new SyncClient({
    engine: authorizedEngine,
    binding: k,
    url: `ws://127.0.0.1:${port}`,
    scoped: false,
    intervalMs: 200,
  });
  const unauthorizedClient = new SyncClient({
    engine: unauthorizedEngine,
    binding: k,
    url: `ws://127.0.0.1:${port}`,
    scoped: false,
    intervalMs: 200,
  });

  try {
    authorizedClient.connect();
    unauthorizedClient.connect();

    // Positive check: the authorized client gets BOTH the open record and the
    // scoped one it's been delegated read access to.
    await waitUntil(
      () => k.exists(authorizedEngine, "public", "p1") && k.exists(authorizedEngine, "secret", "s1"),
      { timeoutMs: 10000, label: "authorized client to receive the scoped namespace" },
    );

    // The unauthorized client should get the open record (proves it's really
    // connected and cycling)...
    await waitUntil(() => k.exists(unauthorizedEngine, "public", "p1"), {
      timeoutMs: 10000,
      label: "unauthorized client to receive the open namespace",
    });

    // ...but let several more cycles run, and it must never get the scoped one.
    await sleep(1500);
    assert.equal(
      k.exists(unauthorizedEngine, "secret", "s1"),
      false,
      "an unauthorized pubkey must never receive a scoped namespace's records",
    );
  } finally {
    authorizedClient.stop();
    unauthorizedClient.stop();
    await hub.stop();
    k.capFree(rootCap);
    k.capFree(delegCap);
    k.destroy(hubEngine);
    k.destroy(authorizedEngine);
    k.destroy(unauthorizedEngine);
  }
});
