import { load } from "kome-sync";

let bindingPromise = null;
export function getBinding() {
  if (!bindingPromise) bindingPromise = load();
  return bindingPromise;
}

let seedCounter = 1;
/** A fresh 32-byte identity seed, distinct per call within a process run. */
export function nextSeed() {
  const s = new Uint8Array(32);
  s.fill(seedCounter++ & 0xff);
  // perturb a couple more bytes so low seed counts still yield distinct identities
  s[16] = (seedCounter * 7) & 0xff;
  s[31] = (seedCounter * 13) & 0xff;
  return s;
}

/** An ephemeral localhost port unlikely to collide across parallel test files. */
export function nextPort() {
  return 20000 + Math.floor(Math.random() * 20000);
}

export function eqBytes(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}

/** Poll `cond` until it returns true, or throw after timeoutMs. */
export async function waitUntil(cond, { timeoutMs = 15000, intervalMs = 50, label = "condition" } = {}) {
  const start = Date.now();
  for (;;) {
    if (await cond()) return;
    if (Date.now() - start > timeoutMs) {
      throw new Error(`kome-sync-runtime test: timed out waiting for ${label}`);
    }
    await sleep(intervalMs);
  }
}

export function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}
