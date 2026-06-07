/* sync_engine.cjs — JavaScript/WASM binding for the replication engine.
 *
 * Wraps the Emscripten module (build-wasm/sync_engine.js) and exposes the same
 * C ABI a browser node uses: create an engine, set/get/delete/exists, and drive
 * the reconciliation *session* (opaque message bytes) — which a browser pumps
 * over its native WebSocket. Mirrors bindings/python/sync_engine.py.
 */
"use strict";

const SEED_LEN = 32, DIGEST_LEN = 32, PUBKEY_LEN = 32;
const SYNC_OK = 0, SYNC_ERR_NOTFOUND = 3;

function bytes(x) {
  if (typeof x === "string") return new TextEncoder().encode(x);
  return x instanceof Uint8Array ? x : new Uint8Array(x);
}

class Binding {
  constructor(M) { this.M = M; }

  _toHeap(u8) {
    const p = this.M._malloc(u8.length || 1);
    this.M.HEAPU8.set(u8, p);
    return p;
  }
  _u32(ptr) { return this.M.HEAPU32[ptr >> 2]; }
  _cstr(str) {
    const u = bytes(str);
    const p = this.M._malloc(u.length + 1);
    this.M.HEAPU8.set(u, p);
    this.M.HEAPU8[p + u.length] = 0;
    return p;
  }

  abiVersion() { return this.M._sync_abi_version(); }

  create(seed) {
    seed = bytes(seed);
    if (seed.length !== SEED_LEN) throw new Error("seed must be 32 bytes");
    const sp = this._toHeap(seed);
    const e = this.M._sync_engine_create(sp);
    this.M._free(sp);
    if (!e) throw new Error("create failed");
    return e;
  }
  /* Durable engine backed by a SQLite file (in MEMFS under Node/browser; mount
   * IDBFS/OPFS in a browser for persistence across reloads). */
  open(path, seed) {
    seed = bytes(seed);
    const pp = this._cstr(path), sp = this._toHeap(seed);
    const e = this.M._sync_engine_open(pp, sp);
    this.M._free(pp); this.M._free(sp);
    if (!e) throw new Error("open failed");
    return e;
  }
  destroy(e) { this.M._sync_engine_destroy(e); }

  identity(e) {
    const buf = this.M._malloc(PUBKEY_LEN);
    this.M._sync_engine_identity(e, buf);
    const pk = this.M.HEAPU8.slice(buf, buf + PUBKEY_LEN);
    this.M._free(buf);
    return pk;
  }

  /* Capabilities. capRoot/capDelegate return opaque pointers; free with capFree. */
  capRoot(owner, ns, access) {
    const pn = this._cstr(ns);
    const c = this.M._sync_capability_root(owner, pn, access);
    this.M._free(pn);
    return c;
  }
  capDelegate(delegator, parent, subjectPubkey, access, expiryMs = 0) {
    const sp = this._toHeap(bytes(subjectPubkey));
    const c = this.M._sync_capability_delegate(delegator, parent, sp, access,
                                               BigInt(expiryMs));
    this.M._free(sp);
    return c;
  }
  grant(e, cap) { return this.M._sync_engine_grant(e, cap); }
  capFree(c) { this.M._sync_capability_free(c); }

  set(e, ns, ent, field, val) {
    ns = bytes(ns); ent = bytes(ent); field = bytes(field); val = bytes(val);
    const pn = this._toHeap(ns), pe = this._toHeap(ent),
          pf = this._toHeap(field), pv = this._toHeap(val);
    const rc = this.M._sync_engine_set(e, pn, ns.length, pe, ent.length,
                                       pf, field.length, pv, val.length);
    this.M._free(pn); this.M._free(pe); this.M._free(pf); this.M._free(pv);
    if (rc !== SYNC_OK) throw new Error("set failed: " + rc);
  }

  del(e, ns, ent) {
    ns = bytes(ns); ent = bytes(ent);
    const pn = this._toHeap(ns), pe = this._toHeap(ent);
    const rc = this.M._sync_engine_delete(e, pn, ns.length, pe, ent.length);
    this.M._free(pn); this.M._free(pe);
    if (rc !== SYNC_OK) throw new Error("delete failed: " + rc);
  }

  get(e, ns, ent, field) {
    ns = bytes(ns); ent = bytes(ent); field = bytes(field);
    const pn = this._toHeap(ns), pe = this._toHeap(ent), pf = this._toHeap(field);
    const outpp = this.M._malloc(4), outlp = this.M._malloc(4);
    const rc = this.M._sync_engine_get(e, pn, ns.length, pe, ent.length,
                                       pf, field.length, outpp, outlp);
    let res = null;
    if (rc === SYNC_OK) {
      const dp = this._u32(outpp), len = this._u32(outlp);
      res = this.M.HEAPU8.slice(dp, dp + len);
      this.M._sync_free(dp);
    }
    this.M._free(pn); this.M._free(pe); this.M._free(pf);
    this.M._free(outpp); this.M._free(outlp);
    if (rc !== SYNC_OK && rc !== SYNC_ERR_NOTFOUND) throw new Error("get: " + rc);
    return res;
  }

  exists(e, ns, ent) {
    ns = bytes(ns); ent = bytes(ent);
    const pn = this._toHeap(ns), pe = this._toHeap(ent), pp = this.M._malloc(4);
    this.M._sync_engine_exists(e, pn, ns.length, pe, ent.length, pp);
    const v = this.M.HEAPU32[pp >> 2];
    this.M._free(pn); this.M._free(pe); this.M._free(pp);
    return v !== 0;
  }

  digest(e) {
    const buf = this.M._malloc(DIGEST_LEN);
    this.M._sync_engine_digest(e, buf);
    const d = this.M.HEAPU8.slice(buf, buf + DIGEST_LEN);
    this.M._free(buf);
    return d;
  }

  sessionBegin(e, initiator) { return this.M._sync_session_begin(e, initiator ? 1 : 0); }
  sessionEnd(s) { this.M._sync_session_end(s); }

  /* Process one incoming message (Uint8Array, possibly empty) and return the
   * next outgoing message + done flag. */
  sessionStep(s, inU8) {
    const inptr = inU8.length ? this._toHeap(inU8) : 0;
    const outpp = this.M._malloc(4), outlp = this.M._malloc(4), donep = this.M._malloc(4);
    const rc = this.M._sync_session_step(s, inptr, inU8.length, outpp, outlp, donep);
    let out = new Uint8Array(0);
    if (rc === SYNC_OK) {
      const dp = this._u32(outpp), len = this._u32(outlp);
      if (len) { out = this.M.HEAPU8.slice(dp, dp + len); this.M._sync_free(dp); }
    }
    const done = this.M.HEAPU32[donep >> 2] !== 0;
    if (inptr) this.M._free(inptr);
    this.M._free(outpp); this.M._free(outlp); this.M._free(donep);
    if (rc !== SYNC_OK) throw new Error("session_step: " + rc);
    return { out, done };
  }

  /* Drive two local engines to convergence over the reconciliation session —
   * the same pump a browser runs, with the messages flowing over its WebSocket
   * instead of directly. */
  sync(a, b) {
    const sa = this.sessionBegin(a, true), sb = this.sessionBegin(b, false);
    let msg = this.sessionStep(sa, new Uint8Array(0)).out;
    let turn = sb, other = sa;
    let empties = msg.length === 0 ? 1 : 0;
    for (let i = 0; i < 100000; i++) {
      const r = this.sessionStep(turn, msg);
      empties = r.out.length === 0 ? empties + 1 : 0;
      if (empties >= 2) break;
      msg = r.out;
      [turn, other] = [other, turn];
    }
    this.sessionEnd(sa); this.sessionEnd(sb);
  }
}

async function load(modulePath) {
  const jsPath = modulePath || require("path").join(__dirname, "../../build-wasm/sync_engine.js");
  const createSyncEngine = require(jsPath);
  // Pass the wasm bytes directly so the loader doesn't try to fetch() a file
  // path (Node 22 exposes a global fetch, which trips Emscripten's web path).
  const fs = require("fs");
  const wasmBinary = fs.readFileSync(jsPath.replace(/\.js$/, ".wasm"));
  const M = await createSyncEngine({ wasmBinary });
  return new Binding(M);
}

module.exports = { load, Binding };
