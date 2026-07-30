/* binding.cjs — the JavaScript API over the engine's exported C ABI.
 *
 * One implementation shared by every entry point: the npm package's CJS/ESM
 * entries (index.cjs / index.mjs), the embedded variants, and the repo dev
 * shim (sync_engine.cjs over build-wasm/). Mirrors bindings/python/kome.
 */
"use strict";

const SEED_LEN = 32, DIGEST_LEN = 32, PUBKEY_LEN = 32, SITE_ID_LEN = 32, BLOB_ID_LEN = 32;
const SYNC_OK = 0, SYNC_ERR_NOTFOUND = 3;

/* Attach the C error code to a thrown Error so callers can branch on it (e.g.
 * distinguishing SYNC_ERR_CORRUPT=7 from SYNC_ERR_NOTFOUND=3) without parsing
 * the message. Used by the newer wrappers (blob*, invite*); the original
 * get/set/etc. wrappers predate this convention and are left as-is. */
function codedError(msg, rc) {
  const e = new Error(msg + ": " + rc);
  e.code = rc;
  return e;
}

function bytes(x) {
  if (typeof x === "string") return new TextEncoder().encode(x);
  return x instanceof Uint8Array ? x : new Uint8Array(x);
}

class Binding {
  constructor(M) { this.M = M; }

  /* malloc that refuses to hand back the null address — writing through 0
   * would silently corrupt the runtime's low memory instead of erroring. */
  _alloc(n) {
    const p = this.M._malloc(n);
    if (!p) throw new Error("wasm out of memory (" + n + " bytes)");
    return p;
  }
  _toHeap(u8) {
    const p = this._alloc(u8.length || 1);
    this.M.HEAPU8.set(u8, p);
    return p;
  }
  /* Copy a pubkey to the heap, validating length first — the C side reads
   * exactly SYNC_PUBKEY_LEN bytes, so a short buffer would expose adjacent
   * heap. */
  _pk(u8) {
    u8 = bytes(u8);
    if (u8.length !== PUBKEY_LEN)
      throw new Error("pubkey must be " + PUBKEY_LEN + " bytes, got " + u8.length);
    return this._toHeap(u8);
  }
  _u32(ptr) { return this.M.HEAPU32[ptr >> 2]; }
  _cstr(str) {
    const u = bytes(str);
    const p = this._alloc(u.length + 1);
    this.M.HEAPU8.set(u, p);
    this.M.HEAPU8[p + u.length] = 0;
    return p;
  }

  abiVersion() { return this.M._sync_abi_version(); }

  /* Human-readable name for a sync_error code (e.g. from a CodedError). */
  strerror(code) { return this.M.UTF8ToString(this.M._sync_strerror(code)); }

  create(seed) {
    seed = bytes(seed);
    if (seed.length !== SEED_LEN) throw new Error("seed must be 32 bytes");
    const sp = this._toHeap(seed);
    const e = this.M._sync_engine_create(sp);
    this.M._free(sp);
    if (!e) throw new Error("create failed");
    return e;
  }
  /* Durable engine backed by an append-only log file (in MEMFS under
   * Node/browser; mount IDBFS/OPFS in a browser for persistence across
   * reloads). */
  open(path, seed) {
    seed = bytes(seed);
    if (seed.length !== SEED_LEN) throw new Error("seed must be 32 bytes");
    const pp = this._cstr(path), sp = this._toHeap(seed);
    const e = this.M._sync_engine_open(pp, sp);
    this.M._free(pp); this.M._free(sp);
    if (!e) throw new Error("open failed");
    return e;
  }
  /* Like open(), but the log is encrypted at rest under a caller-supplied
   * 32-byte key (see sync_engine_open_encrypted). Opening with the wrong key
   * fails cleanly — throws, does not return a half-usable engine. */
  openEncrypted(path, seed, key) {
    seed = bytes(seed); key = bytes(key);
    if (seed.length !== SEED_LEN) throw new Error("seed must be 32 bytes");
    if (key.length !== 32) throw new Error("key must be 32 bytes");
    const pp = this._cstr(path), sp = this._toHeap(seed), kp = this._toHeap(key);
    const e = this.M._sync_engine_open_encrypted(pp, sp, kp);
    this.M._free(pp); this.M._free(sp); this.M._free(kp);
    if (!e) throw new Error("openEncrypted failed (wrong key or corrupt/mismatched log)");
    return e;
  }
  destroy(e) { this.M._sync_engine_destroy(e); }

  /* Flush durable state to disk (a no-op safety net with write-through
   * storage; a no-op for in-memory engines). */
  flush(e) {
    const rc = this.M._sync_engine_flush(e);
    if (rc !== SYNC_OK) throw new Error("flush failed: " + rc);
  }

  identity(e) {
    const buf = this._alloc(PUBKEY_LEN);
    const rc = this.M._sync_engine_identity(e, buf);
    const pk = this.M.HEAPU8.slice(buf, buf + PUBKEY_LEN);
    this.M._free(buf);
    if (rc !== SYNC_OK) throw new Error("identity failed: " + rc);
    return pk;
  }

  /* BLAKE2b-256 of the signing public key (a stable, non-secret peer id). */
  siteId(e) {
    const buf = this._alloc(SITE_ID_LEN);
    const rc = this.M._sync_engine_site_id(e, buf);
    const id = this.M.HEAPU8.slice(buf, buf + SITE_ID_LEN);
    this.M._free(buf);
    if (rc !== SYNC_OK) throw new Error("siteId failed: " + rc);
    return id;
  }

  /* Capabilities. capRoot/capDelegate return opaque pointers; free with capFree. */
  capRoot(owner, ns, access) {
    const pn = this._cstr(ns);
    const c = this.M._sync_capability_root(owner, pn, access);
    this.M._free(pn);
    return c;
  }
  capDelegate(delegator, parent, subjectPubkey, access, expiryMs = 0) {
    const sp = this._pk(subjectPubkey);
    const c = this.M._sync_capability_delegate(delegator, parent, sp, access,
                                               BigInt(expiryMs));
    this.M._free(sp);
    return c;
  }
  grant(e, cap) { return this.M._sync_engine_grant(e, cap); }
  capFree(c) { this.M._sync_capability_free(c); }

  /* Serialize a capability (size-then-fill: size with buf==NULL, then
   * allocate exactly that many bytes). */
  capEncode(cap) {
    const need = this.M._sync_capability_encode(cap, 0, 0);
    if (!need) throw new Error("capEncode failed (invalid capability)");
    const buf = this._alloc(need);
    const n = this.M._sync_capability_encode(cap, buf, need);
    const out = this.M.HEAPU8.slice(buf, buf + n);
    this.M._free(buf);
    if (!n) throw new Error("capEncode failed (invalid capability)");
    return out;
  }
  /* Deserialize a capability; free the returned handle with capFree. */
  capDecode(buf) {
    const u8 = bytes(buf);
    const p = this._toHeap(u8);
    const c = this.M._sync_capability_decode(p, u8.length);
    this.M._free(p);
    if (!c) throw new Error("capDecode failed (malformed capability)");
    return c;
  }
  capSubject(cap) {
    if (!cap) throw new Error("capSubject: invalid capability handle");
    const out = this._alloc(PUBKEY_LEN);
    this.M._sync_capability_subject(cap, out);
    const pk = this.M.HEAPU8.slice(out, out + PUBKEY_LEN);
    this.M._free(out);
    return pk;
  }

  /* Permanently revoke subject_pubkey's access (and everything it
   * sub-delegated) in namespace ns. Returns the raw sync_error code (0 =
   * SYNC_OK), matching grant()'s convention rather than throwing — callers
   * that lack root get SYNC_ERR_UNAUTHORIZED back as data. */
  revoke(e, ns, subjectPubkey) {
    const pn = this._cstr(ns);
    const pk = this._pk(subjectPubkey);
    const rc = this.M._sync_engine_revoke(e, pn, pk);
    this.M._free(pn); this.M._free(pk);
    return rc;
  }
  isRevoked(e, ns, subjectPubkey) {
    const pn = this._cstr(ns);
    const pk = this._pk(subjectPubkey);
    const outp = this._alloc(4);
    const rc = this.M._sync_engine_is_revoked(e, pn, pk, outp);
    const v = this._u32(outp);
    this.M._free(pn); this.M._free(pk); this.M._free(outp);
    if (rc !== SYNC_OK) throw new Error("isRevoked failed: " + rc);
    return v !== 0;
  }

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
    const pn = this._toHeap(ns), pe = this._toHeap(ent), pp = this._alloc(4);
    const rc = this.M._sync_engine_exists(e, pn, ns.length, pe, ent.length, pp);
    const v = this.M.HEAPU32[pp >> 2];
    this.M._free(pn); this.M._free(pe); this.M._free(pp);
    if (rc !== SYNC_OK) throw new Error("exists failed: " + rc);
    return v !== 0;
  }

  /* List entities present in namespace ns, in canonical byte-lexicographic
   * order. startAfter is an exclusive resume cursor (pass the last entity
   * seen to page forward; omit/empty to start from the beginning); limit
   * caps the page size (0 = unlimited). Returns an array of Uint8Array
   * entity names (empty array for an unknown namespace or a cursor past the
   * end — not an error). */
  scan(e, ns, startAfter, limit = 0) {
    if (!Number.isInteger(limit) || limit < 0)
      throw new Error("scan: limit must be a non-negative integer (0 = unlimited)");
    ns = bytes(ns);
    const sa = startAfter == null ? new Uint8Array(0) : bytes(startAfter);
    const pn = this._toHeap(ns);
    const psa = sa.length ? this._toHeap(sa) : 0;
    const outpp = this.M._malloc(4), outcp = this.M._malloc(4);
    const rc = this.M._sync_engine_scan(e, pn, ns.length, psa, sa.length,
                                        limit >>> 0, outpp, outcp);
    this.M._free(pn);
    if (psa) this.M._free(psa);
    if (rc !== SYNC_OK) {
      this.M._free(outpp); this.M._free(outcp);
      throw new Error("scan failed: " + rc);
    }
    const arrPtr = this._u32(outpp), count = this._u32(outcp);
    const out = [];
    for (let i = 0; i < count; i++) {
      const base = arrPtr + i * 8; /* sync_scan_entry: {uint8_t*; size_t;} */
      const entPtr = this._u32(base), entLen = this._u32(base + 4);
      out.push(this.M.HEAPU8.slice(entPtr, entPtr + entLen));
    }
    if (arrPtr) this.M._sync_scan_free(arrPtr, count);
    this.M._free(outpp); this.M._free(outcp);
    return out;
  }

  digest(e) {
    const buf = this._alloc(DIGEST_LEN);
    const rc = this.M._sync_engine_digest(e, buf);
    const d = this.M.HEAPU8.slice(buf, buf + DIGEST_LEN);
    this.M._free(buf);
    if (rc !== SYNC_OK) throw new Error("digest failed: " + rc);
    return d;
  }

  /* ---- Blob extension: content-addressed large-value storage, layered
   * purely over set/get/delete/scan (see include/sync_engine.h). ---- */

  /* Content-address and store data in namespace ns; returns the 32-byte
   * blob id (BLAKE2b-256 of data). Idempotent. */
  blobPut(e, ns, data) {
    ns = bytes(ns); data = bytes(data);
    const pn = this._toHeap(ns), pd = this._toHeap(data);
    const idp = this._alloc(BLOB_ID_LEN);
    const rc = this.M._sync_blob_put(e, pn, ns.length, pd, data.length, idp);
    const id = this.M.HEAPU8.slice(idp, idp + BLOB_ID_LEN);
    this.M._free(pn); this.M._free(pd); this.M._free(idp);
    if (rc !== SYNC_OK) throw codedError("blobPut failed", rc);
    return id;
  }
  /* Reassemble + verify the blob. Returns a Uint8Array (possibly empty, but
   * never null, on success); null on SYNC_ERR_NOTFOUND (unknown id, or a
   * manifest present but incomplete — see blobStat to tell those apart);
   * throws (err.code === 7, SYNC_ERR_CORRUPT) if any chunk or the whole
   * fails its content-hash check. */
  blobGet(e, ns, id) {
    ns = bytes(ns); id = bytes(id);
    if (id.length !== BLOB_ID_LEN) throw new Error("blob id must be 32 bytes");
    const pn = this._toHeap(ns), pid = this._toHeap(id);
    const outpp = this.M._malloc(4), outlp = this.M._malloc(4);
    const rc = this.M._sync_blob_get(e, pn, ns.length, pid, outpp, outlp);
    let res = null;
    if (rc === SYNC_OK) {
      const dp = this._u32(outpp), len = this._u32(outlp);
      res = this.M.HEAPU8.slice(dp, dp + len);
      this.M._sync_free(dp);
    }
    this.M._free(pn); this.M._free(pid); this.M._free(outpp); this.M._free(outlp);
    if (rc !== SYNC_OK && rc !== SYNC_ERR_NOTFOUND) throw codedError("blobGet failed", rc);
    return res;
  }
  /* Size + local replication completeness without reassembling/verifying.
   * Returns {size, complete} on success; null on SYNC_ERR_NOTFOUND; throws
   * (err.code === 7) if the manifest is malformed. */
  blobStat(e, ns, id) {
    ns = bytes(ns); id = bytes(id);
    if (id.length !== BLOB_ID_LEN) throw new Error("blob id must be 32 bytes");
    const pn = this._toHeap(ns), pid = this._toHeap(id);
    const sizep = this._alloc(8), compp = this._alloc(4);
    const rc = this.M._sync_blob_stat(e, pn, ns.length, pid, sizep, compp);
    let res = null;
    if (rc === SYNC_OK) {
      const lo = this.M.HEAPU32[sizep >> 2], hi = this.M.HEAPU32[(sizep >> 2) + 1];
      res = { size: Number(BigInt(hi) * 4294967296n + BigInt(lo)),
              complete: this._u32(compp) !== 0 };
    }
    this.M._free(pn); this.M._free(pid); this.M._free(sizep); this.M._free(compp);
    if (rc !== SYNC_OK && rc !== SYNC_ERR_NOTFOUND) throw codedError("blobStat failed", rc);
    return res;
  }
  /* Delete the manifest and every chunk it references. Throws
   * (err.code === 3 SYNC_ERR_NOTFOUND, or 7 SYNC_ERR_CORRUPT for a malformed
   * manifest — nothing is deleted in that case) rather than being silent. */
  blobDelete(e, ns, id) {
    ns = bytes(ns); id = bytes(id);
    if (id.length !== BLOB_ID_LEN) throw new Error("blob id must be 32 bytes");
    const pn = this._toHeap(ns), pid = this._toHeap(id);
    const rc = this.M._sync_blob_delete(e, pn, ns.length, pid);
    this.M._free(pn); this.M._free(pid);
    if (rc !== SYNC_OK) throw codedError("blobDelete failed", rc);
  }

  sessionBegin(e, initiator) { return this.M._sync_session_begin(e, initiator ? 1 : 0); }
  /* Like sessionBegin, but read-scoped to peerPubkey: records in namespaces
   * that peer cannot read are excluded before any fingerprint is computed,
   * so their existence never leaks to an unauthorized peer. */
  sessionBeginScoped(e, initiator, peerPubkey) {
    const pk = this._pk(peerPubkey);
    const s = this.M._sync_session_begin_scoped(e, initiator ? 1 : 0, pk);
    this.M._free(pk);
    return s;
  }
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
    try {
      let msg = this.sessionStep(sa, new Uint8Array(0)).out;
      let turn = sb;
      let empties = msg.length === 0 ? 1 : 0;
      let converged = empties >= 2;
      for (let i = 0; i < 100000 && !converged; i++) {
        const r = this.sessionStep(turn, msg);
        empties = r.out.length === 0 ? empties + 1 : 0;
        converged = empties >= 2;
        msg = r.out;
        turn = turn === sa ? sb : sa;
      }
      if (!converged) throw new Error("sync did not converge (step cap hit)");
    } finally {
      // A throwing step must not leak the session state in the WASM heap.
      this.sessionEnd(sa); this.sessionEnd(sb);
    }
  }

  /* ---- Invites (M5 discovery): peer pubkey + rendezvous address + an
   * optional capability, shared out-of-band (QR, link, message). ---- */

  /* cap is an optional CapabilityHandle (from capRoot/capDelegate/capDecode);
   * omit (or pass 0) for an invite carrying no capability. Size-then-fill,
   * like capEncode. */
  inviteEncode(peerPubkey, rendezvousAddr, cap = 0) {
    const pk = this._pk(peerPubkey);
    const addr = this._cstr(rendezvousAddr);
    const need = this.M._sync_invite_encode(pk, addr, cap, 0, 0);
    if (!need) {
      this.M._free(pk); this.M._free(addr);
      throw new Error("inviteEncode failed (invalid input)");
    }
    const buf = this._alloc(need);
    const n = this.M._sync_invite_encode(pk, addr, cap, buf, need);
    const out = this.M.HEAPU8.slice(buf, buf + n);
    this.M._free(pk); this.M._free(addr); this.M._free(buf);
    if (!n) throw new Error("inviteEncode failed (invalid input)");
    return out;
  }
  /* Decode an invite. Returns {peerPubkey, addr, cap} — cap is a
   * CapabilityHandle (free with capFree) or null when the invite carries
   * none. Throws (err.code = sync_error) on malformed input. The decoded
   * address can never exceed the encoded buffer's length, so buf.length+1
   * is always sufficient scratch space regardless of the original address. */
  inviteDecode(buf) {
    const u8 = bytes(buf);
    const p = this._toHeap(u8);
    const pkp = this._alloc(PUBKEY_LEN);
    const addrCap = u8.length + 1;
    const addrp = this._alloc(addrCap);
    const capOutP = this.M._malloc(4);
    const rc = this.M._sync_invite_decode(p, u8.length, pkp, addrp, addrCap, capOutP);
    let result = null;
    if (rc === SYNC_OK) {
      const peerPubkey = this.M.HEAPU8.slice(pkp, pkp + PUBKEY_LEN);
      const addr = this.M.UTF8ToString(addrp);
      const capPtr = this._u32(capOutP);
      result = { peerPubkey, addr, cap: capPtr || null };
    }
    this.M._free(p); this.M._free(pkp); this.M._free(addrp); this.M._free(capOutP);
    if (rc !== SYNC_OK) throw codedError("inviteDecode failed", rc);
    return result;
  }

  /* ---- Browser persistence: mount IndexedDB-backed storage under a durable
   * engine's path so state survives a page reload. No-ops (throw) under
   * Node, which has no IndexedDB — a durable engine there just uses a plain
   * MEMFS path via open()/openEncrypted(), or a real file via NODEFS if the
   * embedder configures it. Usage (before open()):
   *   binding.mountIdbfs("/data");
   *   await binding.syncFs(true);           // pull persisted state in
   *   const e = binding.open("/data/db", seed);
   *   ...                                    // later, after writes:
   *   await binding.syncFs(false);          // push writes out to IndexedDB
   */
  mountIdbfs(dir) {
    if (IS_NODE) {
      throw new Error("mountIdbfs() is browser-only (Emscripten IDBFS persists " +
        "via IndexedDB); it is a no-op under Node — use a MEMFS path with open() there");
    }
    const FS = this.M.FS;
    if (!FS.analyzePath(dir).exists) FS.mkdir(dir);
    FS.mount(this.M.IDBFS, {}, dir);
  }
  /* populate=true pulls IndexedDB's persisted state into MEMFS (call once
   * after mountIdbfs, before opening an engine at that path); populate=false
   * pushes MEMFS's current state out to IndexedDB (call after writes you
   * want to survive a reload). Returns a Promise resolving on completion. */
  syncFs(populate) {
    if (IS_NODE) {
      return Promise.reject(new Error("syncFs() is browser-only (Emscripten IDBFS " +
        "persists via IndexedDB); it is a no-op under Node"));
    }
    const FS = this.M.FS;
    return new Promise((resolve, reject) => {
      FS.syncfs(!!populate, (err) => (err ? reject(err) : resolve()));
    });
  }
}

/* Node-side loader for a CommonJS Emscripten output: pass the wasm bytes
 * directly so the loader doesn't try to fetch() a file path (Node exposes a
 * global fetch, which trips Emscripten's web path). */
async function loadCjs(jsPath) {
  const createSyncEngine = require(jsPath);
  const fs = require("fs");
  const wasmBinary = fs.readFileSync(jsPath.replace(/\.js$/, ".wasm"));
  const M = await createSyncEngine({ wasmBinary });
  return new Binding(M);
}

/* One place to answer "is this a Node runtime?" for every entry point. */
const IS_NODE =
  typeof process !== "undefined" && !!(process.versions && process.versions.node);

module.exports = { Binding, loadCjs, IS_NODE };
