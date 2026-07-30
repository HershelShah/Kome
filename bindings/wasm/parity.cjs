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

  // ScanPagination: entities come back sorted, and repeated cursor'd pages
  // union back to exactly the full unpaginated listing.
  {
    const e = eng();
    const names = [];
    for (let i = 0; i < 25; i++) { const n = "ent" + String(i).padStart(3, "0"); k.set(e, "sc", n, "f", "v"); names.push(n); }
    const dec = (u8) => new TextDecoder().decode(u8);
    const full = k.scan(e, "sc", null, 0).map(dec);
    let sorted = true;
    for (let i = 1; i < full.length; i++) if (!(full[i - 1] < full[i])) sorted = false;

    const paged = [];
    let cursor = null;
    for (let guard = 0; guard < 100; guard++) {
      const page = k.scan(e, "sc", cursor, 7);
      if (page.length === 0) break;
      for (const p of page) paged.push(dec(p));
      cursor = page[page.length - 1];
    }
    check("ScanPagination",
          full.length === 25 && sorted &&
          paged.length === full.length && paged.every((v, i) => v === full[i]));
    check("ScanEmptyNamespace", k.scan(e, "nope", null, 0).length === 0);
    k.destroy(e);
  }

  // BlobRoundTripMultiChunk: content spanning >2 SYNC_BLOB_CHUNK_MAX chunks
  // reassembles byte-exact; stat reports size+completeness; delete then
  // NOTFOUND.
  {
    const e = eng();
    const CHUNK = 32768;
    const data = new Uint8Array(CHUNK * 3 + 777);
    for (let i = 0; i < data.length; i++) data[i] = (i * 7 + 3) & 0xff;
    const id = k.blobPut(e, "blobs", data);
    check("BlobIdLen", id.length === 32);
    const got = k.blobGet(e, "blobs", id);
    check("BlobRoundTripMultiChunk", eqBytes(got, data));
    const stat = k.blobStat(e, "blobs", id);
    check("BlobStat", !!stat && stat.size === data.length && stat.complete === true);
    // Idempotent put: same content -> same id.
    const id2 = k.blobPut(e, "blobs", data);
    check("BlobPutIdempotent", eqBytes(id, id2));

    k.blobDelete(e, "blobs", id);
    let deletedOk = false;
    try { deletedOk = k.blobGet(e, "blobs", id) === null; } catch { deletedOk = false; }
    check("BlobDeleteThenNotFound", deletedOk);
    let statAfterDelete = null, statThrew = false;
    try { statAfterDelete = k.blobStat(e, "blobs", id); } catch { statThrew = true; }
    check("BlobStatAfterDelete", statAfterDelete === null && !statThrew);
    k.destroy(e);
  }

  // BlobCorrupt: tampering with a chunk's payload directly (bypassing
  // blobPut) makes blobGet detect the mismatch and fail SYNC_ERR_CORRUPT (7),
  // never handing back unverified bytes.
  {
    const e = eng();
    const data = new Uint8Array(32768 + 55).fill(9);
    const id = k.blobPut(e, "blobs2", data);
    const entities = k.scan(e, "blobs2", null, 0);
    let corrupted = 0;
    for (const ent of entities) {
      if (ent.length === 34 && ent[0] === 0x63 && ent[1] === 0x00) { // 'c' 0x00 chunk prefix
        k.set(e, "blobs2", ent, "d", new TextEncoder().encode("tampered"));
        corrupted++;
      }
    }
    check("BlobCorruptSetup", corrupted > 0);
    let code = null;
    try { k.blobGet(e, "blobs2", id); } catch (err) { code = err.code; }
    check("BlobCorruptDetected", code === 7);
    let statCode = null;
    try { k.blobStat(e, "blobs2", id); } catch (err) { statCode = err.code; }
    // stat only re-derives size/completeness from the manifest (untouched
    // here), so a corrupt *chunk* (as opposed to a corrupt manifest) still
    // reports OK; this just documents that blobGet is the verifying path.
    check("BlobStatIgnoresChunkCorruption", statCode === null);
    k.destroy(e);
  }

  // InviteRoundTrip: peer pubkey + address + an embedded capability survive
  // encode/decode, including the capability's subject.
  {
    const owner = eng(), peer = eng();
    const pk = k.identity(peer);
    const root = k.capRoot(owner, "invNs", READ | WRITE);
    const invite = k.inviteEncode(pk, "wss://relay.example.invalid:4433/r", root);
    const decoded = k.inviteDecode(invite);
    check("InviteRoundTripPubkey", eqBytes(decoded.peerPubkey, pk));
    check("InviteRoundTripAddr", decoded.addr === "wss://relay.example.invalid:4433/r");
    check("InviteRoundTripCapPresent", decoded.cap !== null);
    if (decoded.cap !== null) {
      check("InviteRoundTripCapSubject", eqBytes(k.capSubject(decoded.cap), k.capSubject(root)));
      k.capFree(decoded.cap);
    }
    // No-capability invite decodes with cap === null.
    const inviteNoCap = k.inviteEncode(pk, "udp://example.invalid:1", 0);
    const decodedNoCap = k.inviteDecode(inviteNoCap);
    check("InviteRoundTripNoCap", decodedNoCap.cap === null);
    k.capFree(root);
    k.destroy(owner); k.destroy(peer);
  }

  // RevokeIsRevoked: the namespace owner (who must hold ns's own root to
  // revoke at all) can burn a subject's access; a non-owner's attempt is
  // rejected (SYNC_ERR_UNAUTHORIZED).
  {
    const owner = eng(), subject = eng(), nonOwner = eng();
    const spk = k.identity(subject);
    const root = k.capRoot(owner, "revNs", READ | WRITE);
    const deleg = k.capDelegate(owner, root, spk, WRITE, 0);
    k.grant(owner, root);
    k.grant(subject, deleg);
    check("IsRevokedFalseBeforeRevoke", k.isRevoked(owner, "revNs", spk) === false);
    check("RevokeByNonOwnerRejected", k.revoke(nonOwner, "revNs", spk) === 6 /* SYNC_ERR_UNAUTHORIZED */);
    check("RevokeByOwnerOk", k.revoke(owner, "revNs", spk) === 0);
    check("IsRevokedTrueAfterRevoke", k.isRevoked(owner, "revNs", spk) === true);
    k.capFree(root); k.capFree(deleg);
    [owner, subject, nonOwner].forEach((e) => k.destroy(e));
  }

  // OpenEncryptedRoundtrip: an encrypted durable engine's data survives
  // close/reopen with the right key; the wrong key fails cleanly (throws,
  // no partially-usable engine).
  {
    const key = new Uint8Array(32).fill(0x5a);
    const wrongKey = new Uint8Array(32).fill(0x5b);
    const e1 = k.openEncrypted("/enc-a.db", seed(s++), key);
    k.set(e1, "ns", "secret", "f", "shh");
    const d1 = k.digest(e1);
    k.destroy(e1);

    const e2 = k.openEncrypted("/enc-a.db", seed(0), key);
    check("OpenEncryptedRightKey",
          eqBytes(k.digest(e2), d1) &&
          eqBytes(k.get(e2, "ns", "secret", "f"), enc("shh")));
    k.destroy(e2);

    let wrongKeyThrew = false;
    try { k.openEncrypted("/enc-a.db", seed(0), wrongKey); }
    catch { wrongKeyThrew = true; }
    check("OpenEncryptedWrongKeyFails", wrongKeyThrew);
  }

  // ScopedSessionReadAuthorization: a scoped session sync excludes an
  // unauthorized namespace's records for a third identity while an
  // authorized peer receives them; open (unowned) namespaces stay visible to
  // everyone regardless of scoping.
  {
    const owner = eng(), authorized = eng(), unauthorized = eng();
    const apk = k.identity(authorized);
    const root = k.capRoot(owner, "secretNs", READ | WRITE);
    const readOnly = k.capDelegate(owner, root, apk, READ, 0);
    // The sender's OWN capability store drives scoping/enforcement, so the
    // owner must hold both the root and the delegation it wants to honor.
    k.grant(owner, root);
    k.grant(owner, readOnly);
    k.grant(authorized, readOnly);

    k.set(owner, "secretNs", "e1", "f", "topsecret");
    k.set(owner, "openNs", "pub", "f", "public");

    const pump = (sa, sb) => {
      let msg = k.sessionStep(sa, new Uint8Array(0)).out;
      let turn = sb, empties = msg.length === 0 ? 1 : 0;
      for (let i = 0; i < 100000 && empties < 2; i++) {
        const r = k.sessionStep(turn, msg);
        empties = r.out.length === 0 ? empties + 1 : 0;
        msg = r.out;
        turn = turn === sa ? sb : sa;
      }
      k.sessionEnd(sa); k.sessionEnd(sb);
    };

    pump(k.sessionBeginScoped(owner, true, apk), k.sessionBegin(authorized, false));
    check("ScopedAuthorizedGetsSecret", k.exists(authorized, "secretNs", "e1"));
    check("ScopedAuthorizedGetsOpen", k.exists(authorized, "openNs", "pub"));

    const upk = k.identity(unauthorized);
    pump(k.sessionBeginScoped(owner, true, upk), k.sessionBegin(unauthorized, false));
    check("ScopedUnauthorizedDeniedSecret", !k.exists(unauthorized, "secretNs", "e1"));
    check("ScopedUnauthorizedGetsOpen", k.exists(unauthorized, "openNs", "pub"));

    k.capFree(root); k.capFree(readOnly);
    [owner, authorized, unauthorized].forEach((e) => k.destroy(e));
  }

  console.log(failed ? `\nWASM PARITY FAILED (${failed})` : "\nWASM PARITY OK (sync, storage + reopen, capability enforcement, scan, blobs, invites, revocation, encrypted storage, and read-scoped sessions all in WASM)");
  process.exit(failed ? 1 : 0);
})().catch((e) => { console.error(e); process.exit(1); });
