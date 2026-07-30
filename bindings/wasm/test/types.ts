/* Strict-mode TypeScript consumer of kome-sync's declarations — compiled with
 * `tsc --strict --noEmit` against the installed tarball in the npm gate
 * (wasm.yml). Exercises both entries and the load/Binding surface. */
import {
  load, Binding,
  type BytesLike, type EngineHandle, type SessionHandle, type CapabilityHandle,
  type BlobStat, type DecodedInvite, type CodedError,
} from "kome-sync";
import { load as loadEmbedded } from "kome-sync/embedded";

async function main(): Promise<void> {
  const k: Binding = await load();

  const a: EngineHandle = k.create(new Uint8Array(32));
  const ns: BytesLike = "contacts";
  k.set(a, ns, "alice", "phone", "555-1234");
  const v: Uint8Array | null = k.get(a, ns, "alice", "phone");
  const present: boolean = k.exists(a, ns, "alice");
  const d: Uint8Array = k.digest(a);
  const id: Uint8Array = k.identity(a);
  const site: Uint8Array = k.siteId(a);
  k.flush(a);

  const s: SessionHandle = k.sessionBegin(a, true);
  const step: { out: Uint8Array; done: boolean } = k.sessionStep(s, new Uint8Array(0));
  k.sessionEnd(s);

  const cap: CapabilityHandle = k.capRoot(a, ns, 3);
  const rc: number = k.grant(a, cap);
  const capBytes: Uint8Array = k.capEncode(cap);
  const cap2: CapabilityHandle = k.capDecode(capBytes);
  const subj: Uint8Array = k.capSubject(cap2);
  k.capFree(cap2);

  const b: EngineHandle = k.create(new Uint8Array(32).fill(9));
  const bpk: Uint8Array = k.identity(b);
  const deleg: CapabilityHandle = k.capDelegate(a, cap, bpk, 1, 0);
  const grc: number = k.grant(a, deleg);
  const scoped: SessionHandle = k.sessionBeginScoped(a, true, bpk);
  k.sessionEnd(scoped);

  const revokeRc: number = k.revoke(a, ns, bpk);
  const revoked: boolean = k.isRevoked(a, ns, bpk);
  k.capFree(cap); k.capFree(deleg);

  // scan
  const entities: Uint8Array[] = k.scan(a, ns, null, 10);
  const entities2: Uint8Array[] = k.scan(a, ns, entities[0], 0);

  // blobs
  const blobId: Uint8Array = k.blobPut(a, "blobs", new Uint8Array([1, 2, 3]));
  const blobData: Uint8Array | null = k.blobGet(a, "blobs", blobId);
  const blobInfo: BlobStat | null = k.blobStat(a, "blobs", blobId);
  try {
    k.blobDelete(a, "blobs", blobId);
  } catch (e) {
    const ce = e as CodedError;
    void ce.code;
  }

  // invites
  const invite: Uint8Array = k.inviteEncode(bpk, "wss://example.invalid", 0);
  const decoded: DecodedInvite = k.inviteDecode(invite);
  if (decoded.cap !== null) k.capFree(decoded.cap);

  // encrypted storage + persistence helpers (types only — mountIdbfs/syncFs
  // throw under Node, exercised at runtime by the browser smoke test instead)
  const enc: EngineHandle = k.openEncrypted("/x.db", new Uint8Array(32), new Uint8Array(32));
  k.destroy(enc);
  const mountFn: (dir: string) => void = k.mountIdbfs.bind(k);
  const syncFsFn: (populate: boolean) => Promise<void> = k.syncFs.bind(k);

  k.del(a, ns, "alice");
  k.destroy(a);
  k.destroy(b);

  const k2: Binding = await loadEmbedded();
  void [
    v, present, d, id, site, step, rc, k2, k.abiVersion(), subj, grc,
    revokeRc, revoked, entities2, blobData, blobInfo, mountFn, syncFsFn,
  ];
}

void main;
