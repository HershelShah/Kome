/* Strict-mode TypeScript consumer of kome-sync's declarations — compiled with
 * `tsc --strict --noEmit` against the installed tarball in the npm gate
 * (wasm.yml). Exercises both entries and the load/Binding surface. */
import { load, Binding, type BytesLike, type EngineHandle } from "kome-sync";
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

  const s = k.sessionBegin(a, true);
  const step: { out: Uint8Array; done: boolean } = k.sessionStep(s, new Uint8Array(0));
  k.sessionEnd(s);

  const cap = k.capRoot(a, ns, 3);
  const rc: number = k.grant(a, cap);
  k.capFree(cap);

  k.del(a, ns, "alice");
  k.destroy(a);

  const k2: Binding = await loadEmbedded();
  void [v, present, d, id, step, rc, k2, k.abiVersion()];
}

void main;
