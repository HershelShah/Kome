/* ESM smoke against the installed kome-sync package. Copy into (and run
 * from) a project with kome-sync installed — ESM resolves imports relative
 * to this file. */
import { load } from "kome-sync";

const k = await load();
const a = k.create(new Uint8Array(32).fill(1));
const b = k.create(new Uint8Array(32).fill(2));
k.set(a, "contacts", "alice", "phone", "555-1234");
k.set(b, "contacts", "bob", "email", "bob@example.com");
k.sync(a, b);
const v = new TextDecoder().decode(k.get(a, "contacts", "bob", "email"));
const eq = k.digest(a).every((x, i) => x === k.digest(b)[i]);
if (v !== "bob@example.com" || !eq || k.abiVersion() !== 4)
  throw new Error("ESM smoke failed");
console.log("ESM smoke: OK");
