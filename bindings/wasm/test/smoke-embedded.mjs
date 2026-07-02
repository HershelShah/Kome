/* ESM smoke for the kome-sync/embedded entry (single-file build). Copy into
 * a project with kome-sync installed, then run. */
import { load } from "kome-sync/embedded";

const k = await load();
const a = k.create(new Uint8Array(32).fill(7));
const b = k.create(new Uint8Array(32).fill(8));
k.set(a, "ns", "e", "f", "v");
k.sync(a, b);
if (!k.exists(b, "ns", "e")) throw new Error("embedded ESM smoke failed");
console.log("embedded ESM smoke: OK");
