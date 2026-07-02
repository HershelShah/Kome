import { load } from "kome-sync";

try {
  const k = await load();
  const a = k.create(new Uint8Array(32).fill(1));
  const b = k.create(new Uint8Array(32).fill(2));
  k.set(a, "contacts", "alice", "phone", "555-1234");
  k.set(b, "contacts", "bob", "email", "bob@example.com");
  k.sync(a, b);
  const got = new TextDecoder().decode(k.get(a, "contacts", "bob", "email"));
  const da = k.digest(a), db = k.digest(b);
  const ok = got === "bob@example.com" &&
             k.abiVersion() === 4 &&
             da.length === 32 && da.every((x, i) => x === db[i]);
  document.getElementById("out").textContent = ok ? "converged" : "FAILED";
  document.title = ok ? "KOME_OK" : "KOME_FAIL";
} catch (e) {
  document.getElementById("out").textContent = String(e && e.stack || e);
  document.title = "KOME_FAIL";
}
