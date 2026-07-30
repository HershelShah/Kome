# kome-sync (WASM)

[Kome](https://github.com/HershelShah/Kome) — a private, distributed,
offline-first sync engine — compiled to WebAssembly. A browser tab or Node
process is a full replica: convergent (CRDT) data core, incremental range
reconciliation, per-record Ed25519 signatures, capability-scoped access.

The npm package name is `kome-sync` (`kome` is squatted); it matches the PyPI
distribution of the native Python binding.

## Install

```bash
npm install kome-sync
```

## Node

```js
const { load } = require("kome-sync");        // or: import { load } from "kome-sync"

const k = await load();
const a = k.create(new Uint8Array(32).fill(1));
const b = k.create(new Uint8Array(32).fill(2));
k.set(a, "contacts", "alice", "phone", "555-1234");
k.set(b, "contacts", "bob", "email", "bob@example.com");
k.sync(a, b);                                  // range reconciliation, in-process
console.log(new TextDecoder().decode(k.get(a, "contacts", "bob", "email")));
```

Over a network, a node drives the same reconciliation session
(`sessionBegin`/`sessionStep`/`sessionEnd`) with the messages flowing over its
WebSocket — see the repo's `src/transport/ws.*` for the native peer side.

## Browsers / bundlers

The `browser`/`import` conditions resolve to the ES module entry; bundlers
that understand `new URL(..., import.meta.url)` (vite, webpack 5) emit the
`.wasm` as an asset automatically:

```js
import { load } from "kome-sync";
```

If your pipeline can't serve the `.wasm` asset, use the zero-config embedded
entry — the wasm is base64-embedded in the JS (~33% larger download, no asset
to serve):

```js
import { load } from "kome-sync/embedded";
```

## Persistence

`open(path, seed)` gives a durable engine backed by an append-only log on
Emscripten's filesystem — **MEMFS by default**, which does not survive the
process/tab. In a browser, mount IDBFS at the log's directory for persistence
across reloads:

```js
const k = await load();
k.mountIdbfs("/data");          // browser only; throws under Node
await k.syncFs(true);           // pull any persisted state into MEMFS
const e = k.open("/data/db", seed);
k.set(e, "ns", "entity", "field", "value");
await k.syncFs(false);          // push writes out to IndexedDB
```

In Node, prefer the native binding (`pip install kome-sync` for Python, or
link `libsync_engine`) when you want durability on the real filesystem.

## Beyond the basics

The full surface (see `index.d.ts` for exact types) also covers:

- **Entity scanning** — `scan(e, ns, startAfter, limit)`: paginated listing of
  a namespace's entities in canonical sorted order.
- **Blobs** — `blobPut`/`blobGet`/`blobStat`/`blobDelete`: content-addressed
  large-value storage layered over ordinary records, chunked and reassembled
  transparently; `blobGet`/`blobStat` throw with `.code === 7` on a
  content-hash mismatch (`SYNC_ERR_CORRUPT`).
- **Capabilities** — `capRoot`/`capDelegate`/`grant` (already covered above)
  plus `capEncode`/`capDecode`/`capSubject` for serializing a capability to
  bytes (e.g. to embed in an invite or persist it).
- **Revocation** — `revoke`/`isRevoked`: permanently cut off a compromised
  key's access to a namespace.
- **Invites** — `inviteEncode`/`inviteDecode`: a peer's pubkey + rendezvous
  address + an optional capability, packed for out-of-band sharing (QR, link).
- **Encrypted storage** — `openEncrypted(path, seed, key)`: like `open`, but
  the log is sealed at rest (XChaCha20-Poly1305) under a caller-supplied key.
- **Read-scoped sessions** — `sessionBeginScoped(e, initiator, peerPubkey)`:
  like `sessionBegin`, but excludes records in namespaces `peerPubkey` can't
  read before any fingerprint is computed, so their existence never leaks.
  The scoping check runs against `e`'s *own* capability store, so `e` must
  itself hold the relevant root/delegations it wants to enforce (granting a
  root into an engine is what switches that namespace into enforced mode for
  it — see `grant`'s doc comment in `index.d.ts`).

## Guarantees

The WASM build is not a hand-checked subset: the repo's literal GoogleTest
scenario suites compile to WASM and run under Node in CI, and this package's
tarball is gated on the same parity battery the UDP/TCP/WS transports pass.

## Not exposed (by design)

- **`sync_engine_set_logger`** is exported in the WASM ABI but has no JS
  wrapper: it takes a C function pointer (`sync_log_fn`), and bridging a JS
  callback through Emscripten's function table (`addFunction`, which also
  requires `-sALLOW_TABLE_GROWTH`) for a diagnostics-only, off-by-default hook
  isn't worth the added attack surface / API complexity here. Errors already
  surface as thrown `Error`s (with `.code` on the newer wrappers); reach for
  the native binding if you need the log stream itself.
- **The change-record family** (`sync_engine_export` / `sync_engine_apply` /
  `sync_change_encode` / `sync_change_decode` / `sync_change_sign` /
  `sync_changes_free`) is exported in the WASM ABI but not yet wrapped: it
  needs full `sync_change` struct marshalling in both directions, and the
  usual replication path in JS is the session pump (`sessionBegin*` /
  `sessionStep`), which covers sync without it. Wrap it when an out-of-band
  use case (sneakernet/QR transfer of signed records) actually materializes.
- **OPFS** is not wired up alongside IDBFS: `mountIdbfs`/`syncFs` cover the
  common "persist across reloads" case with a stable, broadly-supported API.
  Nothing prevents mounting OPFS yourself via `binding.M.FS` (the raw
  Emscripten module is exposed for exactly this kind of advanced use) if your
  target browsers support it and you want its performance characteristics.
