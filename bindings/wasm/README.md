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
process/tab. In a browser, mount IDBFS or OPFS at the log's directory for
persistence across reloads. In Node, prefer the native binding
(`pip install kome-sync` for Python, or link `libsync_engine`) when you want
durability on the real filesystem.

## Guarantees

The WASM build is not a hand-checked subset: the repo's literal GoogleTest
scenario suites compile to WASM and run under Node in CI, and this package's
tarball is gated on the same parity battery the UDP/TCP/WS transports pass.
