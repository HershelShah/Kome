# kome-sync-runtime

A generic, app-agnostic sync loop over WebSocket for the [`kome-sync`](../wasm)
WASM binding. `kome-sync` gives you a manual `sessionStep` pump; this package
turns it into a running connection: dial a hub, gossip on an interval,
reconnect on failure, converge. It has **no application/social semantics** —
just namespaces, entities, fields and bytes, exactly like the binding it
wraps.

Two roles:

- **`SyncClient`** — the dialer. Runs in a browser tab or under Node.
- **`SyncHub`** — the listener. Node only (wraps a `ws` `WebSocketServer`);
  many clients connect to it and converge with it (and, transitively across
  gossip cycles, with each other).

## Install

Within this repo, `kome-sync-runtime` depends on the sibling `kome-sync`
package via `"kome-sync": "file:../wasm"`, so it builds in place:

```bash
cd bindings/wasm-runtime
npm install
npm run build   # tsc -> dist/
npm test        # node --test
```

## Usage — browser `SyncClient`

```ts
import { load } from "kome-sync";
import { SyncClient } from "kome-sync-runtime";

const binding = await load();
const engine = binding.create(mySeed); // or binding.open(path, seed) for durable/IDBFS

const client = new SyncClient({
  engine,
  binding,
  url: "wss://my-hub.example.com",
  intervalMs: 2000, // gossip cycle period
});

client.onSync(({ durationMs }) => {
  console.log(`converged a cycle in ${durationMs}ms`);
  // The engine has no change callback, so poll your own state here, e.g.:
  // const rows = binding.scan(engine, "my-ns");
});
client.onError((err) => console.warn("sync error:", err));
client.onStateChange((state) => console.log("connection:", state)); // 'connecting' | 'open' | 'closed'

client.connect();

// later
client.stop(); // idempotent; closes the socket, ends any live session
```

`SyncClient` works completely unchanged under Node >=22, which also has a
global `WebSocket` client — useful for a Node-to-Node hub-to-hub link, or for
tests.

## Usage — Node `SyncHub`

```ts
import { load } from "kome-sync";
import { SyncHub } from "kome-sync-runtime";

const binding = await load();
const engine = binding.open("/data/hub.log", hubSeed); // a durable engine, typically

const hub = new SyncHub({
  engine,
  binding,
  port: 8787,
  token: process.env.HUB_TOKEN, // optional shared bearer token; see Trust model
});

await hub.start();
hub.onError((err) => console.warn("hub error:", err));

// later
await hub.stop(); // closes every connection, ends every session, releases the port
```

## Wire protocol

Each sync-session message is exactly **one binary WebSocket frame**: a 1-byte
tag followed by the payload.

| tag | name | payload |
|-----|------|---------|
| `0x00` | cycle-begin | empty — the initiator announcing the start of a new gossip cycle |
| `0x01` | session | the bytes in/out of `Binding.sessionStep` |

Same code runs on both ends (`src/wire.ts`, `src/peer.ts`): a connection is
never more than one `SessionHandle` deep at a time. A cycle runs as:

1. Initiator: `sessionBegin(engine, true)` (or `sessionBeginScoped` when
   `peerPubkey` + `scoped` are set) → send cycle-begin → drive `sessionStep`,
   sending every non-empty output chunk, until a step produces empty output
   (mirroring the native transport's own drain loop in
   `src/transport/connection.cpp` — a `sessionStep` call's own `done` flag
   only reflects whether *that one call* has more queued output, not whether
   the whole exchange has converged, so neither side relies on it).
2. Whichever side runs out of things to send explicitly says so with an
   empty session frame (needed because the peer may be blocked awaiting a
   reply), then ends its session. `sessionEnd` always runs in a `finally`.
3. A per-cycle timeout (default 30s) aborts a stuck cycle and still ends the
   session cleanly.

A connection that is *not* the current initiator responds to an inbound
cycle-begin as a responder (`sessionBegin(engine, false)` /
`sessionBeginScoped(engine, false, peerPubkey)`); at most one responder
session runs at a time, torn down on completion.

Identity for scoping: a `SyncClient` appends its own engine's identity as
`?pubkey=<hex>` on the connection URL (plus `?token=...` if configured) — this
is how a `SyncHub` learns which pubkey to scope reads by for that connection.

`onChange` is intentionally not provided — `Binding` has no
change-notification callback. Poll your own state (`scan`/`get`/`exists`)
after `onSync` fires to pick up what a cycle just merged in.

## Trust model — read this before pointing a hub at anything but your own devices

This WebSocket path authenticates at the **transport** layer only: terminate
TLS in front of it (`wss://`, e.g. behind a reverse proxy) and optionally
require a shared bearer `token`, checked on the WS upgrade (`SyncHub`'s
`token` option / `SyncClient`'s `token` option). Read-scoping is keyed off the
pubkey each client **self-reports** in its connection URL — there is no
signature or challenge proving the client actually owns that key.

It does **not** perform the Noise XX handshake + identity-proof mutual auth
that the native UDP path (`connect_and_sync` / `komed`) does — the WASM
binding doesn't expose a signing primitive over this API surface capable of
proving pubkey ownership from JS. A malicious or buggy client can claim any
pubkey and thereby attempt to widen the read-scope the hub applies to it
(`sessionBeginScoped` only filters by capabilities *the hub's own engine* has
granted for that claimed key — it will scope generously for a pubkey nobody
actually authenticated, if the hub happens to have granted access for it).

**So:** appropriate for syncing your own devices, or a hub you run whose
clients you also control/deploy (behind your own token + TLS). It is not a
substitute for real peer authentication if you don't trust every holder of
the token. This is the same class of call `komed`'s `cap_file` serving makes
explicit — don't oversell this as more than it is.

## API surface

- `SyncClient({ engine, binding, url, peerPubkey?, scoped=true, intervalMs=2000, cycleTimeoutMs=30000, token? })`
  - `connect()`, `stop()` (idempotent)
  - `onSync(cb)`, `onError(cb)`, `onStateChange(cb)`
  - `liveSessions` — 0 or 1; for leak-checking
- `SyncHub({ engine, binding, port, host='127.0.0.1', scoped=true, cycleTimeoutMs=30000, maxConnections=256, token? })`
  - `start()`, `stop()` (idempotent; both return Promises)
  - `onError(cb)`
  - `liveSessions`, `connectionCount` — for leak-checking / monitoring
- `Socket` interface + `BrowserSocket` (native `WebSocket`) / `NodeSocket`
  (wraps a `ws` connection) — the transport abstraction; swap in a custom
  `Socket` for a different transport without touching the gossip logic.
- `GossipPeer` — the shared, transport-agnostic pump `SyncClient` and
  `SyncHub` both run per connection; exported for advanced use (custom
  transports, instrumentation).

Dependencies: the core (`wire.ts`, `socket.ts`, `peer.ts`, `syncClient.ts`) has
**zero** runtime dependencies — `BrowserSocket` uses only the global
`WebSocket`. `ws` is imported solely by `nodeSocket.ts`, used only by
`SyncHub` (and by `SyncClient` never — Node >=22's own global `WebSocket`
client is what dials out, in Node or a browser alike).

## Tests

`test/*.test.mjs`, run with `node --test` against the built `dist/` (only
in-memory `binding.create()` engines, for speed):

1. **`convergence.test.mjs`** — two `SyncClient`s + one `SyncHub` over real
   localhost WebSocket; each client writes distinct records before
   connecting; asserts both clients and the hub converge to identical
   digests with every record present, within a bounded timeout. The headline
   test.
2. **`reconnect.test.mjs`** — kills the hub mid-run, writes a record on the
   disconnected client, restarts the hub on the same port, asserts the
   client reconnects (backoff) and re-converges, including the
   written-while-disconnected record.
3. **`leak.test.mjs`** — runs 200 gossip cycles on a fast interval, asserting
   `liveSessions` never exceeds 1 and returns to 0 between cycles, no
   unhandled errors, and `stop()` leaves zero live sessions.
4. **`scoped.test.mjs`** — a hub-owned namespace is capability-scoped to one
   authorized client's pubkey; an unauthorized third client's engine never
   receives it, while an open namespace still syncs to both (mirrors the
   binding's own scoped-session parity test, over the runtime).
5. **`lifecycle.test.mjs`** — `SyncClient.stop()` and `SyncHub.stop()` are
   idempotent, abort in-flight cycles cleanly, and a `SyncHub` can `start()`
   again on the same port immediately after `stop()`.

Run everything:

```bash
npm run build && npm test
```

### CI

This package is Node-only tooling (`ws`, `node --test`) with no native/WASM
build step of its own (it consumes the already-built `kome-sync` artifacts),
so it doesn't fit `ctest`. A CI job would be a plain npm job, e.g. add
alongside `npm.yml`:

```yaml
- run: tools/npm_build.sh                       # builds bindings/wasm (kome-sync)
- run: cd bindings/wasm-runtime && npm install && npm run build && npm test
```
