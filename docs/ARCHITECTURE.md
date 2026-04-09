# Kome Architecture

## What Kome Does

Kome is a peer-to-peer key-value replication library. Apps use it to sync data
directly between devices without a central server.

```
┌─────────────┐           ┌─────────────┐
│   Device A  │◄─────────►│   Device B  │
│             │  TCP/WS/   │             │
│  ┌───────┐  │  BLE/any   │  ┌───────┐  │
│  │ Kome  │  │            │  │ Kome  │  │
│  │Engine │  │            │  │Engine │  │
│  └───┬───┘  │            │  └───┬───┘  │
│      │      │            │      │      │
│  ┌───┴───┐  │            │  ┌───┴───┐  │
│  │SQLite │  │            │  │SQLite │  │
│  └───────┘  │            │  └───────┘  │
└─────────────┘            └─────────────┘
```

Each device has its own SQLite database. When two devices connect (via any
transport the app provides), Kome exchanges version vectors to determine who
has newer data, sends only the missing entries, resolves conflicts, and
enters live-push mode where subsequent local writes are forwarded instantly.

## Source Map (2,864 lines)

```
include/
  kome.h              321  Public C99 API — all types, constants, 25 functions

src/
  kome_entry.hpp       50  Unified Entry struct with to_meta/from_meta helpers
  kome_engine.hpp      46  KomeEngine struct — the opaque handle behind the C API
  kome_engine.cpp     667  C API implementation — lifecycle, CRUD, listing, callbacks
  kome_log.hpp         75  KomeLog class — SQLite storage interface
  kome_log.cpp        413  SQLite implementation — tables, prepared stmts, queries
  kome_sync.hpp        77  KomeSyncManager — sync state machine interface
  kome_sync.cpp       540  Sync protocol — handshake, 5-phase entry processing, gossip
  kome_wire.hpp        51  Wire protocol types and encode/decode declarations
  kome_wire.cpp       411  MessagePack serialization using cwpack
  kome_conflict.hpp    29  Conflict resolution interface
  kome_conflict.cpp    44  LWW default + user callback delegation
  kome_util.hpp        24  SHA-256, timestamp, key derivation declarations
  kome_util.cpp       116  SHA-256 implementation, timestamp, derive_db_key
```

## Data Model

### Entry (the fundamental unit)

Every piece of data in Kome is an **Entry**. All entries live in a
**namespace** (a string like `"messages"` or `"profiles"`).

```
┌──────────────────────────────────────────────────────┐
│                      Entry                           │
├──────────────┬───────────────────────────────────────┤
│ ns           │ "messages"           (namespace)      │
│ key          │ [0x6D, 0x73, 0x67]  (binary key)     │
│ value        │ [bytes...]          (binary value)    │
│ timestamp_us │ 1712345678000000    (microseconds)    │
│ author       │ [32-byte SHA-256 fingerprint]         │
│ seq          │ 42                  (per-author mono) │
│ hash         │ [32-byte SHA-256 of value]            │
│ tombstone    │ 0 or 1              (deleted flag)    │
└──────────────┴───────────────────────────────────────┘
```

The `Entry` struct (defined in `kome_entry.hpp`) is used everywhere internally —
both as the storage format (`LogEntry = Entry`) and the wire format
(`SyncEntry = Entry`). The `to_meta()` and `from_meta()` methods convert
between `Entry` and the public `KomeEntryMeta` C struct.

### Storage Schema (SQLite)

```sql
change_log (ns, key, value, timestamp_us, author, seq, hash, value_len, tombstone)
           PRIMARY KEY (ns, key)
           INDEX idx_cl_author_seq ON (author, seq)

version_vector (author, seq)       -- tracks highest seq seen per author

namespace_settings (ns, tombstone_ttl_sec)  -- per-namespace entry TTL
```

## Lifecycle

```
  kome_open()           Create engine, open SQLite database
       │
  kome_set_identity()   SHA-256(key_material) → 32-byte fingerprint
       │                Loads version vector to resume sequence numbering
       │
  ┌────┴──────────────────────────────────────┐
  │  Ready: kome_put / kome_get / kome_delete │
  └────┬──────────────────────────────────────┘
       │
  kome_attach_transport()   Wires up send/recv/peer callbacks
       │                    Creates KomeSyncManager
       │
  ┌────┴──────────────────────────────┐
  │  Connected: sync + live push      │
  │  Peers connect → handshake → LIVE │
  └────┬──────────────────────────────┘
       │
  kome_close()   Shuts down sync, closes SQLite
```

## Sync Protocol (v4)

### Wire Messages

All messages are a 1-byte type prefix followed by a MessagePack payload.

```
0x01 SYNC_REQUEST   { pv: 4, vv: {author→seq, ...}, nf: ["ns1","ns2"] }
0x02 SYNC_ENTRY     { ns, k, v, ts, a, seq, h, t }
0x03 SYNC_DONE      (empty — just the type byte)
0x04 SYNC_ACK       { a: author, seq: N }
0x05 LIVE_ENTRY     (same format as SYNC_ENTRY, different type byte)
0x06 BATCH_ENTRY    { n: count, e: [entry, entry, ...] }
```

### Handshake and Sync Flow

```
     Alice                                    Bob
       │                                       │
       │──── SYNC_REQUEST(vv_A, ns_filter) ───►│
       │                                       │
       │◄─── SYNC_REQUEST(vv_B, ns_filter) ────│
       │                                       │
       │  (compute namespace intersection)     │  (compute namespace intersection)
       │                                       │
       │◄──── SYNC_ENTRY (missing for A) ──────│
       │◄──── SYNC_ENTRY ─────────────────────│
       │◄──── SYNC_DONE ──────────────────────│
       │                                       │
       │───── SYNC_ENTRY (missing for B) ─────►│
       │───── SYNC_ENTRY ────────────────────►│
       │───── SYNC_DONE ─────────────────────►│
       │                                       │
       │         Both → LIVE mode              │
       │                                       │
       │───── LIVE_ENTRY (new write) ─────────►│
       │◄──── SYNC_ACK ───────────────────────│
       │                                       │
       │◄──── LIVE_ENTRY (new write) ──────────│
       │───── SYNC_ACK ──────────────────────►│
```

### Peer Sync State Machine

```
                    peer connects
                         │
                         ▼
                    ┌─────────┐
                    │  IDLE   │
                    └────┬────┘
                         │ initiate_sync()
                         ▼
                    ┌──────────┐
                    │ SYNCING  │
                    └─┬──────┬─┘
         we send      │      │    they send
         SYNC_DONE    │      │    SYNC_DONE
                      ▼      ▼
              ┌──────────┐ ┌───────────┐
              │ WE_DONE  │ │ THEY_DONE │
              └─────┬────┘ └────┬──────┘
                    │           │
         they send  │           │ we send
         SYNC_DONE  │           │ SYNC_DONE
                    ▼           ▼
                    ┌─────────┐
                    │  LIVE   │──► real-time push of all
                    └─────────┘    subsequent local writes

               peer disconnects → state removed entirely
```

### Namespace-Scoped Sync

Both sides declare which namespaces they care about. The intersection
determines what flows:

```
  Alice: sync_namespaces = ["chat", "media"]
  Bob:   sync_namespaces = ["chat", "status"]
                                    │
                            intersection = ["chat"]

  Only "chat" entries are exchanged. Alice's "media" and Bob's "status"
  stay local. Empty list = sync everything (default).
```

### Entry TTL

Per-namespace time-to-live. Expired entries are:
1. **Rejected during sync** — the receiver checks `now - timestamp > TTL`
2. **Garbage-collected** from storage by the tombstone GC (runs every 100 ACKs)

```
  kome_set_entry_ttl(engine, "ephemeral", 3600)  // 1 hour

  Old entry from peer:  timestamp = 2 hours ago → rejected (dropped silently)
  Fresh entry from peer: timestamp = 30 min ago → accepted
```

## Remote Entry Processing (the core algorithm)

When entries arrive from a peer (single entry, live push, or batch), they
all flow through `process_remote_entries()` — a single unified 5-phase
pipeline:

```
  ┌─────────────────────────────────────────────────────────────┐
  │                  process_remote_entries()                    │
  │                                                             │
  │  ┌─────────────────────────────────────────────────────┐    │
  │  │ FILTER (under engine lock)                          │    │
  │  │  - Namespace scope check                            │    │
  │  │  - Size limits (ns/key/value)                       │    │
  │  │  - Clock drift bounds (±24h)                        │    │
  │  │  - Entry TTL expiry                                 │    │
  │  │  - SHA-256 hash verification                        │    │
  │  │  → Drop invalid entries, keep accepted              │    │
  │  └──────────────────────┬──────────────────────────────┘    │
  │                         ▼                                   │
  │  ┌──────────────────────────────────────────────────────┐   │
  │  │ PHASE 1: Read local state (engine lock)              │   │
  │  │  - Snapshot conflict callback                        │   │
  │  │  - For each entry: read local version if exists      │   │
  │  │  - Record local_seq for TOCTOU detection             │   │
  │  └──────────────────────┬───────────────────────────────┘   │
  │                         ▼                                   │
  │  ┌──────────────────────────────────────────────────────┐   │
  │  │ PHASE 2: Conflict resolution (NO LOCKS)              │   │
  │  │  - No local → store remote                           │   │
  │  │  - Conflict → call user callback or LWW default      │   │
  │  │    LWW: higher timestamp > higher author > higher seq│   │
  │  │  - Merge → user provides merged value via malloc      │   │
  │  └──────────────────────┬───────────────────────────────┘   │
  │                         ▼                                   │
  │  ┌──────────────────────────────────────────────────────┐   │
  │  │ PHASE 3: Write (engine lock, inside transaction)     │   │
  │  │  - TOCTOU guard: re-check local seq hasn't changed   │   │
  │  │  - put_entry + update_version_vector                 │   │
  │  │  - Snapshot change callbacks for Phase 4              │   │
  │  └──────────────────────┬───────────────────────────────┘   │
  │                         ▼                                   │
  │  ┌──────────────────────────────────────────────────────┐   │
  │  │ PHASE 4: Fire callbacks (NO LOCKS)                   │   │
  │  │  - on_remote_change callback (global)                │   │
  │  │  - on_remote_change_ns callback (per-namespace)      │   │
  │  └──────────────────────┬───────────────────────────────┘   │
  │                         ▼                                   │
  │  ┌──────────────────────────────────────────────────────┐   │
  │  │ PHASE 5: Gossip + ACK (peers lock, then none)        │   │
  │  │  - Forward stored entries to other LIVE peers         │   │
  │  │    (excluding sender — no echo loops)                 │   │
  │  │  - Send SYNC_ACK per entry                           │   │
  │  └──────────────────────────────────────────────────────┘   │
  └─────────────────────────────────────────────────────────────┘
```

### Why 5 phases?

The phases exist to avoid deadlocks. Two locks are involved:

- **`engine->mu`** — protects the database and all engine state
- **`peers_mu_`** — protects the peer connection map

Lock ordering contract: **always `engine->mu` before `peers_mu_`**. Never
hold `peers_mu_` while acquiring `engine->mu`.

The conflict callback runs **outside all locks** (Phase 2) so user code can
call back into kome_put/kome_get without deadlocking. This creates a TOCTOU
race (another thread might write between Phase 1 and Phase 3), which Phase 3
detects by re-reading the local entry's sequence number.

## Gossip Relay

When peer A sends an entry to peer B, and B has other LIVE peers (C, D),
B forwards the entry to C and D automatically. This creates mesh
replication without requiring full connectivity:

```
  A ──write──► B ──relay──► C
                  └──relay──► D

  All four peers converge to the same state.
  Each relay excludes the sender to prevent echo loops.
```

## Conflict Resolution

Default: **Last-Writer-Wins (LWW)**

```
  Tiebreak chain:
    1. Higher timestamp_us wins
    2. Higher author fingerprint (memcmp of 32 bytes) wins
    3. Higher sequence number wins
```

Custom: register `kome_on_conflict()` with a callback that returns
`KOME_KEEP_LOCAL`, `KOME_KEEP_REMOTE`, or `KOME_MERGE`. For merge,
the callback allocates a new value with `malloc()`.

## Thread Safety

All `kome_*` functions are safe to call concurrently on the same engine.
The engine lock (`mu`) serializes all database access and state mutations.

Callbacks fire **without** the engine lock held, so they may call back into
the kome API freely. This is critical — it means `kome_on_remote_change()`
callbacks can call `kome_put()` or `kome_get()` without deadlocking.

## Transport Interface

Kome does not include any transport. The app provides one by filling in
a `KomeTransport` struct with three function pointers:

```c
struct KomeTransport {
    send               // send bytes to a peer (identified by 32-byte fingerprint)
    set_recv_callback   // register handler for incoming bytes
    set_peer_callback   // register handler for connect/disconnect events
    user_data          // app-owned context pointer
};
```

This lets Kome work over TCP, WebSocket, Bluetooth, libp2p, or anything
else. The only requirement: the transport must deliver the 32-byte peer
fingerprint with every message (so Kome knows who sent it).

## Local Write Flow

```
  App calls kome_put("chat", key, value)
       │
       ▼
  ┌─ engine lock ─────────────────────────────┐
  │  1. Generate metadata (timestamp, seq, hash) │
  │  2. Write to SQLite (put_entry)              │
  │  3. Update version vector                    │
  │  4. Snapshot sync_mgr pointer                │
  └──────────────────────────────────────────────┘
       │
       ▼
  Build Entry from metadata
       │
       ▼
  sync_mgr->on_local_write(entry)
       │
       ▼
  ┌─ peers lock ──────────────────────────┐
  │  Collect LIVE peers whose             │
  │  agreed_namespaces include "chat"     │
  └──────────────────────────────────────────┘
       │
       ▼
  Send LIVE_ENTRY to each matching peer
```

## Public API Summary (24 functions)

```
Lifecycle (3):    open, close, set_identity
CRUD (5):         put, put_batch, delete, get, free_value
Callbacks (5):    on_remote_change, on_remote_change_ns, on_conflict,
                  on_sync_done, on_sync_progress
Transport (2):    attach_transport, sync_with
Data Policy (2):  set_sync_namespaces, set_entry_ttl
Introspection (6): get_meta, version_vector, free_version_vector,
                    list_namespaces, free_namespaces,
                    list_keys, free_keys, get_all, free_entries
Info (3):         stats, errstr, version
```
