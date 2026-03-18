# Kome

Peer-to-peer data replication middleware. C99 public API, C++17 internals, <1 MB binary, ~23 functions.

Kome handles replication, conflict resolution, and version tracking. You own your storage — Kome moves data between peers.

## Build

```bash
cmake -B build
cmake --build build
ctest --test-dir build --output-on-failure
```

With sanitizers:

```bash
cmake -B build -DKOME_SANITIZER=address
cmake --build build
ctest --test-dir build
```

## Install

```bash
cmake --install build --prefix /usr/local
```

## Usage (C)

```c
#include "kome.h"

KomeConfig cfg = { .path = "state.db", .enable_wal = 1, .busy_timeout_ms = 5000 };
KomeEngine *engine = NULL;
kome_open(&cfg, &engine);

uint8_t key[32] = { /* your identity key */ };
kome_set_identity(engine, key, 32);

// Write data
KomeEntryMeta meta;
kome_put(engine, "contacts", (uint8_t*)"alice", 5,
               (uint8_t*)"data", 4, &meta);

// Attach a transport and sync happens automatically
// kome_attach_transport(engine, &my_transport);

kome_close(engine);
```

## Usage (Python)

```python
from kome import Engine

with Engine("state.db") as e:
    e.set_identity(b"my_secret_key_material_here_32b")
    meta = e.put("contacts", b"alice", b"Alice data")
    print(f"seq={meta.seq}")
```

```bash
cd python && LD_LIBRARY_PATH=../build python -m pytest
```

## Transport Interface

Kome is transport-agnostic. Implement the `KomeTransport` interface to use any networking layer:

```c
KomeTransport my_transport = {
    .send = my_send_fn,
    .set_recv_callback = my_set_recv_fn,
    .set_peer_callback = my_set_peer_fn,
    .user_data = my_context,
};
kome_attach_transport(engine, &my_transport);
```

## Architecture

- **Namespaced key-value entries** with automatic metadata (timestamp, author, sequence, hash)
- **Last-Writer-Wins** conflict resolution with pluggable callback override
- **Version vector** sync protocol with live mode for real-time push
- **Replication tracking** with configurable target counts
- **Tombstone GC** with configurable TTL (default 30 days)

## Dependencies

All vendored, zero external:
- SQLite (amalgamation)
- CWPack (MessagePack)
- GoogleTest (fetched at build time, tests only)
