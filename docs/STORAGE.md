# Storage: an append-only log (Bitcask-style)

Kome persists to a single **append-only log**, not a database. SQLite was used
only as a durable key-value store (full state in RAM; load-on-open +
write-through), never as a query engine — so a ~250K-LOC SQL B-tree was overkill
in the trusted path. The log is dependency-free, smaller (native + WASM), uses
one encoding for disk and wire, and makes at-rest encryption and compaction-as-GC
straightforward. See `src/storage.{h,cpp}`.

## On-disk format

```
file   = MAGIC(8 "KOMELOG1")  frame*
frame  = body_len:u32le  body(body_len)  checksum(8 = SHA-256(body)[0:8])
body   = entry_count:u32le  entry*
entry  = type:u8  payload
  META(1)   : key:bytes  value:bytes            (schema_version, seed, hlc, db_clock)
  ENTITY(2) : ns:bytes ent:bytes  causal_length:u64le  ex_author[32] ex_sig[64]
  FIELD(3)  : ns:bytes ent:bytes field:bytes value:bytes
              hlc_physical:u64le hlc_logical:u32le  author[32] sig[64]
  CAP(4)    : blob:bytes
bytes  = varint(len) raw   (reuses the codec/byteorder primitives)
```

One mutation is one frame, `write()`+`fsync()`'d as a unit. A standalone `put_*`
(e.g. a capability grant) is its own frame; calls between `begin()`/`commit()`
land as a single atomic frame.

## Crash safety

A crash leaves at most a **torn trailing frame**. On reopen, `load()` replays
frames in order; the first frame with a short read or a checksum mismatch ends
the replay and the file is truncated to the last good frame. This is safe
because:

- A committed mutation is a fully written, fsync'd frame → it survives.
- An in-flight mutation is at most a torn tail → dropped (it never durably
  committed, exactly like an uncommitted DB transaction).
- **Replay merges each record by the engine's own LWW / existence rule**, so it
  is order-independent and idempotent: a duplicated or partially-written tail
  cannot corrupt state. The same property that makes the CRDT converge makes log
  replay safe.

Signatures are **re-verified on load** — an on-disk record is not trusted just
because it is on disk (a swapped file can't inject forged records). The
identity-bearing file is `chmod 0600` best-effort.

## Compaction (the Bitcask "merge")

Append-only means the log grows with the number of writes. `compact()` rewrites
it to **one record per live cell** (a meta frame + one frame per entity with its
field registers + a capability frame), bounding the file to O(state) and keeping
reopen O(state).

- **Trigger** (`maybe_compact`, from the write path): compact when the log
  exceeds `max(64 KiB, 2 × its size at the last compaction)`. The doubling gives
  amortized O(1) write amplification. It also runs once at load if an existing
  log is more than 2× its live image.
- **Atomicity:** stream the image frame-by-frame through a small bounded
  buffer (256 KiB) to `<path>.tmp` — never building the whole image in RAM —
  then `ftruncate` the temp file to the exact streamed size → `fsync` →
  `rename()` over the log (the atomic commit point, unchanged) → reopen →
  `fsync` the directory. The crash-safety story is exactly what it was before
  streaming: a crash during compaction leaves the original log untouched, so
  it can never lose data — only how the replacement image gets built changed,
  not the commit sequence that makes replacing it safe.
- Serializing the in-RAM state reproduces the exact current state, so the
  **digest is unchanged** across a compaction.
- This is where **tombstone GC** plugs in once the LWW-existence model lands
  (drop tombstones past their TTL during the rewrite — see `docs/DATA_MODEL.md`).

## Deletion & erasure

`sync_engine_delete` is a *logical* delete: it writes a tombstone
(`present=false` at a fresh HLC) and **retains the entity's field registers
hidden underneath it** — in RAM, in the log, and in sync snapshots — until the
tombstone ages past `kTombstoneTtlMs` (30 days) and compaction's tombstone GC
drops the whole entity. That retention is what makes deletion converge, but it
means a delete alone is not an erasure: the bytes are merely hidden.

When the *content* must actually go away (ephemeral posts, expired media), the
recipe is **erase → tombstone → compact**, in that order:

1. **Erase** every field first: `sync_engine_erase_field` (and
   `sync_blob_erase` for a blob's chunk payloads) overwrites the value with an
   empty one under a fresh HLC. This is an ordinary signed LWW record, so the
   erasure **replicates to peers and beats the value it erases** — remote
   copies go empty at their next sync, not just the local one.
2. **Tombstone** with `sync_engine_delete` (`sync_blob_erase` does this
   itself). Order matters: `sync_engine_set` on a tombstoned entity re-asserts
   presence — writing *after* deleting resurrects the entity. The erase APIs
   enforce this by refusing (SYNC_ERR_NOTFOUND) to write through a tombstone.
3. **Compact** with `sync_engine_compact`: the log rewrite drops every
   superseded frame — including the non-empty values the erasure overwrote —
   so the bytes physically leave the disk. What the rewritten log still holds
   for the entity is its tombstone plus the now-empty registers.

### Write batching and the erase → compact recipe

Large writes (the blob paths in particular) can group many mutations into
few fsync'd log frames via `sync_engine_batch_begin`/`batch_commit`/
`batch_abort` — see the "Write batching" section of `include/sync_engine.h`
for the full ABI contract. Two of its properties bear directly on the
recipe above:

- **Nesting is depth-counted, not per-caller.** `batch_begin` calls nest —
  only the first (depth 0→1) opens the log transaction, and only the
  matching outermost `batch_commit` stamps the clock, writes the final
  frame, and may trigger compaction; an inner commit just closes its level.
  The batch itself is **engine-global**: the depth counter cannot tell
  which caller opened which level, so a `batch_abort` at *any* depth
  poisons the whole outermost batch, discarding every enclosing caller's
  un-flushed staged tail too. A component must never open a batch across a
  call into code it does not control.
- **Blob durability is conditional on there being no enclosing batch.**
  `sync_blob_put`/`delete`/`erase` each open their own internal batch, so
  outside any embedder batch `SYNC_OK` still means fsync'd on return. But
  nested inside an embedder's own open `sync_engine_batch_begin`, the
  blob call's commit only closes its nesting level — `SYNC_OK` then means
  *staged*, not durable, until the embedder's own outermost `batch_commit`
  succeeds.

**Capability writes are never staged.** `sync_engine_grant`/
`sync_engine_revoke` bypass batching entirely, batch open or not, and
always write their own immediately-fsync'd frame. This is a deliberate
security exclusion, not an oversight: a revocation is how a compromised
device gets cut off, and a caller that gets back `SYNC_OK` must be able to
trust the cut-off already happened. Staging it like an ordinary mutation
would let a later `batch_abort` — possibly issued by unrelated code sharing
the engine-global batch — silently discard a revocation the caller was
already told succeeded.

**Batch interaction with the recipe (run it OUTSIDE any write batch).**
While a `sync_engine_batch_begin` batch is open, step 3 *fails*: the batch
holds the log transaction for its whole lifetime, so `sync_engine_compact`
returns `SYNC_ERR_INTERNAL` by design until the outermost
`batch_commit`/`batch_abort` closes it. Steps 1–2 inside an open batch also
change meaning: `SYNC_OK` from `sync_engine_erase_field` / `sync_blob_erase`
/ `sync_engine_delete` then means *staged*, not durable — the records reach
disk only at the outermost `batch_commit` (an abort defers them further:
they stay live in RAM and the next compaction persists them — see the
batching section in `include/sync_engine.h`). Perform the whole
erase → tombstone → compact sequence with no batch open — or at minimum
close the batch between step 2 and step 3 — so the compaction that scrubs
the disk can actually run.

**Interplay with `kTombstoneTtlMs`:** for up to 30 days after the delete, the
entity's *keys* survive (entity id, field names, a blob manifest's chunk-hash
list — metadata, not payload) alongside the emptied registers. Once the
tombstone passes the horizon, the next compaction drops the entity entirely.
The horizon is also the resurrection bound: a peer offline longer than 30 days
can bring a purged entity back (see `docs/DATA_MODEL.md`).

**Limits — deletion is cooperative, not cryptographic.** The erasure reaches a
peer only when that peer syncs and honors the records (every implementation
does, but nothing *forces* a hostile one to). A peer that never syncs again
keeps its copy forever; relay mailboxes hold sealed envelopes of the original
records until their retention evicts them; and there is no recall of data a
device has already displayed or exported. This is the same honest bound
Earthstar and Willow document: deletion works when peers receive and honor the
update.

## Why this design (and not a Prolly Tree / LSM / B-tree)

The storage, in-memory index, and sync are three separate concerns; the best
choice differs per layer:

- **Sync stays range-based set reconciliation (RBSR).** It is stateless
  per-connection and DoS-resistant — a concrete advantage over Merkle-tree-based
  sync — and Kome already implements it (combinable fingerprint + prefix sums).
- **Storage is Bitcask** (append-only log + in-RAM index + compaction). It fits
  the "all keys in RAM" assumption and is the minimal durable design. LSM-trees
  target write-heavy, beyond-RAM workloads (overkill); LMDB is a dependency.
- **The in-memory index stays `std::map`** (ordered, gives the prefix-sum range
  summaries RBSR needs).

A **Prolly Tree / Merkle Search Tree** would elegantly unify all three (index +
content-addressed storage + sync). It is deliberately **not** adopted: its
headline payoff is efficient diffs across *historical versions* (the value-prop
of a version-controlled database like Dolt). Kome keeps only current LWW state —
no history — so it would pay the full complexity (content-defined chunking, write
amplification, tuning) for almost none of the benefit, and would replace the
stateless, DoS-resistant RBSR sync with a stateful tree. It is the right tool
only if Kome ever grows Git-style history/versioning. (Research: Dolt prolly
trees; Auvolat & Taïani, "Merkle Search Trees"; Gustafson, "Merklizing the
key/value store"; the Bitcask paper; Meyer, "Range-Based Set Reconciliation".)
