/* storage.h — append-only log persistence. Internal.
 *
 * Sits *under* the M1 convergence logic exactly as the old SQLite layer did:
 * load all state on open, write-through (inside a transaction) on every
 * mutation. The merge code is unchanged and the public method surface is
 * identical to the former SQLite-backed Storage, so the engine and capability
 * code call it the same way.
 *
 * On disk it is a single append-only log of length-prefixed, checksummed frames
 * (see storage.cpp for the format). A frame is one mutation's records written
 * and fsync'd atomically; a crash leaves at most a torn trailing frame, which is
 * detected by its checksum and truncated on reopen. Because the merge is
 * idempotent and commutative, dropping an uncommitted trailing frame is safe.
 * No SQLite, no second dependency — the persisted bytes are the engine's own
 * record encodings. */
#ifndef SYNC_STORAGE_H
#define SYNC_STORAGE_H

#include <atomic>
#include <cstdint>
#include <string>

#include "engine.hpp"
#include "sync_engine.h"

namespace ke {

struct DecodedChange; /* defined in codec.h */

/* Merge one already-verified record into engine state by the same LWW rule the
 * engine uses (order-independent, idempotent — replay calls this per record).
 * `h` is the record's reconciliation-element hash (SHA-256 of its canonical
 * encode_record bytes), computed by the caller; it is installed on the cell
 * when — and only when — the record wins the merge, so the stored hash always
 * describes what is actually in the map (on the degenerate tie against the
 * would-be default Register, the default cell is hashed — before it is
 * inserted, per the hoisting rule — and installed instead). Promoted out of
 * storage.cpp's anonymous namespace so tests can drive it directly. */
void merge_record(sync_engine *e, const DecodedChange &dc, const Hash256 &h);

/* Current on-disk log-format version (stored in a meta record). Opening a file
 * with a newer/unknown version fails cleanly (no backward migration).
 *   1 — append-only log: meta + per-record (existence/register) + capability
 *   2 — LWW existence: entity records carry (present, hlc) not causal_length */
constexpr uint64_t kSchemaVersion = 2;

/* Tombstones (present=false assertions) older than this are dropped during
 * compaction, bounding delete-heavy growth. The horizon is generous because
 * deletion in open P2P is best-effort: a peer offline longer than this may
 * resurrect a deleted entity (the same bound Earthstar documents). 30 days. */
constexpr uint64_t kTombstoneTtlMs = 30ull * 24 * 3600 * 1000;

/* Staged-bytes threshold at which an open batch force-flushes a clock-covered
 * sub-frame (Storage::batch_maybe_flush, fired from the engine's own write
 * path — not caller-optional), so no batch, however large, holds an unbounded
 * RAM transient: staging is capped at ~kBatchFlushBytes + one record. Smaller
 * under Emscripten, where the WASM heap grows but never shrinks, so a large
 * transient would be a permanent per-page memory cost. */
#ifdef __EMSCRIPTEN__
constexpr size_t kBatchFlushBytes = 256u * 1024;
#else
constexpr size_t kBatchFlushBytes = 2u * 1024 * 1024;
#endif

/* Debug/test-only fsync accounting: a process-global counter bumped once per
 * fsync() the log layer issues on its measured write paths — write_frame's
 * per-frame fsync, and rewrite_log_streamed's two fsyncs (temp file before
 * the rename, then the best-effort directory fsync). Open-time header fsyncs and
 * the one-shot torn-tail truncate fsync are NOT counted. Tests (which include
 * this header) and the bench harness read and reset it through the returned
 * mutable reference (e.g. `ke::storage_fsync_count() = 0;`); nothing in the
 * engine itself reads it. std::atomic (relaxed increments): each engine's
 * write path is single-threaded, but the counter is PROCESS-GLOBAL, and
 * independent engines driven from independent threads are a supported,
 * TSan-clean configuration (tests/threading_test.cpp) — a plain uint64_t here
 * is a data race the moment two durable engines fsync concurrently. A relaxed
 * increment per multi-millisecond fsync is free; the function-local static
 * stays free of global-init-order issues and unity-build-safe (single
 * definition, in storage.cpp). */
std::atomic<uint64_t> &storage_fsync_count();

class Storage {
public:
    /* Open (creating if needed) the log at path and validate its header. If
     * key != nullptr the log is encrypted at rest: each frame is sealed with
     * XChaCha20-Poly1305 under the 32-byte key (the embedder derives it from a
     * passphrase / OS keystore). A header key-check rejects a wrong key cleanly
     * instead of mistaking it for corruption. On success returns a Storage*; on
     * failure (incl. wrong key / mode mismatch) returns nullptr and sets *err. */
    static Storage *open(const char *path, sync_error *err,
                         const uint8_t *key = nullptr);
    ~Storage();

    Storage(const Storage &) = delete;
    Storage &operator=(const Storage &) = delete;

    /* Replay the log into engine state (namespaces, registers, capabilities),
     * identity and clock. For a fresh log, derives and persists the identity
     * from seed. Returns false (with *err set) on corruption / version
     * mismatch. */
    bool load(sync_engine *e, const uint8_t seed[32], sync_error *err);

    /* Write-through helpers. Calls between begin()/commit() are staged and land
     * as a single atomic frame; a put_* outside a transaction is its own frame.
     * Group a mutation's records between begin()/commit() for all-or-nothing. */
    bool begin();
    bool commit();
    bool rollback();

    /* Bulk-apply batching: stage many records into few fsync'd frames. While
     * a batch is open the per-mutation tx_* helpers skip their own
     * begin/commit (and the clock/compaction), so a sync that ingests N
     * records does O(1) fsyncs instead of N.
     *
     * Batches NEST (exposed to embedders via the sync_engine_batch_* ABI):
     * batch_begin/batch_commit maintain a depth counter. Only the 0->1 begin
     * opens the underlying transaction, and only the OUTERMOST commit stamps
     * the clock meta, writes + fsyncs the final frame, releases the staging
     * buffer's capacity, and runs maybe_compact; an inner commit merely
     * decrements and writes nothing. batch_abort poisons the batch
     * (batch_failed_, which immediately drops the staged tail — see
     * batch_poison below): the un-flushed tail is never written by the
     * batch, while sub-frames already flushed by batch_maybe_flush are
     * durable and are NOT undone (a batch is a durability boundary, not a
     * rollback mechanism). Nor is the discard an anti-persistence guarantee:
     * the engine's in-RAM maps keep every mutation regardless of the
     * batch's fate, and the next compaction — explicit or the automatic
     * size-triggered one in maybe_compact — re-serializes RAM wholesale,
     * making "aborted" mutations durable after all (documented at the ABI;
     * pinned by Storage.AbortedTailReturnsAtCompaction). The batch is
     * ENGINE-GLOBAL: depth cannot
     * distinguish holders, so a nested abort condemns every enclosing
     * caller's un-flushed mutations too. While any batch is open, in_tx_
     * stays set for its whole lifetime, so compact() refuses BY DESIGN — the
     * erase-then-tombstone-then-compact physical-erasure pairing must be
     * performed outside a batch. */
    bool     in_batch() const { return batch_depth_ > 0; }
    uint32_t batch_depth() const { return batch_depth_; }
    bool batch_begin();
    bool batch_commit(sync_engine *e);
    bool batch_abort();
    /* Mandatory mid-batch flush, fired from the engine's own write path (the
     * tx_* helpers' in-batch branches), never caller-optional: once staged
     * bytes exceed kBatchFlushBytes, stamp the three clock-meta entries
     * (hlc_physical / hlc_logical / db_clock) into the staged sub-frame and
     * write_frame it. Crash-prefix invariant: ANY durable frame with records
     * also carries a covering clock, so a crash between sub-frames can never
     * persist records whose HLC exceeds the persisted clock meta. Returns
     * false (poisoning the batch) on a write failure, and false immediately
     * when the batch is already poisoned. No-op outside a batch. */
    bool batch_maybe_flush(sync_engine *e);
    /* Poison the open batch (no-op outside one): every subsequent in-batch
     * tx_* fails immediately (emit() refuses to stage into a poisoned
     * batch) and the outermost commit discards instead of committing.
     * Poisoning also drops the staged tail — bytes AND capacity — right
     * away: the tail is guaranteed to be discarded at the outermost close,
     * and holding (or worse, growing) condemned staging for the batch's
     * remaining lifetime would defeat the mandatory kBatchFlushBytes RAM
     * bound above exactly when it matters (a caller looping over failed
     * writes). Called by the tx_* write helpers on ANY in-batch failure
     * (spec §3.3 point 9 — not just a flush failure). */
    void batch_poison();
    /* Test/introspection only: bytes currently staged in the open
     * transaction (0 when none, and always 0 while a batch is poisoned). */
    size_t staged_bytes() const { return staging_.size(); }

    bool put_entity(const std::string &ns, const std::string &ent,
                    bool present, const Hlc &presence_hlc, const PubKey &ex_author,
                    const Sig &ex_sig, uint64_t db_clock);
    bool put_field(const std::string &ns, const std::string &ent,
                   const std::string &field, const std::string &value,
                   const Hlc &hlc, const PubKey &author, const Sig &sig,
                   uint64_t db_clock);
    bool put_meta_u64(const char *key, uint64_t v);
    bool put_meta_blob(const char *key, const uint8_t *data, size_t len);
    bool put_capability(const std::string &blob);
    bool put_revocation(const std::string &blob);

    /* Rewrite the log as one record per live cell when it has grown much larger
     * than its live state (the Bitcask "merge"): bounds the file to O(state),
     * keeps reopen O(state), and is where deleted-record purging will hook in.
     * Best-effort — a failure leaves the (correct, larger) log in place. Needs
     * the engine for the current state; called from the write path. */
    void maybe_compact(sync_engine *e);
    bool compact(sync_engine *e); /* force a rewrite now */

private:
    Storage() = default;

    /* Stage one entry (in a transaction) or write it as a standalone frame. */
    bool emit(const std::string &entry);
    /* Stage the three covering clock-meta entries (hlc_physical / hlc_logical
     * / db_clock) into the open transaction — the crash-prefix stamp every
     * batch (sub-)frame carries. */
    bool stamp_clock_meta(sync_engine *e);
    /* Append a complete frame (length + body + checksum) and fsync. */
    bool write_frame(const std::string &body, uint32_t entry_count);
    /* Drop expired tombstones (present=false older than kTombstoneTtlMs) from
     * the engine's state before a compaction rewrites it. */
    void gc_tombstones(sync_engine *e);
    /* Stream a complete compacted log image (header + frames, sealed if
     * encrypted) of the engine's current state directly to `<path_>.tmp`
     * through a small reused buffer (kCompactBufSize), then durably commit it:
     * fsync(tmp) -> close -> rename -> reopen -> fsync(dir). The rename is the
     * sole commit point — a mid-stream failure or crash leaves the original
     * log untouched (plus at most an orphan .tmp that open() never reads and
     * the next compaction O_TRUNCs). Bounds the compaction RAM transient to
     * O(kCompactBufSize + one frame) instead of a full log image (§3.4). */
    bool rewrite_log_streamed(sync_engine *e);
    /* Exact byte size rewrite_log_streamed will produce for the engine's
     * current state — pure arithmetic, no allocation; used by maybe_compact's
     * deferred open-time heuristic and the Debug exactness assert. */
    uint64_t compacted_image_size(const sync_engine *e) const;

    /* Wrap a body into one on-disk frame (plaintext + SHA, or AEAD-sealed). */
    std::string seal_frame(const std::string &body, uint32_t count) const;
    /* The file header (magic, plus a key-check for encrypted logs). */
    std::string header_bytes() const;
    size_t      header_size() const { return encrypted_ ? 8 + 32 : 8; }

    int         fd_ = -1;
    std::string path_;
    std::string staging_;        /* entries buffered between begin()/commit() */
    uint32_t    staged_count_ = 0;
    bool        in_tx_ = false;
    uint32_t    batch_depth_ = 0;      /* nested bulk-apply batch depth */
    bool        batch_failed_ = false; /* an in-batch failure/abort poisoned
                                          the whole engine-global batch */
    uint64_t    file_size_ = 0;       /* current log size in bytes */
    uint64_t    compacted_size_ = 0;  /* log size just after the last compaction */
    bool        tail_torn_ = false;   /* bytes past the last good frame: load
                                         found a torn tail, OR write_frame
                                         failed partway and left a partial
                                         frame on disk. Truncated back to
                                         file_size_ on the next write (never
                                         at open — see load()); leaving it
                                         would strand every later append
                                         behind garbage replay stops at. */
    bool        open_compact_pending_ = false; /* load found a bloated log;
                                         compacted on the first mutation
                                         (never at open) */
    uint8_t     seed_[32] = {0};      /* identity seed, re-persisted on compaction */
    bool        encrypted_ = false;   /* frames sealed with key_ at rest */
    uint8_t     key_[32] = {0};       /* at-rest encryption key (wiped on destroy) */
};

} // namespace ke

#endif /* SYNC_STORAGE_H */
