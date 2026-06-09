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

#include <cstdint>
#include <string>

#include "engine.hpp"
#include "sync_engine.h"

namespace ke {

/* Current on-disk log-format version (stored in a meta record). Opening a file
 * with a newer/unknown version fails cleanly (no backward migration).
 *   1 — append-only log: meta + per-record (existence/register) + capability */
constexpr uint64_t kSchemaVersion = 1;

class Storage {
public:
    /* Open (creating if needed) the log at path and validate its header. On
     * success returns a Storage*; on failure returns nullptr and sets *err. */
    static Storage *open(const char *path, sync_error *err);
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

    bool put_entity(const std::string &ns, const std::string &ent,
                    uint64_t causal_length, const PubKey &ex_author,
                    const Sig &ex_sig, uint64_t db_clock);
    bool put_field(const std::string &ns, const std::string &ent,
                   const std::string &field, const std::string &value,
                   const Hlc &hlc, const PubKey &author, const Sig &sig,
                   uint64_t db_clock);
    bool put_meta_u64(const char *key, uint64_t v);
    bool put_meta_blob(const char *key, const uint8_t *data, size_t len);
    bool put_capability(const std::string &blob);

private:
    Storage() = default;

    /* Stage one entry (in a transaction) or write it as a standalone frame. */
    bool emit(const std::string &entry);
    /* Append a complete frame (length + body + checksum) and fsync. */
    bool write_frame(const std::string &body, uint32_t entry_count);

    int         fd_ = -1;
    std::string path_;
    std::string staging_;        /* entries buffered between begin()/commit() */
    uint32_t    staged_count_ = 0;
    bool        in_tx_ = false;
};

} // namespace ke

#endif /* SYNC_STORAGE_H */
