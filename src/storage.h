/* storage.h — SQLite-backed persistence (M2). Internal.
 *
 * Sits *under* the M1 convergence logic: load all state on open, write-through
 * (inside a transaction) on every mutation. The merge code is unchanged. One
 * SQLite file per replica (plus SQLite's own WAL/shm). */
#ifndef SYNC_STORAGE_H
#define SYNC_STORAGE_H

#include <cstdint>
#include <string>

#include "engine.hpp"
#include "sync_engine.h"

struct sqlite3;

namespace ke {

/* Current on-disk schema version. Opening a file with a newer/unknown version
 * fails cleanly (no migration backward).
 *   1 — M2 (site_id, entity, field with site_id)
 *   2 — M4 (identity seed; per-record author + signature) */
constexpr uint64_t kSchemaVersion = 2;

class Storage {
public:
    /* Open (creating if needed) the database at path and ensure the schema.
     * On success returns a Storage*; on failure returns nullptr and sets *err. */
    static Storage *open(const char *path, sync_error *err);
    ~Storage();

    Storage(const Storage &) = delete;
    Storage &operator=(const Storage &) = delete;

    /* Populate engine state (namespaces, registers), identity and clock from
     * disk. For a fresh database, derives and persists the identity from seed.
     * Returns false (with *err set) on corruption / schema mismatch. */
    bool load(sync_engine *e, const uint8_t seed[32], sync_error *err);

    /* Write-through helpers. Group calls between begin()/commit(). */
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
    bool exec(const char *sql);

    sqlite3 *db_ = nullptr;
};

} // namespace ke

#endif /* SYNC_STORAGE_H */
