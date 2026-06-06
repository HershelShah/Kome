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
 * fails cleanly (no migration backward). */
constexpr uint64_t kSchemaVersion = 1;

class Storage {
public:
    /* Open (creating if needed) the database at path and ensure the schema.
     * On success returns a Storage*; on failure returns nullptr and sets *err. */
    static Storage *open(const char *path, sync_error *err);
    ~Storage();

    Storage(const Storage &) = delete;
    Storage &operator=(const Storage &) = delete;

    /* Populate engine state (namespaces, registers), site_id and clock from
     * disk. For a fresh database, persists site_id_default as the identity.
     * Returns false (with *err set) on corruption / schema mismatch. */
    bool load(sync_engine *e, const SiteId &site_id_default, sync_error *err);

    /* Write-through helpers. Group calls between begin()/commit(). */
    bool begin();
    bool commit();
    bool rollback();

    bool put_entity(const std::string &ns, const std::string &ent,
                    uint64_t causal_length, uint64_t db_clock);
    bool put_field(const std::string &ns, const std::string &ent,
                   const std::string &field, const std::string &value,
                   const Hlc &hlc, const SiteId &site, uint64_t db_clock);
    bool put_meta_u64(const char *key, uint64_t v);

private:
    Storage() = default;
    bool exec(const char *sql);

    sqlite3 *db_ = nullptr;
};

} // namespace ke

#endif /* SYNC_STORAGE_H */
