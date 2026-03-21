#include "kome_log.hpp"
#include "kome_util.hpp"
#include "sqlite3.h"
#include <cstring>

namespace kome {

KomeLog::KomeLog() = default;
KomeLog::~KomeLog() { close(); }

KomeError KomeLog::open(const char *path, int enable_wal, int busy_timeout_ms) {
    int flags = SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE | SQLITE_OPEN_FULLMUTEX;
    if (sqlite3_open_v2(path, &db_, flags, nullptr) != SQLITE_OK)
        return KOME_ERR_STORAGE;

    sqlite3_busy_timeout(db_, busy_timeout_ms > 0 ? busy_timeout_ms : 5000);

    if (enable_wal) {
        char *err = nullptr;
        sqlite3_exec(db_, "PRAGMA journal_mode=WAL;", nullptr, nullptr, &err);
        sqlite3_free(err);
    }

    KomeError e = create_tables();
    if (e != KOME_OK) return e;
    return prepare_stmts();
}

void KomeLog::close() {
    finalize_stmts();
    if (db_) { sqlite3_close(db_); db_ = nullptr; }
}

KomeError KomeLog::create_tables() {
    const char *sql =
        "CREATE TABLE IF NOT EXISTS change_log ("
        "  ns TEXT NOT NULL, key BLOB NOT NULL, value BLOB,"
        "  timestamp_us INTEGER NOT NULL, author BLOB NOT NULL,"
        "  seq INTEGER NOT NULL, hash BLOB NOT NULL,"
        "  value_len INTEGER NOT NULL, tombstone INTEGER NOT NULL DEFAULT 0,"
        "  PRIMARY KEY (ns, key));"
        "CREATE INDEX IF NOT EXISTS idx_cl_author_seq ON change_log(author, seq);"
        "CREATE TABLE IF NOT EXISTS version_vector ("
        "  author BLOB NOT NULL PRIMARY KEY, seq INTEGER NOT NULL);"
        "CREATE TABLE IF NOT EXISTS peer_state ("
        "  peer_fp BLOB NOT NULL, author BLOB NOT NULL, seq INTEGER NOT NULL,"
        "  PRIMARY KEY (peer_fp, author));"
        "CREATE TABLE IF NOT EXISTS replication_targets ("
        "  ns TEXT NOT NULL PRIMARY KEY, target_n INTEGER NOT NULL);"
        "CREATE TABLE IF NOT EXISTS replication_peers ("
        "  ns TEXT NOT NULL, key BLOB NOT NULL, peer_fp BLOB NOT NULL,"
        "  PRIMARY KEY (ns, key, peer_fp));";

    char *err = nullptr;
    int rc = sqlite3_exec(db_, sql, nullptr, nullptr, &err);
    sqlite3_free(err);
    return (rc == SQLITE_OK) ? KOME_OK : KOME_ERR_STORAGE;
}

void KomeLog::finalize_stmts() {
    sqlite3_stmt **all[] = {
        &stmt_put_, &stmt_get_, &stmt_update_vv_, &stmt_get_vv_,
        &stmt_update_ps_, &stmt_after_, &stmt_del_repl_,
        &stmt_set_repl_, &stmt_get_repl_, &stmt_count_repl_,
        &stmt_inc_repl_, &stmt_gc_tomb_, &stmt_list_ns_, &stmt_list_keys_
    };
    for (auto *sp : all) { sqlite3_finalize(*sp); *sp = nullptr; }
}

KomeError KomeLog::prepare_stmts() {
    auto p = [&](const char *sql, sqlite3_stmt **out) {
        return sqlite3_prepare_v2(db_, sql, -1, out, nullptr);
    };

    if (p("INSERT OR REPLACE INTO change_log "
          "(ns, key, value, timestamp_us, author, seq, hash, value_len, tombstone) "
          "VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9)", &stmt_put_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("SELECT value, timestamp_us, author, seq, hash, value_len, tombstone "
          "FROM change_log WHERE ns=?1 AND key=?2", &stmt_get_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("INSERT INTO version_vector (author, seq) VALUES (?1,?2) "
          "ON CONFLICT(author) DO UPDATE SET seq = MAX(seq, excluded.seq)",
          &stmt_update_vv_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("SELECT author, seq FROM version_vector", &stmt_get_vv_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("INSERT INTO peer_state (peer_fp, author, seq) VALUES (?1,?2,?3) "
          "ON CONFLICT(peer_fp, author) DO UPDATE SET seq = MAX(seq, excluded.seq)",
          &stmt_update_ps_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("SELECT ns, key, value, timestamp_us, author, seq, hash, value_len, tombstone "
          "FROM change_log WHERE author=?1 AND seq>?2 ORDER BY seq ASC",
          &stmt_after_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("DELETE FROM replication_peers WHERE ns=?1 AND key=?2",
          &stmt_del_repl_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("INSERT OR REPLACE INTO replication_targets (ns, target_n) VALUES (?1,?2)",
          &stmt_set_repl_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("SELECT target_n FROM replication_targets WHERE ns=?1",
          &stmt_get_repl_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("SELECT COUNT(*) FROM replication_peers WHERE ns=?1 AND key=?2",
          &stmt_count_repl_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("INSERT OR IGNORE INTO replication_peers (ns, key, peer_fp) VALUES (?1,?2,?3)",
          &stmt_inc_repl_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("DELETE FROM change_log WHERE tombstone=1 AND timestamp_us<?1",
          &stmt_gc_tomb_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("SELECT DISTINCT ns FROM change_log ORDER BY ns",
          &stmt_list_ns_) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    if (p("SELECT key FROM change_log WHERE ns=?1 ORDER BY key",
          &stmt_list_keys_) != SQLITE_OK)
        return KOME_ERR_STORAGE;

    return KOME_OK;
}

/* --- CRUD ---------------------------------------------------------------- */

KomeError KomeLog::put_entry(const char *ns, const uint8_t *key, size_t key_len,
                              const uint8_t *value, size_t value_len,
                              const KomeEntryMeta *meta) {
    sqlite3_reset(stmt_put_);
    sqlite3_bind_text(stmt_put_,  1, ns, -1, SQLITE_TRANSIENT);
    sqlite3_bind_blob(stmt_put_,  2, key, (int)key_len, SQLITE_TRANSIENT);
    if (meta->tombstone)
        sqlite3_bind_null(stmt_put_, 3);
    else
        sqlite3_bind_blob(stmt_put_, 3, value, (int)value_len, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt_put_, 4, (sqlite3_int64)meta->timestamp_us);
    sqlite3_bind_blob(stmt_put_,  5, meta->author, 32, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt_put_, 6, (sqlite3_int64)meta->seq);
    sqlite3_bind_blob(stmt_put_,  7, meta->hash, 32, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt_put_,   8, (int)meta->value_len);
    sqlite3_bind_int(stmt_put_,   9, meta->tombstone);
    if (sqlite3_step(stmt_put_) != SQLITE_DONE) return KOME_ERR_STORAGE;

    /* Reset per-peer replication tracking */
    sqlite3_reset(stmt_del_repl_);
    sqlite3_bind_text(stmt_del_repl_, 1, ns, -1, SQLITE_TRANSIENT);
    sqlite3_bind_blob(stmt_del_repl_, 2, key, (int)key_len, SQLITE_TRANSIENT);
    sqlite3_step(stmt_del_repl_);

    return KOME_OK;
}

KomeError KomeLog::get_entry(const char *ns, const uint8_t *key, size_t key_len,
                              LogEntry *out) {
    sqlite3_reset(stmt_get_);
    sqlite3_bind_text(stmt_get_, 1, ns, -1, SQLITE_TRANSIENT);
    sqlite3_bind_blob(stmt_get_, 2, key, (int)key_len, SQLITE_TRANSIENT);

    int rc = sqlite3_step(stmt_get_);
    if (rc == SQLITE_DONE) return KOME_ERR_NOT_FOUND;
    if (rc != SQLITE_ROW) return KOME_ERR_STORAGE;

    out->ns = ns;
    out->key.assign(key, key + key_len);

    const void *val = sqlite3_column_blob(stmt_get_, 0);
    int val_len = sqlite3_column_bytes(stmt_get_, 0);
    if (val && val_len > 0)
        out->value.assign((const uint8_t*)val, (const uint8_t*)val + val_len);
    else
        out->value.clear();

    out->timestamp_us = (uint64_t)sqlite3_column_int64(stmt_get_, 1);
    const void *auth = sqlite3_column_blob(stmt_get_, 2);
    if (auth) std::memcpy(out->author, auth, 32);
    else std::memset(out->author, 0, 32);
    out->seq = (uint64_t)sqlite3_column_int64(stmt_get_, 3);
    const void *h = sqlite3_column_blob(stmt_get_, 4);
    if (h) std::memcpy(out->hash, h, 32);
    else std::memset(out->hash, 0, 32);
    out->tombstone = (uint8_t)sqlite3_column_int(stmt_get_, 6);

    return KOME_OK;
}

KomeError KomeLog::delete_entry(const char *ns, const uint8_t *key, size_t key_len,
                                 const KomeEntryMeta *meta) {
    return put_entry(ns, key, key_len, nullptr, 0, meta);
}

/* --- Version vector / peer state ----------------------------------------- */

KomeError KomeLog::update_version_vector(const uint8_t author[32], uint64_t seq) {
    sqlite3_reset(stmt_update_vv_);
    sqlite3_bind_blob(stmt_update_vv_,  1, author, 32, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt_update_vv_, 2, (sqlite3_int64)seq);
    return (sqlite3_step(stmt_update_vv_) == SQLITE_DONE) ? KOME_OK : KOME_ERR_STORAGE;
}

KomeError KomeLog::get_version_vector(std::map<std::string, uint64_t> &vv) {
    vv.clear();
    sqlite3_reset(stmt_get_vv_);
    while (sqlite3_step(stmt_get_vv_) == SQLITE_ROW) {
        const void *a = sqlite3_column_blob(stmt_get_vv_, 0);
        int alen = sqlite3_column_bytes(stmt_get_vv_, 0);
        uint64_t s = (uint64_t)sqlite3_column_int64(stmt_get_vv_, 1);
        if (a && alen == 32)
            vv[std::string((const char*)a, 32)] = s;
    }
    return KOME_OK;
}

KomeError KomeLog::update_peer_state(const uint8_t peer_fp[32],
                                      const uint8_t author[32], uint64_t seq) {
    sqlite3_reset(stmt_update_ps_);
    sqlite3_bind_blob(stmt_update_ps_,  1, peer_fp, 32, SQLITE_TRANSIENT);
    sqlite3_bind_blob(stmt_update_ps_,  2, author, 32, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt_update_ps_, 3, (sqlite3_int64)seq);
    return (sqlite3_step(stmt_update_ps_) == SQLITE_DONE) ? KOME_OK : KOME_ERR_STORAGE;
}

/* --- Sync queries -------------------------------------------------------- */

KomeError KomeLog::get_entries_after(const uint8_t author[32], uint64_t after_seq,
                                      std::vector<LogEntry> &out) {
    out.clear();
    sqlite3_reset(stmt_after_);
    sqlite3_bind_blob(stmt_after_,  1, author, 32, SQLITE_TRANSIENT);
    sqlite3_bind_int64(stmt_after_, 2, (sqlite3_int64)after_seq);

    while (sqlite3_step(stmt_after_) == SQLITE_ROW) {
        LogEntry e;
        const char *ns_ptr = (const char*)sqlite3_column_text(stmt_after_, 0);
        if (!ns_ptr) continue;
        e.ns = ns_ptr;

        const void *k = sqlite3_column_blob(stmt_after_, 1);
        int klen = sqlite3_column_bytes(stmt_after_, 1);
        if (k && klen > 0)
            e.key.assign((const uint8_t*)k, (const uint8_t*)k + klen);

        const void *v = sqlite3_column_blob(stmt_after_, 2);
        int vlen = sqlite3_column_bytes(stmt_after_, 2);
        if (v && vlen > 0)
            e.value.assign((const uint8_t*)v, (const uint8_t*)v + vlen);

        e.timestamp_us = (uint64_t)sqlite3_column_int64(stmt_after_, 3);
        const void *a = sqlite3_column_blob(stmt_after_, 4);
        if (a) std::memcpy(e.author, a, 32);
        e.seq = (uint64_t)sqlite3_column_int64(stmt_after_, 5);
        const void *h = sqlite3_column_blob(stmt_after_, 6);
        if (h) std::memcpy(e.hash, h, 32);
        e.tombstone = (uint8_t)sqlite3_column_int(stmt_after_, 8);

        out.push_back(std::move(e));
    }
    return KOME_OK;
}

KomeError KomeLog::get_missing_entries(const std::map<std::string, uint64_t> &remote_vv,
                                        std::vector<LogEntry> &out) {
    out.clear();
    std::map<std::string, uint64_t> our_vv;
    get_version_vector(our_vv);

    for (auto &[author_key, our_seq] : our_vv) {
        uint64_t remote_seq = 0;
        auto it = remote_vv.find(author_key);
        if (it != remote_vv.end()) remote_seq = it->second;
        if (our_seq > remote_seq) {
            std::vector<LogEntry> entries;
            get_entries_after((const uint8_t*)author_key.data(), remote_seq, entries);
            for (auto &e : entries)
                out.push_back(std::move(e));
        }
    }
    return KOME_OK;
}

/* --- Replication --------------------------------------------------------- */

KomeError KomeLog::set_replication_target(const char *ns, uint32_t target_n) {
    sqlite3_reset(stmt_set_repl_);
    sqlite3_bind_text(stmt_set_repl_, 1, ns, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int(stmt_set_repl_,  2, (int)target_n);
    return (sqlite3_step(stmt_set_repl_) == SQLITE_DONE) ? KOME_OK : KOME_ERR_STORAGE;
}

KomeError KomeLog::get_replication_target(const char *ns, uint32_t *target_out) {
    sqlite3_reset(stmt_get_repl_);
    sqlite3_bind_text(stmt_get_repl_, 1, ns, -1, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt_get_repl_);
    if (rc == SQLITE_ROW) {
        *target_out = (uint32_t)sqlite3_column_int(stmt_get_repl_, 0);
        return KOME_OK;
    }
    *target_out = 0;
    return KOME_OK;
}

KomeError KomeLog::get_replication_confirmed(const char *ns, const uint8_t *key,
                                              size_t key_len, uint32_t *confirmed_out) {
    sqlite3_reset(stmt_count_repl_);
    sqlite3_bind_text(stmt_count_repl_, 1, ns, -1, SQLITE_TRANSIENT);
    sqlite3_bind_blob(stmt_count_repl_, 2, key, (int)key_len, SQLITE_TRANSIENT);
    int rc = sqlite3_step(stmt_count_repl_);
    if (rc == SQLITE_ROW) {
        *confirmed_out = (uint32_t)sqlite3_column_int(stmt_count_repl_, 0);
        return KOME_OK;
    }
    *confirmed_out = 0;
    return KOME_OK;
}

KomeError KomeLog::increment_replication_peer(const char *ns, const uint8_t *key,
                                                size_t key_len, const uint8_t peer_fp[32]) {
    sqlite3_reset(stmt_inc_repl_);
    sqlite3_bind_text(stmt_inc_repl_, 1, ns, -1, SQLITE_TRANSIENT);
    sqlite3_bind_blob(stmt_inc_repl_, 2, key, (int)key_len, SQLITE_TRANSIENT);
    sqlite3_bind_blob(stmt_inc_repl_, 3, peer_fp, 32, SQLITE_TRANSIENT);
    return (sqlite3_step(stmt_inc_repl_) == SQLITE_DONE) ? KOME_OK : KOME_ERR_STORAGE;
}

/* --- GC ------------------------------------------------------------------ */

KomeError KomeLog::gc_tombstones(uint64_t ttl_seconds) {
    uint64_t cutoff = timestamp_us() - ttl_seconds * 1000000ULL;
    sqlite3_reset(stmt_gc_tomb_);
    sqlite3_bind_int64(stmt_gc_tomb_, 1, (sqlite3_int64)cutoff);
    return (sqlite3_step(stmt_gc_tomb_) == SQLITE_DONE) ? KOME_OK : KOME_ERR_STORAGE;
}

KomeError KomeLog::gc_values() {
    /* Only run if peers are tracked */
    const char *check = "SELECT COUNT(*) FROM peer_state";
    sqlite3_stmt *sc = nullptr;
    if (sqlite3_prepare_v2(db_, check, -1, &sc, nullptr) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    int rc = sqlite3_step(sc);
    int count = 0;
    if (rc == SQLITE_ROW) count = sqlite3_column_int(sc, 0);
    sqlite3_finalize(sc);
    if (count == 0) return KOME_OK;

    const char *sql =
        "UPDATE change_log SET value = NULL "
        "WHERE tombstone = 0 AND value IS NOT NULL "
        "AND NOT EXISTS ("
        "  SELECT 1 FROM peer_state ps "
        "  WHERE ps.author = change_log.author AND ps.seq < change_log.seq)";
    sqlite3_stmt *s = nullptr;
    if (sqlite3_prepare_v2(db_, sql, -1, &s, nullptr) != SQLITE_OK)
        return KOME_ERR_STORAGE;
    rc = sqlite3_step(s);
    sqlite3_finalize(s);
    return (rc == SQLITE_DONE) ? KOME_OK : KOME_ERR_STORAGE;
}

/* --- Transactions -------------------------------------------------------- */

KomeError KomeLog::begin_transaction() {
    char *err = nullptr;
    int rc = sqlite3_exec(db_, "BEGIN", nullptr, nullptr, &err);
    sqlite3_free(err);
    return (rc == SQLITE_OK) ? KOME_OK : KOME_ERR_STORAGE;
}

KomeError KomeLog::commit_transaction() {
    char *err = nullptr;
    int rc = sqlite3_exec(db_, "COMMIT", nullptr, nullptr, &err);
    sqlite3_free(err);
    return (rc == SQLITE_OK) ? KOME_OK : KOME_ERR_STORAGE;
}

KomeError KomeLog::rollback_transaction() {
    char *err = nullptr;
    int rc = sqlite3_exec(db_, "ROLLBACK", nullptr, nullptr, &err);
    sqlite3_free(err);
    return (rc == SQLITE_OK) ? KOME_OK : KOME_ERR_STORAGE;
}

/* --- Stats --------------------------------------------------------------- */

KomeError KomeLog::get_stats(KomeStats *out) {
    std::memset(out, 0, sizeof(KomeStats));
    auto query_count = [&](const char *sql) -> uint64_t {
        sqlite3_stmt *s = nullptr;
        uint64_t val = 0;
        if (sqlite3_prepare_v2(db_, sql, -1, &s, nullptr) == SQLITE_OK) {
            if (sqlite3_step(s) == SQLITE_ROW)
                val = (uint64_t)sqlite3_column_int64(s, 0);
            sqlite3_finalize(s);
        }
        return val;
    };
    out->total_entries   = query_count("SELECT COUNT(*) FROM change_log");
    out->tombstone_count = query_count("SELECT COUNT(*) FROM change_log WHERE tombstone=1");
    out->namespace_count = query_count("SELECT COUNT(DISTINCT ns) FROM change_log");

    /* db size */
    uint64_t pages = query_count("PRAGMA page_count");
    uint64_t page_sz = query_count("PRAGMA page_size");
    out->db_size_bytes = pages * page_sz;

    return KOME_OK;
}

KomeError KomeLog::list_namespaces(std::vector<std::string> &out) {
    out.clear();
    sqlite3_reset(stmt_list_ns_);
    while (sqlite3_step(stmt_list_ns_) == SQLITE_ROW) {
        const char *ns_ptr = (const char*)sqlite3_column_text(stmt_list_ns_, 0);
        if (ns_ptr) out.emplace_back(ns_ptr);
    }
    return KOME_OK;
}

KomeError KomeLog::list_keys(const char *ns, std::vector<std::vector<uint8_t>> &out) {
    out.clear();
    sqlite3_reset(stmt_list_keys_);
    sqlite3_bind_text(stmt_list_keys_, 1, ns, -1, SQLITE_TRANSIENT);
    while (sqlite3_step(stmt_list_keys_) == SQLITE_ROW) {
        const void *k = sqlite3_column_blob(stmt_list_keys_, 0);
        int klen = sqlite3_column_bytes(stmt_list_keys_, 0);
        if (k && klen > 0)
            out.emplace_back((const uint8_t*)k, (const uint8_t*)k + klen);
    }
    return KOME_OK;
}

} /* namespace kome */
