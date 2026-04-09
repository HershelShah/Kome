#ifndef KOME_LOG_HPP
#define KOME_LOG_HPP

/**
 * @file kome_log.hpp
 * @brief SQLite storage layer.
 *
 * KomeLog manages all persistent state: entries, version vectors,
 * namespace TTL settings, and tombstone garbage collection.
 *
 * ## Schema
 *
 * ```
 * change_log       (ns, key) → (value, timestamp_us, author, seq, hash, value_len, tombstone)
 * version_vector   (author)  → (seq)      -- highest seq seen per author
 * namespace_settings (ns)    → (tombstone_ttl_sec)  -- per-ns entry TTL
 * ```
 *
 * ## Thread safety
 *
 * KomeLog is NOT thread-safe on its own. All access is serialized by
 * the engine lock (KomeEngine::mu). The SQLite handle is opened with
 * SQLITE_OPEN_FULLMUTEX for defense-in-depth but the engine lock is
 * the primary concurrency mechanism.
 */

#include "kome_entry.hpp"
#include <map>

struct sqlite3;
struct sqlite3_stmt;

namespace kome {

/// Alias — LogEntry and Entry are the same type
using LogEntry = Entry;

class KomeLog {
public:
    KomeLog();
    ~KomeLog();

    KomeError open(const char *path, int enable_wal, int busy_timeout_ms,
                   const uint8_t *encryption_key = nullptr,
                   size_t encryption_key_len = 0);
    void close();

    /** Insert or replace an entry. Tombstones are stored with NULL value. */
    KomeError put_entry(const char *ns, const uint8_t *key, size_t key_len,
                        const uint8_t *value, size_t value_len,
                        const KomeEntryMeta *meta);
    KomeError get_entry(const char *ns, const uint8_t *key, size_t key_len,
                        LogEntry *out);
    KomeError delete_entry(const char *ns, const uint8_t *key, size_t key_len,
                           const KomeEntryMeta *meta);

    /** Update the version vector: set author's seq to max(current, new). */
    KomeError update_version_vector(const uint8_t author[32], uint64_t seq);
    KomeError get_version_vector(std::map<std::string, uint64_t> &vv);

    /** Get entries by a specific author after a given sequence number. */
    KomeError get_entries_after(const uint8_t author[32], uint64_t after_seq,
                                std::vector<LogEntry> &out);
    /** Diff our version vector against a remote's to find entries they're missing. */
    KomeError get_missing_entries(const std::map<std::string, uint64_t> &remote_vv,
                                   std::vector<LogEntry> &out);

    /** Set per-namespace entry TTL (persisted in namespace_settings table). */
    KomeError set_entry_ttl(const char *ns, uint64_t ttl_sec);

    /** Delete tombstones older than their namespace's TTL (or default). */
    KomeError gc_tombstones(uint64_t default_ttl_seconds);

    KomeError begin_transaction();
    KomeError commit_transaction();
    KomeError rollback_transaction();

    KomeError get_stats(KomeStats *out);
    KomeError list_namespaces(std::vector<std::string> &out);
    KomeError list_keys(const char *ns, std::vector<std::vector<uint8_t>> &out);
    KomeError get_all_entries(const char *ns, std::vector<LogEntry> &out);

private:
    sqlite3 *db_ = nullptr;

    sqlite3_stmt *stmt_put_          = nullptr;
    sqlite3_stmt *stmt_get_          = nullptr;
    sqlite3_stmt *stmt_update_vv_    = nullptr;
    sqlite3_stmt *stmt_get_vv_       = nullptr;
    sqlite3_stmt *stmt_after_        = nullptr;
    sqlite3_stmt *stmt_gc_tomb_      = nullptr;
    sqlite3_stmt *stmt_list_ns_      = nullptr;
    sqlite3_stmt *stmt_list_keys_    = nullptr;
    sqlite3_stmt *stmt_get_all_      = nullptr;
    sqlite3_stmt *stmt_set_ttl_      = nullptr;

    KomeError create_tables();
    void finalize_stmts();
    KomeError prepare_stmts();
};

} /* namespace kome */

#endif /* KOME_LOG_HPP */
