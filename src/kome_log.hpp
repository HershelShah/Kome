#ifndef KOME_LOG_HPP
#define KOME_LOG_HPP

#include "kome.h"
#include <cstdint>
#include <string>
#include <vector>
#include <map>

struct sqlite3;
struct sqlite3_stmt;

namespace kome {

struct LogEntry {
    std::string             ns;
    std::vector<uint8_t>    key;
    std::vector<uint8_t>    value;
    uint64_t                timestamp_us = 0;
    uint8_t                 author[32] = {};
    uint64_t                seq = 0;
    uint8_t                 hash[32] = {};
    uint8_t                 tombstone = 0;
};

class KomeLog {
public:
    KomeLog();
    ~KomeLog();

    KomeError open(const char *path, int enable_wal, int busy_timeout_ms);
    void close();

    KomeError put_entry(const char *ns, const uint8_t *key, size_t key_len,
                        const uint8_t *value, size_t value_len,
                        const KomeEntryMeta *meta);
    KomeError get_entry(const char *ns, const uint8_t *key, size_t key_len,
                        LogEntry *out);
    KomeError delete_entry(const char *ns, const uint8_t *key, size_t key_len,
                           const KomeEntryMeta *meta);

    KomeError update_version_vector(const uint8_t author[32], uint64_t seq);
    KomeError get_version_vector(std::map<std::string, uint64_t> &vv);

    KomeError update_peer_state(const uint8_t peer_fp[32],
                                const uint8_t author[32], uint64_t seq);

    KomeError get_entries_after(const uint8_t author[32], uint64_t after_seq,
                                std::vector<LogEntry> &out);
    KomeError get_missing_entries(const std::map<std::string, uint64_t> &remote_vv,
                                   std::vector<LogEntry> &out);

    KomeError set_replication_target(const char *ns, uint32_t target_n);
    KomeError get_replication_target(const char *ns, uint32_t *target_out);
    KomeError get_replication_confirmed(const char *ns, const uint8_t *key,
                                        size_t key_len, uint32_t *confirmed_out);
    KomeError increment_replication_peer(const char *ns, const uint8_t *key,
                                          size_t key_len, const uint8_t peer_fp[32]);

    KomeError gc_tombstones(uint64_t ttl_seconds);
    KomeError gc_values();

    KomeError begin_transaction();
    KomeError commit_transaction();
    KomeError rollback_transaction();

    KomeError get_stats(KomeStats *out);
    KomeError list_namespaces(std::vector<std::string> &out);
    KomeError list_keys(const char *ns, std::vector<std::vector<uint8_t>> &out);

private:
    sqlite3 *db_ = nullptr;

    /* All prepared statements — initialized once in prepare_stmts() */
    sqlite3_stmt *stmt_put_          = nullptr;
    sqlite3_stmt *stmt_get_          = nullptr;
    sqlite3_stmt *stmt_update_vv_    = nullptr;
    sqlite3_stmt *stmt_get_vv_       = nullptr;
    sqlite3_stmt *stmt_update_ps_    = nullptr;
    sqlite3_stmt *stmt_after_        = nullptr;
    sqlite3_stmt *stmt_del_repl_     = nullptr;
    sqlite3_stmt *stmt_set_repl_     = nullptr;
    sqlite3_stmt *stmt_get_repl_     = nullptr;
    sqlite3_stmt *stmt_count_repl_   = nullptr;
    sqlite3_stmt *stmt_inc_repl_     = nullptr;
    sqlite3_stmt *stmt_gc_tomb_      = nullptr;
    sqlite3_stmt *stmt_list_ns_      = nullptr;
    sqlite3_stmt *stmt_list_keys_    = nullptr;

    KomeError create_tables();
    void finalize_stmts();
    KomeError prepare_stmts();
};

} /* namespace kome */

#endif /* KOME_LOG_HPP */
