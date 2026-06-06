/* storage.cpp — SQLite-backed persistence (M2). */
#include "storage.h"

#include <cstring>

#include "sqlite3.h"

namespace ke {

namespace {

/* Bind a (possibly empty, possibly NUL-containing) byte string as a BLOB. */
int bind_blob(sqlite3_stmt *st, int idx, const std::string &s) {
    return sqlite3_bind_blob(st, idx, s.empty() ? "" : s.data(),
                             (int)s.size(), SQLITE_TRANSIENT);
}

std::string col_blob(sqlite3_stmt *st, int idx) {
    const void *p = sqlite3_column_blob(st, idx);
    int n = sqlite3_column_bytes(st, idx);
    if (!p || n <= 0) return std::string();
    return std::string(static_cast<const char *>(p), (size_t)n);
}

} // namespace

Storage::~Storage() {
    if (db_) sqlite3_close(db_);
}

bool Storage::exec(const char *sql) {
    char *err = nullptr;
    int rc = sqlite3_exec(db_, sql, nullptr, nullptr, &err);
    if (err) sqlite3_free(err);
    return rc == SQLITE_OK;
}

Storage *Storage::open(const char *path, sync_error *err) {
    if (err) *err = SYNC_OK;
    if (!path) {
        if (err) *err = SYNC_ERR_INVALID;
        return nullptr;
    }
    Storage *s = new (std::nothrow) Storage();
    if (!s) {
        if (err) *err = SYNC_ERR_NOMEM;
        return nullptr;
    }
    if (sqlite3_open(path, &s->db_) != SQLITE_OK) {
        if (err) *err = SYNC_ERR_INTERNAL;
        delete s;
        return nullptr;
    }
    /* WAL for crash-atomic, single-writer durability. busy_timeout so a
     * concurrent reader/writer waits rather than failing immediately. */
    s->exec("PRAGMA journal_mode=WAL;");
    s->exec("PRAGMA synchronous=NORMAL;");
    s->exec("PRAGMA busy_timeout=5000;");

    const char *schema =
        "CREATE TABLE IF NOT EXISTS meta ("
        "  key TEXT PRIMARY KEY, value BLOB);"
        "CREATE TABLE IF NOT EXISTS entity ("
        "  ns BLOB NOT NULL, entity BLOB NOT NULL,"
        "  causal_length INTEGER NOT NULL, db_clock INTEGER NOT NULL,"
        "  PRIMARY KEY(ns, entity));"
        "CREATE TABLE IF NOT EXISTS field ("
        "  ns BLOB NOT NULL, entity BLOB NOT NULL, field BLOB NOT NULL,"
        "  value BLOB, hlc_physical INTEGER NOT NULL, hlc_logical INTEGER NOT NULL,"
        "  site_id BLOB NOT NULL, db_clock INTEGER NOT NULL,"
        "  PRIMARY KEY(ns, entity, field));";
    if (!s->exec(schema)) {
        if (err) *err = SYNC_ERR_INTERNAL;
        delete s;
        return nullptr;
    }
    return s;
}

bool Storage::put_meta_u64(const char *key, uint64_t v) {
    sqlite3_stmt *st = nullptr;
    if (sqlite3_prepare_v2(db_,
                           "INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                           -1, &st, nullptr) != SQLITE_OK)
        return false;
    sqlite3_bind_text(st, 1, key, -1, SQLITE_TRANSIENT);
    sqlite3_bind_int64(st, 2, (sqlite3_int64)v);
    bool ok = sqlite3_step(st) == SQLITE_DONE;
    sqlite3_finalize(st);
    return ok;
}

bool Storage::begin() { return exec("BEGIN IMMEDIATE;"); }
bool Storage::commit() { return exec("COMMIT;"); }
bool Storage::rollback() { return exec("ROLLBACK;"); }

bool Storage::put_entity(const std::string &ns, const std::string &ent,
                         uint64_t causal_length, uint64_t db_clock) {
    sqlite3_stmt *st = nullptr;
    if (sqlite3_prepare_v2(
            db_,
            "INSERT OR REPLACE INTO entity(ns,entity,causal_length,db_clock)"
            " VALUES(?,?,?,?)",
            -1, &st, nullptr) != SQLITE_OK)
        return false;
    bind_blob(st, 1, ns);
    bind_blob(st, 2, ent);
    sqlite3_bind_int64(st, 3, (sqlite3_int64)causal_length);
    sqlite3_bind_int64(st, 4, (sqlite3_int64)db_clock);
    bool ok = sqlite3_step(st) == SQLITE_DONE;
    sqlite3_finalize(st);
    return ok;
}

bool Storage::put_field(const std::string &ns, const std::string &ent,
                        const std::string &field, const std::string &value,
                        const Hlc &hlc, const SiteId &site, uint64_t db_clock) {
    sqlite3_stmt *st = nullptr;
    if (sqlite3_prepare_v2(
            db_,
            "INSERT OR REPLACE INTO field"
            "(ns,entity,field,value,hlc_physical,hlc_logical,site_id,db_clock)"
            " VALUES(?,?,?,?,?,?,?,?)",
            -1, &st, nullptr) != SQLITE_OK)
        return false;
    bind_blob(st, 1, ns);
    bind_blob(st, 2, ent);
    bind_blob(st, 3, field);
    bind_blob(st, 4, value);
    sqlite3_bind_int64(st, 5, (sqlite3_int64)hlc.physical);
    sqlite3_bind_int64(st, 6, (sqlite3_int64)hlc.logical);
    sqlite3_bind_blob(st, 7, site.data(), (int)site.size(), SQLITE_TRANSIENT);
    sqlite3_bind_int64(st, 8, (sqlite3_int64)db_clock);
    bool ok = sqlite3_step(st) == SQLITE_DONE;
    sqlite3_finalize(st);
    return ok;
}

bool Storage::load(sync_engine *e, const SiteId &site_id_default,
                   sync_error *err) {
    if (err) *err = SYNC_OK;

    /* Read meta into a small map. */
    bool have_schema = false, have_site = false;
    uint64_t schema_version = 0, hlc_physical = 0, db_clock = 0;
    uint32_t hlc_logical = 0;
    SiteId loaded_site = site_id_default;

    sqlite3_stmt *st = nullptr;
    if (sqlite3_prepare_v2(db_, "SELECT key,value FROM meta", -1, &st,
                           nullptr) != SQLITE_OK) {
        if (err) *err = SYNC_ERR_INTERNAL;
        return false;
    }
    while (sqlite3_step(st) == SQLITE_ROW) {
        std::string k = col_blob(st, 0);
        if (k == "schema_version") {
            schema_version = (uint64_t)sqlite3_column_int64(st, 1);
            have_schema = true;
        } else if (k == "site_id") {
            std::string sv = col_blob(st, 1);
            if (sv.size() == SYNC_SITE_ID_LEN) {
                std::memcpy(loaded_site.data(), sv.data(), SYNC_SITE_ID_LEN);
                have_site = true;
            }
        } else if (k == "hlc_physical") {
            hlc_physical = (uint64_t)sqlite3_column_int64(st, 1);
        } else if (k == "hlc_logical") {
            hlc_logical = (uint32_t)sqlite3_column_int64(st, 1);
        } else if (k == "db_clock") {
            db_clock = (uint64_t)sqlite3_column_int64(st, 1);
        }
    }
    sqlite3_finalize(st);

    /* Schema guard (T2.4): unknown/newer version is rejected cleanly. */
    if (have_schema && schema_version != kSchemaVersion) {
        if (err) *err = SYNC_ERR_INVALID;
        return false;
    }

    if (!have_schema) {
        /* Fresh database: stamp schema and identity. */
        if (!begin()) { if (err) *err = SYNC_ERR_INTERNAL; return false; }
        bool ok = put_meta_u64("schema_version", kSchemaVersion);
        sqlite3_stmt *ms = nullptr;
        if (ok && sqlite3_prepare_v2(
                      db_, "INSERT OR REPLACE INTO meta(key,value) VALUES('site_id',?)",
                      -1, &ms, nullptr) == SQLITE_OK) {
            sqlite3_bind_blob(ms, 1, site_id_default.data(),
                              (int)site_id_default.size(), SQLITE_TRANSIENT);
            ok = ok && sqlite3_step(ms) == SQLITE_DONE;
            sqlite3_finalize(ms);
        } else {
            ok = false;
        }
        if (!ok || !commit()) {
            rollback();
            if (err) *err = SYNC_ERR_INTERNAL;
            return false;
        }
        loaded_site = site_id_default;
    }
    (void)have_site;

    /* Apply identity + clock + db_clock to the engine. */
    e->site_id = loaded_site;
    e->clock.physical = hlc_physical;
    e->clock.logical = hlc_logical;
    e->db_clock = db_clock;

    /* Load entities. */
    if (sqlite3_prepare_v2(db_,
                           "SELECT ns,entity,causal_length FROM entity", -1,
                           &st, nullptr) != SQLITE_OK) {
        if (err) *err = SYNC_ERR_INTERNAL;
        return false;
    }
    while (sqlite3_step(st) == SQLITE_ROW) {
        std::string ns = col_blob(st, 0);
        std::string en = col_blob(st, 1);
        uint64_t cl = (uint64_t)sqlite3_column_int64(st, 2);
        e->ns[ns][en].causal_length = cl;
    }
    sqlite3_finalize(st);

    /* Load field registers. */
    if (sqlite3_prepare_v2(
            db_,
            "SELECT ns,entity,field,value,hlc_physical,hlc_logical,site_id"
            " FROM field",
            -1, &st, nullptr) != SQLITE_OK) {
        if (err) *err = SYNC_ERR_INTERNAL;
        return false;
    }
    while (sqlite3_step(st) == SQLITE_ROW) {
        std::string ns = col_blob(st, 0);
        std::string en = col_blob(st, 1);
        std::string fl = col_blob(st, 2);
        Register r;
        r.value = col_blob(st, 3);
        r.hlc.physical = (uint64_t)sqlite3_column_int64(st, 4);
        r.hlc.logical = (uint32_t)sqlite3_column_int64(st, 5);
        std::string sid = col_blob(st, 6);
        if (sid.size() == SYNC_SITE_ID_LEN)
            std::memcpy(r.site.data(), sid.data(), SYNC_SITE_ID_LEN);
        e->ns[ns][en].fields[fl] = std::move(r);
    }
    sqlite3_finalize(st);

    return true;
}

} // namespace ke
