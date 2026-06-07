/* storage.cpp — SQLite-backed persistence (M2). */
#include "storage.h"

#include <cstring>

#include "capability.h"
#include "codec.h"
#include "crypto.h"
#include "sqlite3.h"

namespace ke {

namespace {

/* Re-verify a record's signature on load. Persisted rows are NOT trusted just
 * because they're on disk — a crafted/swapped DB file could otherwise inject
 * forged records that bypass the signature gate the network path enforces (and
 * be re-gossiped as authentic). Same defense the capability load already uses. */
bool record_sig_ok(const sync_change &c) {
    std::string signing;
    encode_signing(c, signing);
    return verify(c.author, signing.data(), signing.size(), c.signature);
}

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
        "  causal_length INTEGER NOT NULL, ex_author BLOB, ex_sig BLOB,"
        "  db_clock INTEGER NOT NULL,"
        "  PRIMARY KEY(ns, entity));"
        "CREATE TABLE IF NOT EXISTS field ("
        "  ns BLOB NOT NULL, entity BLOB NOT NULL, field BLOB NOT NULL,"
        "  value BLOB, hlc_physical INTEGER NOT NULL, hlc_logical INTEGER NOT NULL,"
        "  author BLOB NOT NULL, sig BLOB NOT NULL, db_clock INTEGER NOT NULL,"
        "  PRIMARY KEY(ns, entity, field));"
        /* Additive (IF NOT EXISTS): granted capabilities, stored as wire blobs.
         * Backward compatible with v2 files, so no schema bump needed. */
        "CREATE TABLE IF NOT EXISTS capability ("
        "  id INTEGER PRIMARY KEY, blob BLOB NOT NULL);";
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

bool Storage::put_meta_blob(const char *key, const uint8_t *data, size_t len) {
    sqlite3_stmt *st = nullptr;
    if (sqlite3_prepare_v2(db_,
                           "INSERT OR REPLACE INTO meta(key,value) VALUES(?,?)",
                           -1, &st, nullptr) != SQLITE_OK)
        return false;
    sqlite3_bind_text(st, 1, key, -1, SQLITE_TRANSIENT);
    sqlite3_bind_blob(st, 2, data, (int)len, SQLITE_TRANSIENT);
    bool ok = sqlite3_step(st) == SQLITE_DONE;
    sqlite3_finalize(st);
    return ok;
}

bool Storage::put_capability(const std::string &blob) {
    sqlite3_stmt *st = nullptr;
    if (sqlite3_prepare_v2(db_, "INSERT INTO capability(blob) VALUES(?)", -1,
                           &st, nullptr) != SQLITE_OK)
        return false;
    sqlite3_bind_blob(st, 1, blob.data(), (int)blob.size(), SQLITE_TRANSIENT);
    bool ok = sqlite3_step(st) == SQLITE_DONE;
    sqlite3_finalize(st);
    return ok;
}

bool Storage::put_entity(const std::string &ns, const std::string &ent,
                         uint64_t causal_length, const PubKey &ex_author,
                         const Sig &ex_sig, uint64_t db_clock) {
    sqlite3_stmt *st = nullptr;
    if (sqlite3_prepare_v2(
            db_,
            "INSERT OR REPLACE INTO entity"
            "(ns,entity,causal_length,ex_author,ex_sig,db_clock)"
            " VALUES(?,?,?,?,?,?)",
            -1, &st, nullptr) != SQLITE_OK)
        return false;
    bind_blob(st, 1, ns);
    bind_blob(st, 2, ent);
    sqlite3_bind_int64(st, 3, (sqlite3_int64)causal_length);
    sqlite3_bind_blob(st, 4, ex_author.data(), (int)ex_author.size(),
                      SQLITE_TRANSIENT);
    sqlite3_bind_blob(st, 5, ex_sig.data(), (int)ex_sig.size(),
                      SQLITE_TRANSIENT);
    sqlite3_bind_int64(st, 6, (sqlite3_int64)db_clock);
    bool ok = sqlite3_step(st) == SQLITE_DONE;
    sqlite3_finalize(st);
    return ok;
}

bool Storage::put_field(const std::string &ns, const std::string &ent,
                        const std::string &field, const std::string &value,
                        const Hlc &hlc, const PubKey &author, const Sig &sig,
                        uint64_t db_clock) {
    sqlite3_stmt *st = nullptr;
    if (sqlite3_prepare_v2(
            db_,
            "INSERT OR REPLACE INTO field"
            "(ns,entity,field,value,hlc_physical,hlc_logical,author,sig,db_clock)"
            " VALUES(?,?,?,?,?,?,?,?,?)",
            -1, &st, nullptr) != SQLITE_OK)
        return false;
    bind_blob(st, 1, ns);
    bind_blob(st, 2, ent);
    bind_blob(st, 3, field);
    bind_blob(st, 4, value);
    sqlite3_bind_int64(st, 5, (sqlite3_int64)hlc.physical);
    sqlite3_bind_int64(st, 6, (sqlite3_int64)hlc.logical);
    sqlite3_bind_blob(st, 7, author.data(), (int)author.size(), SQLITE_TRANSIENT);
    sqlite3_bind_blob(st, 8, sig.data(), (int)sig.size(), SQLITE_TRANSIENT);
    sqlite3_bind_int64(st, 9, (sqlite3_int64)db_clock);
    bool ok = sqlite3_step(st) == SQLITE_DONE;
    sqlite3_finalize(st);
    return ok;
}

bool Storage::load(sync_engine *e, const uint8_t seed[32], sync_error *err) {
    if (err) *err = SYNC_OK;

    /* Read meta. */
    bool have_schema = false, have_seed = false;
    uint64_t schema_version = 0, hlc_physical = 0, db_clock = 0;
    uint32_t hlc_logical = 0;
    uint8_t loaded_seed[32];
    std::memcpy(loaded_seed, seed, 32);

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
        } else if (k == "seed") {
            std::string sv = col_blob(st, 1);
            if (sv.size() == 32) {
                std::memcpy(loaded_seed, sv.data(), 32);
                have_seed = true;
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
        /* Fresh database: stamp schema and identity seed. */
        if (!begin()) { if (err) *err = SYNC_ERR_INTERNAL; return false; }
        bool ok = put_meta_u64("schema_version", kSchemaVersion) &&
                  put_meta_blob("seed", loaded_seed, 32);
        if (!ok || !commit()) {
            rollback();
            if (err) *err = SYNC_ERR_INTERNAL;
            return false;
        }
    }
    (void)have_seed;

    /* Derive identity and apply clock to the engine. */
    e->identity = keypair_from_seed(loaded_seed);
    site_id_from_pubkey(e->identity.sign_pk.data(), e->site_id.data());
    e->clock.physical = hlc_physical;
    e->clock.logical = hlc_logical;
    e->db_clock = db_clock;

    /* Load entities. */
    if (sqlite3_prepare_v2(
            db_, "SELECT ns,entity,causal_length,ex_author,ex_sig FROM entity",
            -1, &st, nullptr) != SQLITE_OK) {
        if (err) *err = SYNC_ERR_INTERNAL;
        return false;
    }
    while (sqlite3_step(st) == SQLITE_ROW) {
        std::string ns = col_blob(st, 0);
        std::string en = col_blob(st, 1);
        uint64_t cl = (uint64_t)sqlite3_column_int64(st, 2);
        std::string a = col_blob(st, 3), s = col_blob(st, 4);
        if (a.size() != SYNC_PUBKEY_LEN || s.size() != SYNC_SIG_LEN) continue;

        /* A present/tombstoned entity (cl>0) carries a signed existence
         * assertion — re-verify it; drop the row if forged. (cl==0 rows hold no
         * signed assertion and only persist a not-present entity for its
         * fields, which are verified below.) */
        if (cl > 0) {
            sync_change c;
            std::memset(&c, 0, sizeof c);
            c.kind = SYNC_CHANGE_EXISTENCE;
            c.ns = (const uint8_t *)ns.data(); c.ns_len = ns.size();
            c.entity = (const uint8_t *)en.data(); c.entity_len = en.size();
            c.causal_length = cl;
            std::memcpy(c.author, a.data(), SYNC_PUBKEY_LEN);
            std::memcpy(c.signature, s.data(), SYNC_SIG_LEN);
            if (!record_sig_ok(c)) continue; /* forged existence assertion */
        }

        Entity &ent = e->ns[ns][en];
        ent.causal_length = cl;
        std::memcpy(ent.ex_author.data(), a.data(), SYNC_PUBKEY_LEN);
        std::memcpy(ent.ex_sig.data(), s.data(), SYNC_SIG_LEN);
    }
    sqlite3_finalize(st);

    /* Load field registers. */
    if (sqlite3_prepare_v2(
            db_,
            "SELECT ns,entity,field,value,hlc_physical,hlc_logical,author,sig"
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
        std::string a = col_blob(st, 6), s = col_blob(st, 7);
        if (a.size() != SYNC_PUBKEY_LEN || s.size() != SYNC_SIG_LEN) continue;
        std::memcpy(r.author.data(), a.data(), SYNC_PUBKEY_LEN);
        std::memcpy(r.sig.data(), s.data(), SYNC_SIG_LEN);

        /* Every field carries a signed register — re-verify; drop if forged. */
        sync_change c;
        std::memset(&c, 0, sizeof c);
        c.kind = SYNC_CHANGE_REGISTER;
        c.ns = (const uint8_t *)ns.data(); c.ns_len = ns.size();
        c.entity = (const uint8_t *)en.data(); c.entity_len = en.size();
        c.field = (const uint8_t *)fl.data(); c.field_len = fl.size();
        c.value = (const uint8_t *)r.value.data(); c.value_len = r.value.size();
        c.hlc.physical = r.hlc.physical;
        c.hlc.logical = r.hlc.logical;
        std::memcpy(c.author, a.data(), SYNC_PUBKEY_LEN);
        std::memcpy(c.signature, s.data(), SYNC_SIG_LEN);
        if (!record_sig_ok(c)) continue; /* forged register */

        e->ns[ns][en].fields[fl] = std::move(r);
    }
    sqlite3_finalize(st);

    /* Load granted capabilities (re-verifying each signature). */
    if (sqlite3_prepare_v2(db_, "SELECT blob FROM capability ORDER BY id", -1,
                           &st, nullptr) == SQLITE_OK) {
        while (sqlite3_step(st) == SQLITE_ROW) {
            std::string blob = col_blob(st, 0);
            Capability cap;
            if (cap_decode((const uint8_t *)blob.data(), blob.size(), cap) &&
                cap_sig_valid(cap)) {
                if (!e->caps) e->caps = new CapStore();
                e->caps->add(cap);
            }
        }
        sqlite3_finalize(st);
    }

    return true;
}

} // namespace ke
