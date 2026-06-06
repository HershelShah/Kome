/* storage_test.cpp — M2 durable storage acceptance tests (T2.1-T2.7).
 *
 * Verifies that on-disk replicas behave identically to in-memory ones: reopen
 * identity, convergence with persistence, crash atomicity, schema guarding,
 * single-file storage, scale, and that the M1 oracle still holds. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <array>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <dirent.h>
#include <random>
#include <set>
#include <string>
#include <vector>

#include "sqlite3.h" /* T2.4 tampers with the file directly */

namespace {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;

const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

std::array<uint8_t, SYNC_SITE_ID_LEN> site_from(uint8_t seed) {
    std::array<uint8_t, SYNC_SITE_ID_LEN> s{};
    for (auto &b : s) b = seed;
    return s;
}

Digest digest(sync_engine *e) {
    Digest d{};
    EXPECT_EQ(sync_engine_digest(e, d.data()), SYNC_OK);
    return d;
}

void replicate(sync_engine *from, sync_engine *into) {
    sync_change *recs = nullptr;
    size_t n = 0;
    ASSERT_EQ(sync_engine_export(from, &recs, &n), SYNC_OK);
    for (size_t i = 0; i < n; i++)
        ASSERT_EQ(sync_engine_apply(into, &recs[i]), SYNC_OK);
    sync_changes_free(recs, n);
}

void random_ops(sync_engine *e, std::mt19937 &rng, int count) {
    const char *nss[] = {"a", "b"};
    for (int i = 0; i < count; i++) {
        std::string ns = nss[rng() % 2];
        std::string ent = "e" + std::to_string(rng() % 8);
        if (rng() % 5 == 0) {
            sync_engine_delete(e, B(ns), ns.size(), B(ent), ent.size());
        } else {
            std::string field = "f" + std::to_string(rng() % 3);
            std::string val = "v" + std::to_string(rng() % 100);
            sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(),
                            B(field), field.size(), B(val), val.size());
        }
    }
}

/* A unique temp directory that cleans itself up. */
struct TempDir {
    std::string path;
    TempDir() {
        char tmpl[] = "/tmp/sync_storage_XXXXXX";
        char *p = mkdtemp(tmpl);
        EXPECT_NE(p, nullptr);
        path = p;
    }
    ~TempDir() {
        DIR *d = opendir(path.c_str());
        if (d) {
            struct dirent *e;
            while ((e = readdir(d))) {
                std::string n = e->d_name;
                if (n == "." || n == "..") continue;
                std::remove((path + "/" + n).c_str());
            }
            closedir(d);
        }
        rmdir(path.c_str());
    }
    std::string file(const char *name) const { return path + "/" + name; }
};

} // namespace

/* ---- T2.1 Reopen identity ---------------------------------------------- */
TEST(Storage, ReopenIdentity) {
    TempDir dir;
    std::string db = dir.file("state.db");
    auto site = site_from(0x01);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    std::mt19937 rng(1234);
    random_ops(e, rng, 100);
    Digest before = digest(e);
    sync_engine_destroy(e);

    /* Capture identity before close. */
    uint8_t id_before[SYNC_SITE_ID_LEN], pk_before[SYNC_PUBKEY_LEN];
    {
        sync_engine *e1 = sync_engine_open(db.c_str(), site.data());
        ASSERT_NE(e1, nullptr);
        sync_engine_site_id(e1, id_before);
        sync_engine_identity(e1, pk_before);
        sync_engine_destroy(e1);
    }

    sync_engine *e2 = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e2, nullptr);
    Digest after = digest(e2);
    EXPECT_EQ(before, after);

    /* Identity persists and site_id == BLAKE2b-256(pubkey) is stable. */
    uint8_t id[SYNC_SITE_ID_LEN], pk[SYNC_PUBKEY_LEN];
    sync_engine_site_id(e2, id);
    sync_engine_identity(e2, pk);
    EXPECT_EQ(0, std::memcmp(id, id_before, SYNC_SITE_ID_LEN));
    EXPECT_EQ(0, std::memcmp(pk, pk_before, SYNC_PUBKEY_LEN));
    sync_engine_destroy(e2);
}

/* ---- T2.2 Convergence with persistence (reopen mid-exchange) ----------- */
TEST(Storage, ConvergenceWithPersistence) {
    TempDir dir;
    std::string dba = dir.file("a.db"), dbb = dir.file("b.db");
    auto sa = site_from(0x0A), sb = site_from(0x0B);

    sync_engine *a = sync_engine_open(dba.c_str(), sa.data());
    sync_engine *b = sync_engine_open(dbb.c_str(), sb.data());
    ASSERT_NE(a, nullptr);
    ASSERT_NE(b, nullptr);

    std::mt19937 ra(11), rb(22);
    random_ops(a, ra, 50);
    random_ops(b, rb, 50);

    /* First exchange. */
    replicate(a, b);

    /* Reopen A mid-exchange. */
    sync_engine_destroy(a);
    a = sync_engine_open(dba.c_str(), sa.data());
    ASSERT_NE(a, nullptr);

    replicate(b, a);
    /* Reopen B too. */
    sync_engine_destroy(b);
    b = sync_engine_open(dbb.c_str(), sb.data());
    ASSERT_NE(b, nullptr);

    /* Final settle. */
    replicate(a, b);
    replicate(b, a);

    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T2.3 Crash atomicity (SIGKILL mid-write) -------------------------- */
TEST(Storage, CrashAtomicity) {
    TempDir dir;
    std::string db = dir.file("crash.db");
    auto site = site_from(0x05);

    /* Seed a known committed record, then crash a writer mid-stream. */
    sync_engine *seed = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(seed, nullptr);
    sync_engine_set(seed, B(std::string("n")), 1, B(std::string("anchor")), 6,
                    B(std::string("f")), 1, B(std::string("v")), 1);
    sync_engine_destroy(seed);

    pid_t pid = fork();
    ASSERT_GE(pid, 0);
    if (pid == 0) {
        /* Child: hammer writes forever; parent will SIGKILL us mid-write. */
        sync_engine *c = sync_engine_open(db.c_str(), site.data());
        if (!c) _exit(2);
        std::mt19937 rng(99);
        for (int i = 0;; i++) {
            std::string ent = "k" + std::to_string(i);
            std::string val = "val" + std::to_string(i);
            sync_engine_set(c, B(std::string("n")), 1, B(ent), ent.size(),
                            B(std::string("f")), 1, B(val), val.size());
        }
        _exit(0); /* unreachable */
    }

    usleep(40 * 1000); /* let it write a while */
    kill(pid, SIGKILL);
    int status = 0;
    waitpid(pid, &status, 0);

    /* Reopen must succeed with a consistent, convergent state (no corruption,
     * no partial record), and the pre-crash anchor must survive. */
    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr) << "database corrupted by crash mid-write";
    Digest d{};
    EXPECT_EQ(sync_engine_digest(e, d.data()), SYNC_OK);

    uint8_t *v = nullptr;
    size_t l = 0;
    EXPECT_EQ(sync_engine_get(e, B(std::string("n")), 1,
                              B(std::string("anchor")), 6,
                              B(std::string("f")), 1, &v, &l),
              SYNC_OK);
    sync_free(v);

    /* Convergence still holds: its export applies cleanly into a fresh peer. */
    auto sp = site_from(0x06);
    sync_engine *peer = sync_engine_create(sp.data());
    replicate(e, peer);
    EXPECT_EQ(digest(e), digest(peer));

    sync_engine_destroy(e);
    sync_engine_destroy(peer);
}

/* ---- T2.4 Schema guard ------------------------------------------------- */
TEST(Storage, SchemaGuard) {
    TempDir dir;
    std::string db = dir.file("schema.db");
    auto site = site_from(0x07);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    sync_engine_set(e, B(std::string("n")), 1, B(std::string("x")), 1,
                    B(std::string("f")), 1, B(std::string("v")), 1);
    sync_engine_destroy(e);

    /* Forge a newer schema_version directly in the file. */
    sqlite3 *raw = nullptr;
    ASSERT_EQ(sqlite3_open(db.c_str(), &raw), SQLITE_OK);
    ASSERT_EQ(sqlite3_exec(
                  raw,
                  "UPDATE meta SET value=9999 WHERE key='schema_version'",
                  nullptr, nullptr, nullptr),
              SQLITE_OK);
    sqlite3_close(raw);

    /* Opening must fail cleanly (no crash, no corruption). */
    sync_engine *bad = sync_engine_open(db.c_str(), site.data());
    EXPECT_EQ(bad, nullptr);

    /* File is still intact and re-openable once the version is restored. */
    ASSERT_EQ(sqlite3_open(db.c_str(), &raw), SQLITE_OK);
    ASSERT_EQ(sqlite3_exec(raw,
                           "UPDATE meta SET value=2 WHERE key='schema_version'",
                           nullptr, nullptr, nullptr),
              SQLITE_OK);
    sqlite3_close(raw);
    sync_engine *ok = sync_engine_open(db.c_str(), site.data());
    EXPECT_NE(ok, nullptr);
    sync_engine_destroy(ok);
}

/* ---- T2.5 Single file -------------------------------------------------- */
TEST(Storage, SingleFile) {
    TempDir dir;
    std::string db = dir.file("only.db");
    auto site = site_from(0x08);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    std::mt19937 rng(7);
    random_ops(e, rng, 100);
    sync_engine_flush(e);

    std::set<std::string> allowed = {"only.db", "only.db-wal", "only.db-shm",
                                     "only.db-journal"};
    DIR *d = opendir(dir.path.c_str());
    ASSERT_NE(d, nullptr);
    struct dirent *ent;
    while ((ent = readdir(d))) {
        std::string n = ent->d_name;
        if (n == "." || n == "..") continue;
        EXPECT_TRUE(allowed.count(n) > 0) << "unexpected file: " << n;
    }
    closedir(d);
    sync_engine_destroy(e);
}

/* ---- T2.6 Scale load --------------------------------------------------- */
TEST(Storage, ScaleLoad) {
    TempDir dir;
    std::string db = dir.file("scale.db");
    auto site = site_from(0x09);

    const int N = 400;
    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    for (int i = 0; i < N; i++) {
        std::string ent = "entity" + std::to_string(i);
        for (int f = 0; f < 3; f++) {
            std::string field = "f" + std::to_string(f);
            std::string val = "value-" + std::to_string(i) + "-" + std::to_string(f);
            sync_engine_set(e, B(std::string("ns")), 2, B(ent), ent.size(),
                            B(field), field.size(), B(val), val.size());
        }
    }
    Digest before = digest(e);
    sync_engine_destroy(e);

    /* Reopen: everything present, digest stable. */
    sync_engine *e2 = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e2, nullptr);
    EXPECT_EQ(before, digest(e2));
    for (int i = 0; i < N; i++) {
        std::string ent = "entity" + std::to_string(i);
        int present = 0;
        sync_engine_exists(e2, B(std::string("ns")), 2, B(ent), ent.size(),
                           &present);
        EXPECT_EQ(present, 1) << "missing entity " << i;
    }

    /* In-memory equivalent: applying the reopened export reproduces the digest. */
    auto sm = site_from(0x10);
    sync_engine *mem = sync_engine_create(sm.data());
    replicate(e2, mem);
    EXPECT_EQ(digest(e2), digest(mem));

    sync_engine_destroy(e2);
    sync_engine_destroy(mem);
}

/* ---- T2.7 Oracle still green (convergence over persisted engines) ------ */
TEST(Storage, OracleConvergesPersisted) {
    TempDir dir;
    const unsigned base = 0x4242u;
    for (int trial = 0; trial < 25; trial++) {
        std::string dba = dir.file(("oa" + std::to_string(trial) + ".db").c_str());
        std::string dbb = dir.file(("ob" + std::to_string(trial) + ".db").c_str());
        auto sa = site_from(0x0A), sb = site_from(0x0B);

        sync_engine *a = sync_engine_open(dba.c_str(), sa.data());
        sync_engine *b = sync_engine_open(dbb.c_str(), sb.data());
        ASSERT_NE(a, nullptr);
        ASSERT_NE(b, nullptr);

        std::mt19937 ra(base + trial * 2), rb(base + trial * 2 + 1);
        random_ops(a, ra, 30);
        random_ops(b, rb, 30);

        replicate(a, b);
        replicate(b, a);
        replicate(a, b);
        replicate(b, a);

        ASSERT_EQ(digest(a), digest(b)) << "persisted divergence trial " << trial;
        sync_engine_destroy(a);
        sync_engine_destroy(b);
    }
}
