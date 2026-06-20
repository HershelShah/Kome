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

#include "byteorder.h" /* T2.4 tampers with the log file directly */
#include "cluster.hpp"
#include "sha256.h"
#include "storage.h" /* kSchemaVersion */
#include "tempdir.hpp"

namespace {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
using cluster::B;
using synctest::TempDir;

/* ---- direct log-file manipulation (for the tamper/version tests) -------- *
 * The store is an append-only log of length-prefixed, SHA-checksummed frames
 * (storage.cpp). To corrupt a record on disk, edit its bytes in place then
 * recompute the enclosing frames' checksums — otherwise the frame is rejected
 * as a torn write before the per-record signature check we want to exercise. */
std::string read_file(const std::string &p) {
    FILE *f = fopen(p.c_str(), "rb");
    if (!f) return {};
    std::string b;
    char tmp[4096];
    size_t n;
    while ((n = fread(tmp, 1, sizeof tmp, f)) > 0) b.append(tmp, n);
    fclose(f);
    return b;
}
void write_file(const std::string &p, const std::string &b) {
    FILE *f = fopen(p.c_str(), "wb");
    ASSERT_NE(f, nullptr);
    ASSERT_EQ(fwrite(b.data(), 1, b.size(), f), b.size());
    fclose(f);
}
/* Rewrite every frame's trailing 8-byte checksum to match its (edited) body. */
void recompute_frames(std::string &buf) {
    size_t pos = 8; /* skip the 8-byte magic header */
    while (pos + 4 <= buf.size()) {
        uint32_t blen = ke::read_u32le((const uint8_t *)buf.data() + pos);
        size_t body = pos + 4;
        if (body + blen + 8 > buf.size()) break;
        uint8_t d[32];
        sync_engine_detail::sha256(buf.data() + body, blen, d);
        std::memcpy(&buf[body + blen], d, 8);
        pos = body + blen + 8;
    }
}
size_t find_or_die(const std::string &b, const std::string &needle) {
    size_t i = b.find(needle);
    EXPECT_NE(i, std::string::npos);
    return i;
}

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

/* S2: rows are NOT trusted just for being on disk. A crafted/swapped DB file
 * with a corrupted signature must be dropped on load, not laundered into the
 * trusted (and re-gossiped) set. */
TEST(Storage, ForgedRowRejectedOnLoad) {
    TempDir dir;
    std::string db = dir.file("forged.db");
    auto site = site_from(0x05);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    cluster::put(e, "ns", "keep", "f", "good");      /* stays valid */
    cluster::put(e, "ns", "tamper", "f", "secret");  /* field sig corrupted */
    cluster::put(e, "ns", "ghost", "f", "boo");       /* existence sig corrupted */
    sync_engine_destroy(e);

    /* Corrupt signatures directly in the log, then fix the frame checksums so
     * the per-record signature check (not the frame check) is what rejects them.
     * Field entry after the value bytes: phys(8) log(4) author(32) sig(64).
     * Entity entry after "<ent>": present(1) phys(8) log(4) author(32) sig(64). */
    std::string buf = read_file(db);
    {
        size_t v = find_or_die(buf, "secret");      /* tamper's field value */
        size_t sig = v + 6 /*secret*/ + 8 + 4 + 32; /* -> field sig */
        for (int k = 0; k < (int)SYNC_SIG_LEN; k++) buf[sig + k] = 0;
    }
    {
        /* The ghost ENTITY record (not its field record): kEntity(2) ns="ns"
         * ent="ghost". After "ghost": present(1) hlc(12) author(32) sig(64). */
        std::string needle;
        needle.push_back((char)0x02);  /* kEntity */
        needle.push_back((char)0x02);  /* ns length = 2 */
        needle += "ns";
        needle.push_back((char)0x05);  /* entity length = 5 */
        needle += "ghost";
        size_t g = find_or_die(buf, needle);
        size_t sig = g + needle.size() + 1 /*present*/ + 12 /*hlc*/ + 32 /*author*/;
        for (int k = 0; k < (int)SYNC_SIG_LEN; k++) buf[sig + k] = 0;
    }
    recompute_frames(buf);
    write_file(db, buf);

    sync_engine *e2 = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e2, nullptr);
    EXPECT_EQ(cluster::get(e2, "ns", "keep", "f"), "good")
        << "legit signed row must survive";
    EXPECT_TRUE(cluster::exists(e2, "ns", "tamper")); /* existence intact */
    EXPECT_EQ(cluster::get(e2, "ns", "tamper", "f"), "<none>")
        << "field with a forged signature must be dropped";
    EXPECT_FALSE(cluster::exists(e2, "ns", "ghost"))
        << "entity with a forged existence signature must be dropped";
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

    /* Forge a newer schema_version directly in the log. The meta entry is
     * key="schema_version" then value = varint(8) + u64le; overwrite the 8
     * value bytes, then fix the frame checksum. */
    auto set_version = [&](uint64_t v) {
        std::string buf = read_file(db);
        size_t k = find_or_die(buf, "schema_version");
        size_t val = k + 14 /*key*/ + 1 /*varint len=8*/;
        uint8_t le[8];
        ke::store_u64le(le, v);
        for (int i = 0; i < 8; i++) buf[val + i] = (char)le[i];
        recompute_frames(buf);
        write_file(db, buf);
    };
    set_version(9999);

    /* Opening must fail cleanly (no crash, no corruption). */
    sync_engine *bad = sync_engine_open(db.c_str(), site.data());
    EXPECT_EQ(bad, nullptr);

    /* File is still intact and re-openable once the version is restored. */
    set_version(ke::kSchemaVersion);
    sync_engine *ok = sync_engine_open(db.c_str(), site.data());
    EXPECT_NE(ok, nullptr);
    sync_engine_destroy(ok);
}

/* Regression: a frame's length prefix is untrusted bytes off disk. A crafted
 * (or torn) frame claiming a body far larger than the file must not make load()
 * size a buffer off that length — the nightly storage fuzzer found a 2.7 GB
 * allocation (malloc(2857319244)) from the input "KOMELOG1" + a bogus u32 len.
 * The frame must be treated as a torn tail: open cleanly, prior data intact, no
 * gigabyte allocation / OOM. */
TEST(Storage, HugeFrameLengthRejectedOnLoad) {
    TempDir dir;
    std::string db = dir.file("hugeframe.db");
    auto site = site_from(0x11);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    sync_engine_set(e, B(std::string("n")), 1, B(std::string("x")), 1,
                    B(std::string("f")), 1, B(std::string("v")), 1);
    sync_engine_destroy(e);

    /* Append a frame whose length prefix claims ~4 GiB of body, backed by only a
     * handful of bytes — exactly the shape the fuzzer hit. */
    std::string buf = read_file(db);
    std::string forged;
    ke::put_u32le(forged, 0xFFFFFFF0u);
    forged.append(8, '\xaa'); /* far fewer bytes than the length claims */
    write_file(db, buf + forged);

    /* Must open without OOM/crash; the forged trailing frame is dropped and the
     * committed key survives. */
    sync_engine *r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);
    int exists = 0;
    EXPECT_EQ(sync_engine_exists(r, B(std::string("n")), 1, B(std::string("x")), 1,
                                 &exists),
              SYNC_OK);
    EXPECT_EQ(exists, 1);
    sync_engine_destroy(r);

    /* The torn tail was truncated, so the file is clean and re-openable. */
    sync_engine *r2 = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r2, nullptr);
    sync_engine_destroy(r2);
}

/* Compaction bounds the append-only log: hammering one cell would grow the log
 * without limit, but the Bitcask "merge" rewrites it to one record per live
 * cell. The file must stay small and the state must be preserved across reopen. */
TEST(Storage, CompactionBoundsLog) {
    TempDir dir;
    std::string db = dir.file("compact.db");
    auto site = site_from(0x0C);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    const int kWrites = 5000;
    for (int i = 0; i < kWrites; i++)
        cluster::put(e, "ns", "k", "f", "v" + std::to_string(i));
    Digest d0;
    ASSERT_EQ(sync_engine_digest(e, d0.data()), SYNC_OK);
    sync_engine_destroy(e);

    /* One live cell, so the log must be tiny vs. the ~kWrites records it would
     * hold uncompacted (each record is a few hundred bytes). */
    size_t sz = read_file(db).size();
    EXPECT_LT(sz, 256u * 1024u) << "log was not compacted (size=" << sz << ")";

    /* Reopen: compaction preserved exactly the current state. */
    sync_engine *e2 = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e2, nullptr);
    Digest d1;
    ASSERT_EQ(sync_engine_digest(e2, d1.data()), SYNC_OK);
    EXPECT_EQ(d0, d1) << "compaction changed the engine state";
    EXPECT_EQ(cluster::get(e2, "ns", "k", "f"), "v" + std::to_string(kWrites - 1));
    sync_engine_destroy(e2);
}

/* Compaction drops tombstones older than kTombstoneTtlMs (bounding delete-heavy
 * growth) while keeping live entities and fresh tombstones. */
TEST(Storage, TombstoneGcOnCompaction) {
    TempDir dir;
    std::string db = dir.file("gc.db");
    auto site = site_from(0x0D);

    /* Whether an entity appears in the exported state at all (a tombstone is
     * still exported as an existence record; a GC'd entity is not). */
    auto has_entity = [](sync_engine *e, const char *ent) {
        sync_change *r = nullptr;
        size_t n = 0;
        sync_engine_export(e, &r, &n);
        bool found = false;
        for (size_t i = 0; i < n; i++)
            if (std::string((char *)r[i].entity, r[i].entity_len) == ent)
                found = true;
        sync_changes_free(r, n);
        return found;
    };

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    cluster::put(e, "ns", "live", "f", "v");      /* live -> kept */
    cluster::put(e, "ns", "recent", "f", "v");
    cluster::del(e, "ns", "recent");               /* fresh tombstone -> kept */

    /* An expired tombstone: present=false at physical=1 (epoch), signed. */
    const std::string ns = "ns", ent = "old";
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_EXISTENCE;
    c.ns = B(ns); c.ns_len = ns.size();
    c.entity = B(ent); c.entity_len = ent.size();
    c.causal_length = 0; /* present = false */
    c.hlc.physical = 1; c.hlc.logical = 0;
    ASSERT_EQ(sync_change_sign(&c, site_from(0x0E).data()), SYNC_OK);
    ASSERT_EQ(sync_engine_apply(e, &c), SYNC_OK);
    EXPECT_TRUE(has_entity(e, "old")); /* present before GC */

    ASSERT_TRUE(e->store->compact(e)); /* forces gc_tombstones */

    EXPECT_TRUE(has_entity(e, "live"));
    EXPECT_TRUE(has_entity(e, "recent")); /* fresh tombstone survives */
    EXPECT_FALSE(has_entity(e, "old"));   /* expired tombstone purged */
    sync_engine_destroy(e);

    /* Reopen: the purge persisted. */
    sync_engine *e2 = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e2, nullptr);
    EXPECT_TRUE(has_entity(e2, "live"));
    EXPECT_FALSE(has_entity(e2, "old"));
    sync_engine_destroy(e2);
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

/* ---- Capability persistence (security follow-up) ----------------------- */
TEST(Storage, CapabilityPersistence) {
    TempDir dir;
    std::string db = dir.file("caps.db");

    /* In-memory identities used to mint capabilities and author records. */
    sync_engine *owner = sync_engine_create(site_from(0x70).data());
    sync_engine *writer = sync_engine_create(site_from(0x71).data());
    sync_engine *stranger = sync_engine_create(site_from(0x72).data());
    uint8_t wpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(writer, wpk);

    auto apply_all = [](sync_engine *target, sync_engine *src) {
        sync_change *recs = nullptr; size_t n = 0;
        EXPECT_EQ(sync_engine_export(src, &recs, &n), SYNC_OK);
        int rc = SYNC_OK;
        for (size_t i = 0; i < n; i++) {
            int r = sync_engine_apply(target, &recs[i]);
            if (r != SYNC_OK) { rc = r; break; }
        }
        sync_changes_free(recs, n);
        return rc;
    };

    auto vseed = site_from(0x79);
    /* Durable engine V owns nsA and is granted a delegation to `writer`. */
    {
        sync_engine *v = sync_engine_open(db.c_str(), vseed.data());
        ASSERT_NE(v, nullptr);
        sync_capability *root = sync_capability_root(
            owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        sync_capability *deleg =
            sync_capability_delegate(owner, root, wpk, SYNC_ACCESS_WRITE, 0);
        ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
        ASSERT_EQ(sync_engine_grant(v, deleg), SYNC_OK);
        sync_capability_free(root);
        sync_capability_free(deleg);
        sync_engine_destroy(v); /* capabilities persisted */
    }

    /* Reopen: enforcement must still be active from the persisted caps. */
    sync_engine *v = sync_engine_open(db.c_str(), vseed.data());
    ASSERT_NE(v, nullptr);

    sync_engine_set(writer, B(std::string("nsA")), 3, B(std::string("x")), 1,
                    B(std::string("f")), 1, B(std::string("ok")), 2);
    EXPECT_EQ(apply_all(v, writer), SYNC_OK) << "authorized writer rejected after reopen";

    sync_engine_set(stranger, B(std::string("nsA")), 3, B(std::string("y")), 1,
                    B(std::string("f")), 1, B(std::string("no")), 2);
    EXPECT_EQ(apply_all(v, stranger), SYNC_ERR_UNAUTHORIZED)
        << "unauthorized writer accepted after reopen";

    sync_engine_destroy(v);
    sync_engine_destroy(owner);
    sync_engine_destroy(writer);
    sync_engine_destroy(stranger);
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

/* At-rest encryption: the log is sealed with a caller key; a wrong key (or a
 * mode mismatch) fails the open cleanly, and an encrypted log round-trips
 * (including across a compaction). */
TEST(Storage, AtRestEncryption) {
    TempDir dir;
    std::string db = dir.file("enc.db");
    auto site = site_from(0x0F);
    uint8_t key[32];  for (int i = 0; i < 32; i++) key[i] = (uint8_t)(i + 1);
    uint8_t wrong[32]; for (int i = 0; i < 32; i++) wrong[i] = (uint8_t)(i + 2);

    /* Write some data into an encrypted log, then close. */
    sync_engine *e = sync_engine_open_encrypted(db.c_str(), site.data(), key);
    ASSERT_NE(e, nullptr);
    cluster::put(e, "ns", "alice", "name", "Alice");
    cluster::put(e, "ns", "bob", "name", "Bob");
    Digest d0;
    ASSERT_EQ(sync_engine_digest(e, d0.data()), SYNC_OK);
    sync_engine_destroy(e);

    /* The raw file must not contain the plaintext value. */
    std::string raw = read_file(db);
    EXPECT_EQ(raw.find("Alice"), std::string::npos) << "value leaked in plaintext";
    EXPECT_EQ(raw.compare(0, 8, "KOMEENC1"), 0) << "missing encrypted magic";

    /* Wrong key: open must fail cleanly (and not truncate the file). */
    EXPECT_EQ(sync_engine_open_encrypted(db.c_str(), site.data(), wrong), nullptr);
    /* Opening an encrypted log as plaintext (no key) must also fail. */
    EXPECT_EQ(sync_engine_open(db.c_str(), site.data()), nullptr);
    EXPECT_EQ(read_file(db).size(), raw.size()) << "failed open mutated the file";

    /* Right key: reopens, decrypts, and matches. */
    sync_engine *e2 = sync_engine_open_encrypted(db.c_str(), site.data(), key);
    ASSERT_NE(e2, nullptr);
    Digest d1;
    ASSERT_EQ(sync_engine_digest(e2, d1.data()), SYNC_OK);
    EXPECT_EQ(d0, d1);
    EXPECT_EQ(cluster::get(e2, "ns", "alice", "name"), "Alice");

    /* Force a compaction and confirm the rewritten log stays encrypted + valid. */
    ASSERT_TRUE(e2->store->compact(e2));
    sync_engine_destroy(e2);
    EXPECT_EQ(read_file(db).compare(0, 8, "KOMEENC1"), 0) << "compaction lost encryption";

    sync_engine *e3 = sync_engine_open_encrypted(db.c_str(), site.data(), key);
    ASSERT_NE(e3, nullptr);
    Digest d2;
    ASSERT_EQ(sync_engine_digest(e3, d2.data()), SYNC_OK);
    EXPECT_EQ(d0, d2) << "compaction changed encrypted state";
    sync_engine_destroy(e3);
}

/* F2: every sealed frame must carry a fresh random 24-byte nonce. A zero/reused
 * nonce (what an unchecked random_bytes() failure would leave behind) is
 * catastrophic for XChaCha20-Poly1305. Parse the raw encrypted log
 * ([magic 8][keycheck 32] header, then [plen:4][nonce:24][ct:plen][mac:16]
 * frames) and assert all per-frame nonces are distinct and non-zero. */
TEST(Storage, EncryptedFramesUseDistinctNonces) {
    TempDir dir;
    std::string db = dir.file("enc_nonce.db");
    auto site = site_from(0x2F);
    uint8_t key[32]; for (int i = 0; i < 32; i++) key[i] = (uint8_t)(i * 3 + 1);

    sync_engine *e = sync_engine_open_encrypted(db.c_str(), site.data(), key);
    ASSERT_NE(e, nullptr);
    /* Several distinct mutations -> several sealed frames. */
    for (int i = 0; i < 8; i++)
        cluster::put(e, "ns", "e" + std::to_string(i), "f", "v" + std::to_string(i));
    sync_engine_destroy(e);

    std::string raw = read_file(db);
    ASSERT_EQ(raw.compare(0, 8, "KOMEENC1"), 0);
    const size_t header = 8 + 16 + 16; /* magic + key-check ct + mac */
    std::vector<std::string> nonces;
    size_t off = header;
    while (off + 4 <= raw.size()) {
        uint32_t plen = (uint8_t)raw[off] | ((uint8_t)raw[off + 1] << 8) |
                        ((uint8_t)raw[off + 2] << 16) |
                        ((uint32_t)(uint8_t)raw[off + 3] << 24);
        if (plen == 0) break;
        size_t frame = 4 + 24 + (size_t)plen + 16;
        if (off + frame > raw.size()) break;
        std::string nonce = raw.substr(off + 4, 24);
        EXPECT_NE(nonce, std::string(24, '\0')) << "zero nonce on disk";
        nonces.push_back(nonce);
        off += frame;
    }
    ASSERT_GE(nonces.size(), 3u) << "expected several sealed frames";
    std::set<std::string> uniq(nonces.begin(), nonces.end());
    EXPECT_EQ(uniq.size(), nonces.size()) << "nonce reuse across frames";
}
