/* storage_test.cpp — M2 durable storage acceptance tests (T2.1-T2.7).
 *
 * Verifies that on-disk replicas behave identically to in-memory ones: reopen
 * identity, convergence with persistence, crash atomicity, schema guarding,
 * single-file storage, scale, and that the M1 oracle still holds. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <sys/resource.h> /* RLIMIT_FSIZE: forced mid-frame write failure */
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <array>
#include <csignal> /* SIGXFSZ must be ignored for EFBIG partial writes */
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <dirent.h>
#include <random>
#include <set>
#include <string>
#include <thread> /* hardware_concurrency: prove the threaded verify branch */
#include <vector>

#include "byteorder.h" /* T2.4 tampers with the log file directly */
#include "cluster.hpp"
#include "codec.h"   /* change_from_* / element_hash / DecodedChange (Phase 2) */
#include "engine.hpp" /* white-box: cached per-cell element hashes (Phase 2) */
#include "log_frames.hpp" /* frame walker + fsync counter (Phase 3, §3.3) */
#include "sha256.h"
#include "storage.h" /* kSchemaVersion; ke::merge_record (Phase 2) */
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

/* ---- Open is read-only ------------------------------------------------- *
 * Opening a database must never modify the file. load() used to ftruncate a
 * torn tail at open, which made every open destructive: a concurrent
 * read-only consumer (a status tool, `komed --identity`, a test poller) could
 * chop a frame the owning process had just committed — the owner's in-memory
 * state kept the change and never re-appended it, silently losing the record
 * from disk (the komed_test nightly flake). The truncation is now deferred to
 * the writer's first append. */
TEST(Storage, OpenLeavesFileUntouched) {
    TempDir dir;
    std::string db = dir.file("readonly.db");
    auto site = site_from(0x21);

    sync_engine *w = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(w, nullptr);
    sync_engine_set(w, B(std::string("n")), 1, B(std::string("e1")), 2,
                    B(std::string("f")), 1, B(std::string("v1")), 2);
    Digest before = digest(w);
    sync_engine_destroy(w);

    /* Simulate a torn trailing write — or, equivalently, an append caught
     * mid-flight by an open racing the owner. */
    const std::string garbage = "TORN-TAIL-GARBAGE";
    std::string torn = read_file(db) + garbage;
    write_file(db, torn);

    /* A read-only open sees the good frames and leaves the file untouched. */
    sync_engine *r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);
    EXPECT_EQ(digest(r), before);
    sync_engine_destroy(r);
    EXPECT_EQ(read_file(db), torn) << "open() modified the database file";

    /* A writer still cleans the torn tail before its first append, so the
     * log replays to exactly the new state afterwards. */
    w = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(w, nullptr);
    sync_engine_set(w, B(std::string("n")), 1, B(std::string("e2")), 2,
                    B(std::string("f")), 1, B(std::string("v2")), 2);
    Digest after = digest(w);
    sync_engine_destroy(w);
    EXPECT_EQ(read_file(db).find(garbage), std::string::npos)
        << "torn tail survived the first append";
    r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);
    EXPECT_EQ(digest(r), after);
    sync_engine_destroy(r);
}

/* The end-to-end shape of the same bug: a reader open/close loop racing a
 * live writer must not lose any of the writer's fsync'd frames. */
TEST(Storage, ConcurrentOpenDoesNotLoseWrites) {
    TempDir dir;
    std::string db = dir.file("shared.db");
    auto site = site_from(0x22);

    /* Seed so the reader never races the header write of a fresh file. */
    sync_engine *w = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(w, nullptr);
    sync_engine_set(w, B(std::string("n")), 1, B(std::string("seed")), 4,
                    B(std::string("f")), 1, B(std::string("v")), 1);
    sync_engine_destroy(w);

    pid_t pid = fork();
    ASSERT_GE(pid, 0);
    if (pid == 0) {
        /* Child: open/close the db in a tight loop, never writing — the way a
         * monitoring tool would. Killed by the parent when it's done. */
        alarm(30); /* backstop so an orphan can't loop forever */
        for (;;) {
            sync_engine *r = sync_engine_open(db.c_str(), site.data());
            if (r) sync_engine_destroy(r);
        }
        _exit(0); /* unreachable */
    }

    w = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(w, nullptr);
    const int kWrites = 400;
    for (int i = 0; i < kWrites; i++) {
        std::string ent = "k" + std::to_string(i);
        ASSERT_EQ(sync_engine_set(w, B(std::string("n")), 1, B(ent), ent.size(),
                                  B(std::string("f")), 1, B(ent), ent.size()),
                  SYNC_OK);
    }
    sync_engine_destroy(w);
    kill(pid, SIGKILL);
    int status = 0;
    waitpid(pid, &status, 0);

    /* Every fsync'd write must still be on disk. */
    sync_engine *r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);
    int missing = 0;
    for (int i = 0; i < kWrites; i++) {
        std::string ent = "k" + std::to_string(i);
        int ex = 0;
        sync_engine_exists(r, B(std::string("n")), 1, B(ent), ent.size(), &ex);
        if (!ex) missing++;
    }
    EXPECT_EQ(missing, 0) << "concurrent read-only opens lost committed frames";
    sync_engine_destroy(r);
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

    ASSERT_EQ(sync_engine_compact(e), SYNC_OK); /* forces gc_tombstones */

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

    /* Force a compaction (through the public ABI) and confirm the rewritten
     * log stays encrypted + valid. */
    ASSERT_EQ(sync_engine_compact(e2), SYNC_OK);
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

/* ---- Erasure + compaction: superseded bytes leave the disk -------------- */

/* sync_engine_compact via the public ABI on a plaintext log: same rewrite the
 * engine's size trigger runs, callable on demand. In-memory engines have no
 * log to rewrite and must refuse cleanly. */
TEST(Storage, CompactAbiShrinksPlaintextLog) {
    TempDir dir;
    std::string db = dir.file("compact_abi.db");
    auto site = site_from(0x30);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    /* Enough overwrites of one cell to bloat the log, few enough to stay
     * under the 64 KiB auto-compaction floor — so the shrink observed below
     * is attributable to this call alone. */
    for (int i = 0; i < 150; i++)
        cluster::put(e, "ns", "k", "f", "v" + std::to_string(i));
    size_t before = read_file(db).size();
    ASSERT_LT(before, 65536u) << "auto-compaction already ran; shrink ambiguous";
    Digest d0;
    ASSERT_EQ(sync_engine_digest(e, d0.data()), SYNC_OK);

    ASSERT_EQ(sync_engine_compact(e), SYNC_OK);
    size_t after = read_file(db).size();
    EXPECT_LT(after, before) << "compaction did not shrink the log";
    sync_engine_destroy(e);

    /* State preserved across the rewrite + reopen. */
    sync_engine *r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);
    Digest d1;
    ASSERT_EQ(sync_engine_digest(r, d1.data()), SYNC_OK);
    EXPECT_EQ(d0, d1);
    EXPECT_EQ(cluster::get(r, "ns", "k", "f"), "v149");
    sync_engine_destroy(r);

    /* No log to rewrite: NULL and in-memory engines refuse cleanly. */
    EXPECT_EQ(sync_engine_compact(nullptr), SYNC_ERR_INVALID);
    sync_engine *mem = sync_engine_create(site_from(0x31).data());
    ASSERT_NE(mem, nullptr);
    EXPECT_EQ(sync_engine_compact(mem), SYNC_ERR_INVALID);
    sync_engine_destroy(mem);
}

/* The proof that matters for ephemeral media: after sync_blob_erase +
 * sync_engine_compact, the ENCRYPTED log file is smaller than it was while it
 * held the payload — the erased bytes physically left the disk, not just the
 * read surface. (Circles verified this shape on-device: kome_enc.db shrank
 * 34368 -> 27512 bytes across an expiry sweep.) */
TEST(Storage, BlobEraseThenCompactShrinksEncryptedLog) {
    TempDir dir;
    std::string db = dir.file("erase_enc.db");
    auto site = site_from(0x32);
    uint8_t key[32];
    for (int i = 0; i < 32; i++) key[i] = (uint8_t)(i * 7 + 3);

    sync_engine *e = sync_engine_open_encrypted(db.c_str(), site.data(), key);
    ASSERT_NE(e, nullptr);

    /* ~100 KiB of pseudo-random "media" (4 chunks). */
    std::vector<uint8_t> data(100 * 1024);
    uint32_t x = 0xC0FFEE;
    for (auto &b : data) {
        x ^= x << 13; x ^= x >> 17; x ^= x << 5;
        b = (uint8_t)x;
    }
    uint8_t id[SYNC_BLOB_ID_LEN];
    ASSERT_EQ(sync_blob_put(e, B(std::string("ph")), 2, data.data(),
                            data.size(), id),
              SYNC_OK);
    size_t pre_erase = read_file(db).size();
    ASSERT_GT(pre_erase, data.size()) << "log must hold the payload";

    ASSERT_EQ(sync_blob_erase(e, B(std::string("ph")), 2, id), SYNC_OK);
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK);

    size_t post = read_file(db).size();
    EXPECT_LT(post, pre_erase) << "erased payload still on disk";
    /* Stronger: what remains (tombstoned entities with EMPTY payload
     * registers + manifest metadata) is far smaller than the payload was. */
    EXPECT_LT(post, data.size()) << "payload-sized residue after erase+compact";

    Digest d0;
    ASSERT_EQ(sync_engine_digest(e, d0.data()), SYNC_OK);
    sync_engine_destroy(e);

    /* Still a valid encrypted log; state survives reopen; blob stays gone. */
    std::string raw = read_file(db);
    EXPECT_EQ(raw.compare(0, 8, "KOMEENC1"), 0) << "compaction lost encryption";
    sync_engine *r = sync_engine_open_encrypted(db.c_str(), site.data(), key);
    ASSERT_NE(r, nullptr);
    Digest d1;
    ASSERT_EQ(sync_engine_digest(r, d1.data()), SYNC_OK);
    EXPECT_EQ(d0, d1);
    uint8_t *out = nullptr;
    size_t out_len = 0;
    EXPECT_EQ(sync_blob_get(r, B(std::string("ph")), 2, id, &out, &out_len),
              SYNC_ERR_NOTFOUND);
    sync_engine_destroy(r);
}

/* ---- Phase 4 (§3.4): streamed compaction -------------------------------- *
 * Gate tests for rewrite_log_streamed / compacted_image_size: structural
 * determinism of the compacted image (amendment 5), the cap/rev-bearing
 * compaction path (amendment 4), the deferred open-time heuristic (fire and
 * skip — the skip with a derived threshold, amendment 9), and stale-.tmp
 * hygiene around the rename commit point. All raw-file structure goes through
 * the shared frame walker (tests/log_frames.hpp). */

namespace {

/* On-disk entry-type tags — the log-format contract documented at the top of
 * storage.cpp (entry = type:u8 payload; META=1 ENTITY=2 FIELD=3 CAP=4 REV=5).
 * This suite parses raw formats by hand (see recompute_frames above), so the
 * tags are restated here rather than exported from the anonymous namespace. */
constexpr uint8_t kEntryMeta = 1, kEntryEntity = 2, kEntryCap = 4,
                  kEntryRev = 5;

/* Type byte of a PLAINTEXT frame's first entry (0 if empty/short). */
uint8_t frame_first_type(const std::string &raw, const synctest::LogFrame &f) {
    if (f.body_len < 5 || f.body_offset + 5 > raw.size()) return 0;
    return (uint8_t)raw[f.body_offset + 4]; /* skip the u32le entry count */
}

/* (ns, entity) of a PLAINTEXT entity frame's FIRST entry, read from the entry
 * encoding storage.cpp writes: type:u8, varint(ns_len) ns, varint(ent_len)
 * ent, ... — exactly enough to extract the frame's entity key. */
bool frame_first_entity_key(const std::string &raw, const synctest::LogFrame &f,
                            std::string &ns, std::string &ent) {
    if (f.body_offset + f.body_len > raw.size() || f.body_len < 5) return false;
    const uint8_t *p = (const uint8_t *)raw.data() + f.body_offset + 4;
    const uint8_t *end =
        (const uint8_t *)raw.data() + f.body_offset + f.body_len;
    if (p >= end || *p != kEntryEntity) return false;
    p++;
    uint64_t n = 0;
    if (!ke::get_varint(p, end, n) || (uint64_t)(end - p) < n) return false;
    ns.assign((const char *)p, (size_t)n);
    p += n;
    if (!ke::get_varint(p, end, n) || (uint64_t)(end - p) < n) return false;
    ent.assign((const char *)p, (size_t)n);
    return true;
}

} // namespace

/* §3.4 amendment 5 — the determinism gate is STRUCTURAL, not self-comparison:
 * after compacting an engine holding several entities (scrambled insertion
 * order, a tombstone, a multi-byte-varint entity name) plus granted
 * capabilities and a revocation, the compacted file must be exactly
 *   [meta frame][one frame per entity, byte-lex (ns, entity)][cap][rev]
 * with each entity frame's entry count == 1 existence entry + its field
 * registers. The frame walker + first-entry decode pin every one of those
 * properties against the real on-disk bytes. Compact-twice byte-equality is
 * kept only as a SECONDARY check — see the comment at the bottom. */
TEST(Storage, CompactionIsDeterministicByteForByte) {
    TempDir dir;
    std::string db = dir.file("det.db");
    auto site = site_from(0x81);

    /* Identities for the delegation / revocation subjects. */
    sync_engine *writer = sync_engine_create(site_from(0x82).data());
    sync_engine *third = sync_engine_create(site_from(0x83).data());
    ASSERT_NE(writer, nullptr);
    ASSERT_NE(third, nullptr);
    uint8_t wpk[SYNC_PUBKEY_LEN], tpk[SYNC_PUBKEY_LEN];
    ASSERT_EQ(sync_engine_identity(writer, wpk), SYNC_OK);
    ASSERT_EQ(sync_engine_identity(third, tpk), SYNC_OK);

    sync_engine *v = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(v, nullptr);

    /* 150-char entity name: its length prefix needs a 2-byte varint, so the
     * first-entry decode below exercises the multi-byte varint path too. */
    const std::string long_ent = "e" + std::string(149, 'x');

    /* Insertion order deliberately scrambled versus byte-lex output order,
     * and "b10"/"b2" chosen so byte-lex ("b10" < "b2") is distinguishable
     * from numeric or length order. "beta"/"z" becomes a FRESH tombstone:
     * present=false with its (hidden) field register still serialized. */
    cluster::put(v, "beta", "z", "f1", "vz");
    cluster::del(v, "beta", "z");
    cluster::put(v, "alpha0", "a", "f1", "va1");
    cluster::put(v, "alpha0", "a", "f2", "va2");
    cluster::put(v, "alpha", "b2", "f1", "vb2");
    cluster::put(v, "alpha", long_ent, "f1", "vlong");
    cluster::put(v, "alpha", "b10", "f1", "v1");
    cluster::put(v, "alpha", "b10", "f2", "v2");
    cluster::put(v, "alpha", "b10", "f3", "v3");

    /* Capabilities + a revocation, on a namespace unrelated to the entity
     * writes (so enforcement never interferes with the puts above): the
     * durable engine mints its own root — making it the owner, so it may
     * revoke — plus one delegation; then revokes an uninvolved third key. */
    sync_capability *root =
        sync_capability_root(v, "zeta", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    sync_capability *deleg =
        sync_capability_delegate(v, root, wpk, SYNC_ACCESS_WRITE, 0);
    ASSERT_NE(deleg, nullptr);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(v, deleg), SYNC_OK);
    sync_capability_free(root);
    sync_capability_free(deleg);
    ASSERT_EQ(sync_engine_revoke(v, "zeta", tpk), SYNC_OK);

    /* Under the 64 KiB auto-compaction floor: the structure verified below is
     * attributable to the explicit compact alone. */
    ASSERT_LT(read_file(db).size(), 65536u);
    Digest d0 = digest(v);

    ASSERT_EQ(sync_engine_compact(v), SYNC_OK);
    EXPECT_EQ(digest(v), d0) << "digest changed across compaction";

    std::string raw = read_file(db);
    synctest::LogWalk w = synctest::walk_frames(raw);
    ASSERT_TRUE(w.ok);
    EXPECT_FALSE(w.encrypted);
    EXPECT_EQ(w.trailing, 0u) << "compacted image has a torn/garbage tail";

    /* Expected entity frames, in byte-lexicographic (ns, entity) order, each
     * with entry count == 1 (existence) + field-register count. */
    struct EntFrame {
        std::string ns, ent;
        uint32_t entries;
    };
    const EntFrame expect[] = {
        {"alpha", "b10", 4},    /* 3 fields */
        {"alpha", "b2", 2},     /* 1 field; "b10" < "b2" in byte-lex */
        {"alpha", long_ent, 2}, /* 1 field; 2-byte varint name */
        {"alpha0", "a", 3},     /* 2 fields; ns "alpha" < "alpha0" < "beta" */
        {"beta", "z", 2},       /* tombstone + its 1 hidden field register */
    };
    const size_t n_ent = sizeof expect / sizeof expect[0];

    /* Exactly 1 meta + n_ent entity + 1 cap + 1 rev frames. */
    ASSERT_EQ(w.frames.size(), 1u + n_ent + 1u + 1u)
        << "compacted image is not [meta][entities...][cap][rev]";

    /* [0]: the meta frame — schema_version, seed, hlc_physical, hlc_logical,
     * db_clock — and no OTHER frame may be a meta frame (exactly one). */
    EXPECT_EQ(frame_first_type(raw, w.frames[0]), kEntryMeta);
    EXPECT_EQ(synctest::frame_entry_count(raw, w.frames[0]), 5u)
        << "meta frame must hold exactly the 5 meta entries";
    for (size_t i = 1; i < w.frames.size(); i++)
        EXPECT_NE(frame_first_type(raw, w.frames[i]), kEntryMeta)
            << "second meta frame at index " << i;

    /* [1..n_ent]: entity frames in byte-lex (ns, entity) order with exact
     * entry counts. */
    for (size_t i = 0; i < n_ent; i++) {
        const synctest::LogFrame &f = w.frames[1 + i];
        EXPECT_EQ(frame_first_type(raw, f), kEntryEntity)
            << "frame " << (1 + i) << " is not an entity frame";
        std::string fns, fent;
        ASSERT_TRUE(frame_first_entity_key(raw, f, fns, fent))
            << "frame " << (1 + i) << ": undecodable first entity entry";
        EXPECT_EQ(fns, expect[i].ns) << "entity frame " << i << " out of order";
        EXPECT_EQ(fent, expect[i].ent)
            << "entity frame " << i << " out of order (byte-lex (ns, entity))";
        EXPECT_EQ(synctest::frame_entry_count(raw, f), expect[i].entries)
            << "frame for (" << expect[i].ns << ", " << expect[i].ent
            << "): entry count != 1 + field count";
    }

    /* [n_ent+1]: the cap frame (root + delegation), then [n_ent+2]: the rev
     * frame (one revocation), closing the file. */
    EXPECT_EQ(frame_first_type(raw, w.frames[1 + n_ent]), kEntryCap);
    EXPECT_EQ(synctest::frame_entry_count(raw, w.frames[1 + n_ent]), 2u)
        << "cap frame must hold the root + the delegation";
    EXPECT_EQ(frame_first_type(raw, w.frames[2 + n_ent]), kEntryRev);
    EXPECT_EQ(synctest::frame_entry_count(raw, w.frames[2 + n_ent]), 1u)
        << "rev frame must hold the one revocation";

    /* SECONDARY check only: compacting again reproduces the bytes. Weak on
     * its own — a writer that consistently dropped the cap frame or reordered
     * fields would emit the same wrong bytes both times and self-compare
     * clean — which is why the structural walk above is the primary gate
     * (§3.4 amendment 5). */
    ASSERT_EQ(sync_engine_compact(v), SYNC_OK);
    EXPECT_EQ(read_file(db), raw) << "recompacting an unchanged engine "
                                     "produced different bytes";

    sync_engine_destroy(v);
    sync_engine_destroy(writer);
    sync_engine_destroy(third);
}

/* §3.4 amendment 4 — the cap/rev branch of compacted_image_size, previously
 * unexercised by any compaction test, on the ENCRYPTED path (the plaintext
 * cap/rev structure is pinned byte-level by the structural test above): an
 * engine holding granted capabilities AND an ingested revocation compacts via
 * the public ABI — in Debug builds this runs the live
 * assert(sink.total == compacted_image_size(e)) over the cap/rev arithmetic —
 * and a reopen from the compacted image alone still enforces writes
 * (delegated writer accepted, stranger rejected, revoked key still revoked:
 * the CapabilityPersistence pattern). */
TEST(Storage, CapRevCompactionPersistsEnforcement) {
    TempDir dir;
    std::string db = dir.file("caprev.db");
    auto vseed = site_from(0x84);
    uint8_t key[32];
    for (int i = 0; i < 32; i++) key[i] = (uint8_t)(i * 5 + 7);

    sync_engine *writer = sync_engine_create(site_from(0x85).data());
    sync_engine *stranger = sync_engine_create(site_from(0x86).data());
    sync_engine *stolen = sync_engine_create(site_from(0x87).data());
    ASSERT_NE(writer, nullptr);
    ASSERT_NE(stranger, nullptr);
    ASSERT_NE(stolen, nullptr);
    uint8_t wpk[SYNC_PUBKEY_LEN], spk[SYNC_PUBKEY_LEN];
    ASSERT_EQ(sync_engine_identity(writer, wpk), SYNC_OK);
    ASSERT_EQ(sync_engine_identity(stolen, spk), SYNC_OK);

    auto apply_all = [](sync_engine *target, sync_engine *src) {
        sync_change *recs = nullptr;
        size_t n = 0;
        EXPECT_EQ(sync_engine_export(src, &recs, &n), SYNC_OK);
        int rc = SYNC_OK;
        for (size_t i = 0; i < n; i++) {
            int r = sync_engine_apply(target, &recs[i]);
            if (r != SYNC_OK) { rc = r; break; }
        }
        sync_changes_free(recs, n);
        return rc;
    };

    sync_engine *v = sync_engine_open_encrypted(db.c_str(), vseed.data(), key);
    ASSERT_NE(v, nullptr);

    /* v mints its own root (so it owns nsA and may revoke), delegates WRITE
     * to `writer`, and revokes a "stolen device" key. */
    sync_capability *root =
        sync_capability_root(v, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    sync_capability *deleg =
        sync_capability_delegate(v, root, wpk, SYNC_ACCESS_WRITE, 0);
    ASSERT_NE(deleg, nullptr);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(v, deleg), SYNC_OK);
    sync_capability_free(root);
    sync_capability_free(deleg);
    ASSERT_EQ(sync_engine_revoke(v, "nsA", spk), SYNC_OK);

    /* Entities under the enforced namespace: two authored by the owner and
     * one by the delegated writer (accepted pre-compact). */
    cluster::put(v, "nsA", "own1", "f", "v1");
    cluster::put(v, "nsA", "own2", "f", "v2");
    sync_engine_set(writer, B(std::string("nsA")), 3, B(std::string("w1")), 2,
                    B(std::string("f")), 1, B(std::string("wv")), 2);
    ASSERT_EQ(apply_all(v, writer), SYNC_OK)
        << "delegated writer rejected before compaction";

    Digest d0 = digest(v);
    ASSERT_EQ(sync_engine_compact(v), SYNC_OK);
    EXPECT_EQ(digest(v), d0) << "digest changed across compaction";

    /* Structural anchor (the encrypted walk is length-driven): the compacted
     * image must be 1 meta + 3 entity frames + 1 cap frame + 1 rev frame —
     * the cap/rev frames really were emitted (and, in Debug, their
     * compacted_image_size arithmetic held exactly). */
    std::string raw1 = read_file(db);
    synctest::LogWalk w1 = synctest::walk_frames(raw1);
    ASSERT_TRUE(w1.ok);
    EXPECT_TRUE(w1.encrypted);
    EXPECT_EQ(w1.trailing, 0u);
    EXPECT_EQ(w1.frames.size(), 1u + 3u + 1u + 1u)
        << "cap/rev frames missing from the encrypted compacted image";

    /* One more compaction, instrumented: exactly the 2 counted fsyncs (temp
     * file + directory — the Phase-3 counter contract rewrite_log_streamed
     * inherits from atomic_replace), and an idempotent file size (fresh
     * nonces change the bytes, never the arithmetic size). */
    synctest::fsync_reset();
    ASSERT_EQ(sync_engine_compact(v), SYNC_OK);
    EXPECT_EQ(synctest::fsync_count(), 2u)
        << "one compaction must cost exactly the temp-file + directory fsyncs";
    EXPECT_EQ(read_file(db).size(), raw1.size())
        << "recompacting an unchanged engine changed the image size";
    sync_engine_destroy(v);

    /* Reopen from the compacted image alone: enforcement is intact. */
    v = sync_engine_open_encrypted(db.c_str(), vseed.data(), key);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(digest(v), d0);
    int revoked = 0;
    EXPECT_EQ(sync_engine_is_revoked(v, "nsA", spk, &revoked), SYNC_OK);
    EXPECT_EQ(revoked, 1) << "revocation lost across compact+reopen";

    sync_engine_set(writer, B(std::string("nsA")), 3, B(std::string("w2")), 2,
                    B(std::string("f")), 1, B(std::string("wv2")), 3);
    EXPECT_EQ(apply_all(v, writer), SYNC_OK)
        << "authorized writer rejected after compact+reopen";
    sync_engine_set(stranger, B(std::string("nsA")), 3, B(std::string("s1")), 2,
                    B(std::string("f")), 1, B(std::string("sv")), 2);
    EXPECT_EQ(apply_all(v, stranger), SYNC_ERR_UNAUTHORIZED)
        << "unauthorized writer accepted after compact+reopen";

    /* And the load -> compact round trip once more, from replayed caps. */
    Digest d1 = digest(v);
    ASSERT_EQ(sync_engine_compact(v), SYNC_OK);
    EXPECT_EQ(digest(v), d1);
    sync_engine_destroy(v);
    v = sync_engine_open_encrypted(db.c_str(), vseed.data(), key);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(digest(v), d1);

    sync_engine_destroy(v);
    sync_engine_destroy(writer);
    sync_engine_destroy(stranger);
    sync_engine_destroy(stolen);
}

/* The deferred open-time compaction: a log left bloated at close (live image
 * far under half the file) is rewritten by the FIRST MUTATION after reopen —
 * never by the open itself — through rewrite_log_streamed, shrinking the file
 * to exactly the compacted image with the digest preserved.
 *
 * Construction (deterministic, write-path only): a 200 KiB value trips the
 * in-session auto-compaction (64 KiB floor), ratcheting compacted_size_ to
 * ~200 KiB; overwriting it with a tiny value then collapses the LIVE image to
 * ~1 KiB while the file keeps the dead 200 KiB frame (the next in-session
 * trigger would be 2 x 200 KiB — never reached). Non-vacuity: after reopen
 * the normal threshold re-anchors at 2 x the bloated file size, so the shrink
 * observed below is attributable ONLY to the open_compact_pending_ branch. */
TEST(Storage, OpenCompactHeuristicFires) {
    TempDir dir;
    std::string db = dir.file("heur_fire.db");
    auto site = site_from(0x88);

    /* Session 1: manufacture the bloated-but-idle log. */
    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    const std::string big(200u * 1024u, 'x');
    cluster::put(e, "ns", "pad", "f", big); /* auto-compacts; ratchets 2x bar */
    cluster::put(e, "ns", "pad", "f", "tiny"); /* live image -> ~1 KiB */
    Digest d0 = digest(e);
    sync_engine_destroy(e);

    const size_t bloated = read_file(db).size();
    ASSERT_GT(bloated, 65536u)
        << "construction failed: file too small to arm the open-time check";
    ASSERT_GT(bloated, 150u * 1024u)
        << "construction failed: the dead 200 KiB frame is not on disk";

    /* Session 2: open must not write (read-only consumers must never rewrite
     * the file out from under a live owner) — the rewrite is deferred. */
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(read_file(db).size(), bloated) << "open itself mutated the file";
    EXPECT_EQ(digest(e), d0);

    /* The first mutation fires the deferred streamed rewrite. */
    cluster::put(e, "ns2", "t", "f", "v");
    std::string raw = read_file(db);
    EXPECT_LT(raw.size(), 65536u) << "open-time compaction did not fire";
    EXPECT_LT(raw.size() * 10, bloated)
        << "file did not shrink to anywhere near the live image";

    /* Not just smaller — exactly the compacted image: 1 meta frame + the two
     * live entities ("ns","pad") and ("ns2","t"), nothing else, no tail. */
    synctest::LogWalk w = synctest::walk_frames(raw);
    ASSERT_TRUE(w.ok);
    EXPECT_EQ(w.trailing, 0u);
    EXPECT_EQ(w.frames.size(), 3u)
        << "post-rewrite file is not the pure compacted image";

    /* Digest stable across the rewrite: reopen reproduces the exact state. */
    Digest d1 = digest(e);
    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(digest(e), d1) << "open-time rewrite lost state";
    EXPECT_EQ(cluster::get(e, "ns", "pad", "f"), "tiny");
    EXPECT_EQ(cluster::get(e, "ns2", "t", "f"), "v");
    sync_engine_destroy(e);
}

/* §3.4 amendment 9 — the skip side of the open-time heuristic, with a DERIVED
 * threshold: the healthy log's observed size must lie strictly between the
 * 64 KiB arming floor and 2 x a sibling engine's post-compaction size for the
 * SAME state (the sibling is a byte copy of the log, compacted). If a later
 * change to the meta set, value sizes, or per-frame overhead drifts the
 * geometry out of that band, these guards fail LOUDLY — instead of the test
 * silently inverting into "the heuristic fired and nothing noticed" (the
 * hand-tuned-ratio trap the respecification removes). */
TEST(Storage, OpenCompactHeuristicSkipsHealthyLog) {
    TempDir dir;
    std::string db = dir.file("healthy.db");
    std::string sib = dir.file("healthy_sib.db");
    auto site = site_from(0x89);

    /* ~150 KiB of DISTINCT live entities, compacted to exactly the live
     * image, plus a small same-length overwrite history: a healthy log
     * (image/file ratio well inside (0.5, 1)). */
    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    const int N = 150;
    const std::string val(700, 'v');
    for (int i = 0; i < N; i++)
        cluster::put(e, "ns", "ent" + std::to_string(i), "f", val);
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK);
    for (int i = 0; i < 20; i++)
        cluster::put(e, "ns", "ent" + std::to_string(i), "f", val);
    Digest d0 = digest(e);
    sync_engine_destroy(e);

    const std::string before = read_file(db);

    /* Sibling: the same bytes, compacted — its size IS this state's
     * post-compaction size, from which the healthy band is derived. */
    write_file(sib, before);
    sync_engine *s = sync_engine_open(sib.c_str(), site.data());
    ASSERT_NE(s, nullptr);
    ASSERT_EQ(digest(s), d0) << "sibling copy diverged from the original";
    ASSERT_EQ(sync_engine_compact(s), SYNC_OK);
    sync_engine_destroy(s);
    const size_t compacted = read_file(sib).size();

    /* THE DERIVED-THRESHOLD GUARDS: fail loudly, never invert silently. */
    ASSERT_GT(before.size(), 65536u)
        << "log below the arming floor: the open-time check never runs and "
           "the skip assertion below would be vacuous";
    ASSERT_LT(before.size(), 2u * compacted)
        << "log is not healthy (>= 2x its compacted image): the heuristic "
           "SHOULD fire here, so this test would be checking the wrong branch";
    ASSERT_GT(before.size(), compacted)
        << "log has no append history: skip would be trivial";

    /* Reopen + mutate: the armed heuristic must SKIP — the file may change
     * only by the one appended frame (the old bytes stay a byte-prefix). */
    sync_engine *r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);
    EXPECT_EQ(read_file(db).size(), before.size()) << "open mutated the file";
    EXPECT_EQ(digest(r), d0);
    cluster::put(r, "ns", "fresh", "f", "v");
    const std::string after = read_file(db);
    ASSERT_GT(after.size(), before.size()) << "mutation appended nothing";
    EXPECT_EQ(after.compare(0, before.size(), before), 0)
        << "file was rewritten: the open-time heuristic fired on a HEALTHY log";
    synctest::LogWalk wb = synctest::walk_frames(before);
    synctest::LogWalk wa = synctest::walk_frames(after);
    ASSERT_TRUE(wa.ok);
    EXPECT_EQ(wa.trailing, 0u);
    EXPECT_EQ(wa.frames.size(), wb.frames.size() + 1)
        << "expected exactly the one appended frame";
    sync_engine_destroy(r);
}

/* A stale `<path>.tmp` (the orphan a crash mid-compaction leaves behind) is
 * IGNORED by open — even when it is a valid log holding different state, the
 * adversarial confusion case — and replaced by the next compaction's O_TRUNC
 * + rename, leaving no stray files (the SingleFile pattern for the allowed
 * set). */
TEST(Storage, StaleTmpIgnoredAtOpenReplacedAtCompact) {
    TempDir dir;
    TempDir decoy_dir;
    std::string db = dir.file("stale.db");
    std::string tmp = db + ".tmp";
    auto site = site_from(0x8A);

    /* The real state. */
    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    for (int i = 0; i < 5; i++)
        cluster::put(e, "ns", "e" + std::to_string(i), "f",
                     "v" + std::to_string(i));
    Digest d0 = digest(e);
    sync_engine_destroy(e);

    /* Plant the stale tmp: a VALID plaintext log with DIFFERENT,
     * distinguishable state, plus a garbage tail (a plausible torn artifact
     * of a crashed previous compaction). If open consulted it, the digest
     * and the impostor lookup below would give it away. */
    std::string decoy_db = decoy_dir.file("decoy.db");
    sync_engine *decoy = sync_engine_open(decoy_db.c_str(),
                                          site_from(0x8B).data());
    ASSERT_NE(decoy, nullptr);
    cluster::put(decoy, "ns", "impostor", "f", "not-yours");
    Digest d_decoy = digest(decoy);
    sync_engine_destroy(decoy);
    ASSERT_NE(d_decoy, d0);
    const std::string planted = read_file(decoy_db) + std::string(1024, '\xa5');
    write_file(tmp, planted);
    ASSERT_EQ(read_file(tmp), planted); /* the stale tmp is really in place */

    /* Open reads ONLY <path>: state intact, tmp neither consulted, mutated,
     * nor removed. */
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(digest(e), d0) << "open consulted the stale .tmp";
    EXPECT_EQ(cluster::get(e, "ns", "impostor", "f"), "<none>")
        << "decoy state leaked out of the stale .tmp";
    EXPECT_EQ(read_file(tmp), planted) << "open mutated/removed the stale .tmp";

    /* The next compaction truncates + replaces it: the rename consumes the
     * path, so no .tmp survives a successful compact. */
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK);
    EXPECT_EQ(digest(e), d0);
    struct stat st;
    EXPECT_NE(::stat(tmp.c_str(), &st), 0)
        << "stale .tmp still present after a successful compaction";

    /* No stray files next to the log (SingleFile's allowed-set pattern). */
    std::set<std::string> allowed = {"stale.db"};
    DIR *d = opendir(dir.path.c_str());
    ASSERT_NE(d, nullptr);
    struct dirent *ent;
    while ((ent = readdir(d))) {
        std::string n = ent->d_name;
        if (n == "." || n == "..") continue;
        EXPECT_TRUE(allowed.count(n) > 0) << "unexpected file: " << n;
    }
    closedir(d);

    /* And the replacement log is intact and reopenable. */
    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(digest(e), d0);
    EXPECT_EQ(cluster::get(e, "ns", "e3", "f"), "v3");
    sync_engine_destroy(e);
}

/* F2 on the STREAMED path: every frame the compaction writes must carry its
 * own fresh, non-zero nonce. EncryptedFramesUseDistinctNonces pins this for
 * the append path only — it walks a log built purely by write_frame and never
 * compacts — so the whole-file rewrite, which seals more frames in one call
 * than any other code path, had no nonce coverage at all. A seal_frame that
 * reused or zeroed a nonce here would be catastrophic for XChaCha20-Poly1305
 * and invisible to every other encrypted test (they only assert the log still
 * decrypts, which a reused nonce does). */
TEST(Storage, CompactedEncryptedFramesUseDistinctNonces) {
    TempDir dir;
    std::string db = dir.file("compact_nonce.db");
    auto site = site_from(0x3C);
    uint8_t key[32];
    for (int i = 0; i < 32; i++) key[i] = (uint8_t)(i * 5 + 9);

    sync_engine *e = sync_engine_open_encrypted(db.c_str(), site.data(), key);
    ASSERT_NE(e, nullptr);
    /* Several entities and a capability + revocation, so the rewrite seals a
     * meta frame, many entity frames, and the cap/rev frames — every frame
     * kind the streamed writer emits. */
    for (int i = 0; i < 12; i++)
        cluster::put(e, "ns", "e" + std::to_string(i), "f",
                     "v" + std::to_string(i));
    sync_capability *root =
        sync_capability_root(e, "ns", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_EQ(sync_engine_grant(e, root), SYNC_OK);
    uint8_t sub[SYNC_PUBKEY_LEN];
    std::memset(sub, 0x5C, sizeof sub);
    ASSERT_EQ(sync_engine_revoke(e, "ns", sub), SYNC_OK);
    sync_capability_free(root);

    Digest d0;
    ASSERT_EQ(sync_engine_digest(e, d0.data()), SYNC_OK);
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK);
    sync_engine_destroy(e);

    std::string raw = read_file(db);
    ASSERT_EQ(raw.compare(0, 8, "KOMEENC1"), 0) << "compaction lost encryption";
    synctest::LogWalk w = synctest::walk_frames(raw);
    ASSERT_TRUE(w.ok);
    EXPECT_EQ(w.trailing, 0u);
    /* meta + 12 entities + cap + rev: every one of them freshly sealed. */
    ASSERT_GE(w.frames.size(), 15u) << "expected the full rewritten image";

    std::set<std::string> nonces;
    for (const synctest::LogFrame &f : w.frames) {
        /* Encrypted framing: [len:4][nonce:24][ct][mac:16] (log_frames.hpp). */
        ASSERT_LE(f.offset + 4 + 24, raw.size());
        std::string nonce = raw.substr(f.offset + 4, 24);
        EXPECT_NE(nonce, std::string(24, '\0'))
            << "zero nonce in a compacted frame at offset " << f.offset;
        nonces.insert(nonce);
    }
    EXPECT_EQ(nonces.size(), w.frames.size())
        << "nonce reuse across compacted frames";

    /* The rewrite is still a valid, decryptable log holding the same state. */
    sync_engine *r = sync_engine_open_encrypted(db.c_str(), site.data(), key);
    ASSERT_NE(r, nullptr);
    Digest d1;
    ASSERT_EQ(sync_engine_digest(r, d1.data()), SYNC_OK);
    EXPECT_EQ(d0, d1);
    sync_engine_destroy(r);
}

/* ---- Phase 2: cached element hashes across the load path ----------------- */

namespace {

/* Fresh, from-scratch hash of a cell's canonical record: the SHARED
 * change_from_* construction (codec.h — exactly what build_snapshot encodes),
 * hashed by a direct sha256 call rather than element_hash, so the check
 * shares no hashing code with what it audits. */
ke::Hash256 fresh_entity_hash(const std::string &ns, const std::string &ent,
                              const ke::Entity &en) {
    std::string rec;
    ke::encode_record(ke::change_from_entity(ns, ent, en), rec);
    ke::Hash256 h;
    sync_engine_detail::sha256(rec.data(), rec.size(), h.data());
    return h;
}

ke::Hash256 fresh_register_hash(const std::string &ns, const std::string &ent,
                                const std::string &field,
                                const ke::Register &r) {
    std::string rec;
    ke::encode_record(ke::change_from_register(ns, ent, field, r), rec);
    ke::Hash256 h;
    sync_engine_detail::sha256(rec.data(), rec.size(), h.data());
    return h;
}

/* memcmp every cell's stored cached hash against the fresh recompute.
 * Unasserted shells emit no existence element (build_snapshot skips them), so
 * their ex_hash is skipped here too. Returns cells checked (non-vacuity). */
size_t verify_all_cell_hashes(sync_engine *e, const char *ctx) {
    size_t checked = 0;
    for (const auto &np : e->ns) {
        for (const auto &ep : np.second) {
            const ke::Entity &en = ep.second;
            if (en.asserted()) {
                ke::Hash256 f = fresh_entity_hash(np.first, ep.first, en);
                EXPECT_EQ(0, std::memcmp(f.data(), en.ex_hash.data(), 32))
                    << ctx << ": stale existence hash at ns=" << np.first
                    << " entity=" << ep.first;
                checked++;
            }
            for (const auto &fp : en.fields) {
                ke::Hash256 f =
                    fresh_register_hash(np.first, ep.first, fp.first, fp.second);
                EXPECT_EQ(0, std::memcmp(f.data(), fp.second.elem_hash.data(), 32))
                    << ctx << ": stale register hash at ns=" << np.first
                    << " entity=" << ep.first << " field=" << fp.first;
                checked++;
            }
        }
    }
    return checked;
}

/* Number of records sync_engine_export would emit — a LOWER bound on the
 * load path's pending-record count n (every live cell was replayed from at
 * least one log record; superseded duplicates only add to n). Used to prove
 * the `n >= 64 && workers > 1` threaded-verify branch is really taken. */
size_t exported_record_count(sync_engine *e) {
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_EQ(sync_engine_export(e, &recs, &n), SYNC_OK);
    sync_changes_free(recs, n);
    return n;
}

} // namespace

/* Reopen recomputes every cell's element hash on the THREADED verify branch
 * (verify_and_merge in storage.cpp: `n >= 64 && workers > 1`, workers =
 * min(hardware_concurrency, 8), with per-index disjoint hashes[i] writes).
 * The branch is provably exercised, not assumed: the record count is proven
 * >= 64 via the export lower bound, and workers > 1 is asserted from
 * hardware_concurrency — with a documented skip on a single-vCPU runner,
 * where the branch is unreachable and the serial path is covered by the
 * companion test below. */
TEST(Storage, ReopenPreservesElementHashes) {
    unsigned hw = std::thread::hardware_concurrency();
    if (hw <= 1)
        GTEST_SKIP() << "single-vCPU runner: the n>=64 && workers>1 threaded "
                        "verify branch cannot be taken here; the serial branch "
                        "is covered by ReopenPreservesElementHashesSerial";

    TempDir dir;
    std::string db = dir.file("elemhash.db");
    auto site = site_from(0x40);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    const int N = 120; /* 120 existence + 120 register records >> 64 */
    for (int i = 0; i < N; i++)
        cluster::put(e, "ns", "ent" + std::to_string(i), "f",
                     "value-" + std::to_string(i));
    /* Shape coverage: tombstones and empty-value registers reload too. */
    for (int i = 0; i < 6; i++)
        cluster::del(e, "ns", "ent" + std::to_string(i));
    for (int i = 6; i < 12; i++) {
        std::string ent = "ent" + std::to_string(i);
        ASSERT_EQ(sync_engine_erase_field(e, B(std::string("ns")), 2, B(ent),
                                          ent.size(), B(std::string("f")), 1),
                  SYNC_OK);
    }
    /* Every one of these live cells was loaded from >= 1 log record, so the
     * load-path n is at least this — comfortably past the 64 threshold. */
    ASSERT_GE(exported_record_count(e), 64u);
    Digest d0 = digest(e);
    sync_engine_destroy(e);

    sync_engine *r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);
    EXPECT_EQ(digest(r), d0);
    size_t checked = verify_all_cell_hashes(r, "threaded reopen");
    EXPECT_EQ(checked, 2u * N) << "walk did not cover the full cell population";
    sync_engine_destroy(r);
}

/* Companion: under 64 records the load verifies (and hashes) on the SERIAL
 * branch — same disjoint-write code, no threads. 10 fresh entities, one set
 * each, no overwrites: exactly 20 signed records in the log, < 64 by
 * construction whether or not a compaction rewrote it (compaction emits one
 * record per live cell, and there are 20 live cells). */
TEST(Storage, ReopenPreservesElementHashesSerial) {
    TempDir dir;
    std::string db = dir.file("elemhash_serial.db");
    auto site = site_from(0x41);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    const int N = 10;
    for (int i = 0; i < N; i++)
        cluster::put(e, "ns", "s" + std::to_string(i), "f",
                     "v" + std::to_string(i));
    ASSERT_LT(exported_record_count(e), 64u)
        << "test bug: record count reaches the threaded threshold";
    Digest d0 = digest(e);
    sync_engine_destroy(e);

    sync_engine *r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);
    EXPECT_EQ(digest(r), d0);
    EXPECT_EQ(verify_all_cell_hashes(r, "serial reopen"), 2u * N);
    sync_engine_destroy(r);
}

/* The degenerate merge_record tie: a decoded record whose (hlc, author,
 * value) exactly TIE a freshly default-constructed Register — register_cmp
 * ignores the signature, so a record with a NONZERO signature still ties —
 * leaves the DEFAULT cell in the map. The stored hash must then describe that
 * default cell's own canonical encoding, NOT the incoming record's (their
 * encodings differ in the signature bytes, so the two hashes differ — which
 * is what makes this test able to tell the two apart). Drives ke::merge_record
 * directly (promoted out of storage.cpp's anonymous namespace for exactly
 * this). */
TEST(Storage, DefaultInsertedRegisterGetsHash) {
    sync_engine *e = sync_engine_create(site_from(0x42).data());
    ASSERT_NE(e, nullptr);
    const std::string ns = "n", ent = "e", field = "f";

    ke::DecodedChange dc;
    dc.kind = SYNC_CHANGE_REGISTER;
    dc.ns = ns;
    dc.entity = ent;
    dc.field = field;
    dc.value = "";              /* ties the default cell's empty value */
    dc.hlc.physical = 0;        /* ties the default {0,0} hlc */
    dc.hlc.logical = 0;
    /* dc.author stays all-zero (ties the default author). The signature is
     * NOT part of register_cmp, so this record still ties — but its canonical
     * encoding (and hence its element hash) differs from the default cell's. */
    dc.signature.fill(0x5A);
    ke::Hash256 h_in = ke::element_hash(dc.view()); /* the honest caller hash */

    ke::merge_record(e, dc, h_in);

    /* The map now holds a Register on the fresh slot... */
    auto ni = e->ns.find(ns);
    ASSERT_NE(ni, e->ns.end());
    auto ei = ni->second.find(ent);
    ASSERT_NE(ei, ni->second.end());
    auto fi = ei->second.fields.find(field);
    ASSERT_NE(fi, ei->second.fields.end()) << "tie left no cell in the map";
    const ke::Register &reg = fi->second;

    /* ...and it is the DEFAULT cell (the tie did not install the record). */
    EXPECT_TRUE(reg.value.empty());
    EXPECT_EQ(reg.sig, ke::Sig{}) << "tie installed the incoming record";

    /* Its stored hash describes its OWN canonical encoding... */
    ke::Hash256 own =
        ke::element_hash(ke::change_from_register(ns, ent, field, reg));
    EXPECT_EQ(0, std::memcmp(own.data(), reg.elem_hash.data(), 32))
        << "default-inserted register's hash is not its own encoding's hash";
    EXPECT_NE(0, std::memcmp(own.data(), ke::Hash256{}.data(), 32))
        << "hash left zeroed";
    /* ...NOT the incoming record's — the discriminator that keeps this test
     * non-vacuous (the two encodings differ only in the signature bytes). */
    EXPECT_NE(0, std::memcmp(h_in.data(), reg.elem_hash.data(), 32))
        << "tie path stored the incoming record's hash for the default cell";

    /* Control: a record that WINS the same slot installs the caller's hash. */
    ke::DecodedChange win = dc;
    win.value = "w";
    win.hlc.physical = 5;
    win.signature.fill(0x77);
    ke::Hash256 h_win = ke::element_hash(win.view());
    ke::merge_record(e, win, h_win);
    const ke::Register &reg2 = e->ns[ns][ent].fields[field];
    EXPECT_EQ(reg2.value, "w");
    EXPECT_EQ(0, std::memcmp(h_win.data(), reg2.elem_hash.data(), 32))
        << "winning merge did not install the incoming record's hash";

    sync_engine_destroy(e);
}

/* ---- Phase 3 (§3.3): batched blob writes -------------------------------- *
 * Gate tests for the nesting-safe write batch: fsync-counter cost bound for
 * a large blob put, single-commit-point nesting, abort semantics (durability
 * boundary, not rollback), and the erase-before-tombstone durable-prefix
 * invariant under batching. All assertions on write cost go through the
 * debug/test fsync counter (ke::storage_fsync_count via log_frames.hpp), NOT
 * on-disk frame counts — the outermost commit of a large batch ends with a
 * maybe_compact full rewrite whose rewrite_log_streamed streams many frames
 * under a single fsync pair (spec §3.3 amendment 1). */

namespace {

/* Deterministic pseudo-random fill (blob_test.cpp's generator): an all-zero
 * buffer would make every chunk content-address to the same entity. */
std::vector<uint8_t> blob_data(size_t n, uint32_t s) {
    std::vector<uint8_t> v(n);
    uint32_t x = s ? s : 1;
    for (size_t i = 0; i < n; i++) {
        x ^= x << 13; x ^= x >> 17; x ^= x << 5;
        v[i] = (uint8_t)x;
    }
    return v;
}

} // namespace

/* An 8 MiB blob put must cost O(size / kBatchFlushBytes) fsyncs — the
 * mandatory sub-frame flushes — plus one final commit frame and exactly one
 * compaction rewrite. Asserted on the fsync counter, with the compaction
 * separately pinned both by counter arithmetic and structurally.
 *
 * Arithmetic (plaintext log, ns="blobs"):
 *   8 MiB / SYNC_BLOB_CHUNK_MAX (32 KiB) = 256 chunk records, staged as one
 *   entity entry (~151 B) + one field entry (32768 B payload + ~155 B framing)
 *   per chunk, ~33.07 KiB staged per chunk. batch_maybe_flush fires at
 *   staging >= kBatchFlushBytes (2 MiB): 64 chunks stage >= 64*32768 =
 *   kBatchFlushBytes exactly, while 63 chunks stage at most 63*(32768+306) =
 *   2,083,662 < 2,097,152 — so a sub-frame flushes after every 64th chunk for
 *   any per-chunk overhead in [0, 520] B (current: 306 B). 256 chunks =>
 *   exactly 4 sub-frame fsyncs. The manifest record (+ the tail's clock-meta
 *   stamp) then lands in the outermost commit's frame: +1 fsync. That commit's
 *   maybe_compact sees an ~8.6 MB log against the fresh-log 64 KiB floor and
 *   rewrites it: rewrite_log_streamed = +2 counted fsyncs (temp file +
 *   directory). Total: 4 + 1 + 2 = 7. */
TEST(Storage, BlobPutFrameBounded) {
    TempDir dir;
    std::string db = dir.file("batch_blob.db");
    auto site = site_from(0x61);
    const std::string ns = "blobs";

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);

    /* The arithmetic above needs the flush threshold to be a whole number of
     * chunks; fail loudly if a retune breaks that before trusting the sums. */
    ASSERT_EQ(ke::kBatchFlushBytes % SYNC_BLOB_CHUNK_MAX, 0u);
    const uint64_t chunks_per_flush = ke::kBatchFlushBytes / SYNC_BLOB_CHUNK_MAX;
    const size_t kBlobLen = 8u * 1024 * 1024;
    const uint64_t chunks = kBlobLen / SYNC_BLOB_CHUNK_MAX; /* 256, exact */
    ASSERT_EQ(chunks % chunks_per_flush, 0u);
    const uint64_t subframes = chunks / chunks_per_flush; /* 4 */

    std::vector<uint8_t> data = blob_data(kBlobLen, 0xB10B);
    uint8_t id[SYNC_BLOB_ID_LEN];
    synctest::fsync_reset();
    ASSERT_EQ(sync_blob_put(e, B(ns), ns.size(), data.data(), data.size(), id),
              SYNC_OK);
    uint64_t fsyncs = synctest::fsync_count();

    /* subframes + 1 outermost-commit frame + 2 for exactly one
     * compaction-driven rewrite_log_streamed (temp-file fsync + directory
     * fsync; one rename). A second compaction would show up as +2 here. */
    EXPECT_EQ(fsyncs, subframes + 1 + 2) << "8 MiB put cost the wrong number "
                                            "of fsyncs (sub-frame bound or "
                                            "compaction count broken)";

    /* Structural pin for "exactly one compaction": the log on disk is exactly
     * the live-state image the rewrite produces — 1 meta frame + one frame
     * per entity (256 chunk entities + 1 manifest entity) — not the batch's
     * append history (which would be ~6 giant frames). */
    synctest::LogWalk w = synctest::walk_log_file(db);
    ASSERT_TRUE(w.ok);
    EXPECT_FALSE(w.encrypted);
    EXPECT_EQ(w.trailing, 0u);
    EXPECT_EQ(w.frames.size(), 1u + chunks + 1u);

    /* And nothing was lost to the batching: full round-trip after reopen. */
    Digest d0 = digest(e);
    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(digest(e), d0);
    uint8_t *out = nullptr;
    size_t out_len = 0;
    ASSERT_EQ(sync_blob_get(e, B(ns), ns.size(), id, &out, &out_len), SYNC_OK);
    ASSERT_EQ(out_len, kBlobLen);
    EXPECT_EQ(0, std::memcmp(out, data.data(), kBlobLen));
    sync_free(out);
    sync_engine_destroy(e);
}

/* Nested begin/begin/commit/commit: only the OUTERMOST commit writes — the
 * fsync counter stays at zero across the inner commit and every staged
 * mutation — and the whole batch lands as ONE frame whose clock meta is
 * stamped once per (sub-)frame, not once per record. */
TEST(Storage, NestedBatchSingleCommitPoint) {
    TempDir dir;
    std::string db = dir.file("nested_batch.db");
    auto site = site_from(0x62);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    size_t frames_before = synctest::walk_log_file(db).frames.size();

    synctest::fsync_reset();
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK); /* depth 1 */
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK); /* depth 2 */
    cluster::put(e, "ns", "k1", "f", "v1");
    cluster::put(e, "ns", "k2", "f", "v2");
    EXPECT_EQ(synctest::fsync_count(), 0u) << "staged writes hit the disk";

    ASSERT_EQ(sync_engine_batch_commit(e), SYNC_OK); /* inner: depth 2 -> 1 */
    EXPECT_EQ(synctest::fsync_count(), 0u)
        << "inner commit wrote/fsynced; durability must arrive only at the "
           "outermost commit";

    cluster::put(e, "ns", "k3", "f", "v3");
    cluster::put(e, "ns", "k4", "f", "v4");
    EXPECT_EQ(synctest::fsync_count(), 0u);

    ASSERT_EQ(sync_engine_batch_commit(e), SYNC_OK); /* outermost */
    EXPECT_EQ(synctest::fsync_count(), 1u)
        << "outermost commit must be the single durability point (one frame, "
           "one fsync; log small enough that no compaction follows)";

    /* One frame for the whole batch; its entry count is 4 mutations x
     * (entity + field entry) + exactly 3 clock-meta entries (hlc_physical /
     * hlc_logical / db_clock) stamped once for the frame — a per-record (or
     * per-mutation) clock stamp would inflate this count. */
    std::string raw = read_file(db);
    synctest::LogWalk w = synctest::walk_frames(raw);
    ASSERT_TRUE(w.ok);
    EXPECT_EQ(w.trailing, 0u);
    ASSERT_EQ(w.frames.size(), frames_before + 1);
    EXPECT_EQ(synctest::frame_entry_count(raw, w.frames.back()), 4u * 2u + 3u);

    /* Digest correct on reopen: the single frame carried everything. */
    Digest d0 = digest(e);
    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(digest(e), d0);
    for (const char *k : {"k1", "k2", "k3", "k4"})
        EXPECT_EQ(cluster::exists(e, "ns", k), true) << k;
    sync_engine_destroy(e);
}

/* Abort discards STAGED (not-yet-flushed) bytes only. The contract pinned
 * here, read off the implementation (Storage::batch_abort + the tx_* in-batch
 * branches): a batch is a DURABILITY boundary, not a rollback mechanism —
 * in-RAM engine state keeps every mutation (they were committed to the maps
 * before the tx_* staging step), so after an abort RAM and disk genuinely
 * diverge for those keys. This test keeps the log below the auto-compact
 * threshold, so nothing here re-persists them and the divergence resolves in
 * disk's favor at the next reopen (the aborted mutations are simply gone).
 * That is deliberately NOT a general keep-off-disk guarantee: a compaction's
 * streamed rewrite re-serializes the log from RAM wholesale, so once the batch is
 * closed, an explicit sync_engine_compact — or the size-triggered
 * auto-compaction that ordinary later writes set off — persists the aborted
 * mutations after all. That half of the contract is documented at
 * sync_engine_batch_abort and pinned by AbortedTailReturnsAtCompaction
 * below; compact() refusing mid-batch only defers it. A nested abort poisons
 * the whole engine-global batch: subsequent in-batch writes fail fast and
 * the outermost commit reports failure instead of committing. */
TEST(Storage, AbortSemantics) {
    TempDir dir;
    std::string db = dir.file("abort.db");
    auto site = site_from(0x63);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    cluster::put(e, "ns", "keep", "f", "v0"); /* write-through, durable */

    /* -- 1. Plain abort: staged tail discarded, RAM keeps the mutation. -- */
    synctest::fsync_reset();
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
    cluster::put(e, "ns", "gone", "f", "staged");
    EXPECT_EQ(cluster::get(e, "ns", "gone", "f"), "staged"); /* RAM immediate */
    ASSERT_EQ(sync_engine_batch_abort(e), SYNC_OK);
    EXPECT_EQ(synctest::fsync_count(), 0u)
        << "aborted batch wrote to disk (staged tail must be discarded)";
    EXPECT_EQ(cluster::get(e, "ns", "gone", "f"), "staged")
        << "abort must NOT roll back in-memory state (durability boundary, "
           "not rollback)";

    /* Engine fully usable after the abort: ordinary write-through resumes. */
    cluster::put(e, "ns", "later", "f", "v1");

    /* -- 2. Nested abort poisons the outer batch, engine-global. -- */
    synctest::fsync_reset();
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK); /* outer */
    cluster::put(e, "ns", "outer1", "f", "vo");
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK); /* inner */
    cluster::put(e, "ns", "inner1", "f", "vi");
    ASSERT_EQ(sync_engine_batch_abort(e), SYNC_OK); /* inner abort: poison */

    /* Poisoned: the write path fails immediately... */
    const std::string pns = "ns", pent = "poisoned", pf = "f", pv = "vp";
    EXPECT_EQ(sync_engine_set(e, B(pns), pns.size(), B(pent), pent.size(),
                              B(pf), pf.size(), B(pv), pv.size()),
              SYNC_ERR_INTERNAL);
    /* ...though its RAM commit had already happened (same boundary rule). */
    EXPECT_EQ(cluster::get(e, "ns", "poisoned", "f"), "vp");

    /* The outermost commit reports the poisoning and persists nothing. */
    EXPECT_EQ(sync_engine_batch_commit(e), SYNC_ERR_INTERNAL);
    EXPECT_EQ(synctest::fsync_count(), 0u)
        << "poisoned batch still wrote a frame";

    /* Batch fully closed and the engine healthy again. */
    EXPECT_EQ(sync_engine_batch_commit(e), SYNC_ERR_INVALID); /* unbalanced */
    cluster::put(e, "ns", "after", "f", "v2");

    /* Reopen: durable writes present; every aborted/poisoned mutation gone —
     * the RAM-vs-disk divergence heals in disk's favor. */
    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(cluster::get(e, "ns", "keep", "f"), "v0");
    EXPECT_EQ(cluster::get(e, "ns", "later", "f"), "v1");
    EXPECT_EQ(cluster::get(e, "ns", "after", "f"), "v2");
    for (const char *k : {"gone", "outer1", "inner1", "poisoned"})
        EXPECT_EQ(cluster::exists(e, "ns", k), false)
            << k << ": aborted mutation survived on disk";
    sync_engine_destroy(e);
}

/* The abort boundary is durability-only: aborted mutations stay live in RAM,
 * and the next compaction — the explicit ABI call here; the automatic
 * size-triggered one behaves identically — re-serializes RAM into the log,
 * making them durable after all. This pins the corrected public contract
 * (sync_engine_batch_abort and the blob write functions promise exactly
 * this): "aborted" means "not written by the batch", never "kept off disk".
 * If aborts ever grow real rollback semantics, update those header docs in
 * the same change that turns this test around. */
TEST(Storage, AbortedTailReturnsAtCompaction) {
    TempDir dir;
    std::string db = dir.file("abort_compact.db");
    auto site = site_from(0x67);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
    cluster::put(e, "ns", "aborted", "f", "v");
    ASSERT_EQ(sync_engine_batch_abort(e), SYNC_OK);

    /* Not written by the batch (AbortSemantics pins that side) — but still
     * live in RAM... */
    EXPECT_EQ(cluster::get(e, "ns", "aborted", "f"), "v");
    /* ...so the next compaction persists it wholesale. */
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK);
    sync_engine_destroy(e);

    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(cluster::get(e, "ns", "aborted", "f"), "v")
        << "compaction no longer re-persists aborted-but-in-RAM mutations — "
           "the sync_engine_batch_abort docs say it does; change them "
           "together";
    sync_engine_destroy(e);
}

/* A poisoned batch must hold — and keep holding — ZERO staged bytes: poison
 * drops the condemned tail immediately (Storage::batch_poison) and the write
 * path refuses to stage into it (emit()'s poison check), because that tail
 * is guaranteed to be discarded at the outermost close anyway. Without both,
 * a caller looping over post-poison writes — each failing SYNC_ERR_INTERNAL,
 * e.g. a bulk ingest that ignores per-record errors — would grow staging_
 * without bound while batch_maybe_flush (which bails out on poison before
 * its size check) never fires: the exact unbounded RAM transient the
 * mandatory-flush amendment exists to prevent (spec §3.3). White-box via
 * Storage::staged_bytes(). */
TEST(Storage, PoisonedBatchHoldsNoStaging) {
    TempDir dir;
    std::string db = dir.file("poison_ram.db");
    auto site = site_from(0x68);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);

    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK); /* outer */
    cluster::put(e, "ns", "pre", "f", std::string(1000, 'x'));
    EXPECT_GT(e->store->staged_bytes(), 0u) << "healthy batch not staging";
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK); /* inner */
    ASSERT_EQ(sync_engine_batch_abort(e), SYNC_OK); /* poison at depth 1 */
    EXPECT_EQ(e->store->staged_bytes(), 0u)
        << "poison kept the condemned staged tail in RAM";

    /* Push ~2.5x kBatchFlushBytes through the poisoned batch: every set
     * fails fast (RAM keeps the value — the boundary rule), nothing may be
     * staged, and no condemned sub-frame may be flushed. */
    const std::string ns = "ns", field = "f";
    const std::string val(64u * 1024, 'y');
    const int n = (int)(ke::kBatchFlushBytes * 5 / 2 / val.size()) + 1;
    synctest::fsync_reset();
    for (int i = 0; i < n; i++) {
        std::string ent = "p" + std::to_string(i);
        EXPECT_EQ(sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(),
                                  B(field), field.size(), B(val), val.size()),
                  SYNC_ERR_INTERNAL);
        ASSERT_EQ(e->store->staged_bytes(), 0u)
            << "write " << i
            << " grew a poisoned batch's staging (unbounded RAM transient)";
    }
    EXPECT_EQ(synctest::fsync_count(), 0u)
        << "a poisoned batch flushed a condemned sub-frame";

    EXPECT_EQ(sync_engine_batch_commit(e), SYNC_ERR_INTERNAL); /* outermost */
    /* Healthy again: write-through resumes and survives reopen. */
    cluster::put(e, "ns", "after", "f", "v");
    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(cluster::get(e, "ns", "after", "f"), "v");
    sync_engine_destroy(e);
}

/* A FAILED frame write must not strand the log. A short write leaves partial
 * frame bytes on disk past the last good frame; if later appends landed
 * after that garbage they would return SYNC_OK yet be unreachable by replay
 * (load() stops at the first bad frame) — silently lost at the next reopen.
 * write_frame therefore marks the tail torn on any write/fsync failure, so
 * the NEXT write truncates back to the last good frame before appending
 * (the same deferred-cleanup mechanism load() uses for crash-torn tails).
 * Forced deterministically with RLIMIT_FSIZE: with SIGXFSZ ignored, the
 * over-limit write writes what fits and then fails with EFBIG — a genuine
 * torn mid-log region. */
TEST(Storage, FailedFrameWriteDoesNotOrphanLaterWrites) {
    TempDir dir;
    std::string db = dir.file("efbig.db");
    auto site = site_from(0x69);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    cluster::put(e, "ns", "anchor", "f", "v0"); /* durable, pre-failure */

    /* Cap the file at its current size + 100 bytes: the next ~4.5 KiB frame
     * write fails partway through. */
    struct rlimit old {};
    ASSERT_EQ(getrlimit(RLIMIT_FSIZE, &old), 0);
    const size_t pre_size = read_file(db).size();
    struct rlimit lim = old;
    lim.rlim_cur = (rlim_t)pre_size + 100;
    ASSERT_EQ(setrlimit(RLIMIT_FSIZE, &lim), 0);
    auto oldsig = std::signal(SIGXFSZ, SIG_IGN);
    ASSERT_NE(oldsig, SIG_ERR);

    const std::string ns = "ns", ent = "lost", field = "f";
    const std::string big(4096, 'z');
    EXPECT_EQ(sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(),
                              B(field), field.size(), B(big), big.size()),
              SYNC_ERR_INTERNAL)
        << "precondition: the capped write was supposed to fail";
    EXPECT_GT(read_file(db).size(), pre_size)
        << "precondition: the failed write was supposed to leave partial "
           "bytes (a torn region) on disk";

    std::signal(SIGXFSZ, oldsig);
    ASSERT_EQ(setrlimit(RLIMIT_FSIZE, &old), 0);

    /* Recovery: later writes must truncate the garbage first, then land
     * replayably. Before the torn-tail marking these returned SYNC_OK and
     * vanished at reopen. */
    cluster::put(e, "ns", "after1", "f", "v1");
    cluster::put(e, "ns", "after2", "f", "v2");
    synctest::LogWalk w = synctest::walk_log_file(db);
    ASSERT_TRUE(w.ok);
    EXPECT_EQ(w.trailing, 0u)
        << "torn mid-log region still present after successful writes";

    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(cluster::get(e, "ns", "anchor", "f"), "v0");
    EXPECT_EQ(cluster::get(e, "ns", "after1", "f"), "v1")
        << "post-failure write returned SYNC_OK but was lost on reopen";
    EXPECT_EQ(cluster::get(e, "ns", "after2", "f"), "v2")
        << "post-failure write returned SYNC_OK but was lost on reopen";
    /* The failed key itself: RAM kept it (boundary rule) but its frame never
     * reached disk — reopen heals in disk's favor. */
    EXPECT_EQ(cluster::exists(e, "ns", "lost"), false);
    sync_engine_destroy(e);
}

/* Batched sync_blob_erase stages its records in append order — every zeroing
 * overwrite BEFORE any tombstone — and sub-frames fsync in append order, so
 * every durable prefix of the log satisfies: no chunk tombstone precedes its
 * zeroing overwrite (a violating prefix would reopen with a non-empty payload
 * hidden under a tombstone, unreachable by a re-erase). Verified by a
 * truncation sweep: every frame boundary (plus mid-frame cuts, which load()
 * drops as a torn tail) reopens to a state where every non-empty chunk
 * payload still belongs to a PRESENT (un-tombstoned) entity.
 *
 * PINNED AS NEAR-VACUOUS TODAY, BY DESIGN (spec §3.3, minor hazard): with
 * kMaxChunks = 1000 an erase stages ~200 B/record, far below kBatchFlushBytes,
 * so the whole erase lands in ONE frame and every prefix contains none or all
 * of it. The sweep is kept as a pin against a future kBatchFlushBytes
 * reduction (or per-record staging growth) that would split an erase across
 * sub-frames — the append-order staging + append-order sub-frame fsync +
 * load()'s stop-at-first-bad-frame argument is what must keep each prefix
 * safe on that day, and this test is what will catch its violation. */
TEST(Storage, EraseTombstonePrefixInvariant) {
    TempDir dir;
    std::string db = dir.file("erase_prefix.db");
    auto site = site_from(0x64);
    const std::string ns = "blobs";

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);

    /* 80 chunks (2.5 MiB): the batched put crosses one sub-frame boundary
     * (flush after chunk 64), then its outermost commit compacts the log into
     * a per-entity image; the erase then appends its single batch frame. */
    const size_t kBlobLen = 80u * SYNC_BLOB_CHUNK_MAX;
    std::vector<uint8_t> data = blob_data(kBlobLen, 0xE7A5);
    uint8_t id[SYNC_BLOB_ID_LEN];
    ASSERT_EQ(sync_blob_put(e, B(ns), ns.size(), data.data(), data.size(), id),
              SYNC_OK);
    ASSERT_EQ(sync_blob_erase(e, B(ns), ns.size(), id), SYNC_OK);
    sync_engine_destroy(e);

    std::string raw = read_file(db);
    synctest::LogWalk w = synctest::walk_frames(raw);
    ASSERT_TRUE(w.ok);
    ASSERT_EQ(w.trailing, 0u);
    ASSERT_GE(w.frames.size(), 3u); /* meta + entities + the erase frame */

    /* Cut points: after the header, after every frame, and a few mid-frame
     * offsets inside the last (erase) frame — those reopen identically to the
     * boundary before them, exercising the stop-at-first-bad-frame path. */
    std::vector<size_t> cuts;
    cuts.push_back(w.header_size);
    for (const synctest::LogFrame &f : w.frames)
        cuts.push_back(f.offset + f.size);
    const synctest::LogFrame &last = w.frames.back();
    cuts.push_back(last.offset + 1);
    cuts.push_back(last.offset + last.size / 2);
    cuts.push_back(last.offset + last.size - 1);

    for (size_t cut : cuts) {
        std::string prefix = raw.substr(0, cut);
        std::string pdb = dir.file("prefix.db");
        write_file(pdb, prefix);
        sync_engine *p = sync_engine_open(pdb.c_str(), site.data());
        ASSERT_NE(p, nullptr) << "prefix at " << cut << " failed to open";

        /* The invariant: every chunk register still holding payload bytes
         * must belong to a present entity — a tombstone durable before its
         * zeroing overwrite would surface here as a hidden non-empty payload
         * (export sees registers hidden under tombstones). */
        sync_change *recs = nullptr;
        size_t n = 0;
        ASSERT_EQ(sync_engine_export(p, &recs, &n), SYNC_OK);
        for (size_t i = 0; i < n; i++) {
            const sync_change &c = recs[i];
            if (c.kind != SYNC_CHANGE_REGISTER || c.value_len == 0) continue;
            if (c.entity_len != 34 || c.entity[0] != 'c' || c.entity[1] != 0)
                continue;
            int present = 0;
            ASSERT_EQ(sync_engine_exists(p, c.ns, c.ns_len, c.entity,
                                         c.entity_len, &present),
                      SYNC_OK);
            EXPECT_EQ(present, 1)
                << "prefix at " << cut << ": tombstone durable before its "
                << "zeroing overwrite (non-empty payload under a tombstone)";
        }
        sync_changes_free(recs, n);
        sync_engine_destroy(p);
    }
}

/* ---- Phase 3 (§3.3): fork-based mid-batch crash prefix (RESPECIFIED) ----- *
 * The naive form of this test ("crash mid-batch, reopen, write, everything
 * converges") is VACUOUS: Hlc::tick's wall-clock branch makes any post-reopen
 * local write dominate any wall-clock-stamped record whether or not the
 * sub-frames carried clock meta, so it passes with the stamp deleted. The
 * respecified form (spec §3.3 hazard table) makes the clock itself the
 * subject: the crashing child applies SIGNED REMOTE records whose HLC
 * physical lies decades ahead of the wall clock, so each accepted apply's
 * e->clock.receive() pushes the engine clock far past now_ms(). The
 * per-sub-frame clock-meta stamp (Storage::batch_maybe_flush) is then the
 * ONLY thing that persists that future clock: load() restores the clock from
 * meta entries alone (storage.cpp, replay epilogue) and never receive()s a
 * replayed record's HLC. With the stamp, the reopened clock has replayed past
 * the future HLCs and a fresh local write ticks {future, n+1} — strictly
 * newer, it wins LWW everywhere. Without it, the reopened clock falls back to
 * the last pre-batch (wall-clock) meta, the local write ticks ~now_ms() and
 * LOSES the LWW merge to the durable future-HLC record on the next replay —
 * the exact "durable records whose HLC exceeds the persisted clock" crash
 * hazard the stamp exists to close.
 *
 * Native-only by construction: this file is registered under
 * if(NOT EMSCRIPTEN) in CMakeLists.txt (fork/waitpid, like CrashAtomicity
 * above), so no per-test guard is needed. */

namespace {

/* The one future instant every batched record carries: 2100-01-01T00:00:00Z
 * in ms. Far enough ahead that no test-runner wall clock reaches it; the test
 * asserts that precondition rather than assuming it. */
constexpr uint64_t kFutureMs = 4102444800000ull;

/* Per-record payload size. kBatchFlushBytes must divide by it so the
 * sub-frame boundary falls on a whole record count (same arithmetic as
 * BlobPutFrameBounded): with value_len = 32 KiB a record stages
 * 32768 + ~238 B (117 B entity shell row + 121 B field-entry framing), so the
 * mandatory flush fires after every 64th apply for any per-record overhead in
 * [0, 520] B — 63 records stage at most 63*(32768+520) = 2,097,144 <
 * kBatchFlushBytes while 64 stage at least 64*32768 = kBatchFlushBytes. */
constexpr size_t kFutureValLen = 32u * 1024;
constexpr int    kFutureRecords = 160; /* 2 full sub-frames + a 32-record
                                        * staged tail the crash discards */

std::string future_ent(int i) {
    char b[16];
    std::snprintf(b, sizeof b, "r%03d", i);
    return std::string(b);
}

/* Build, sign, and apply record i: REGISTER n/r{i}/f = 32 KiB pseudo-random
 * payload, HLC {kFutureMs, i}, authored by one fixed REMOTE identity (not the
 * engine's own). Ed25519 signing is deterministic, so the child (feeding the
 * crashing batch) and the parent (rebuilding the expected committed prefix
 * independently) construct byte-identical records. */
bool apply_future_record(sync_engine *e, int i) {
    const std::string ns = "n", ent = future_ent(i), field = "f";
    std::vector<uint8_t> val = blob_data(kFutureValLen, 0xC0DE0000u + (uint32_t)i);
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_REGISTER;
    c.ns = B(ns);
    c.ns_len = ns.size();
    c.entity = B(ent);
    c.entity_len = ent.size();
    c.field = B(field);
    c.field_len = field.size();
    c.value = val.data();
    c.value_len = val.size();
    c.hlc.physical = kFutureMs;
    c.hlc.logical = (uint32_t)i;
    auto s = cluster::seed_from(0xF07u); /* the remote author's seed */
    if (sync_change_sign(&c, s.data()) != SYNC_OK) return false;
    return sync_engine_apply(e, &c) == SYNC_OK;
}

/* White-box register lookup (find-only — never inserts). */
const ke::Register *find_reg(sync_engine *e, const std::string &ns,
                             const std::string &ent, const std::string &field) {
    auto ni = e->ns.find(ns);
    if (ni == e->ns.end()) return nullptr;
    auto ei = ni->second.find(ent);
    if (ei == ni->second.end()) return nullptr;
    auto fi = ei->second.fields.find(field);
    return fi == ei->second.fields.end() ? nullptr : &fi->second;
}

} // namespace

TEST(Storage, MidBatchCrashPrefix) {
    TempDir dir;
    std::string db = dir.file("midbatch.db");
    auto site = site_from(0x65);

    /* Precondition for the whole construction: the record HLCs really are in
     * the future (retune kFutureMs before the year 2100). */
    ASSERT_GT(kFutureMs, ke::now_ms() + 3600u * 1000u)
        << "kFutureMs is no longer far ahead of the wall clock";

    ASSERT_EQ(ke::kBatchFlushBytes % kFutureValLen, 0u)
        << "retune kFutureValLen: the sub-frame arithmetic needs the flush "
           "threshold to be a whole number of records";
    const int per_flush = (int)(ke::kBatchFlushBytes / kFutureValLen); /* 64 */
    const int expect_survivors = 2 * per_flush;                       /* 128 */
    ASSERT_LT(expect_survivors, kFutureRecords); /* a tail must be staged */

    /* Seed a committed pre-batch anchor. Its write-through commit persists
     * wall-clock meta — exactly the stale clock a stamp-less reopen would
     * fall back to. Mirror it into `expected`, the independently-built
     * committed-prefix oracle (in-memory, different site). */
    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    cluster::put(e, "n", "anchor", "f", "v0");
    auto oracle_site = site_from(0x66);
    sync_engine *expected = sync_engine_create(oracle_site.data());
    ASSERT_NE(expected, nullptr);
    replicate(e, expected);
    sync_engine_destroy(e);
    const size_t frames_pre = synctest::walk_log_file(db).frames.size();

    /* Child: open the durable engine, open a batch, apply the future-HLC
     * records — each accepted apply receive()s {kFutureMs, i} into the engine
     * clock — until the mandatory flush has cut exactly two durable
     * sub-frames, then _exit(0) WITHOUT committing: a mid-batch crash with a
     * staged, never-written tail. No gtest in the child; it self-validates
     * and reports through its exit code. */
    pid_t pid = fork();
    ASSERT_GE(pid, 0);
    if (pid == 0) {
        sync_engine *c = sync_engine_open(db.c_str(), site.data());
        if (!c) _exit(2);
        synctest::fsync_reset();
        if (sync_engine_batch_begin(c) != SYNC_OK) _exit(3);
        for (int i = 0; i < kFutureRecords; i++)
            if (!apply_future_record(c, i)) _exit(4);
        /* Exactly the two sub-frame flushes hit the disk — nothing else may
         * fsync inside a batch (no per-record frames, no compaction). */
        if (synctest::fsync_count() != 2) _exit(5);
        /* The applies really pushed the clock past the wall time. */
        if (c->clock.physical != kFutureMs) _exit(6);
        _exit(0); /* crash: no batch_commit, no destroy, no unwind */
    }
    int status = 0;
    ASSERT_EQ(waitpid(pid, &status, 0), pid);
    ASSERT_TRUE(WIFEXITED(status));
    ASSERT_EQ(WEXITSTATUS(status), 0)
        << "child failed (2=open 3=batch_begin 4=apply 5=sub-frame fsync "
           "count != 2 6=clock not pushed to kFutureMs)";

    /* On-disk shape: the two durable sub-frames and NOTHING for the staged
     * tail. Each sub-frame carries per_flush records (2 entries each: entity
     * shell + field register) + the 3 clock-meta entries stamped once per
     * sub-frame by batch_maybe_flush — the entry count pins the stamp's
     * presence structurally before the semantic checks below. */
    {
        std::string raw = read_file(db);
        synctest::LogWalk w = synctest::walk_frames(raw);
        ASSERT_TRUE(w.ok);
        EXPECT_EQ(w.trailing, 0u);
        ASSERT_EQ(w.frames.size(), frames_pre + 2)
            << "expected exactly the two crash-surviving sub-frames";
        for (size_t fi = frames_pre; fi < w.frames.size(); fi++)
            EXPECT_EQ(synctest::frame_entry_count(raw, w.frames[fi]),
                      (uint32_t)(per_flush * 2 + 3))
                << "sub-frame " << (fi - frames_pre)
                << ": missing the per-sub-frame clock-meta stamp (3 meta "
                   "entries) beside its " << per_flush << " records";
    }

    /* Reopen. The committed prefix must be exactly the two sub-frames'
     * records; the staged tail must be gone. */
    sync_engine *r = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r, nullptr);

    int survivors = 0;
    bool prefix_exact = true;
    for (int i = 0; i < kFutureRecords; i++) {
        bool have = find_reg(r, "n", future_ent(i), "f") != nullptr;
        if (have) {
            if (i != survivors) prefix_exact = false; /* gap: not a prefix */
            survivors++;
        }
    }
    EXPECT_TRUE(prefix_exact) << "surviving records are not a log prefix";
    ASSERT_GT(survivors, 0) << "flushed sub-frames lost";
    ASSERT_LT(survivors, kFutureRecords)
        << "uncommitted staged tail survived the crash";
    EXPECT_EQ(survivors, expect_survivors)
        << "sub-frame boundary drifted (per-record staging overhead left the "
           "[0, 520] B window? see the arithmetic at kFutureValLen)";

    /* Reopen state == the committed prefix, built independently: the oracle
     * engine applies the same deterministic signed records 0..survivors-1
     * (plus the anchor it already mirrored). */
    for (int i = 0; i < survivors; i++)
        ASSERT_TRUE(apply_future_record(expected, i)) << "oracle apply " << i;
    EXPECT_EQ(digest(r), digest(expected))
        << "reopened state is not exactly the committed prefix";

    /* Spot-checks: a surviving record's payload round-tripped, and the cell
     * the local write below must beat still carries its future HLC. */
    {
        const ke::Register *r1 = find_reg(r, "n", future_ent(1), "f");
        ASSERT_NE(r1, nullptr);
        std::vector<uint8_t> want = blob_data(kFutureValLen, 0xC0DE0000u + 1u);
        EXPECT_TRUE(r1->value.size() == want.size() &&
                    std::memcmp(r1->value.data(), want.data(), want.size()) == 0)
            << "surviving record payload corrupted";
        const ke::Register *r0 = find_reg(r, "n", future_ent(0), "f");
        ASSERT_NE(r0, nullptr);
        EXPECT_EQ(r0->hlc.physical, kFutureMs);
        EXPECT_EQ(r0->hlc.logical, 0u);
    }

    /* THE MECHANISM: the reopened clock must have replayed PAST every
     * surviving future HLC — restorable only from the sub-frames' own clock
     * meta (the last stamp wrote {kFutureMs, survivors}; the anchor's meta
     * holds mere wall time). */
    EXPECT_EQ(r->clock.physical, kFutureMs)
        << "reopened clock fell back to wall-clock meta: the sub-frames did "
           "not carry the batch's clock";
    EXPECT_GE(r->clock.logical, (uint32_t)survivors)
        << "reopened clock logical is behind the flushed sub-frames' stamp";

    /* THE DISCRIMINATING ASSERTION: a fresh LOCAL write to a future-HLC cell
     * must WIN LWW — its tick must be strictly newer than {kFutureMs,
     * survivors-1} (the newest durable record). Without the per-sub-frame
     * stamp it ticks ~now_ms() << kFutureMs and loses. */
    cluster::put(r, "n", future_ent(0), "f", "local-wins");
    {
        const ke::Register *lw = find_reg(r, "n", future_ent(0), "f");
        ASSERT_NE(lw, nullptr);
        /* RAM always shows the value (set installs unconditionally) — the
         * HLC is what decides every future merge/replay. */
        EXPECT_TRUE(lw->value == "local-wins");
        EXPECT_TRUE(lw->hlc.physical > kFutureMs ||
                    (lw->hlc.physical == kFutureMs &&
                     lw->hlc.logical > (uint32_t)(survivors - 1)))
            << "fresh local write does NOT dominate the replayed future HLC "
               "(got {" << lw->hlc.physical << "," << lw->hlc.logical
            << "} vs record {" << kFutureMs << "," << (survivors - 1)
            << "}): the local write LOSES LWW to a record the engine itself "
               "durably holds";
    }
    Digest pre_destroy = digest(r);
    sync_engine_destroy(r);

    /* And the LWW verdict must survive a replay: on the next reopen the
     * future record and the local write meet in merge_record, and the local
     * write must be the winner. A wall-clock-ticked write would lose here —
     * disk would resurrect the future-HLC value over the caller's own
     * committed update. */
    sync_engine *r2 = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(r2, nullptr);
    EXPECT_TRUE(cluster::get(r2, "n", future_ent(0), "f") == "local-wins")
        << "replay resurrected the future-HLC record over the fresh local "
           "write: the local write lost LWW on reopen";
    EXPECT_EQ(digest(r2), pre_destroy)
        << "reopened state diverged from the engine that wrote it";
    sync_engine_destroy(r2);
    sync_engine_destroy(expected);
}

/* ---- Phase 4: crash / failure injection against the streamed rewrite ---- *
 * The two tests below attack rewrite_log_streamed's one hard crash-safety
 * invariant (§3.4): THE RENAME IS THE SOLE COMMIT POINT. Everything before it
 * — temp-file creation, every FrameSink flush, ftruncate, fsync(tmp) — must
 * be free to die or fail at any byte without the original log changing by a
 * single bit, and a failure must leave the engine fully serviceable.
 *
 * Both inject the failure with RLIMIT_FSIZE, sized so the FIRST buffered
 * flush (~kCompactBufSize = 256 KiB, restated below) overruns the cap while
 * streaming to <db>.tmp: the kernel writes what fits below the limit, then
 * the next write at the limit raises SIGXFSZ — process death mid-flush when
 * the disposition is default (the fork test), a genuine EFBIG short write
 * when ignored (the in-process test). The seeded image is made comfortably
 * larger than one flush so the failure lands inside the entity loop — mid-
 * stream — not in the final flush before fsync. */

namespace {

/* Restated flush granularity of storage.cpp's FrameSink (kCompactBufSize,
 * anonymous namespace there — restated here the way kEntryMeta is above). */
constexpr size_t kStreamBufSize = 256u * 1024;
/* Temp-file byte cap for the injected failure: far below one flush. */
constexpr rlim_t kTmpCapBytes = 64u * 1024;

/* Seed n distinct 4-KiB-valued entities — ~n*4.2 KiB of live image, so
 * n = 200 gives ~850 KiB: > 3 flushes worth of stream. */
void seed_bulk_entities(sync_engine *e, int n) {
    for (int i = 0; i < n; i++) {
        char ent[16];
        std::snprintf(ent, sizeof ent, "e%03d", i);
        cluster::put(e, "bulk", ent, "f",
                     std::string(4096, (char)('a' + i % 26)));
    }
}

/* Open file descriptors of this process, via /proc/self/fd. The readdir fd
 * itself is included in every count identically, so equality between two
 * counts is meaningful. */
int count_open_fds() {
    DIR *d = opendir("/proc/self/fd");
    if (!d) return -1;
    int n = 0;
    struct dirent *ent;
    while ((ent = readdir(d))) {
        std::string s = ent->d_name;
        if (s != "." && s != "..") n++;
    }
    closedir(d);
    return n;
}

} // namespace

/* A compaction KILLED mid-stream (SIGXFSZ, default disposition — no unwind,
 * no TmpFile destructor, exactly like SIGKILL power loss) must leave the
 * original log BYTE-IDENTICAL: the child dies during the first 256-KiB flush
 * to <db>.tmp, having never reached fsync/rename. The orphaned partial .tmp
 * it strands must be ignored by the next open (never read, never deleted)
 * and consumed by the next successful compaction — the StaleTmp contract,
 * here proven against a REAL crash artifact rather than a planted one.
 *
 * The child self-validates and reports through its exit code (the
 * MidBatchCrashPrefix pattern — no gtest in the child); the expected verdict
 * is death BY SIGXFSZ, not any exit code. It snapshots the pre-crash log and
 * digest to side files BEFORE arming the limit, so the parent can compare
 * bytes and digest across the crash without cross-process plumbing. */
TEST(Storage, CrashMidStreamLeavesLogIntact) {
    TempDir dir;
    std::string db = dir.file("crashstream.db");
    std::string tmp = db + ".tmp";
    std::string pre_copy = db + ".pre";  /* child's pre-crash byte snapshot */
    std::string pre_dig = db + ".dig";   /* child's pre-crash digest        */
    auto site = site_from(0x90);

    /* Seed live state, then compact so image ~= file: the child's open-time
     * heuristic (compacted_image_size*2 < file_size_) then deterministically
     * declines to rewrite under the child's first put. */
    sync_engine *seed = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(seed, nullptr);
    seed_bulk_entities(seed, 200);
    ASSERT_EQ(sync_engine_compact(seed), SYNC_OK);
    sync_engine_destroy(seed);
    ASSERT_GT(read_file(db).size(), kStreamBufSize + (size_t)kTmpCapBytes)
        << "seed too small: the crash would not land mid-stream";

    pid_t pid = fork();
    ASSERT_GE(pid, 0);
    if (pid == 0) {
        /* Child. Deterministic dispositions first: SIGXFSZ back to default
         * (an earlier test in this binary ignores it), no core dump. */
        std::signal(SIGXFSZ, SIG_DFL);
        struct rlimit nocore {0, 0};
        setrlimit(RLIMIT_CORE, &nocore);

        sync_engine *c = sync_engine_open(db.c_str(), site.data());
        if (!c) _exit(2);
        /* Write state of our own, so the crashed compaction is attacking a
         * log with post-open writes, not just the parent's seed. */
        const std::string ns = "crash", f = "f", va = "written-pre-crash-a",
                          vb = "written-pre-crash-b";
        const std::string ea = "a", eb = "b";
        if (sync_engine_set(c, B(ns), ns.size(), B(ea), ea.size(), B(f),
                            f.size(), B(va), va.size()) != SYNC_OK)
            _exit(3);
        if (sync_engine_set(c, B(ns), ns.size(), B(eb), eb.size(), B(f),
                            f.size(), B(vb), vb.size()) != SYNC_OK)
            _exit(3);

        /* Pre-crash snapshot + digest to side files (limit not armed yet). */
        {
            std::string bytes = read_file(db);
            if (bytes.empty()) _exit(4);
            FILE *out = fopen(pre_copy.c_str(), "wb");
            if (!out || fwrite(bytes.data(), 1, bytes.size(), out) !=
                            bytes.size()) _exit(4);
            fclose(out);
            uint8_t d[SYNC_DIGEST_LEN];
            if (sync_engine_digest(c, d) != SYNC_OK) _exit(5);
            out = fopen(pre_dig.c_str(), "wb");
            if (!out || fwrite(d, 1, sizeof d, out) != sizeof d) _exit(5);
            fclose(out);
        }

        /* Arm: any file this process extends past 64 KiB kills it. The live
         * log is bigger already but never extended before the crash; the
         * stream's first 256-KiB flush to .tmp dies partway. */
        struct rlimit lim {kTmpCapBytes, kTmpCapBytes};
        if (setrlimit(RLIMIT_FSIZE, &lim) != 0) _exit(6);
        sync_engine_compact(c); /* expected: no return — SIGXFSZ mid-flush */
        _exit(7); /* compaction survived the cap: injection failed */
    }

    int status = 0;
    ASSERT_EQ(waitpid(pid, &status, 0), pid);
    ASSERT_TRUE(WIFSIGNALED(status) && WTERMSIG(status) == SIGXFSZ)
        << "child did not die mid-stream by SIGXFSZ (exit code "
        << (WIFEXITED(status) ? WEXITSTATUS(status) : -1)
        << ": 2=open 3=set 4=snapshot 5=digest 6=setrlimit "
           "7=compact returned)";

    /* THE INVARIANT: the original log is bit-for-bit what it was when the
     * compaction started. Rename never ran, so nothing else may have. */
    const std::string pre = read_file(pre_copy);
    ASSERT_FALSE(pre.empty());
    EXPECT_EQ(read_file(db), pre)
        << "a compaction crash BEFORE the rename commit point mutated the "
           "original log";

    /* The crash really stranded a partial .tmp (no unwind ran): it must hold
     * some bytes but at most the cap — a mid-flush corpse, not an image. */
    struct stat st {};
    ASSERT_EQ(::stat(tmp.c_str(), &st), 0)
        << "no orphan .tmp: the crash did not interrupt the temp stream";
    EXPECT_GT(st.st_size, 0);
    EXPECT_LE(st.st_size, (off_t)kTmpCapBytes);

    Digest want{};
    {
        std::string d = read_file(pre_dig);
        ASSERT_EQ(d.size(), (size_t)SYNC_DIGEST_LEN);
        std::memcpy(want.data(), d.data(), d.size());
    }

    /* Reopen: full pre-crash state, digest unchanged, orphan .tmp neither
     * consulted nor removed by open. */
    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr) << "crashed compaction corrupted the log";
    EXPECT_EQ(digest(e), want) << "digest changed across a crashed compaction";
    EXPECT_EQ(cluster::get(e, "crash", "a", "f"), "written-pre-crash-a");
    EXPECT_EQ(cluster::get(e, "crash", "b", "f"), "written-pre-crash-b");
    EXPECT_EQ(cluster::get(e, "bulk", "e007", "f"),
              std::string(4096, (char)('a' + 7)));
    EXPECT_EQ(::stat(tmp.c_str(), &st), 0)
        << "open consumed/removed the orphan .tmp (open must never write)";

    /* A later SUCCESSFUL compaction replaces the orphan: the O_TRUNC + rename
     * consume the path, state and digest carry over, and the log reopens. */
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK)
        << "orphan .tmp blocked the next compaction";
    EXPECT_NE(::stat(tmp.c_str(), &st), 0)
        << "orphan .tmp survived a successful compaction";
    EXPECT_EQ(digest(e), want);
    sync_engine_destroy(e);

    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(digest(e), want)
        << "post-crash compacted image does not replay to the same state";
    sync_engine_destroy(e);
}

/* A compaction that FAILS mid-stream in-process (EFBIG short write with
 * SIGXFSZ ignored — the ENOSPC shape: write_all returns false partway into a
 * flush) must fail CLEANLY: SYNC_ERR_INTERNAL out of the ABI, the live log
 * untouched byte-for-byte, no leaked descriptor (TmpFile's destructor must
 * close AND unlink — §3.4 amendment 3), no stale .tmp, and the engine still
 * fully appendable with intact bookkeeping — subsequent writes land at the
 * correct offset (no hole, no torn region) and survive reopen. */
TEST(Storage, EnospcMidStreamFailsCleanly) {
    TempDir dir;
    std::string db = dir.file("enospc.db");
    std::string tmp = db + ".tmp";
    auto site = site_from(0x91);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    seed_bulk_entities(e, 200);
    /* Normalize: compacted_size_ = file_size_, so nothing auto-compacts
     * behind the assertions below; also image ~= file from here on. */
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK);

    const std::string before = read_file(db);
    ASSERT_GT(before.size(), kStreamBufSize + (size_t)kTmpCapBytes)
        << "seed too small: the failure would not land mid-stream";
    const Digest d0 = digest(e);

    /* Arm the failure: .tmp writes past 64 KiB fail with EFBIG. */
    struct rlimit old {};
    ASSERT_EQ(getrlimit(RLIMIT_FSIZE, &old), 0);
    struct rlimit lim = old;
    lim.rlim_cur = kTmpCapBytes;
    ASSERT_EQ(setrlimit(RLIMIT_FSIZE, &lim), 0);
    auto oldsig = std::signal(SIGXFSZ, SIG_IGN);
    ASSERT_NE(oldsig, SIG_ERR);

    const int fds_before = count_open_fds();
    ASSERT_GT(fds_before, 0);

    EXPECT_EQ(sync_engine_compact(e), SYNC_ERR_INTERNAL)
        << "precondition: the capped temp stream was supposed to fail";

    EXPECT_EQ(count_open_fds(), fds_before)
        << "failed compaction leaked a descriptor (TmpFile close, or the "
           "engine's own log fd)";

    std::signal(SIGXFSZ, oldsig);
    ASSERT_EQ(setrlimit(RLIMIT_FSIZE, &old), 0);

    /* The live log: untouched, byte for byte — and no .tmp left behind
     * (the RAII guard unlinks the partial temp on the failure path). */
    EXPECT_EQ(read_file(db), before)
        << "failed compaction modified the live log";
    struct stat st {};
    EXPECT_NE(::stat(tmp.c_str(), &st), 0)
        << "failed compaction left a partial .tmp behind";
    EXPECT_EQ(digest(e), d0) << "failed compaction changed engine state";

    /* Still appendable with intact bookkeeping: new writes must land as
     * well-formed frames at the true end of the log (a corrupted file_size_
     * or a spuriously-set torn-tail flag would leave a gap, truncate good
     * frames, or strand the appends), and survive reopen. */
    cluster::put(e, "post", "p1", "f", "v1");
    cluster::put(e, "post", "p2", "f", "v2");
    {
        synctest::LogWalk w = synctest::walk_log_file(db);
        ASSERT_TRUE(w.ok);
        EXPECT_EQ(w.trailing, 0u)
            << "post-failure appends left a hole/torn region in the log";
    }
    EXPECT_GT(read_file(db).size(), before.size())
        << "post-failure appends never reached the file";
    const Digest d1 = digest(e);
    sync_engine_destroy(e);

    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr) << "log unopenable after failed compaction + writes";
    EXPECT_EQ(digest(e), d1)
        << "post-failure writes were lost or corrupted at reopen";
    EXPECT_EQ(cluster::get(e, "post", "p1", "f"), "v1");
    EXPECT_EQ(cluster::get(e, "post", "p2", "f"), "v2");
    EXPECT_EQ(cluster::get(e, "bulk", "e199", "f"),
              std::string(4096, (char)('a' + 199 % 26)));
    sync_engine_destroy(e);
}


/* ---------------------------------------------------------------------------
 * Integer-boundary regressions: a reserved value minted at a narrowing cast or
 * a counter wrap.
 * ------------------------------------------------------------------------ */

/* A frame is [body_len:u32le][body...], and 0 is RESERVED in that prefix:
 * load()'s replay loop reads body_len == 0 as a clean end of log — the same
 * break as real EOF. `full.size()` is a size_t, so `(uint32_t)full.size()` did
 * not merely mis-frame an oversized body: at an exact 4 GiB multiple it MINTED
 * that terminator, and every frame after it was silently discarded on the next
 * open with load() still returning SYNC_OK. On the compaction path that means
 * the capability and revocation frames — written last, and fsynced
 * synchronously by put_revocation precisely so they cannot be dropped.
 *
 * CI cannot allocate 4 GiB, so the boundary is pinned through the predicate the
 * fix is expressed in. PRE-FIX there was no predicate and no check at all. */
TEST(Storage, OversizedFrameBodyIsRefusedNotTruncated) {
    /* Everything representable in the u32 prefix stays writable. */
    EXPECT_FALSE(ke::frame_body_too_large(0));
    EXPECT_FALSE(ke::frame_body_too_large(1));
    EXPECT_FALSE(ke::frame_body_too_large(0xFFFFFFFEull));
    EXPECT_FALSE(ke::frame_body_too_large(0xFFFFFFFFull));

    /* One past the prefix, and the two sizes that truncate onto the reserved
     * terminator itself (exact multiples of 2^32). */
    EXPECT_TRUE(ke::frame_body_too_large(0x100000000ull))
        << "a 4 GiB body truncates to body_len == 0, the end-of-log marker";
    EXPECT_TRUE(ke::frame_body_too_large(0x100000001ull));
    EXPECT_TRUE(ke::frame_body_too_large(0x200000000ull));
    EXPECT_TRUE(ke::frame_body_too_large(UINT64_MAX));
}

/* batch_depth_ is a uint32 and 0 is the reserved "no batch open" sentinel —
 * in_batch(), batch_commit, batch_abort, batch_maybe_flush and batch_poison all
 * read it. An uncapped `batch_depth_++` mints that sentinel while in_tx_ is
 * still set and staging_ still holds the batch's records, after which the tx_*
 * helpers take their non-batch branch into begin(), which CLEARS staging_ and
 * silently drops records the caller was told were staged.
 *
 * PRE-FIX batch_begin() returned true unconditionally, so there was no depth at
 * which it refused. */
TEST(Storage, BatchDepthRefusesRatherThanWrapping) {
    TempDir dir;
    ASSERT_FALSE(dir.path.empty());
    const std::string db = dir.file("depth.db");
    auto site = cluster::seed_from(0xD1);
    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    ASSERT_NE(e->store, nullptr);

    for (uint32_t i = 0; i < ke::kMaxBatchDepth; i++)
        ASSERT_TRUE(e->store->batch_begin()) << "refused at legitimate depth " << i;
    EXPECT_EQ(e->store->batch_depth(), ke::kMaxBatchDepth);

    EXPECT_FALSE(e->store->batch_begin())
        << "the depth counter wrapped instead of refusing";
    EXPECT_EQ(e->store->batch_depth(), ke::kMaxBatchDepth)
        << "a refused begin must not move the depth";
    EXPECT_TRUE(e->store->in_batch())
        << "the batch was closed out from under its holders";

    /* The batch is intact: a write staged at full depth still lands, and every
     * matching commit unwinds cleanly. */
    cluster::put(e, "ns", "deep", "f", "v");
    for (uint32_t i = 0; i < ke::kMaxBatchDepth; i++)
        ASSERT_TRUE(e->store->batch_commit(e)) << "unbalanced unwind at " << i;
    EXPECT_FALSE(e->store->in_batch());
    EXPECT_EQ(cluster::get(e, "ns", "deep", "f"), "v");

    const Digest d = digest(e);
    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(digest(e), d) << "records staged at full depth were dropped";
    EXPECT_EQ(cluster::get(e, "ns", "deep", "f"), "v");
    sync_engine_destroy(e);
}
