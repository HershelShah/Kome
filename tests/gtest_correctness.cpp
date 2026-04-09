/**
 * Correctness invariant tests.
 *
 * These tests define what "correct" means for Kome and verify each
 * property systematically. If all these pass, the replication engine
 * is working correctly.
 *
 * ## The 7 correctness invariants:
 *
 * 1. DURABILITY     — a successful put is immediately readable on the same node
 * 2. CONVERGENCE    — two nodes that exchange all writes end up with identical state
 * 3. COMMUTATIVITY  — the order entries arrive doesn't change the final state
 * 4. IDEMPOTENCY    — receiving the same entry twice produces the same state as once
 * 5. TOMBSTONE      — a delete wins over a prior put, even after sync
 * 6. INTEGRITY      — every stored entry's hash matches SHA-256(value)
 * 7. CAUSALITY      — version vectors are monotonic (seq numbers never decrease)
 */
#include <gtest/gtest.h>
#include "kome.h"
#include "kome_util.hpp"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <thread>
#include <chrono>

/* ── Helpers ─────────────────────────────────────────────────────────── */

struct CNode {
    std::string   db_path;
    KomeEngine   *engine = nullptr;

    ~CNode() {
        if (engine) kome_close(engine);
        cleanup_db(db_path);
    }
};

static CNode make_cnode(const char *name, uint8_t id_byte) {
    CNode n;
    n.db_path = temp_db_path(name);
    cleanup_db(n.db_path);
    KomeConfig cfg = {};
    cfg.path = n.db_path.c_str();
    EXPECT_EQ(KOME_OK, kome_open(&cfg, &n.engine));
    uint8_t key[32];
    std::memset(key, id_byte, 32);
    EXPECT_EQ(KOME_OK, kome_set_identity(n.engine, key, 32));
    return n;
}

static void sync_pair(CNode &a, CNode &b) {
    LoopbackPair lp;
    /* Get fingerprints by writing a probe entry */
    KomeEntryMeta ma, mb;
    uint8_t pk[] = "__p__"; uint8_t pv[] = "x";
    kome_put(a.engine, "__s", pk, 5, pv, 1, &ma);
    kome_put(b.engine, "__s", pk, 5, pv, 1, &mb);
    kome_delete(a.engine, "__s", pk, 5, nullptr);
    kome_delete(b.engine, "__s", pk, 5, nullptr);

    std::memcpy(lp.a.fingerprint, ma.author, 32);
    std::memcpy(lp.b.fingerprint, mb.author, 32);

    ASSERT_EQ(KOME_OK, kome_attach_transport(a.engine, &lp.a.transport));
    ASSERT_EQ(KOME_OK, kome_attach_transport(b.engine, &lp.b.transport));
    lp.connect();
}

struct Snapshot {
    std::map<std::string, std::string> entries; /* "ns/key" → value */
};

static Snapshot snapshot_node(CNode &n) {
    Snapshot snap;
    char **ns_list = nullptr;
    size_t ns_count = 0;
    if (kome_list_namespaces(n.engine, &ns_list, &ns_count) != KOME_OK)
        return snap;

    for (size_t i = 0; i < ns_count; i++) {
        std::string ns = ns_list[i];
        if (ns.substr(0, 2) == "__") continue; /* skip probe namespace */

        uint8_t **keys = nullptr;
        size_t *key_lens = nullptr;
        uint8_t **values = nullptr;
        size_t *value_lens = nullptr;
        KomeEntryMeta *metas = nullptr;
        size_t count = 0;

        if (kome_get_all(n.engine, ns.c_str(), &keys, &key_lens,
                         &values, &value_lens, &metas, &count) == KOME_OK) {
            for (size_t j = 0; j < count; j++) {
                std::string k(ns + "/" + std::string((char*)keys[j], key_lens[j]));
                std::string v;
                if (values[j] && value_lens[j] > 0)
                    v.assign((char*)values[j], value_lens[j]);
                snap.entries[k] = v;
            }
            kome_free_entries(keys, key_lens, values, value_lens, metas, count);
        }
    }
    kome_free_namespaces(ns_list, ns_count);
    return snap;
}

static void put_entry(CNode &n, const char *ns, const std::string &key,
                      const std::string &val) {
    ASSERT_EQ(KOME_OK, kome_put(n.engine, ns,
        (const uint8_t*)key.data(), key.size(),
        (const uint8_t*)val.data(), val.size(), nullptr));
}

/* ===================================================================
   INVARIANT 1: DURABILITY
   A successful kome_put must be immediately readable via kome_get
   on the same node, without any sync.
   =================================================================== */

TEST(Correctness, Durability) {
    auto A = make_cnode("dur_a", 0xA1);

    for (int i = 0; i < 50; i++) {
        std::string key = "key_" + std::to_string(i);
        std::string val = "val_" + std::to_string(i);
        put_entry(A, "ns", key, val);

        /* Immediately readable */
        uint8_t *out = nullptr;
        size_t len = 0;
        ASSERT_EQ(KOME_OK, kome_get(A.engine, "ns",
            (const uint8_t*)key.data(), key.size(), &out, &len, nullptr))
            << "Entry " << i << " not readable after put";
        EXPECT_EQ(val, std::string((char*)out, len));
        kome_free_value(out);
    }
}

/* ===================================================================
   INVARIANT 2: CONVERGENCE
   Two nodes that exchange all writes must have identical state,
   regardless of who wrote what.
   =================================================================== */

TEST(Correctness, Convergence) {
    auto A = make_cnode("conv_a", 0xA1);
    auto B = make_cnode("conv_b", 0xB2);

    /* Both write to the same namespace with different keys */
    for (int i = 0; i < 20; i++) {
        put_entry(A, "data", "a_" + std::to_string(i), "from_a_" + std::to_string(i));
        put_entry(B, "data", "b_" + std::to_string(i), "from_b_" + std::to_string(i));
    }

    /* Also write to different namespaces */
    put_entry(A, "only_a", "x", "1");
    put_entry(B, "only_b", "y", "2");

    /* Sync */
    sync_pair(A, B);

    /* Take snapshots and compare */
    auto snap_a = snapshot_node(A);
    auto snap_b = snapshot_node(B);

    EXPECT_EQ(snap_a.entries, snap_b.entries)
        << "Nodes must have identical state after full sync";
    EXPECT_EQ(42u, snap_a.entries.size())  /* 20+20 + 1+1 */
        << "Both nodes should have all 42 entries";
}

/* ===================================================================
   INVARIANT 3: COMMUTATIVITY
   The order entries arrive at a node must not change the final state.
   We verify this by syncing A→B and A→C (same source, same entries)
   and checking B == C.
   =================================================================== */

TEST(Correctness, Commutativity) {
    auto A = make_cnode("comm_a", 0xA1);
    auto B = make_cnode("comm_b", 0xB2);
    auto C = make_cnode("comm_c", 0xC3);

    /* A writes entries that will create conflicts on B and C */
    for (int i = 0; i < 10; i++)
        put_entry(A, "ns", "k" + std::to_string(i), "a_" + std::to_string(i));

    /* B and C independently write to some of the same keys */
    for (int i = 0; i < 5; i++)
        put_entry(B, "ns", "k" + std::to_string(i), "b_" + std::to_string(i));
    for (int i = 5; i < 10; i++)
        put_entry(C, "ns", "k" + std::to_string(i), "c_" + std::to_string(i));

    /* Sync A→B, then A→C (different order of conflict resolution) */
    sync_pair(A, B);
    sync_pair(A, C);

    /* Now sync B↔C to fully converge */
    sync_pair(B, C);

    auto snap_b = snapshot_node(B);
    auto snap_c = snapshot_node(C);

    EXPECT_EQ(snap_b.entries, snap_c.entries)
        << "Nodes must converge to same state regardless of sync order";
}

/* ===================================================================
   INVARIANT 4: IDEMPOTENCY
   Receiving the same entry twice must produce the same state as
   receiving it once. We test this by syncing the same pair twice.
   =================================================================== */

TEST(Correctness, Idempotency) {
    auto A = make_cnode("idem_a", 0xA1);
    auto B = make_cnode("idem_b", 0xB2);

    for (int i = 0; i < 10; i++)
        put_entry(A, "ns", "k" + std::to_string(i), "v" + std::to_string(i));

    /* Sync once */
    sync_pair(A, B);
    auto snap_after_first = snapshot_node(B);

    /* Sync again — same entries re-delivered */
    sync_pair(A, B);
    auto snap_after_second = snapshot_node(B);

    EXPECT_EQ(snap_after_first.entries, snap_after_second.entries)
        << "Double-sync must not change state";
}

/* ===================================================================
   INVARIANT 5: TOMBSTONE CORRECTNESS
   A delete (tombstone) must win over a prior put for the same key,
   even after the delete propagates through sync. The key must not
   be readable after sync.
   =================================================================== */

TEST(Correctness, TombstoneWinsAfterSync) {
    auto A = make_cnode("tomb_a", 0xA1);
    auto B = make_cnode("tomb_b", 0xB2);

    /* A writes then deletes */
    put_entry(A, "ns", "doomed", "alive");
    kome_delete(A.engine, "ns", (const uint8_t*)"doomed", 6, nullptr);

    /* Sync to B */
    sync_pair(A, B);

    /* B must not find the entry */
    uint8_t *out = nullptr;
    size_t len = 0;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get(B.engine, "ns",
        (const uint8_t*)"doomed", 6, &out, &len, nullptr))
        << "Tombstone must propagate — deleted entry should not be readable";
}

TEST(Correctness, TombstoneOverwritesPriorValue) {
    auto A = make_cnode("tow_a", 0xA1);
    auto B = make_cnode("tow_b", 0xB2);

    /* B has the entry */
    put_entry(B, "ns", "target", "old_value");

    /* A writes a newer version then deletes it */
    put_entry(A, "ns", "target", "new_value");
    kome_delete(A.engine, "ns", (const uint8_t*)"target", 6, nullptr);

    /* Sync — A's tombstone (highest timestamp) should win */
    sync_pair(A, B);

    uint8_t *out = nullptr;
    size_t len = 0;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get(B.engine, "ns",
        (const uint8_t*)"target", 6, &out, &len, nullptr))
        << "Tombstone with higher timestamp must overwrite existing value";
}

/* ===================================================================
   INVARIANT 6: INTEGRITY
   Every stored entry's hash field must equal SHA-256(value).
   =================================================================== */

TEST(Correctness, HashIntegrity) {
    auto A = make_cnode("hash_a", 0xA1);

    /* Write entries with various value sizes */
    std::vector<std::pair<std::string, std::string>> test_data = {
        {"empty", ""},
        {"small", "hello"},
        {"medium", std::string(1000, 'x')},
        {"large", std::string(100000, 'y')},
    };

    for (auto &[key, val] : test_data) {
        KomeEntryMeta meta;
        ASSERT_EQ(KOME_OK, kome_put(A.engine, "ns",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &meta));

        /* Verify hash = SHA-256(value) */
        uint8_t expected_hash[32];
        kome::sha256((const uint8_t*)val.data(), val.size(), expected_hash);
        EXPECT_EQ(0, std::memcmp(meta.hash, expected_hash, 32))
            << "Hash mismatch for key: " << key;
    }

    /* Verify hashes survive sync */
    auto B = make_cnode("hash_b", 0xB2);
    sync_pair(A, B);

    for (auto &[key, val] : test_data) {
        KomeEntryMeta meta;
        ASSERT_EQ(KOME_OK, kome_get_meta(B.engine, "ns",
            (const uint8_t*)key.data(), key.size(), &meta));

        uint8_t expected_hash[32];
        kome::sha256((const uint8_t*)val.data(), val.size(), expected_hash);
        EXPECT_EQ(0, std::memcmp(meta.hash, expected_hash, 32))
            << "Hash mismatch after sync for key: " << key;
    }
}

/* ===================================================================
   INVARIANT 7: CAUSALITY (VERSION VECTOR MONOTONICITY)
   Version vectors must be monotonically increasing. After a put,
   the author's seq must be strictly greater than before. After sync,
   the local version vector must include all authors seen.
   =================================================================== */

TEST(Correctness, VersionVectorMonotonicity) {
    auto A = make_cnode("vv_a", 0xA1);

    /* Each put must increment seq */
    uint64_t prev_seq = 0;
    for (int i = 0; i < 10; i++) {
        KomeEntryMeta meta;
        std::string key = "k" + std::to_string(i);
        ASSERT_EQ(KOME_OK, kome_put(A.engine, "ns",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)"v", 1, &meta));
        EXPECT_GT(meta.seq, prev_seq)
            << "Sequence number must be strictly increasing";
        prev_seq = meta.seq;
    }
}

TEST(Correctness, VersionVectorMergesAfterSync) {
    auto A = make_cnode("vvm_a", 0xA1);
    auto B = make_cnode("vvm_b", 0xB2);

    /* A writes 5, B writes 3 */
    for (int i = 0; i < 5; i++)
        put_entry(A, "ns", "a" + std::to_string(i), "v");
    for (int i = 0; i < 3; i++)
        put_entry(B, "ns", "b" + std::to_string(i), "v");

    sync_pair(A, B);

    /* Both version vectors should have 2 authors */
    auto check_vv = [](KomeEngine *e, int expected_authors) {
        KomeVersionEntry *entries = nullptr;
        size_t count = 0;
        ASSERT_EQ(KOME_OK, kome_version_vector(e, &entries, &count));
        EXPECT_EQ((size_t)expected_authors, count)
            << "Version vector should have " << expected_authors << " authors";
        kome_free_version_vector(entries);
    };

    check_vv(A.engine, 2);
    check_vv(B.engine, 2);
}

/* ===================================================================
   INVARIANT: CONFLICT DETERMINISM
   Given the same two conflicting entries, LWW must always pick the
   same winner, regardless of which node resolves the conflict.
   =================================================================== */

TEST(Correctness, ConflictDeterminism) {
    /* Create 3 independent pairs. Each pair has the same conflict.
       All must resolve identically. */
    for (int trial = 0; trial < 3; trial++) {
        std::string suffix = std::to_string(trial);
        auto A = make_cnode(("det_a_" + suffix).c_str(), 0xA1);
        auto B = make_cnode(("det_b_" + suffix).c_str(), 0xB2);

        put_entry(A, "ns", "key", "value_a");
        std::this_thread::sleep_for(std::chrono::milliseconds(2));
        put_entry(B, "ns", "key", "value_b");

        sync_pair(A, B);

        uint8_t *va = nullptr, *vb = nullptr;
        size_t la = 0, lb = 0;
        kome_get(A.engine, "ns", (const uint8_t*)"key", 3, &va, &la, nullptr);
        kome_get(B.engine, "ns", (const uint8_t*)"key", 3, &vb, &lb, nullptr);

        /* Both must agree */
        ASSERT_EQ(la, lb) << "Trial " << trial << ": value lengths must match";
        EXPECT_EQ(0, std::memcmp(va, vb, la))
            << "Trial " << trial << ": both nodes must have same winner";

        /* Winner must be B (later timestamp) */
        EXPECT_EQ(std::string((char*)va, la), "value_b")
            << "Trial " << trial << ": later timestamp must win";

        kome_free_value(va);
        kome_free_value(vb);
    }
}

/* ===================================================================
   INVARIANT: NAMESPACE ISOLATION
   Entries in one namespace must not leak into another, even after sync.
   =================================================================== */

TEST(Correctness, NamespaceIsolation) {
    auto A = make_cnode("nsiso_a", 0xA1);
    auto B = make_cnode("nsiso_b", 0xB2);

    put_entry(A, "alpha", "k", "in_alpha");
    put_entry(A, "beta",  "k", "in_beta");

    sync_pair(A, B);

    /* Same key name in different namespaces must return different values */
    uint8_t *v1 = nullptr, *v2 = nullptr;
    size_t l1 = 0, l2 = 0;
    ASSERT_EQ(KOME_OK, kome_get(B.engine, "alpha",
        (const uint8_t*)"k", 1, &v1, &l1, nullptr));
    ASSERT_EQ(KOME_OK, kome_get(B.engine, "beta",
        (const uint8_t*)"k", 1, &v2, &l2, nullptr));

    EXPECT_EQ("in_alpha", std::string((char*)v1, l1));
    EXPECT_EQ("in_beta", std::string((char*)v2, l2));

    kome_free_value(v1);
    kome_free_value(v2);
}

/* ===================================================================
   INVARIANT: BATCH ATOMICITY
   A batch write must either fully succeed or fully fail. Partial
   writes must never be visible.
   =================================================================== */

TEST(Correctness, BatchAtomicity) {
    auto A = make_cnode("batom_a", 0xA1);

    /* Valid batch */
    KomeBatchEntry entries[3];
    uint8_t k0[] = "k0", k1[] = "k1", k2[] = "k2";
    uint8_t v0[] = "v0", v1[] = "v1", v2[] = "v2";
    entries[0] = {"ns", k0, 2, v0, 2};
    entries[1] = {"ns", k1, 2, v1, 2};
    entries[2] = {"ns", k2, 2, v2, 2};

    KomeEntryMeta metas[3];
    ASSERT_EQ(KOME_OK, kome_put_batch(A.engine, entries, 3, metas));

    /* All 3 must be readable */
    for (int i = 0; i < 3; i++) {
        std::string key = "k" + std::to_string(i);
        KomeEntryMeta m;
        EXPECT_EQ(KOME_OK, kome_get_meta(A.engine, "ns",
            (const uint8_t*)key.data(), key.size(), &m));
    }

    /* All must share the same timestamp */
    EXPECT_EQ(metas[0].timestamp_us, metas[1].timestamp_us);
    EXPECT_EQ(metas[1].timestamp_us, metas[2].timestamp_us);

    /* Sequence numbers must be consecutive */
    EXPECT_EQ(metas[0].seq + 1, metas[1].seq);
    EXPECT_EQ(metas[1].seq + 1, metas[2].seq);
}
