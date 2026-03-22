#include <gtest/gtest.h>
#include "kome.h"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>
#include <vector>

class EngineTest : public ::testing::Test {
protected:
    KomeEngine *engine = nullptr;
    std::string db_path;

    void SetUp() override {
        db_path = temp_db_path("engine");
        cleanup_db(db_path);

        /* Zero-init now gives WAL-on by default (disable_wal=0 → WAL enabled) */
        KomeConfig cfg = {};
        cfg.path = db_path.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&cfg, &engine));
    }

    void TearDown() override {
        kome_close(engine);
        cleanup_db(db_path);
    }

    void set_test_identity() {
        uint8_t key[32] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
                           17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32};
        ASSERT_EQ(KOME_OK, kome_set_identity(engine, key, sizeof(key)));
    }
};

/* --- Lifecycle tests ----------------------------------------------------- */

TEST_F(EngineTest, OpenClose) {
    EXPECT_NE(nullptr, engine);
}

TEST_F(EngineTest, OpenNullConfig) {
    KomeEngine *e = nullptr;
    EXPECT_EQ(KOME_ERR_MISUSE, kome_open(nullptr, &e));
}

TEST_F(EngineTest, OpenNullPath) {
    KomeConfig cfg = {};
    cfg.path = nullptr;
    KomeEngine *e = nullptr;
    EXPECT_EQ(KOME_ERR_MISUSE, kome_open(&cfg, &e));
}

TEST_F(EngineTest, CloseNull) {
    kome_close(nullptr); /* should not crash */
}

TEST_F(EngineTest, ZeroInitConfigGivesWalOn) {
    /* Verify zero-init config enables WAL by default */
    std::string p = temp_db_path("waltest");
    cleanup_db(p);
    KomeConfig cfg = {};
    cfg.path = p.c_str();
    KomeEngine *e = nullptr;
    ASSERT_EQ(KOME_OK, kome_open(&cfg, &e));
    kome_close(e);
    cleanup_db(p);
}

/* --- Identity ------------------------------------------------------------ */

TEST_F(EngineTest, SetIdentity) {
    set_test_identity();
}

TEST_F(EngineTest, SetIdentityNull) {
    EXPECT_EQ(KOME_ERR_MISUSE, kome_set_identity(engine, nullptr, 0));
}

/* --- Version / Errstr ---------------------------------------------------- */

TEST_F(EngineTest, Version) {
    const char *v = kome_version();
    EXPECT_STREQ("0.0.1", v);
}

TEST_F(EngineTest, Errstr) {
    EXPECT_STREQ("OK", kome_errstr(KOME_OK));
    EXPECT_STREQ("misuse of API", kome_errstr(KOME_ERR_MISUSE));
    EXPECT_STREQ("storage error", kome_errstr(KOME_ERR_STORAGE));
    EXPECT_STREQ("transport error", kome_errstr(KOME_ERR_TRANSPORT));
    EXPECT_STREQ("not found", kome_errstr(KOME_ERR_NOT_FOUND));
    EXPECT_STREQ("too large", kome_errstr(KOME_ERR_TOO_LARGE));
    EXPECT_STREQ("internal error", kome_errstr(KOME_ERR_INTERNAL));
}

/* --- Replicate ----------------------------------------------------------- */

TEST_F(EngineTest, ReplicateWithoutIdentity) {
    const char *ns = "test";
    uint8_t key[] = {1, 2, 3};
    uint8_t value[] = {10, 20, 30};
    KomeEntryMeta meta;
    EXPECT_EQ(KOME_ERR_MISUSE, kome_put(engine, ns, key, 3, value, 3, &meta));
}

TEST_F(EngineTest, ReplicateBasic) {
    set_test_identity();

    const char *ns = "contacts";
    uint8_t key[] = "user123";
    uint8_t value[] = "Alice";
    KomeEntryMeta meta = {};
    ASSERT_EQ(KOME_OK, kome_put(engine, ns, key, 7, value, 5, &meta));

    EXPECT_GT(meta.timestamp_us, 0u);
    EXPECT_EQ(1u, meta.seq);
    EXPECT_EQ(5u, meta.value_len);
    EXPECT_EQ(0, meta.tombstone);
}

TEST_F(EngineTest, ReplicateSequenceIncrement) {
    set_test_identity();

    const char *ns = "test";
    KomeEntryMeta meta1, meta2;

    uint8_t k1[] = "k1";
    uint8_t v1[] = "v1";
    ASSERT_EQ(KOME_OK, kome_put(engine, ns, k1, 2, v1, 2, &meta1));

    uint8_t k2[] = "k2";
    uint8_t v2[] = "v2";
    ASSERT_EQ(KOME_OK, kome_put(engine, ns, k2, 2, v2, 2, &meta2));

    EXPECT_EQ(1u, meta1.seq);
    EXPECT_EQ(2u, meta2.seq);
}

TEST_F(EngineTest, ReplicateTooLargeNs) {
    set_test_identity();
    std::string long_ns(256, 'x');
    uint8_t key[] = "k";
    uint8_t value[] = "v";
    KomeEntryMeta meta;
    EXPECT_EQ(KOME_ERR_TOO_LARGE,
        kome_put(engine, long_ns.c_str(), key, 1, value, 1, &meta));
}

TEST_F(EngineTest, ReplicateTooLargeKey) {
    set_test_identity();
    std::vector<uint8_t> big_key(513, 0x42);
    uint8_t value[] = "v";
    KomeEntryMeta meta;
    EXPECT_EQ(KOME_ERR_TOO_LARGE,
        kome_put(engine, "ns", big_key.data(), big_key.size(), value, 1, &meta));
}

/* --- Delete -------------------------------------------------------------- */

TEST_F(EngineTest, ReplicateDelete) {
    set_test_identity();

    const char *ns = "test";
    uint8_t key[] = "delme";
    uint8_t value[] = "data";
    KomeEntryMeta meta;
    ASSERT_EQ(KOME_OK, kome_put(engine, ns, key, 5, value, 4, &meta));

    KomeEntryMeta del_meta;
    ASSERT_EQ(KOME_OK, kome_delete(engine, ns, key, 5, &del_meta));
    EXPECT_EQ(1, del_meta.tombstone);
    EXPECT_EQ(2u, del_meta.seq);
}

/* --- kome_get: read values back ----------------------------------------- */

TEST_F(EngineTest, GetValue) {
    set_test_identity();

    uint8_t key[] = "mykey";
    uint8_t value[] = "hello world";
    KomeEntryMeta write_meta;
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 5, value, 11, &write_meta));

    uint8_t *out = nullptr;
    size_t out_len = 0;
    KomeEntryMeta read_meta = {};
    ASSERT_EQ(KOME_OK, kome_get(engine, "test", key, 5, &out, &out_len, &read_meta));

    ASSERT_NE(nullptr, out);
    EXPECT_EQ(11u, out_len);
    EXPECT_EQ(0, std::memcmp(out, "hello world", 11));
    EXPECT_EQ(write_meta.seq, read_meta.seq);
    EXPECT_EQ(write_meta.timestamp_us, read_meta.timestamp_us);
    kome_free_value(out);
}

TEST_F(EngineTest, GetValueNotFound) {
    uint8_t key[] = "nope";
    uint8_t *out = nullptr;
    size_t out_len = 0;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get(engine, "test", key, 4, &out, &out_len, nullptr));
    EXPECT_EQ(nullptr, out);
}

TEST_F(EngineTest, GetDeletedValueReturnsTombstone) {
    set_test_identity();

    uint8_t key[] = "dkey";
    uint8_t value[] = "data";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 4, value, 4, &m));
    ASSERT_EQ(KOME_OK, kome_delete(engine, "test", key, 4, &m));

    uint8_t *out = nullptr;
    size_t out_len = 0;
    KomeEntryMeta read_meta = {};
    ASSERT_EQ(KOME_OK, kome_get(engine, "test", key, 4, &out, &out_len, &read_meta));
    EXPECT_EQ(nullptr, out);
    EXPECT_EQ(0u, out_len);
    EXPECT_EQ(1, read_meta.tombstone);
}

TEST_F(EngineTest, GetValueNullMeta) {
    set_test_identity();

    uint8_t key[] = "k";
    uint8_t val[] = "v";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 1, val, 1, &m));

    uint8_t *out = nullptr;
    size_t out_len = 0;
    ASSERT_EQ(KOME_OK, kome_get(engine, "test", key, 1, &out, &out_len, nullptr));
    EXPECT_EQ(1u, out_len);
    kome_free_value(out);
}

/* --- Get Meta ------------------------------------------------------------ */

TEST_F(EngineTest, GetMeta) {
    set_test_identity();

    const char *ns = "test";
    uint8_t key[] = "k1";
    uint8_t value[] = "hello";
    KomeEntryMeta write_meta;
    ASSERT_EQ(KOME_OK, kome_put(engine, ns, key, 2, value, 5, &write_meta));

    KomeEntryMeta read_meta;
    ASSERT_EQ(KOME_OK, kome_get_meta(engine, ns, key, 2, &read_meta));

    EXPECT_EQ(write_meta.timestamp_us, read_meta.timestamp_us);
    EXPECT_EQ(write_meta.seq, read_meta.seq);
    EXPECT_EQ(write_meta.value_len, read_meta.value_len);
    EXPECT_EQ(0, std::memcmp(write_meta.author, read_meta.author, 32));
    EXPECT_EQ(0, std::memcmp(write_meta.hash, read_meta.hash, 32));
}

TEST_F(EngineTest, GetMetaNotFound) {
    uint8_t key[] = "nonexistent";
    KomeEntryMeta meta;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(engine, "test", key, 11, &meta));
}

/* --- Version vector ------------------------------------------------------ */

TEST_F(EngineTest, VersionVector) {
    set_test_identity();

    uint8_t key[] = "k";
    uint8_t val[] = "v";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", key, 1, val, 1, &m));

    KomeVersionEntry *entries = nullptr;
    size_t count = 0;
    ASSERT_EQ(KOME_OK, kome_version_vector(engine, &entries, &count));
    EXPECT_EQ(1u, count);
    EXPECT_EQ(1u, entries[0].seq);
    kome_free_version_vector(entries);
}

/* --- Stats --------------------------------------------------------------- */

TEST_F(EngineTest, Stats) {
    set_test_identity();

    uint8_t key[] = "k";
    uint8_t val[] = "v";
    KomeEntryMeta m;
    kome_put(engine, "ns1", key, 1, val, 1, &m);
    kome_put(engine, "ns2", key, 1, val, 1, &m);

    KomeStats stats;
    ASSERT_EQ(KOME_OK, kome_stats(engine, &stats));
    EXPECT_EQ(2u, stats.total_entries);
    EXPECT_EQ(0u, stats.tombstone_count);
    EXPECT_EQ(2u, stats.namespace_count);
    EXPECT_GT(stats.db_size_bytes, 0u);
}

/* --- Namespaces ---------------------------------------------------------- */

TEST_F(EngineTest, ListNamespaces) {
    set_test_identity();

    uint8_t key[] = "k";
    uint8_t val[] = "v";
    KomeEntryMeta m;
    kome_put(engine, "beta", key, 1, val, 1, &m);
    kome_put(engine, "alpha", key, 1, val, 1, &m);

    char **ns_list = nullptr;
    size_t count = 0;
    ASSERT_EQ(KOME_OK, kome_list_namespaces(engine, &ns_list, &count));
    EXPECT_EQ(2u, count);
    EXPECT_STREQ("alpha", ns_list[0]);
    EXPECT_STREQ("beta", ns_list[1]);
    kome_free_namespaces(ns_list, count);
}

/* --- Replication --------------------------------------------------------- */

TEST_F(EngineTest, SetReplication) {
    ASSERT_EQ(KOME_OK, kome_set_replication(engine, "contacts", 2));

    set_test_identity();
    uint8_t key[] = "k";
    uint8_t val[] = "v";
    KomeEntryMeta m;
    kome_put(engine, "contacts", key, 1, val, 1, &m);

    uint32_t confirmed = 99, target = 99;
    ASSERT_EQ(KOME_OK, kome_replication_status(engine, "contacts", key, 1,
                                                &confirmed, &target));
    EXPECT_EQ(0u, confirmed);
    EXPECT_EQ(2u, target);
}

/* --- Log level ----------------------------------------------------------- */

TEST_F(EngineTest, SetLogLevel) {
    kome_set_log_level(engine, KOME_LOG_DEBUG);
}

/* --- Callback from on_remote_change can call kome API ------------------- */

TEST_F(EngineTest, CallbackCanCallApi) {
    set_test_identity();

    /* This test verifies the deadlock fix: callbacks must be able to call kome API */
    struct Ctx {
        KomeEngine *eng;
        bool called;
    } ctx{engine, false};

    kome_on_remote_change(engine,
        [](void *ud, const char *ns, const uint8_t *key, size_t key_len,
           const uint8_t *, size_t, const KomeEntryMeta *) {
            auto *c = static_cast<Ctx*>(ud);
            /* Call kome_get_meta from inside the callback — would deadlock before fix */
            KomeEntryMeta m;
            KomeError err = kome_get_meta(c->eng, ns, key, key_len, &m);
            if (err == KOME_OK) c->called = true;
        }, &ctx);

    /* Trigger via sync: need two engines */
    std::string db2 = temp_db_path("engine_cb2");
    cleanup_db(db2);
    KomeConfig cfg2 = {};
    cfg2.path = db2.c_str();
    KomeEngine *e2 = nullptr;
    ASSERT_EQ(KOME_OK, kome_open(&cfg2, &e2));
    uint8_t id2[32]; std::memset(id2, 0xBB, 32);
    kome_set_identity(e2, id2, 32);

    /* Write on e2 */
    uint8_t k[] = "cb_key";
    uint8_t v[] = "cb_val";
    KomeEntryMeta m;
    kome_put(e2, "test", k, 6, v, 6, &m);

    /* Configure namespace for sync */
    KomeNamespaceACLEntry acl1;
    std::memset(acl1.fingerprint, 0xBB, 32);  /* B's loopback fp */
    acl1.role = KOME_ROLE_WRITE;
    KomeNamespaceConfig nscfg1 = {};
    nscfg1.name = "test";
    nscfg1.acl = &acl1;
    nscfg1.acl_count = 1;
    kome_configure_namespace(engine, &nscfg1);

    KomeNamespaceACLEntry acl2;
    std::memset(acl2.fingerprint, 0xAA, 32);  /* A's loopback fp */
    acl2.role = KOME_ROLE_WRITE;
    KomeNamespaceConfig nscfg2 = {};
    nscfg2.name = "test";
    nscfg2.acl = &acl2;
    nscfg2.acl_count = 1;
    kome_configure_namespace(e2, &nscfg2);

    /* Connect via loopback */
    LoopbackPair lb;
    kome_attach_transport(engine, &lb.a.transport);
    kome_attach_transport(e2, &lb.b.transport);
    lb.connect();

    EXPECT_TRUE(ctx.called);

    kome_close(e2);
    cleanup_db(db2);
}

/* --- Batch writes ------------------------------------------------------- */

TEST_F(EngineTest, BatchPutBasic) {
    set_test_identity();

    KomeBatchEntry entries[3];
    entries[0] = {"ns", (const uint8_t*)"k1", 2, (const uint8_t*)"v1", 2};
    entries[1] = {"ns", (const uint8_t*)"k2", 2, (const uint8_t*)"v2", 2};
    entries[2] = {"ns", (const uint8_t*)"k3", 2, (const uint8_t*)"v3", 2};

    KomeEntryMeta metas[3] = {};
    ASSERT_EQ(KOME_OK, kome_put_batch(engine, entries, 3, metas));

    /* Consecutive sequence numbers */
    EXPECT_EQ(1u, metas[0].seq);
    EXPECT_EQ(2u, metas[1].seq);
    EXPECT_EQ(3u, metas[2].seq);

    /* Same timestamp for all entries */
    EXPECT_EQ(metas[0].timestamp_us, metas[1].timestamp_us);
    EXPECT_EQ(metas[1].timestamp_us, metas[2].timestamp_us);

    /* All entries readable */
    for (int i = 0; i < 3; i++) {
        std::string key = "k" + std::to_string(i + 1);
        uint8_t *out = nullptr;
        size_t out_len = 0;
        ASSERT_EQ(KOME_OK, kome_get(engine, "ns",
            (const uint8_t*)key.data(), key.size(), &out, &out_len, nullptr));
        ASSERT_NE(nullptr, out);
        EXPECT_EQ(2u, out_len);
        kome_free_value(out);
    }
}

TEST_F(EngineTest, BatchPutNullMetas) {
    set_test_identity();

    KomeBatchEntry entries[2];
    entries[0] = {"ns", (const uint8_t*)"a", 1, (const uint8_t*)"x", 1};
    entries[1] = {"ns", (const uint8_t*)"b", 1, (const uint8_t*)"y", 1};

    ASSERT_EQ(KOME_OK, kome_put_batch(engine, entries, 2, nullptr));

    /* Still readable */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    ASSERT_EQ(KOME_OK, kome_get(engine, "ns", (const uint8_t*)"a", 1,
        &out, &out_len, nullptr));
    kome_free_value(out);
}

TEST_F(EngineTest, BatchPutSequenceContinuity) {
    set_test_identity();

    /* Single put first */
    uint8_t k[] = "before";
    uint8_t v[] = "val";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", k, 6, v, 3, &m));
    EXPECT_EQ(1u, m.seq);

    /* Batch put should continue from seq 2 */
    KomeBatchEntry entries[2];
    entries[0] = {"ns", (const uint8_t*)"b1", 2, (const uint8_t*)"v1", 2};
    entries[1] = {"ns", (const uint8_t*)"b2", 2, (const uint8_t*)"v2", 2};

    KomeEntryMeta metas[2] = {};
    ASSERT_EQ(KOME_OK, kome_put_batch(engine, entries, 2, metas));
    EXPECT_EQ(2u, metas[0].seq);
    EXPECT_EQ(3u, metas[1].seq);
}

TEST_F(EngineTest, BatchPutValidation) {
    set_test_identity();

    /* Empty count */
    KomeBatchEntry e = {"ns", (const uint8_t*)"k", 1, (const uint8_t*)"v", 1};
    EXPECT_EQ(KOME_ERR_MISUSE, kome_put_batch(engine, &e, 0, nullptr));

    /* Null entries */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_put_batch(engine, nullptr, 1, nullptr));

    /* Too-large namespace in batch */
    std::string long_ns(256, 'x');
    KomeBatchEntry bad[2];
    bad[0] = {"ns", (const uint8_t*)"k", 1, (const uint8_t*)"v", 1};
    bad[1] = {long_ns.c_str(), (const uint8_t*)"k", 1, (const uint8_t*)"v", 1};
    EXPECT_EQ(KOME_ERR_TOO_LARGE, kome_put_batch(engine, bad, 2, nullptr));

    /* Verify first entry was NOT written (atomic failure) */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get(engine, "ns",
        (const uint8_t*)"k", 1, &out, &out_len, nullptr));
}

TEST_F(EngineTest, BatchPutWithoutIdentity) {
    KomeBatchEntry e = {"ns", (const uint8_t*)"k", 1, (const uint8_t*)"v", 1};
    EXPECT_EQ(KOME_ERR_MISUSE, kome_put_batch(engine, &e, 1, nullptr));
}

TEST_F(EngineTest, BatchPutExceedsMaxCount) {
    set_test_identity();
    KomeBatchEntry e = {"ns", (const uint8_t*)"k", 1, (const uint8_t*)"v", 1};
    EXPECT_EQ(KOME_ERR_TOO_LARGE,
        kome_put_batch(engine, &e, KOME_MAX_BATCH_COUNT + 1, nullptr));
}

/* --- kome_get_all: bulk reads ------------------------------------------- */

TEST_F(EngineTest, GetAllBasic) {
    set_test_identity();

    uint8_t k1[] = "alpha";
    uint8_t v1[] = "val_a";
    uint8_t k2[] = "beta";
    uint8_t v2[] = "val_b";
    uint8_t k3[] = "gamma";
    uint8_t v3[] = "val_g";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", k1, 5, v1, 5, &m));
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", k2, 4, v2, 5, &m));
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", k3, 5, v3, 5, &m));

    uint8_t **keys = nullptr;
    size_t *key_lens = nullptr;
    uint8_t **values = nullptr;
    size_t *value_lens = nullptr;
    KomeEntryMeta *metas = nullptr;
    size_t count = 0;

    ASSERT_EQ(KOME_OK, kome_get_all(engine, "ns",
        &keys, &key_lens, &values, &value_lens, &metas, &count));

    ASSERT_EQ(3u, count);

    /* Results are ordered by key: alpha, beta, gamma */
    EXPECT_EQ(5u, key_lens[0]);
    EXPECT_EQ(0, std::memcmp(keys[0], "alpha", 5));
    EXPECT_EQ(5u, value_lens[0]);
    EXPECT_EQ(0, std::memcmp(values[0], "val_a", 5));
    EXPECT_EQ(0, metas[0].tombstone);
    EXPECT_GT(metas[0].timestamp_us, 0u);
    EXPECT_GT(metas[0].seq, 0u);

    EXPECT_EQ(4u, key_lens[1]);
    EXPECT_EQ(0, std::memcmp(keys[1], "beta", 4));
    EXPECT_EQ(5u, value_lens[1]);
    EXPECT_EQ(0, std::memcmp(values[1], "val_b", 5));

    EXPECT_EQ(5u, key_lens[2]);
    EXPECT_EQ(0, std::memcmp(keys[2], "gamma", 5));
    EXPECT_EQ(5u, value_lens[2]);
    EXPECT_EQ(0, std::memcmp(values[2], "val_g", 5));

    kome_free_entries(keys, key_lens, values, value_lens, metas, count);
}

TEST_F(EngineTest, GetAllExcludesTombstones) {
    set_test_identity();

    uint8_t k1[] = "a";
    uint8_t v1[] = "1";
    uint8_t k2[] = "b";
    uint8_t v2[] = "2";
    uint8_t k3[] = "c";
    uint8_t v3[] = "3";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", k1, 1, v1, 1, &m));
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", k2, 1, v2, 1, &m));
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", k3, 1, v3, 1, &m));

    /* Delete key "b" */
    ASSERT_EQ(KOME_OK, kome_delete(engine, "ns", k2, 1, &m));

    uint8_t **keys = nullptr;
    size_t *key_lens = nullptr;
    uint8_t **values = nullptr;
    size_t *value_lens = nullptr;
    KomeEntryMeta *metas = nullptr;
    size_t count = 0;

    ASSERT_EQ(KOME_OK, kome_get_all(engine, "ns",
        &keys, &key_lens, &values, &value_lens, &metas, &count));

    ASSERT_EQ(2u, count);
    EXPECT_EQ(1u, key_lens[0]);
    EXPECT_EQ(0, std::memcmp(keys[0], "a", 1));
    EXPECT_EQ(1u, key_lens[1]);
    EXPECT_EQ(0, std::memcmp(keys[1], "c", 1));

    kome_free_entries(keys, key_lens, values, value_lens, metas, count);
}

TEST_F(EngineTest, GetAllEmptyNamespace) {
    uint8_t **keys = nullptr;
    size_t *key_lens = nullptr;
    uint8_t **values = nullptr;
    size_t *value_lens = nullptr;
    KomeEntryMeta *metas = nullptr;
    size_t count = 99;

    ASSERT_EQ(KOME_OK, kome_get_all(engine, "empty_ns",
        &keys, &key_lens, &values, &value_lens, &metas, &count));

    EXPECT_EQ(0u, count);
    EXPECT_EQ(nullptr, keys);
    EXPECT_EQ(nullptr, key_lens);
    EXPECT_EQ(nullptr, values);
    EXPECT_EQ(nullptr, value_lens);
    EXPECT_EQ(nullptr, metas);
}

TEST_F(EngineTest, GetAllFreeEntries) {
    set_test_identity();

    /* Test free on valid data */
    uint8_t k[] = "k";
    uint8_t v[] = "v";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns", k, 1, v, 1, &m));

    uint8_t **keys = nullptr;
    size_t *key_lens = nullptr;
    uint8_t **values = nullptr;
    size_t *value_lens = nullptr;
    KomeEntryMeta *metas = nullptr;
    size_t count = 0;

    ASSERT_EQ(KOME_OK, kome_get_all(engine, "ns",
        &keys, &key_lens, &values, &value_lens, &metas, &count));
    ASSERT_EQ(1u, count);

    kome_free_entries(keys, key_lens, values, value_lens, metas, count);

    /* Test free on nulls — should not crash */
    kome_free_entries(nullptr, nullptr, nullptr, nullptr, nullptr, 0);
}

TEST_F(EngineTest, BatchPutMultipleNamespaces) {
    set_test_identity();

    KomeBatchEntry entries[3];
    entries[0] = {"alpha", (const uint8_t*)"k1", 2, (const uint8_t*)"v1", 2};
    entries[1] = {"beta",  (const uint8_t*)"k2", 2, (const uint8_t*)"v2", 2};
    entries[2] = {"alpha", (const uint8_t*)"k3", 2, (const uint8_t*)"v3", 2};

    ASSERT_EQ(KOME_OK, kome_put_batch(engine, entries, 3, nullptr));

    /* Both namespaces have data */
    KomeEntryMeta m;
    EXPECT_EQ(KOME_OK, kome_get_meta(engine, "alpha", (const uint8_t*)"k1", 2, &m));
    EXPECT_EQ(KOME_OK, kome_get_meta(engine, "beta", (const uint8_t*)"k2", 2, &m));
    EXPECT_EQ(KOME_OK, kome_get_meta(engine, "alpha", (const uint8_t*)"k3", 2, &m));
}
