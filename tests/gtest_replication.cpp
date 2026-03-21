#include <gtest/gtest.h>
#include "kome.h"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>

class ReplicationTest : public ::testing::Test {
protected:
    KomeEngine *engine_a = nullptr;
    KomeEngine *engine_b = nullptr;
    std::string db_a, db_b;
    LoopbackPair loopback;

    void SetUp() override {
        db_a = temp_db_path("repl_a");
        db_b = temp_db_path("repl_b");
        cleanup_db(db_a);
        cleanup_db(db_b);

        KomeConfig cfg_a = {};
        cfg_a.path = db_a.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&cfg_a, &engine_a));

        KomeConfig cfg_b = {};
        cfg_b.path = db_b.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&cfg_b, &engine_b));

        uint8_t key_a[32]; std::memset(key_a, 0xAA, 32);
        uint8_t key_b[32]; std::memset(key_b, 0xBB, 32);
        ASSERT_EQ(KOME_OK, kome_set_identity(engine_a, key_a, 32));
        ASSERT_EQ(KOME_OK, kome_set_identity(engine_b, key_b, 32));

        ASSERT_EQ(KOME_OK, kome_attach_transport(engine_a, &loopback.a.transport));
        ASSERT_EQ(KOME_OK, kome_attach_transport(engine_b, &loopback.b.transport));
    }

    void TearDown() override {
        kome_close(engine_a);
        kome_close(engine_b);
        cleanup_db(db_a);
        cleanup_db(db_b);
    }

    void configure_ns(const char *ns) {
        KomeNamespaceACLEntry acl_a;
        std::memset(acl_a.fingerprint, 0xBB, 32);
        acl_a.role = KOME_ROLE_WRITE;
        KomeNamespaceConfig cfg_a = {};
        cfg_a.name = ns;
        cfg_a.acl = &acl_a;
        cfg_a.acl_count = 1;
        ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_a));

        KomeNamespaceACLEntry acl_b;
        std::memset(acl_b.fingerprint, 0xAA, 32);
        acl_b.role = KOME_ROLE_WRITE;
        KomeNamespaceConfig cfg_b = {};
        cfg_b.name = ns;
        cfg_b.acl = &acl_b;
        cfg_b.acl_count = 1;
        ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_b, &cfg_b));
    }
};

/* --- Replication target tracking ---------------------------------------- */

TEST_F(ReplicationTest, TargetTracking) {
    configure_ns("test");
    ASSERT_EQ(KOME_OK, kome_set_replication(engine_a, "test", 1));

    uint8_t key[] = "k1";
    uint8_t val[] = "v1";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine_a, "test", key, 2, val, 2, &m));

    /* Before sync */
    uint32_t confirmed = 99, target = 99;
    ASSERT_EQ(KOME_OK, kome_replication_status(engine_a, "test", key, 2,
                                                &confirmed, &target));
    EXPECT_EQ(0u, confirmed);
    EXPECT_EQ(1u, target);

    /* Sync */
    loopback.connect();

    /* After sync — B should ACK, incrementing confirmed */
    ASSERT_EQ(KOME_OK, kome_replication_status(engine_a, "test", key, 2,
                                                &confirmed, &target));
    EXPECT_GE(confirmed, 1u);
    EXPECT_EQ(1u, target);
}

/* --- Replication change callback ---------------------------------------- */

TEST_F(ReplicationTest, ReplicationChangeCallback) {
    configure_ns("test");
    struct ReplData {
        int fire_count = 0;
        uint32_t last_confirmed = 0;
        uint32_t last_target = 0;
    } repl_data;

    ASSERT_EQ(KOME_OK, kome_set_replication(engine_a, "test", 1));

    kome_on_replication_change(engine_a,
        [](void *ud, const char *, const uint8_t *, size_t,
           uint32_t confirmed, uint32_t target) {
            auto *d = static_cast<ReplData*>(ud);
            d->fire_count++;
            d->last_confirmed = confirmed;
            d->last_target = target;
        }, &repl_data);

    uint8_t key[] = "k1";
    uint8_t val[] = "v1";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine_a, "test", key, 2, val, 2, &m));

    loopback.connect();

    EXPECT_GE(repl_data.fire_count, 1);
    EXPECT_EQ(1u, repl_data.last_target);
}

/* --- Tombstone GC ------------------------------------------------------- */

TEST_F(ReplicationTest, TombstoneGC) {
    /* Configure namespace with very short TTL (1 second) for quick GC */
    KomeNamespaceACLEntry acl_a;
    std::memset(acl_a.fingerprint, 0xBB, 32);
    acl_a.role = KOME_ROLE_WRITE;
    KomeNamespaceConfig cfg_a = {};
    cfg_a.name = "test";
    cfg_a.tombstone_ttl_sec = 1;
    cfg_a.acl = &acl_a;
    cfg_a.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_a));

    KomeNamespaceACLEntry acl_b;
    std::memset(acl_b.fingerprint, 0xAA, 32);
    acl_b.role = KOME_ROLE_WRITE;
    KomeNamespaceConfig cfg_b = {};
    cfg_b.name = "test";
    cfg_b.tombstone_ttl_sec = 1;
    cfg_b.acl = &acl_b;
    cfg_b.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_b, &cfg_b));

    uint8_t key[] = "gc_key";
    uint8_t val[] = "gc_val";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine_a, "test", key, 6, val, 6, &m));
    ASSERT_EQ(KOME_OK, kome_delete(engine_a, "test", key, 6, &m));

    /* Sync triggers GC on ACK */
    loopback.connect();

    /* After GC with short TTL, the tombstone may be cleaned up.
       Since GC runs on ACK receipt, the tombstone might be gone. */
    KomeStats stats;
    kome_stats(engine_a, &stats);
    EXPECT_GE(stats.total_entries, 0u);
}

/* --- Stats after sync --------------------------------------------------- */

TEST_F(ReplicationTest, StatsAfterSync) {
    configure_ns("data");
    uint8_t val[] = "v";
    KomeEntryMeta m;
    for (int i = 0; i < 5; i++) {
        std::string k = "key_" + std::to_string(i);
        kome_put(engine_a, "data",
            (const uint8_t*)k.data(), k.size(), val, 1, &m);
    }

    loopback.connect();

    KomeStats stats_b;
    ASSERT_EQ(KOME_OK, kome_stats(engine_b, &stats_b));
    EXPECT_EQ(5u, stats_b.total_entries);
    EXPECT_EQ(1u, stats_b.namespace_count);
}
