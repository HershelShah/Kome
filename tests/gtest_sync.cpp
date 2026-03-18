#include <gtest/gtest.h>
#include "kome.h"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>
#include <vector>
#include <thread>
#include <chrono>

class SyncTest : public ::testing::Test {
protected:
    KomeEngine *engine_a = nullptr;
    KomeEngine *engine_b = nullptr;
    std::string db_a, db_b;
    LoopbackPair loopback;

    void SetUp() override {
        db_a = temp_db_path("sync_a");
        db_b = temp_db_path("sync_b");
        cleanup_db(db_a);
        cleanup_db(db_b);

        KomeConfig cfg_a = {};
        cfg_a.path = db_a.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&cfg_a, &engine_a));

        KomeConfig cfg_b = {};
        cfg_b.path = db_b.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&cfg_b, &engine_b));

        /* Set identities */
        uint8_t key_a[32]; std::memset(key_a, 0xAA, 32);
        uint8_t key_b[32]; std::memset(key_b, 0xBB, 32);
        ASSERT_EQ(KOME_OK, kome_set_identity(engine_a, key_a, 32));
        ASSERT_EQ(KOME_OK, kome_set_identity(engine_b, key_b, 32));

        /* Attach transports */
        ASSERT_EQ(KOME_OK, kome_attach_transport(engine_a, &loopback.a.transport));
        ASSERT_EQ(KOME_OK, kome_attach_transport(engine_b, &loopback.b.transport));
    }

    void TearDown() override {
        kome_close(engine_a);
        kome_close(engine_b);
        cleanup_db(db_a);
        cleanup_db(db_b);
    }

    void replicate_n(KomeEngine *e, const char *ns, int n) {
        for (int i = 0; i < n; i++) {
            std::string key = "key_" + std::to_string(i);
            std::string val = "val_" + std::to_string(i);
            KomeEntryMeta m;
            ASSERT_EQ(KOME_OK, kome_put(e, ns,
                (const uint8_t*)key.data(), key.size(),
                (const uint8_t*)val.data(), val.size(), &m));
        }
    }
};

/* --- Basic sync: A writes, B connects, B gets everything ---------------- */

TEST_F(SyncTest, BasicSync) {
    replicate_n(engine_a, "test", 10);

    /* Connect — triggers sync */
    loopback.connect();

    /* Verify B has all entries */
    for (int i = 0; i < 10; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "test",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "Missing key: " << key;
    }
}

/* --- Bidirectional sync: A has 0-4, B has 5-9, both get all ------------- */

TEST_F(SyncTest, BidirectionalSync) {
    /* A writes keys 0-4 */
    for (int i = 0; i < 5; i++) {
        std::string key = "key_" + std::to_string(i);
        std::string val = "val_a_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "test",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* B writes keys 5-9 */
    for (int i = 5; i < 10; i++) {
        std::string key = "key_" + std::to_string(i);
        std::string val = "val_b_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_b, "test",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* Connect */
    loopback.connect();

    /* Both should have all 10 keys */
    for (int i = 0; i < 10; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta_a, meta_b;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_a, "test",
            (const uint8_t*)key.data(), key.size(), &meta_a))
            << "A missing: " << key;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "test",
            (const uint8_t*)key.data(), key.size(), &meta_b))
            << "B missing: " << key;
    }
}

/* --- Incremental sync: sync, write more, sync again --------------------- */

TEST_F(SyncTest, IncrementalSync) {
    replicate_n(engine_a, "test", 5);
    loopback.connect();

    /* Verify first batch */
    for (int i = 0; i < 5; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "test",
            (const uint8_t*)key.data(), key.size(), &meta));
    }

    /* Disconnect and write more */
    loopback.disconnect();

    for (int i = 5; i < 10; i++) {
        std::string key = "key_" + std::to_string(i);
        std::string val = "val_" + std::to_string(i);
        KomeEntryMeta m;
        kome_put(engine_a, "test",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m);
    }

    /* Reconnect */
    loopback.connect();

    /* Verify second batch */
    for (int i = 5; i < 10; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "test",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "Missing after incremental sync: " << key;
    }
}

/* --- Tombstone propagation ---------------------------------------------- */

TEST_F(SyncTest, TombstoneSync) {
    /* A writes and deletes */
    uint8_t key[] = "del_key";
    uint8_t val[] = "some_value";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine_a, "test", key, 7, val, 10, &m));
    ASSERT_EQ(KOME_OK, kome_delete(engine_a, "test", key, 7, &m));

    /* Connect */
    loopback.connect();

    /* B should see the tombstone */
    KomeEntryMeta meta_b;
    ASSERT_EQ(KOME_OK, kome_get_meta(engine_b, "test", key, 7, &meta_b));
    EXPECT_EQ(1, meta_b.tombstone);
}

/* --- Live mode: real-time push after sync ------------------------------- */

TEST_F(SyncTest, LiveModePush) {
    /* Connect first (triggers sync with empty state) */
    loopback.connect();

    /* Now write on A — should be pushed live to B */
    uint8_t key[] = "live_key";
    uint8_t val[] = "live_val";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine_a, "test", key, 8, val, 8, &m));

    /* B should have it */
    KomeEntryMeta meta_b;
    EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "test", key, 8, &meta_b));
}

/* --- Conflict during sync (LWW) ---------------------------------------- */

TEST_F(SyncTest, ConflictDuringSync) {
    /* Both write the same key with different values */
    uint8_t key[] = "conflict_key";
    uint8_t val_a[] = "value_a";
    uint8_t val_b[] = "value_b";

    /* A writes first (lower timestamp) */
    KomeEntryMeta meta_a;
    ASSERT_EQ(KOME_OK, kome_put(engine_a, "test", key, 12, val_a, 7, &meta_a));

    /* Small delay to ensure different timestamps */
    std::this_thread::sleep_for(std::chrono::milliseconds(2));

    /* B writes second (higher timestamp) */
    KomeEntryMeta meta_b;
    ASSERT_EQ(KOME_OK, kome_put(engine_b, "test", key, 12, val_b, 7, &meta_b));

    /* B's write should have higher timestamp */
    EXPECT_GT(meta_b.timestamp_us, meta_a.timestamp_us);

    /* Connect — sync should resolve conflict via LWW */
    loopback.connect();

    /* Both should agree on the winner (B's value, higher timestamp) */
    KomeEntryMeta final_a, final_b;
    ASSERT_EQ(KOME_OK, kome_get_meta(engine_a, "test", key, 12, &final_a));
    ASSERT_EQ(KOME_OK, kome_get_meta(engine_b, "test", key, 12, &final_b));

    /* Both should have the same timestamp (the winner's) */
    EXPECT_EQ(final_a.timestamp_us, final_b.timestamp_us);
    EXPECT_EQ(meta_b.timestamp_us, final_a.timestamp_us);
}

/* --- on_remote_change callback ------------------------------------------ */

TEST_F(SyncTest, RemoteChangeCallback) {
    struct CallbackData {
        int count = 0;
        std::string last_ns;
    } cb_data;

    kome_on_remote_change(engine_b,
        [](void *ud, const char *ns, const uint8_t *, size_t,
           const uint8_t *, size_t, const KomeEntryMeta *) {
            auto *d = static_cast<CallbackData*>(ud);
            d->count++;
            d->last_ns = ns;
        }, &cb_data);

    replicate_n(engine_a, "events", 3);
    loopback.connect();

    EXPECT_EQ(3, cb_data.count);
    EXPECT_EQ("events", cb_data.last_ns);
}

/* --- on_sync_done callback ---------------------------------------------- */

TEST_F(SyncTest, SyncDoneCallback) {
    int done_count = 0;
    kome_on_sync_done(engine_b, [](void *ud, const uint8_t *) {
        (*static_cast<int*>(ud))++;
    }, &done_count);

    loopback.connect();
    EXPECT_GE(done_count, 1);
}
