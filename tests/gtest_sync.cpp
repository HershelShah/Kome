#include <gtest/gtest.h>
#include "kome.h"
#include "kome_test_helpers.hpp"
#include "kome_wire.hpp"
#include "kome_util.hpp"
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

    /* Configure a namespace for bidirectional WRITE between A and B */
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
    configure_ns("test");
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
    configure_ns("test");
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
    configure_ns("test");
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
    configure_ns("test");
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
    configure_ns("test");
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
    configure_ns("test");
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
    configure_ns("events");
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
    configure_ns("dummy");  /* Need at least one configured ns for sync to proceed */
    int done_count = 0;
    kome_on_sync_done(engine_b, [](void *ud, const uint8_t *) {
        (*static_cast<int*>(ud))++;
    }, &done_count);

    loopback.connect();
    EXPECT_GE(done_count, 1);
}

/* --- Batch writes sync -------------------------------------------------- */

TEST_F(SyncTest, BatchLivePush) {
    configure_ns("test");
    /* Connect first (triggers sync with empty state, enters live mode) */
    loopback.connect();

    /* Batch write on A — should be pushed live to B as BATCH_ENTRY */
    KomeBatchEntry entries[3];
    entries[0] = {"test", (const uint8_t*)"bk1", 3, (const uint8_t*)"bv1", 3};
    entries[1] = {"test", (const uint8_t*)"bk2", 3, (const uint8_t*)"bv2", 3};
    entries[2] = {"test", (const uint8_t*)"bk3", 3, (const uint8_t*)"bv3", 3};

    KomeEntryMeta metas[3] = {};
    ASSERT_EQ(KOME_OK, kome_put_batch(engine_a, entries, 3, metas));

    /* B should have all entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "bk" + std::to_string(i + 1);
        KomeEntryMeta meta_b;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "test",
            (const uint8_t*)key.data(), key.size(), &meta_b))
            << "B missing batch key: " << key;
        EXPECT_EQ(metas[i].seq, meta_b.seq);
    }
}

TEST_F(SyncTest, BatchSyncOnConnect) {
    configure_ns("data");
    /* Batch write on A before connecting */
    KomeBatchEntry entries[2];
    entries[0] = {"data", (const uint8_t*)"x1", 2, (const uint8_t*)"val1", 4};
    entries[1] = {"data", (const uint8_t*)"x2", 2, (const uint8_t*)"val2", 4};

    ASSERT_EQ(KOME_OK, kome_put_batch(engine_a, entries, 2, nullptr));

    /* Connect — B should get entries during initial sync */
    loopback.connect();

    for (int i = 0; i < 2; i++) {
        std::string key = "x" + std::to_string(i + 1);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "data",
            (const uint8_t*)key.data(), key.size(), &meta));
    }
}

TEST_F(SyncTest, BatchRemoteChangeCallbackOrder) {
    configure_ns("ns");
    struct CallbackData {
        std::vector<uint64_t> seqs;
    } cb_data;

    kome_on_remote_change(engine_b,
        [](void *ud, const char *, const uint8_t *, size_t,
           const uint8_t *, size_t, const KomeEntryMeta *meta) {
            auto *d = static_cast<CallbackData*>(ud);
            d->seqs.push_back(meta->seq);
        }, &cb_data);

    /* Connect first */
    loopback.connect();

    /* Batch write on A */
    KomeBatchEntry entries[3];
    entries[0] = {"ns", (const uint8_t*)"a", 1, (const uint8_t*)"1", 1};
    entries[1] = {"ns", (const uint8_t*)"b", 1, (const uint8_t*)"2", 1};
    entries[2] = {"ns", (const uint8_t*)"c", 1, (const uint8_t*)"3", 1};

    KomeEntryMeta metas[3] = {};
    ASSERT_EQ(KOME_OK, kome_put_batch(engine_a, entries, 3, metas));

    /* Callbacks should fire once per entry in sequence order */
    ASSERT_EQ(3u, cb_data.seqs.size());
    EXPECT_EQ(metas[0].seq, cb_data.seqs[0]);
    EXPECT_EQ(metas[1].seq, cb_data.seqs[1]);
    EXPECT_EQ(metas[2].seq, cb_data.seqs[2]);
}

/* --- Per-namespace change callback -------------------------------------- */

TEST_F(SyncTest, PerNamespaceChangeCallback) {
    configure_ns("ns_a");
    configure_ns("ns_b");

    struct CallbackData {
        int count = 0;
        std::string last_ns;
    } cb_data;

    kome_on_remote_change_ns(engine_b, "ns_a",
        [](void *ud, const char *ns, const uint8_t *, size_t,
           const uint8_t *, size_t, const KomeEntryMeta *) {
            auto *d = static_cast<CallbackData*>(ud);
            d->count++;
            d->last_ns = ns;
        }, &cb_data);

    /* Write to both namespaces on A */
    replicate_n(engine_a, "ns_a", 3);
    replicate_n(engine_a, "ns_b", 2);

    loopback.connect();

    /* The per-namespace callback should only fire for ns_a */
    EXPECT_EQ(3, cb_data.count);
    EXPECT_EQ("ns_a", cb_data.last_ns);
}

TEST_F(SyncTest, PerNamespaceAndGlobalCallback) {
    configure_ns("ns_a");
    configure_ns("ns_b");

    struct GlobalData {
        int count = 0;
    } global_data;

    struct NsData {
        int count = 0;
        std::string last_ns;
    } ns_data;

    kome_on_remote_change(engine_b,
        [](void *ud, const char *, const uint8_t *, size_t,
           const uint8_t *, size_t, const KomeEntryMeta *) {
            auto *d = static_cast<GlobalData*>(ud);
            d->count++;
        }, &global_data);

    kome_on_remote_change_ns(engine_b, "ns_a",
        [](void *ud, const char *ns, const uint8_t *, size_t,
           const uint8_t *, size_t, const KomeEntryMeta *) {
            auto *d = static_cast<NsData*>(ud);
            d->count++;
            d->last_ns = ns;
        }, &ns_data);

    replicate_n(engine_a, "ns_a", 2);
    replicate_n(engine_a, "ns_b", 3);

    loopback.connect();

    /* Global callback fires for all 5 writes */
    EXPECT_EQ(5, global_data.count);
    /* Per-namespace callback fires only for ns_a (2 writes) */
    EXPECT_EQ(2, ns_data.count);
    EXPECT_EQ("ns_a", ns_data.last_ns);
}

TEST_F(SyncTest, UnregisterPerNamespaceCallback) {
    configure_ns("ns_a");

    struct CallbackData {
        int count = 0;
    } cb_data;

    kome_on_remote_change_ns(engine_b, "ns_a",
        [](void *ud, const char *, const uint8_t *, size_t,
           const uint8_t *, size_t, const KomeEntryMeta *) {
            auto *d = static_cast<CallbackData*>(ud);
            d->count++;
        }, &cb_data);

    /* Unregister by passing NULL callback */
    kome_on_remote_change_ns(engine_b, "ns_a", nullptr, nullptr);

    replicate_n(engine_a, "ns_a", 3);

    loopback.connect();

    /* Callback should not have fired */
    EXPECT_EQ(0, cb_data.count);
}

TEST_F(SyncTest, BatchMixedWithSingleWrites) {
    configure_ns("mix");
    loopback.connect();

    /* Single write */
    uint8_t k1[] = "single";
    uint8_t v1[] = "val";
    KomeEntryMeta m1;
    ASSERT_EQ(KOME_OK, kome_put(engine_a, "mix", k1, 6, v1, 3, &m1));

    /* Batch write */
    KomeBatchEntry entries[2];
    entries[0] = {"mix", (const uint8_t*)"bat1", 4, (const uint8_t*)"bv1", 3};
    entries[1] = {"mix", (const uint8_t*)"bat2", 4, (const uint8_t*)"bv2", 3};
    KomeEntryMeta metas[2] = {};
    ASSERT_EQ(KOME_OK, kome_put_batch(engine_a, entries, 2, metas));

    /* Another single write */
    uint8_t k2[] = "after";
    uint8_t v2[] = "val";
    KomeEntryMeta m2;
    ASSERT_EQ(KOME_OK, kome_put(engine_a, "mix", k2, 5, v2, 3, &m2));

    /* Sequence numbers should be continuous */
    EXPECT_EQ(1u, m1.seq);
    EXPECT_EQ(2u, metas[0].seq);
    EXPECT_EQ(3u, metas[1].seq);
    EXPECT_EQ(4u, m2.seq);

    /* B should have everything */
    EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "mix", k1, 6, &m1));
    EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "mix", (const uint8_t*)"bat1", 4, &m1));
    EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "mix", (const uint8_t*)"bat2", 4, &m1));
    EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "mix", k2, 5, &m1));
}

/* --- Non-blocking kome_sync_with tests (issue #10) ---------------------- */

TEST_F(SyncTest, SyncWithReturnsImmediately) {
    configure_ns("test");
    replicate_n(engine_a, "test", 5);

    /* Connect peers so transport is wired up */
    loopback.connect();

    /* kome_sync_with should return KOME_OK without blocking.
       Since connect() already initiated sync, this is a no-op on
       an already-syncing/live peer, which still must return KOME_OK. */
    uint8_t peer_b_fp[32];
    std::memset(peer_b_fp, 0xBB, 32);
    auto start = std::chrono::steady_clock::now();
    KomeError err = kome_sync_with(engine_a, peer_b_fp);
    auto elapsed = std::chrono::steady_clock::now() - start;

    EXPECT_EQ(KOME_OK, err);
    /* Must return in well under 1 second — synchronous loopback is instant */
    EXPECT_LT(std::chrono::duration_cast<std::chrono::milliseconds>(elapsed).count(), 1000);
}

TEST_F(SyncTest, SyncWithFiresSyncDoneCallback) {
    configure_ns("test");
    replicate_n(engine_a, "test", 3);

    /* Register on_sync_done on both engines */
    int done_count_a = 0;
    int done_count_b = 0;
    kome_on_sync_done(engine_a, [](void *ud, const uint8_t *) {
        (*static_cast<int*>(ud))++;
    }, &done_count_a);
    kome_on_sync_done(engine_b, [](void *ud, const uint8_t *) {
        (*static_cast<int*>(ud))++;
    }, &done_count_b);

    /* Connect — this triggers bidirectional sync via on_peer_connected
       which calls initiate_sync internally.  The loopback transport is
       synchronous so sync completes inside connect(). */
    loopback.connect();

    /* Both sides should have received on_sync_done at least once */
    EXPECT_GE(done_count_a, 1) << "Engine A should fire on_sync_done";
    EXPECT_GE(done_count_b, 1) << "Engine B should fire on_sync_done";

    /* Verify data actually arrived */
    for (int i = 0; i < 3; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "test",
            (const uint8_t*)key.data(), key.size(), &meta));
    }
}

TEST_F(SyncTest, SyncWithAlreadySyncingPeerIsNoop) {
    configure_ns("test");
    replicate_n(engine_a, "test", 5);

    /* Connect — triggers sync and enters live mode */
    loopback.connect();

    /* Verify the first sync completed */
    for (int i = 0; i < 5; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "test",
            (const uint8_t*)key.data(), key.size(), &meta));
    }

    /* Register a fresh callback counter */
    int done_count = 0;
    kome_on_sync_done(engine_a, [](void *ud, const uint8_t *) {
        (*static_cast<int*>(ud))++;
    }, &done_count);

    /* Call kome_sync_with on a peer that is already in live mode — should be a no-op */
    uint8_t peer_b_fp[32];
    std::memset(peer_b_fp, 0xBB, 32);
    EXPECT_EQ(KOME_OK, kome_sync_with(engine_a, peer_b_fp));

    /* The callback should NOT fire again since it was a no-op */
    EXPECT_EQ(0, done_count) << "Duplicate sync_with on a live peer should not re-trigger sync";
}

TEST_F(SyncTest, SyncWithNullArgs) {
    /* NULL engine */
    uint8_t fp[32] = {};
    EXPECT_EQ(KOME_ERR_MISUSE, kome_sync_with(nullptr, fp));
    /* NULL peer_fp */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_sync_with(engine_a, nullptr));
}

TEST_F(SyncTest, SyncWithNoTransport) {
    /* Create a bare engine without transport attached */
    std::string db_c = temp_db_path("sync_c");
    cleanup_db(db_c);

    KomeConfig cfg = {};
    cfg.path = db_c.c_str();
    KomeEngine *engine_c = nullptr;
    ASSERT_EQ(KOME_OK, kome_open(&cfg, &engine_c));

    uint8_t key_c[32]; std::memset(key_c, 0xCC, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine_c, key_c, 32));

    /* No transport attached — sync_with should return KOME_ERR_MISUSE */
    uint8_t fp[32] = {};
    EXPECT_EQ(KOME_ERR_MISUSE, kome_sync_with(engine_c, fp));

    kome_close(engine_c);
    cleanup_db(db_c);
}

/* --- Far-future timestamp rejection ------------------------------------ */

/* Helper: build a SyncEntry and inject it as a LIVE_ENTRY from A to B */
static void inject_live_entry(LoopbackPair &loopback,
                              const char *ns, const char *key_str,
                              const char *val_str, uint64_t ts_us) {
    using namespace kome;
    SyncEntry se;
    se.ns = ns;
    se.key.assign((const uint8_t*)key_str,
                  (const uint8_t*)key_str + std::strlen(key_str));
    se.value.assign((const uint8_t*)val_str,
                    (const uint8_t*)val_str + std::strlen(val_str));
    se.timestamp_us = ts_us;
    std::memset(se.author, 0xAA, 32);  /* A's fingerprint */
    se.seq = ts_us;                     /* unique-enough sequence number */
    sha256(se.value.data(), se.value.size(), se.hash);
    se.tombstone = 0;
    /* Set a non-zero placeholder signature so the entry passes the
       signature_is_nonzero check in apply_remote_entry. */
    std::memset(se.signature, 0xDD, 64);

    auto wire = encode_live_entry(se);
    ASSERT_FALSE(wire.empty());

    /* Deliver to B's recv callback as if A sent it */
    loopback.b.recv_cb(loopback.b.recv_ud, loopback.a.fingerprint,
                       wire.data(), wire.size());
}

TEST_F(SyncTest, RejectFarFutureTimestamp) {
    configure_ns("ts");
    loopback.connect();

    /* 48 hours in the future — should be rejected */
    uint64_t far_future = kome::timestamp_us() + 48ULL * 3600 * 1000000;
    inject_live_entry(loopback, "ts", "future_key", "evil", far_future);

    KomeEntryMeta meta;
    EXPECT_EQ(KOME_ERR_NOT_FOUND,
              kome_get_meta(engine_b, "ts",
                            (const uint8_t*)"future_key", 10, &meta))
        << "Entry 48h in future should be rejected";
}

TEST_F(SyncTest, AcceptNearFutureTimestamp) {
    configure_ns("ts");
    loopback.connect();

    /* 12 hours in the future — within 24h tolerance, should be accepted */
    uint64_t near_future = kome::timestamp_us() + 12ULL * 3600 * 1000000;
    inject_live_entry(loopback, "ts", "near_key", "ok", near_future);

    KomeEntryMeta meta;
    EXPECT_EQ(KOME_OK,
              kome_get_meta(engine_b, "ts",
                            (const uint8_t*)"near_key", 8, &meta))
        << "Entry 12h in future should be accepted";
    EXPECT_EQ(near_future, meta.timestamp_us);
}

TEST_F(SyncTest, AcceptCurrentTimestamp) {
    configure_ns("ts");
    loopback.connect();

    /* Current timestamp — should be accepted */
    uint64_t now = kome::timestamp_us();
    inject_live_entry(loopback, "ts", "now_key", "val", now);

    KomeEntryMeta meta;
    EXPECT_EQ(KOME_OK,
              kome_get_meta(engine_b, "ts",
                            (const uint8_t*)"now_key", 7, &meta))
        << "Entry with current timestamp should be accepted";
    EXPECT_EQ(now, meta.timestamp_us);
}

/* --- Rate limiting tests ------------------------------------------------ */

TEST_F(SyncTest, RateLimitDropsExcessEntries) {
    configure_ns("test");

    /* Set very low entry limit on B (receiver): 3 entries/min, generous byte limit */
    ASSERT_EQ(KOME_OK, kome_set_peer_limits(engine_b, 50ULL * 1024 * 1024, 3));

    /* Write 10 entries on A before connecting */
    replicate_n(engine_a, "test", 10);

    /* Connect — sync will push entries from A to B */
    loopback.connect();

    /* B should have at most 3 entries (rate limit) */
    int found = 0;
    for (int i = 0; i < 10; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta;
        if (kome_get_meta(engine_b, "test",
                (const uint8_t*)key.data(), key.size(), &meta) == KOME_OK)
            found++;
    }
    EXPECT_EQ(3, found) << "Expected exactly 3 entries to pass rate limit, got " << found;
}

TEST_F(SyncTest, RateLimitDropsExcessBytes) {
    configure_ns("test");

    /* Set very low byte limit on B: 100 bytes/min, generous entry limit */
    ASSERT_EQ(KOME_OK, kome_set_peer_limits(engine_b, 100, 10000));

    /* Write entries with ~50 bytes each — only ~2 should fit in 100 bytes */
    for (int i = 0; i < 10; i++) {
        std::string key = "key_" + std::to_string(i);
        std::string val(50, 'x');  /* 50-byte value */
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "test",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* Connect */
    loopback.connect();

    /* Count how many made it through */
    int found = 0;
    for (int i = 0; i < 10; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta;
        if (kome_get_meta(engine_b, "test",
                (const uint8_t*)key.data(), key.size(), &meta) == KOME_OK)
            found++;
    }
    /* With 50 bytes per entry and 100 byte limit, exactly 2 should pass */
    EXPECT_EQ(2, found) << "Expected 2 entries to pass byte rate limit, got " << found;
}

TEST_F(SyncTest, DefaultLimitsAreGenerous) {
    configure_ns("test");

    /* Use default limits (50 MiB/min, 1000 entries/min) — 100 entries should be fine */
    replicate_n(engine_a, "test", 100);

    /* Connect */
    loopback.connect();

    /* All 100 entries should make it through */
    int found = 0;
    for (int i = 0; i < 100; i++) {
        std::string key = "key_" + std::to_string(i);
        KomeEntryMeta meta;
        if (kome_get_meta(engine_b, "test",
                (const uint8_t*)key.data(), key.size(), &meta) == KOME_OK)
            found++;
    }
    EXPECT_EQ(100, found);
}

TEST_F(SyncTest, RateLimitNullEngine) {
    /* Calling with null engine should return KOME_ERR_MISUSE */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_set_peer_limits(nullptr, 100, 100));
}
