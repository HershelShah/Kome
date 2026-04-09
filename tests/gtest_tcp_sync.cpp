/**
 * TCP integration tests.
 *
 * These run the same sync scenarios as the loopback tests but over
 * real localhost TCP sockets with background recv threads. This exercises:
 *   - Message framing (length-prefix over a stream socket)
 *   - Async send/recv concurrency (recv fires on a different thread)
 *   - Kernel socket buffer back-pressure
 *   - Lock ordering under real threading (detectable by TSan)
 */
#include <gtest/gtest.h>
#include "kome.h"
#include "kome_test_helpers.hpp"
#include "tcp_test_transport.hpp"
#include <cstring>
#include <string>
#include <thread>
#include <chrono>
#include <atomic>

class TcpSyncTest : public ::testing::Test {
protected:
    std::string db_a, db_b;
    KomeEngine *ea = nullptr, *eb = nullptr;
    TcpTestNode node_a, node_b;

    void SetUp() override {
        db_a = temp_db_path("tcp_a");
        db_b = temp_db_path("tcp_b");
        cleanup_db(db_a);
        cleanup_db(db_b);

        KomeConfig ca = {}; ca.path = db_a.c_str();
        KomeConfig cb = {}; cb.path = db_b.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&ca, &ea));
        ASSERT_EQ(KOME_OK, kome_open(&cb, &eb));

        /* Set identities */
        uint8_t ka[32], kb[32];
        std::memset(ka, 0xAA, 32);
        std::memset(kb, 0xBB, 32);
        ASSERT_EQ(KOME_OK, kome_set_identity(ea, ka, 32));
        ASSERT_EQ(KOME_OK, kome_set_identity(eb, kb, 32));

        /* Set fingerprints on transport nodes */
        KomeEntryMeta m;
        uint8_t probe[] = "__probe__";
        uint8_t pv[] = "x";
        kome_put(ea, "__sys", probe, 9, pv, 1, &m);
        std::memcpy(node_a.fingerprint, m.author, 32);
        kome_delete(ea, "__sys", probe, 9, nullptr);

        kome_put(eb, "__sys", probe, 9, pv, 1, &m);
        std::memcpy(node_b.fingerprint, m.author, 32);
        kome_delete(eb, "__sys", probe, 9, nullptr);
    }

    void TearDown() override {
        node_a.stop();
        node_b.stop();
        kome_close(ea);
        kome_close(eb);
        cleanup_db(db_a);
        cleanup_db(db_b);
    }

    /* Connect engines over TCP and trigger peer-connected */
    void connect_tcp() {
        tcp_connect_pair(node_a, node_b);
        ASSERT_EQ(KOME_OK, kome_attach_transport(ea, &node_a.transport));
        ASSERT_EQ(KOME_OK, kome_attach_transport(eb, &node_b.transport));
        tcp_fire_connected(node_a, node_b);
        /* Give recv threads time to process the handshake */
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }

    /* Wait until a key appears on a node (for async operations).
       Returns true if found within timeout, false otherwise. */
    bool wait_for_key(KomeEngine *e, const char *ns, const uint8_t *key,
                      size_t key_len, int timeout_ms = 2000) {
        auto deadline = std::chrono::steady_clock::now() +
                        std::chrono::milliseconds(timeout_ms);
        while (std::chrono::steady_clock::now() < deadline) {
            KomeEntryMeta m;
            if (kome_get_meta(e, ns, key, key_len, &m) == KOME_OK)
                return true;
            std::this_thread::sleep_for(std::chrono::milliseconds(10));
        }
        return false;
    }
};

/* ── Basic sync over TCP ─────────────────────────────────────────────── */

TEST_F(TcpSyncTest, BasicRoundTrip) {
    uint8_t key[] = "greeting";
    uint8_t val[] = "hello over TCP";
    ASSERT_EQ(KOME_OK, kome_put(ea, "chat", key, 8, val, 14, nullptr));

    connect_tcp();

    uint8_t *out = nullptr;
    size_t len = 0;
    ASSERT_EQ(KOME_OK, kome_get(eb, "chat", key, 8, &out, &len, nullptr));
    EXPECT_EQ(14u, len);
    EXPECT_EQ(0, std::memcmp(out, "hello over TCP", 14));
    kome_free_value(out);
}

/* ── Bidirectional sync ──────────────────────────────────────────────── */

TEST_F(TcpSyncTest, BidirectionalSync) {
    uint8_t ak[] = "from_a"; uint8_t av[] = "val_a";
    uint8_t bk[] = "from_b"; uint8_t bv[] = "val_b";
    ASSERT_EQ(KOME_OK, kome_put(ea, "shared", ak, 6, av, 5, nullptr));
    ASSERT_EQ(KOME_OK, kome_put(eb, "shared", bk, 6, bv, 5, nullptr));

    connect_tcp();

    KomeEntryMeta m;
    EXPECT_EQ(KOME_OK, kome_get_meta(eb, "shared", ak, 6, &m));
    EXPECT_EQ(KOME_OK, kome_get_meta(ea, "shared", bk, 6, &m));
}

/* ── Live push over TCP ──────────────────────────────────────────────── */

TEST_F(TcpSyncTest, LivePush) {
    connect_tcp();

    /* Write after connection established (live mode) */
    uint8_t key[] = "live_msg";
    uint8_t val[] = "pushed";
    ASSERT_EQ(KOME_OK, kome_put(ea, "ns", key, 8, val, 6, nullptr));

    ASSERT_TRUE(wait_for_key(eb, "ns", key, 8));

    uint8_t *out = nullptr;
    size_t len = 0;
    ASSERT_EQ(KOME_OK, kome_get(eb, "ns", key, 8, &out, &len, nullptr));
    EXPECT_EQ(6u, len);
    EXPECT_EQ(0, std::memcmp(out, "pushed", 6));
    kome_free_value(out);
}

/* ── Bulk sync: many entries over TCP ────────────────────────────────── */

TEST_F(TcpSyncTest, BulkSync) {
    /* Write 100 entries on A */
    for (int i = 0; i < 100; i++) {
        std::string key = "k" + std::to_string(i);
        std::string val = "v" + std::to_string(i);
        ASSERT_EQ(KOME_OK, kome_put(ea, "bulk",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), nullptr));
    }

    connect_tcp();

    /* Wait for the last entry to arrive, then check all */
    std::string last_key = "k99";
    ASSERT_TRUE(wait_for_key(eb, "bulk",
        (const uint8_t*)last_key.data(), last_key.size()));

    for (int i = 0; i < 100; i++) {
        std::string key = "k" + std::to_string(i);
        KomeEntryMeta m;
        EXPECT_EQ(KOME_OK, kome_get_meta(eb, "bulk",
            (const uint8_t*)key.data(), key.size(), &m))
            << "Missing key: " << key;
    }
}

/* ── Conflict resolution over TCP ────────────────────────────────────── */

TEST_F(TcpSyncTest, ConflictResolution) {
    uint8_t key[] = "contested";
    uint8_t av[] = "from_a";
    uint8_t bv[] = "from_b";

    ASSERT_EQ(KOME_OK, kome_put(ea, "ns", key, 9, av, 6, nullptr));
    std::this_thread::sleep_for(std::chrono::milliseconds(2));
    ASSERT_EQ(KOME_OK, kome_put(eb, "ns", key, 9, bv, 6, nullptr));

    connect_tcp();

    /* Both should converge to B's value (later timestamp) */
    uint8_t *out = nullptr;
    size_t len = 0;
    ASSERT_EQ(KOME_OK, kome_get(ea, "ns", key, 9, &out, &len, nullptr));
    EXPECT_EQ(0, std::memcmp(out, "from_b", 6));
    kome_free_value(out);
}

/* ── Delete propagation over TCP ─────────────────────────────────────── */

TEST_F(TcpSyncTest, DeletePropagation) {
    uint8_t key[] = "doomed";
    uint8_t val[] = "temporary";
    ASSERT_EQ(KOME_OK, kome_put(ea, "ns", key, 6, val, 9, nullptr));

    connect_tcp();

    /* B has it */
    KomeEntryMeta dm;
    EXPECT_EQ(KOME_OK, kome_get_meta(eb, "ns", key, 6, &dm));

    /* Delete on A, wait for tombstone to propagate */
    kome_delete(ea, "ns", key, 6, nullptr);
    /* Poll until B sees the delete */
    {
        auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(2);
        while (std::chrono::steady_clock::now() < deadline) {
            KomeEntryMeta m;
            if (kome_get_meta(eb, "ns", key, 6, &m) == KOME_ERR_NOT_FOUND) break;
            std::this_thread::sleep_for(std::chrono::milliseconds(10));
        }
    }

    /* B should see NOT_FOUND */
    uint8_t *out = nullptr;
    size_t len = 0;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get(eb, "ns", key, 6, &out, &len, nullptr));
}

/* ── Sync-done callback fires over TCP ───────────────────────────────── */

TEST_F(TcpSyncTest, SyncDoneCallback) {
    std::atomic<int> done_count{0};
    kome_on_sync_done(ea,
        [](void *ud, const uint8_t *) {
            static_cast<std::atomic<int>*>(ud)->fetch_add(1);
        }, &done_count);

    ASSERT_EQ(KOME_OK, kome_put(ea, "ns", (const uint8_t*)"k", 1,
                                 (const uint8_t*)"v", 1, nullptr));

    connect_tcp();

    EXPECT_GE(done_count.load(), 1);
}

/* ── Batch write over TCP ────────────────────────────────────────────── */

TEST_F(TcpSyncTest, BatchWritePush) {
    connect_tcp();

    KomeBatchEntry entries[3];
    uint8_t k0[] = "k0", k1[] = "k1", k2[] = "k2";
    uint8_t v0[] = "v0", v1[] = "v1", v2[] = "v2";
    entries[0] = {"batch", k0, 2, v0, 2};
    entries[1] = {"batch", k1, 2, v1, 2};
    entries[2] = {"batch", k2, 2, v2, 2};
    ASSERT_EQ(KOME_OK, kome_put_batch(ea, entries, 3, nullptr));

    ASSERT_TRUE(wait_for_key(eb, "batch", k2, 2));

    for (int i = 0; i < 3; i++) {
        std::string key = "k" + std::to_string(i);
        KomeEntryMeta m;
        EXPECT_EQ(KOME_OK, kome_get_meta(eb, "batch",
            (const uint8_t*)key.data(), key.size(), &m));
    }
}

/* ── Namespace-scoped sync over TCP ──────────────────────────────────── */

TEST_F(TcpSyncTest, NamespaceScopedSync) {
    const char *a_ns[] = {"chat"};
    kome_set_sync_namespaces(ea, a_ns, 1);
    kome_set_sync_namespaces(eb, a_ns, 1);

    ASSERT_EQ(KOME_OK, kome_put(ea, "chat",
        (const uint8_t*)"msg", 3, (const uint8_t*)"hi", 2, nullptr));
    ASSERT_EQ(KOME_OK, kome_put(ea, "private",
        (const uint8_t*)"secret", 6, (const uint8_t*)"hidden", 6, nullptr));

    connect_tcp();

    KomeEntryMeta nm;
    EXPECT_EQ(KOME_OK, kome_get_meta(eb, "chat", (const uint8_t*)"msg", 3, &nm));
    KomeEntryMeta m;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(eb, "private",
        (const uint8_t*)"secret", 6, &m));
}
