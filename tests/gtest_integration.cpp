/**
 * End-to-end integration tests.
 *
 * These test the FULL stack: identity → encryption → signing → sync →
 * conflict resolution → bulk reads → callbacks.
 * Written independently from the feature agents to validate behavior.
 */
#include <gtest/gtest.h>
#include "kome.h"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>
#include <vector>
#include <set>
#include <atomic>
#include <thread>
#include <chrono>

class IntegrationTest : public ::testing::Test {
protected:
    KomeEngine *alice = nullptr;
    KomeEngine *bob = nullptr;
    LoopbackPair loopback;

    void SetUp() override {
        KomeConfig cfg = {};
        cfg.path = ":memory:";
        ASSERT_EQ(KOME_OK, kome_open(&cfg, &alice));
        ASSERT_EQ(KOME_OK, kome_open(&cfg, &bob));
    }

    void TearDown() override {
        kome_close(alice);
        kome_close(bob);
    }

    /* After kome_set_identity, write a scratch entry to discover the
     * actual fingerprint, then set it on the loopback side. */
    void get_fingerprint(KomeEngine *engine, uint8_t fp_out[32]) {
        uint8_t k[] = "_fp_probe";
        uint8_t v[] = "x";
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine, "_internal", k, 9, v, 1, &m));
        std::memcpy(fp_out, m.author, 32);
    }

    void set_identities() {
        uint8_t alice_key[] = "alice_key_material_32bytes!!!!!";
        uint8_t bob_key[]   = "bob_key_material_32_bytes!!!!!!";
        ASSERT_EQ(KOME_OK, kome_set_identity(alice, alice_key, 31));
        ASSERT_EQ(KOME_OK, kome_set_identity(bob, bob_key, 31));

        /* Sync loopback fingerprints with actual identity fingerprints */
        get_fingerprint(alice, loopback.a.fingerprint);
        get_fingerprint(bob, loopback.b.fingerprint);
    }

    void attach_transports() {
        ASSERT_EQ(KOME_OK, kome_attach_transport(alice, &loopback.a.transport));
        ASSERT_EQ(KOME_OK, kome_attach_transport(bob, &loopback.b.transport));
    }

    void connect_peers() {
        attach_transports();
        loopback.connect();
    }
};

/* ===== Test 1: Basic round-trip ===== */
TEST_F(IntegrationTest, WriteOnAliceReadOnBob) {
    set_identities();

    /* Alice writes */
    uint8_t key[] = "greeting";
    uint8_t val[] = "hello world";
    KomeEntryMeta meta;
    ASSERT_EQ(KOME_OK, kome_put(alice, "chat", key, 8, val, 11, &meta));

    /* Connect and sync */
    connect_peers();

    /* Bob reads Alice's data */
    uint8_t *out_val = nullptr;
    size_t out_len = 0;
    KomeEntryMeta out_meta;
    KomeError err = kome_get(bob, "chat", key, 8, &out_val, &out_len, &out_meta);
    ASSERT_EQ(KOME_OK, err) << "Bob should see Alice's entry after sync";
    ASSERT_EQ(11u, out_len);
    EXPECT_EQ(0, std::memcmp(out_val, val, 11));

    /* Verify author is Alice */
    EXPECT_EQ(0, std::memcmp(out_meta.author, meta.author, 32));

    kome_free_value(out_val);
}

/* ===== Test 2: Bidirectional sync ===== */
TEST_F(IntegrationTest, BidirectionalSync) {
    set_identities();

    /* Both write to a shared namespace */
    uint8_t ak[] = "alice_key";
    uint8_t av[] = "alice_val";
    uint8_t bk[] = "bob_key";
    uint8_t bv[] = "bob_val";

    KomeEntryMeta am, bm;
    ASSERT_EQ(KOME_OK, kome_put(alice, "shared", ak, 9, av, 9, &am));
    ASSERT_EQ(KOME_OK, kome_put(bob, "shared", bk, 7, bv, 7, &bm));

    connect_peers();

    /* Alice should have Bob's key */
    KomeEntryMeta check;
    EXPECT_EQ(KOME_OK, kome_get_meta(alice, "shared", bk, 7, &check));

    /* Bob should have Alice's key */
    EXPECT_EQ(KOME_OK, kome_get_meta(bob, "shared", ak, 9, &check));
}

/* ===== Test 3: Tombstone behavior ===== */
TEST_F(IntegrationTest, DeletedEntriesNotVisible) {
    set_identities();

    uint8_t key[] = "ephemeral";
    uint8_t val[] = "temporary data";
    KomeEntryMeta meta;
    ASSERT_EQ(KOME_OK, kome_put(alice, "ns", key, 9, val, 14, &meta));

    /* Delete it */
    ASSERT_EQ(KOME_OK, kome_delete(alice, "ns", key, 9, &meta));

    /* kome_get should return NOT_FOUND */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    KomeEntryMeta out_meta;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get(alice, "ns", key, 9, &out, &out_len, &out_meta));
    EXPECT_EQ(nullptr, out);
    EXPECT_EQ(1, out_meta.tombstone);

}

/* ===== Test 4: Bulk reads ===== */
TEST_F(IntegrationTest, BulkReadReturnsAllEntries) {
    set_identities();

    /* Write 50 entries */
    for (int i = 0; i < 50; i++) {
        std::string key = "item_" + std::to_string(i);
        std::string val = "value_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(alice, "bulk", (const uint8_t*)key.data(),
                                      key.size(), (const uint8_t*)val.data(),
                                      val.size(), &m));
    }

    /* Delete 5 of them */
    for (int i = 0; i < 5; i++) {
        std::string key = "item_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_delete(alice, "bulk", (const uint8_t*)key.data(),
                                         key.size(), &m));
    }

    /* kome_get_all should return 45 (excludes tombstones) */
    uint8_t **keys = nullptr, **values = nullptr;
    size_t *key_lens = nullptr, *value_lens = nullptr;
    KomeEntryMeta *metas = nullptr;
    size_t count = 0;

    ASSERT_EQ(KOME_OK, kome_get_all(alice, "bulk", &keys, &key_lens,
                                      &values, &value_lens, &metas, &count));
    EXPECT_EQ(45u, count);

    /* Verify no tombstones in results */
    for (size_t i = 0; i < count; i++) {
        EXPECT_EQ(0, metas[i].tombstone);
    }

    kome_free_entries(keys, key_lens, values, value_lens, metas, count);
}

/* ===== Test 5: Per-namespace callback ===== */
TEST_F(IntegrationTest, PerNamespaceCallbackFilters) {
    set_identities();

    int chat_changes = 0;
    int other_changes = 0;

    kome_on_remote_change_ns(bob, "chat",
        [](void *ud, const char*, const uint8_t*, size_t,
           const uint8_t*, size_t, const KomeEntryMeta*) {
            (*static_cast<int*>(ud))++;
        }, &chat_changes);

    kome_on_remote_change_ns(bob, "other",
        [](void *ud, const char*, const uint8_t*, size_t,
           const uint8_t*, size_t, const KomeEntryMeta*) {
            (*static_cast<int*>(ud))++;
        }, &other_changes);

    /* Alice writes to chat (3 entries) and other (1 entry) */
    for (int i = 0; i < 3; i++) {
        std::string key = "msg_" + std::to_string(i);
        std::string val = "hello " + std::to_string(i);
        KomeEntryMeta m;
        kome_put(alice, "chat", (const uint8_t*)key.data(), key.size(),
                 (const uint8_t*)val.data(), val.size(), &m);
    }
    {
        uint8_t ok[] = "note";
        uint8_t ov[] = "other_data";
        KomeEntryMeta m;
        kome_put(alice, "other", ok, 4, ov, 10, &m);
    }

    connect_peers();

    EXPECT_EQ(3, chat_changes) << "chat callback should fire 3 times";
    EXPECT_EQ(1, other_changes) << "other callback should fire 1 time";
}

/* ===== Test 7: Conflict resolution (LWW) ===== */
TEST_F(IntegrationTest, LastWriterWins) {
    set_identities();

    uint8_t key[] = "contested";

    /* Both write different values for the same key */
    uint8_t av[] = "alice_version";
    uint8_t bv[] = "bob_version";
    KomeEntryMeta am, bm;
    ASSERT_EQ(KOME_OK, kome_put(alice, "shared", key, 9, av, 13, &am));

    /* Small delay to ensure different timestamp */
    std::this_thread::sleep_for(std::chrono::milliseconds(2));
    ASSERT_EQ(KOME_OK, kome_put(bob, "shared", key, 9, bv, 11, &bm));

    /* Bob's timestamp should be higher */
    EXPECT_GT(bm.timestamp_us, am.timestamp_us);

    connect_peers();

    /* Both should converge to Bob's value (later timestamp) */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    ASSERT_EQ(KOME_OK, kome_get(alice, "shared", key, 9, &out, &out_len, nullptr));
    EXPECT_EQ(11u, out_len);
    EXPECT_EQ(0, std::memcmp(out, bv, 11));
    kome_free_value(out);

    out = nullptr;
    ASSERT_EQ(KOME_OK, kome_get(bob, "shared", key, 9, &out, &out_len, nullptr));
    EXPECT_EQ(11u, out_len);
    EXPECT_EQ(0, std::memcmp(out, bv, 11));
    kome_free_value(out);
}

/* ===== Test 10: Large value sync ===== */
TEST_F(IntegrationTest, LargeValueSurvivesSync) {
    set_identities();

    /* Write a 1 MB value */
    std::vector<uint8_t> big_val(1024 * 1024, 0);
    for (size_t i = 0; i < big_val.size(); i++)
        big_val[i] = (uint8_t)(i & 0xFF);

    uint8_t key[] = "bigdata";
    KomeEntryMeta am;
    ASSERT_EQ(KOME_OK, kome_put(alice, "data", key, 7,
                                  big_val.data(), big_val.size(), &am));

    connect_peers();

    /* Bob reads the 1 MB value */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    ASSERT_EQ(KOME_OK, kome_get(bob, "data", key, 7, &out, &out_len, nullptr));
    ASSERT_EQ(big_val.size(), out_len);
    EXPECT_EQ(0, std::memcmp(out, big_val.data(), big_val.size()));
    kome_free_value(out);
}

/* ===== Test: Namespace-scoped sync ===== */
TEST_F(IntegrationTest, NamespaceScopedSyncFiltersCorrectly) {
    set_identities();

    /* Alice syncs only "chat", Bob syncs only "chat" and "media" */
    const char *alice_ns[] = {"chat"};
    const char *bob_ns[] = {"chat", "media"};
    ASSERT_EQ(KOME_OK, kome_set_sync_namespaces(alice, alice_ns, 1));
    ASSERT_EQ(KOME_OK, kome_set_sync_namespaces(bob, bob_ns, 2));

    /* Alice writes to "chat" and "private" */
    uint8_t ck[] = "msg1";
    uint8_t cv[] = "hello";
    uint8_t pk[] = "secret";
    uint8_t pv[] = "hidden";
    kome_put(alice, "chat", ck, 4, cv, 5, nullptr);
    kome_put(alice, "private", pk, 6, pv, 6, nullptr);

    /* Bob writes to "media" */
    uint8_t mk[] = "photo1";
    uint8_t mv[] = "jpeg_data";
    kome_put(bob, "media", mk, 6, mv, 9, nullptr);

    connect_peers();

    /* Bob should have "chat/msg1" (intersection includes chat) */
    KomeEntryMeta meta;
    EXPECT_EQ(KOME_OK, kome_get_meta(bob, "chat", ck, 4, &meta));

    /* Bob should NOT have "private/secret" (not in intersection) */
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(bob, "private", pk, 6, &meta));

    /* Alice should NOT have "media/photo1" (not in Alice's sync_namespaces) */
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(alice, "media", mk, 6, &meta));
}

/* ===== Test: Entry TTL ===== */
TEST_F(IntegrationTest, EntryTTLRejectsExpiredDuringSync) {
    set_identities();

    /* Set 1-second TTL on "ephemeral" namespace for Bob */
    ASSERT_EQ(KOME_OK, kome_set_entry_ttl(bob, "ephemeral", 1));

    /* Alice writes an entry */
    uint8_t key[] = "msg";
    uint8_t val[] = "fleeting";
    kome_put(alice, "ephemeral", key, 3, val, 8, nullptr);

    /* Wait for TTL to expire */
    std::this_thread::sleep_for(std::chrono::milliseconds(1100));

    connect_peers();

    /* Bob should NOT have the expired entry */
    KomeEntryMeta meta;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(bob, "ephemeral", key, 3, &meta));

    /* Write a fresh entry after connecting */
    uint8_t key2[] = "msg2";
    uint8_t val2[] = "current";
    kome_put(alice, "ephemeral", key2, 4, val2, 7, nullptr);

    /* Bob should have the fresh entry (pushed live) */
    EXPECT_EQ(KOME_OK, kome_get_meta(bob, "ephemeral", key2, 4, &meta));
}

/* ===== Test: Sync all namespaces when no filter set ===== */
TEST_F(IntegrationTest, NoFilterSyncsEverything) {
    set_identities();

    /* No namespace filter set — default is sync all */
    uint8_t k1[] = "a";
    uint8_t k2[] = "b";
    uint8_t v[] = "x";
    kome_put(alice, "ns1", k1, 1, v, 1, nullptr);
    kome_put(alice, "ns2", k2, 1, v, 1, nullptr);

    connect_peers();

    KomeEntryMeta meta;
    EXPECT_EQ(KOME_OK, kome_get_meta(bob, "ns1", k1, 1, &meta));
    EXPECT_EQ(KOME_OK, kome_get_meta(bob, "ns2", k2, 1, &meta));
}
