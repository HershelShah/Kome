/**
 * End-to-end integration tests.
 *
 * These test the FULL stack: identity → encryption → signing → sync →
 * conflict resolution → ACL enforcement → bulk reads → callbacks.
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

    void setup_shared_namespace(const char *ns) {
        /* Get fingerprints */
        KomeStats alice_stats, bob_stats;
        kome_stats(alice, &alice_stats);
        kome_stats(bob, &bob_stats);

        /* Give both WRITE access on both engines */
        uint8_t alice_fp[32], bob_fp[32];
        /* We need actual fingerprints - get them via version vector after a write */
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

    /* Verify signature is populated */
    bool has_sig = false;
    for (int i = 0; i < 64; i++) {
        if (meta.signature[i] != 0) { has_sig = true; break; }
    }
    EXPECT_TRUE(has_sig) << "Entry should be signed";

    /* Configure ACLs so Bob can read Alice's namespace */
    KomeNamespaceACLEntry acl[2];
    std::memcpy(acl[0].fingerprint, meta.author, 32);
    acl[0].role = KOME_ROLE_WRITE;

    /* Get Bob's fingerprint by having him write something */
    uint8_t bkey[] = "tmp";
    uint8_t bval[] = "x";
    KomeEntryMeta bmeta;
    ASSERT_EQ(KOME_OK, kome_put(bob, "scratch", bkey, 3, bval, 1, &bmeta));
    std::memcpy(acl[1].fingerprint, bmeta.author, 32);
    acl[1].role = KOME_ROLE_WRITE;

    KomeNamespaceConfig ns_cfg = {};
    ns_cfg.name = "chat";
    ns_cfg.acl = acl;
    ns_cfg.acl_count = 2;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(alice, &ns_cfg));
    ASSERT_EQ(KOME_OK, kome_configure_namespace(bob, &ns_cfg));

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

    /* Configure ACLs */
    KomeNamespaceACLEntry acl[2];
    std::memcpy(acl[0].fingerprint, am.author, 32);
    acl[0].role = KOME_ROLE_WRITE;
    std::memcpy(acl[1].fingerprint, bm.author, 32);
    acl[1].role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg = {};
    cfg.name = "shared";
    cfg.acl = acl;
    cfg.acl_count = 2;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(alice, &cfg));
    ASSERT_EQ(KOME_OK, kome_configure_namespace(bob, &cfg));

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

    /* kome_get_with_tombstones should return OK */
    EXPECT_EQ(KOME_OK, kome_get_with_tombstones(alice, "ns", key, 9, &out, &out_len, &out_meta));
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

    /* Setup ACLs for both namespaces */
    uint8_t ak[] = "x";
    KomeEntryMeta am;
    kome_put(alice, "scratch", ak, 1, ak, 1, &am);
    uint8_t bk[] = "y";
    KomeEntryMeta bm;
    kome_put(bob, "scratch", bk, 1, bk, 1, &bm);

    KomeNamespaceACLEntry acl[2];
    std::memcpy(acl[0].fingerprint, am.author, 32);
    acl[0].role = KOME_ROLE_WRITE;
    std::memcpy(acl[1].fingerprint, bm.author, 32);
    acl[1].role = KOME_ROLE_WRITE;

    for (const char *ns : {"chat", "other"}) {
        KomeNamespaceConfig cfg = {};
        cfg.name = ns;
        cfg.acl = acl;
        cfg.acl_count = 2;
        kome_configure_namespace(alice, &cfg);
        kome_configure_namespace(bob, &cfg);
    }

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

/* ===== Test 6: ACL enforcement ===== */
TEST_F(IntegrationTest, ACLBlocksUnauthorizedSync) {
    set_identities();

    /* Alice writes to a private namespace */
    uint8_t key[] = "secret";
    uint8_t val[] = "classified";
    KomeEntryMeta am;
    ASSERT_EQ(KOME_OK, kome_put(alice, "private", key, 6, val, 10, &am));

    /* Configure ACL: only Alice has access, Bob does NOT */
    KomeNamespaceACLEntry acl;
    std::memcpy(acl.fingerprint, am.author, 32);
    acl.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg = {};
    cfg.name = "private";
    cfg.acl = &acl;
    cfg.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(alice, &cfg));
    ASSERT_EQ(KOME_OK, kome_configure_namespace(bob, &cfg));

    connect_peers();

    /* Bob should NOT have the entry */
    KomeEntryMeta check;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(bob, "private", key, 6, &check))
        << "Bob should not receive entries from a namespace he has no access to";
}

/* ===== Test 7: Identity rotation ===== */
TEST_F(IntegrationTest, IdentityRotationPreservesAccess) {
    set_identities();

    /* Write something to establish Alice's fingerprint */
    uint8_t key[] = "data";
    uint8_t val[] = "important";
    KomeEntryMeta meta;
    ASSERT_EQ(KOME_OK, kome_put(alice, "ns", key, 4, val, 9, &meta));

    uint8_t old_author[32];
    std::memcpy(old_author, meta.author, 32);

    /* Configure ACL with Alice's current fingerprint */
    KomeNamespaceACLEntry acl;
    std::memcpy(acl.fingerprint, meta.author, 32);
    acl.role = KOME_ROLE_WRITE;
    KomeNamespaceConfig cfg = {};
    cfg.name = "ns";
    cfg.acl = &acl;
    cfg.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(alice, &cfg));

    /* Rotate identity */
    uint8_t new_key[] = "alice_new_key_material_32bytes!";
    ASSERT_EQ(KOME_OK, kome_rotate_identity(alice, new_key, 31));

    /* Write with new identity */
    uint8_t key2[] = "data2";
    uint8_t val2[] = "new stuff";
    KomeEntryMeta meta2;
    ASSERT_EQ(KOME_OK, kome_put(alice, "ns", key2, 5, val2, 9, &meta2));

    /* New author should differ from old */
    EXPECT_NE(0, std::memcmp(meta2.author, old_author, 32))
        << "Author fingerprint should change after rotation";

    /* Old data should still be readable */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    EXPECT_EQ(KOME_OK, kome_get(alice, "ns", key, 4, &out, &out_len, nullptr));
    kome_free_value(out);
}

/* ===== Test 8: Conflict resolution (LWW) ===== */
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

    /* Configure ACLs */
    KomeNamespaceACLEntry acl[2];
    std::memcpy(acl[0].fingerprint, am.author, 32);
    acl[0].role = KOME_ROLE_WRITE;
    std::memcpy(acl[1].fingerprint, bm.author, 32);
    acl[1].role = KOME_ROLE_WRITE;
    KomeNamespaceConfig cfg = {};
    cfg.name = "shared";
    cfg.acl = acl;
    cfg.acl_count = 2;
    kome_configure_namespace(alice, &cfg);
    kome_configure_namespace(bob, &cfg);

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

/* ===== Test 9: Namespace listing includes empty configured namespaces ===== */
TEST_F(IntegrationTest, ListNamespacesIncludesEmpty) {
    set_identities();

    KomeNamespaceACLEntry acl;
    std::memset(acl.fingerprint, 0xCC, 32);
    acl.role = KOME_ROLE_READ;

    KomeNamespaceConfig cfg = {};
    cfg.name = "empty_ns";
    cfg.acl = &acl;
    cfg.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(alice, &cfg));

    char **ns_list = nullptr;
    size_t count = 0;
    ASSERT_EQ(KOME_OK, kome_list_namespaces(alice, &ns_list, &count));

    bool found = false;
    for (size_t i = 0; i < count; i++) {
        if (std::string(ns_list[i]) == "empty_ns") found = true;
    }
    EXPECT_TRUE(found) << "Configured-but-empty namespace should appear";
    kome_free_namespaces(ns_list, count);
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

    /* Setup ACLs */
    uint8_t bk[] = "x";
    KomeEntryMeta bm;
    kome_put(bob, "scratch", bk, 1, bk, 1, &bm);

    KomeNamespaceACLEntry acl[2];
    std::memcpy(acl[0].fingerprint, am.author, 32);
    acl[0].role = KOME_ROLE_WRITE;
    std::memcpy(acl[1].fingerprint, bm.author, 32);
    acl[1].role = KOME_ROLE_WRITE;
    KomeNamespaceConfig cfg = {};
    cfg.name = "data";
    cfg.acl = acl;
    cfg.acl_count = 2;
    kome_configure_namespace(alice, &cfg);
    kome_configure_namespace(bob, &cfg);

    connect_peers();

    /* Bob reads the 1 MB value */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    ASSERT_EQ(KOME_OK, kome_get(bob, "data", key, 7, &out, &out_len, nullptr));
    ASSERT_EQ(big_val.size(), out_len);
    EXPECT_EQ(0, std::memcmp(out, big_val.data(), big_val.size()));
    kome_free_value(out);
}
