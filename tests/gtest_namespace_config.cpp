#include <gtest/gtest.h>
#include "kome.h"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>

/* ========================================================================
 * NamespaceConfigTest — single-engine CRUD tests
 * ======================================================================== */

class NamespaceConfigTest : public ::testing::Test {
protected:
    KomeEngine *engine = nullptr;
    std::string db_path;

    void SetUp() override {
        db_path = temp_db_path("ns_config");
        cleanup_db(db_path);

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

/* Configure a namespace with TTL and ACL, then read it back */
TEST_F(NamespaceConfigTest, ConfigureAndGet) {
    KomeNamespaceACLEntry acl[2];
    std::memset(acl[0].fingerprint, 0xAA, 32);
    acl[0].role = KOME_ROLE_READ;
    std::memset(acl[1].fingerprint, 0xBB, 32);
    acl[1].role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg = {};
    cfg.name = "contacts";
    cfg.tombstone_ttl_sec = 86400;
    cfg.acl = acl;
    cfg.acl_count = 2;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg));

    KomeNamespaceConfig out = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "contacts", &out));

    EXPECT_STREQ("contacts", out.name);
    EXPECT_EQ(86400u, out.tombstone_ttl_sec);
    ASSERT_EQ(2u, out.acl_count);

    /* Verify first ACL entry */
    uint8_t expected_fp_a[32];
    std::memset(expected_fp_a, 0xAA, 32);
    EXPECT_EQ(0, std::memcmp(out.acl[0].fingerprint, expected_fp_a, 32));
    EXPECT_EQ(KOME_ROLE_READ, out.acl[0].role);

    /* Verify second ACL entry */
    uint8_t expected_fp_b[32];
    std::memset(expected_fp_b, 0xBB, 32);
    EXPECT_EQ(0, std::memcmp(out.acl[1].fingerprint, expected_fp_b, 32));
    EXPECT_EQ(KOME_ROLE_WRITE, out.acl[1].role);

    kome_free_namespace_config(&out);
}

/* Configure with acl_count=0 (owner-only), verify empty ACL comes back */
TEST_F(NamespaceConfigTest, ConfigureOwnerOnly) {
    KomeNamespaceConfig cfg = {};
    cfg.name = "private";
    cfg.tombstone_ttl_sec = 0;
    cfg.acl = nullptr;
    cfg.acl_count = 0;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg));

    KomeNamespaceConfig out = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "private", &out));

    EXPECT_STREQ("private", out.name);
    EXPECT_EQ(0u, out.tombstone_ttl_sec);
    EXPECT_EQ(0u, out.acl_count);

    kome_free_namespace_config(&out);
}

/* Configure, then remove, verify get returns NOT_FOUND */
TEST_F(NamespaceConfigTest, RemoveNamespace) {
    KomeNamespaceConfig cfg = {};
    cfg.name = "removeme";
    cfg.acl_count = 0;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg));

    /* Verify it exists */
    KomeNamespaceConfig out = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "removeme", &out));
    kome_free_namespace_config(&out);

    /* Remove it */
    ASSERT_EQ(KOME_OK, kome_remove_namespace(engine, "removeme"));

    /* Verify it's gone */
    KomeNamespaceConfig out2 = {};
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_namespace_config(engine, "removeme", &out2));
}

/* Configure twice; second config replaces first */
TEST_F(NamespaceConfigTest, ReconfigureOverwrites) {
    /* First config: TTL=100, one ACL entry with READ */
    KomeNamespaceACLEntry acl1;
    std::memset(acl1.fingerprint, 0xAA, 32);
    acl1.role = KOME_ROLE_READ;

    KomeNamespaceConfig cfg1 = {};
    cfg1.name = "evolving";
    cfg1.tombstone_ttl_sec = 100;
    cfg1.acl = &acl1;
    cfg1.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg1));

    /* Second config: TTL=9999, different ACL with WRITE */
    KomeNamespaceACLEntry acl2;
    std::memset(acl2.fingerprint, 0xBB, 32);
    acl2.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg2 = {};
    cfg2.name = "evolving";
    cfg2.tombstone_ttl_sec = 9999;
    cfg2.acl = &acl2;
    cfg2.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg2));

    /* Read back — should match second config */
    KomeNamespaceConfig out = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "evolving", &out));

    EXPECT_EQ(9999u, out.tombstone_ttl_sec);
    ASSERT_EQ(1u, out.acl_count);

    uint8_t expected_fp[32];
    std::memset(expected_fp, 0xBB, 32);
    EXPECT_EQ(0, std::memcmp(out.acl[0].fingerprint, expected_fp, 32));
    EXPECT_EQ(KOME_ROLE_WRITE, out.acl[0].role);

    kome_free_namespace_config(&out);
}

/* Getting config for a namespace that was never configured returns NOT_FOUND */
TEST_F(NamespaceConfigTest, GetUnconfigured) {
    KomeNamespaceConfig out = {};
    EXPECT_EQ(KOME_ERR_NOT_FOUND,
              kome_get_namespace_config(engine, "nonexistent", &out));
}

/* kome_free_namespace_config(nullptr) must not crash */
TEST_F(NamespaceConfigTest, FreeNullConfig) {
    kome_free_namespace_config(nullptr); /* should not crash */
}

/* Null arguments to configure/get/remove return MISUSE */
TEST_F(NamespaceConfigTest, ConfigureMisuse) {
    KomeNamespaceConfig cfg = {};
    cfg.name = "test";
    cfg.acl_count = 0;

    /* Null engine */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_configure_namespace(nullptr, &cfg));

    /* Null config */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_configure_namespace(engine, nullptr));

    /* Null name inside config */
    KomeNamespaceConfig bad_cfg = {};
    bad_cfg.name = nullptr;
    EXPECT_EQ(KOME_ERR_MISUSE, kome_configure_namespace(engine, &bad_cfg));

    /* Null engine for get */
    KomeNamespaceConfig out = {};
    EXPECT_EQ(KOME_ERR_MISUSE, kome_get_namespace_config(nullptr, "ns", &out));

    /* Null name for get */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_get_namespace_config(engine, nullptr, &out));

    /* Null engine for remove */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_remove_namespace(nullptr, "ns"));

    /* Null name for remove */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_remove_namespace(engine, nullptr));
}

/* Writing to an unconfigured namespace auto-creates a config with empty ACL */
TEST_F(NamespaceConfigTest, AutoCreateOnPut) {
    set_test_identity();

    /* Namespace "auto_ns" has never been configured */
    uint8_t key[] = "k1";
    uint8_t val[] = "v1";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "auto_ns", key, 2, val, 2, &m));

    /* Config should now exist with empty ACL (owner-only) */
    KomeNamespaceConfig out = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "auto_ns", &out));
    EXPECT_STREQ("auto_ns", out.name);
    EXPECT_EQ(0u, out.acl_count);

    kome_free_namespace_config(&out);
}

/* Deleting in an unconfigured namespace also auto-creates the config */
TEST_F(NamespaceConfigTest, AutoCreateOnDelete) {
    set_test_identity();

    /* First put something so delete has a target */
    uint8_t key[] = "dk";
    uint8_t val[] = "dv";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "auto_del_ns", key, 2, val, 2, &m));

    /* Now delete */
    ASSERT_EQ(KOME_OK, kome_delete(engine, "auto_del_ns", key, 2, &m));

    /* Config should exist with empty ACL */
    KomeNamespaceConfig out = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "auto_del_ns", &out));
    EXPECT_STREQ("auto_del_ns", out.name);
    EXPECT_EQ(0u, out.acl_count);

    kome_free_namespace_config(&out);
}

/* kome_list_namespaces should include namespaces that are configured but have
   no data, and should not produce duplicates when data is later written. */
TEST_F(NamespaceConfigTest, ListNamespacesIncludesConfiguredEmpty) {
    set_test_identity();

    /* Configure a namespace with an ACL but do NOT write any data */
    KomeNamespaceACLEntry acl;
    std::memset(acl.fingerprint, 0xCC, 32);
    acl.role = KOME_ROLE_READ;

    KomeNamespaceConfig cfg = {};
    cfg.name = "configured_only";
    cfg.tombstone_ttl_sec = 0;
    cfg.acl = &acl;
    cfg.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg));

    /* List namespaces — configured_only must appear even though it has no data */
    char **ns_list = nullptr;
    size_t ns_count = 0;
    ASSERT_EQ(KOME_OK, kome_list_namespaces(engine, &ns_list, &ns_count));

    bool found = false;
    for (size_t i = 0; i < ns_count; i++) {
        if (std::string(ns_list[i]) == "configured_only") found = true;
    }
    EXPECT_TRUE(found) << "configured_only should appear in list_namespaces";
    kome_free_namespaces(ns_list, ns_count);

    /* Now write data to the namespace */
    uint8_t key[] = "k1";
    uint8_t val[] = "v1";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "configured_only", key, 2, val, 2, &m));

    /* List again — configured_only must appear exactly once (no duplicates) */
    ns_list = nullptr;
    ns_count = 0;
    ASSERT_EQ(KOME_OK, kome_list_namespaces(engine, &ns_list, &ns_count));

    int count_configured = 0;
    for (size_t i = 0; i < ns_count; i++) {
        if (std::string(ns_list[i]) == "configured_only") count_configured++;
    }
    EXPECT_EQ(1, count_configured)
        << "configured_only should appear exactly once after writing data";
    kome_free_namespaces(ns_list, ns_count);
}

/* ========================================================================
 * NamespaceSyncTest — two-engine ACL-based sync filtering
 * ======================================================================== */

class NamespaceSyncTest : public ::testing::Test {
protected:
    KomeEngine *engine_a = nullptr;
    KomeEngine *engine_b = nullptr;
    std::string db_a, db_b;
    LoopbackPair loopback;

    void SetUp() override {
        db_a = temp_db_path("ns_sync_a");
        db_b = temp_db_path("ns_sync_b");
        cleanup_db(db_a);
        cleanup_db(db_b);

        KomeConfig cfg_a = {};
        cfg_a.path = db_a.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&cfg_a, &engine_a));

        KomeConfig cfg_b = {};
        cfg_b.path = db_b.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&cfg_b, &engine_b));

        /* Set identities — matching loopback fingerprints */
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

    /*
     * configure_ns: configure a namespace for bidirectional WRITE access
     * between engine A and engine B.
     *
     * On A's side, the ACL grants WRITE to B's transport fingerprint (0xBB*32).
     * On B's side, the ACL grants WRITE to A's transport fingerprint (0xAA*32).
     */
    void configure_ns(const char *ns) {
        /* A grants WRITE to B */
        KomeNamespaceACLEntry acl_a;
        std::memset(acl_a.fingerprint, 0xBB, 32);
        acl_a.role = KOME_ROLE_WRITE;

        KomeNamespaceConfig cfg_a = {};
        cfg_a.name = ns;
        cfg_a.acl = &acl_a;
        cfg_a.acl_count = 1;
        ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_a));

        /* B grants WRITE to A */
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

/* A configures ns granting B READ, B configures ns granting A WRITE.
   A writes, connect. B receives the entries. */
TEST_F(NamespaceSyncTest, ReadAccessReceivesEntries) {
    /* A grants B READ access */
    KomeNamespaceACLEntry acl_a;
    std::memset(acl_a.fingerprint, 0xBB, 32);
    acl_a.role = KOME_ROLE_READ;

    KomeNamespaceConfig cfg_a = {};
    cfg_a.name = "shared";
    cfg_a.acl = &acl_a;
    cfg_a.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_a));

    /* B grants A WRITE access */
    KomeNamespaceACLEntry acl_b;
    std::memset(acl_b.fingerprint, 0xAA, 32);
    acl_b.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg_b = {};
    cfg_b.name = "shared";
    cfg_b.acl = &acl_b;
    cfg_b.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_b, &cfg_b));

    /* A writes entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "rk_" + std::to_string(i);
        std::string val = "rv_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "shared",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* Connect — triggers sync */
    loopback.connect();

    /* B should have all entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "rk_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "shared",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "B missing key: " << key;
    }
}

/* Same setup but B has WRITE access (which implies read). Works the same. */
TEST_F(NamespaceSyncTest, WriteAccessReceivesEntries) {
    /* A grants B WRITE access */
    KomeNamespaceACLEntry acl_a;
    std::memset(acl_a.fingerprint, 0xBB, 32);
    acl_a.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg_a = {};
    cfg_a.name = "shared";
    cfg_a.acl = &acl_a;
    cfg_a.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_a));

    /* B grants A WRITE access */
    KomeNamespaceACLEntry acl_b;
    std::memset(acl_b.fingerprint, 0xAA, 32);
    acl_b.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg_b = {};
    cfg_b.name = "shared";
    cfg_b.acl = &acl_b;
    cfg_b.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_b, &cfg_b));

    /* A writes entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "wk_" + std::to_string(i);
        std::string val = "wv_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "shared",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* Connect — triggers sync */
    loopback.connect();

    /* B should have all entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "wk_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "shared",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "B missing key: " << key;
    }
}

/* A writes to ns without granting B any access. Connect. B does NOT get entries. */
TEST_F(NamespaceSyncTest, NoAccessBlocked) {
    /* A configures ns as owner-only (no ACL entries) */
    KomeNamespaceConfig cfg_a = {};
    cfg_a.name = "secret";
    cfg_a.acl = nullptr;
    cfg_a.acl_count = 0;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_a));

    /* A writes entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "sk_" + std::to_string(i);
        std::string val = "sv_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "secret",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* Connect */
    loopback.connect();

    /* B should NOT have any of the entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "sk_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(engine_b, "secret",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "B should NOT have key: " << key;
    }
}

/* B writes to ns. A configures ns granting B READ only. Connect.
   A does NOT accept B's write (B lacks WRITE authorization on A's side). */
TEST_F(NamespaceSyncTest, WriteAuthorizationRequired) {
    /* B writes entries to its local store first */
    for (int i = 0; i < 3; i++) {
        std::string key = "uk_" + std::to_string(i);
        std::string val = "uv_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_b, "controlled",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* A configures ns granting B READ only */
    KomeNamespaceACLEntry acl_a;
    std::memset(acl_a.fingerprint, 0xBB, 32);
    acl_a.role = KOME_ROLE_READ;

    KomeNamespaceConfig cfg_a = {};
    cfg_a.name = "controlled";
    cfg_a.acl = &acl_a;
    cfg_a.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_a));

    /* B configures ns granting A WRITE */
    KomeNamespaceACLEntry acl_b;
    std::memset(acl_b.fingerprint, 0xAA, 32);
    acl_b.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg_b = {};
    cfg_b.name = "controlled";
    cfg_b.acl = &acl_b;
    cfg_b.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_b, &cfg_b));

    /* Connect */
    loopback.connect();

    /* A should NOT have B's entries (B only has READ, not WRITE on A's ACL) */
    for (int i = 0; i < 3; i++) {
        std::string key = "uk_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(engine_a, "controlled",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "A should NOT have accepted B's write: " << key;
    }
}

/* B writes to ns. A configures ns granting B WRITE. Connect. A accepts B's write. */
TEST_F(NamespaceSyncTest, WriteAuthorizationGranted) {
    /* B writes entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "gk_" + std::to_string(i);
        std::string val = "gv_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_b, "granted",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* A configures ns granting B WRITE */
    KomeNamespaceACLEntry acl_a;
    std::memset(acl_a.fingerprint, 0xBB, 32);
    acl_a.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg_a = {};
    cfg_a.name = "granted";
    cfg_a.acl = &acl_a;
    cfg_a.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_a));

    /* B configures ns granting A WRITE */
    KomeNamespaceACLEntry acl_b;
    std::memset(acl_b.fingerprint, 0xAA, 32);
    acl_b.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg_b = {};
    cfg_b.name = "granted";
    cfg_b.acl = &acl_b;
    cfg_b.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_b, &cfg_b));

    /* Connect */
    loopback.connect();

    /* A should have B's entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "gk_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_a, "granted",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "A should have accepted B's write: " << key;
    }
}

/* Connect both sides in LIVE mode, then A writes to an ns B has no access to
   (B doesn't get it), then A writes to an ns B has READ access to (B gets it). */
TEST_F(NamespaceSyncTest, LiveModePushFiltered) {
    /* Configure "open_ns" with bidirectional access */
    KomeNamespaceACLEntry acl_open_a;
    std::memset(acl_open_a.fingerprint, 0xBB, 32);
    acl_open_a.role = KOME_ROLE_READ;

    KomeNamespaceConfig cfg_open_a = {};
    cfg_open_a.name = "open_ns";
    cfg_open_a.acl = &acl_open_a;
    cfg_open_a.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_open_a));

    KomeNamespaceACLEntry acl_open_b;
    std::memset(acl_open_b.fingerprint, 0xAA, 32);
    acl_open_b.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg_open_b = {};
    cfg_open_b.name = "open_ns";
    cfg_open_b.acl = &acl_open_b;
    cfg_open_b.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_b, &cfg_open_b));

    /* Configure "closed_ns" as owner-only on A's side */
    KomeNamespaceConfig cfg_closed_a = {};
    cfg_closed_a.name = "closed_ns";
    cfg_closed_a.acl = nullptr;
    cfg_closed_a.acl_count = 0;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_closed_a));

    /* Connect first (both in LIVE mode with empty state) */
    loopback.connect();

    /* A writes to closed_ns — B should NOT receive it */
    {
        uint8_t key[] = "closed_key";
        uint8_t val[] = "closed_val";
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "closed_ns",
            key, 10, val, 10, &m));
    }

    KomeEntryMeta meta;
    EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(engine_b, "closed_ns",
        (const uint8_t*)"closed_key", 10, &meta))
        << "B should NOT have received closed_ns entry via live push";

    /* A writes to open_ns — B SHOULD receive it */
    {
        uint8_t key[] = "open_key";
        uint8_t val[] = "open_val";
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "open_ns",
            key, 8, val, 8, &m));
    }

    EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "open_ns",
        (const uint8_t*)"open_key", 8, &meta))
        << "B should have received open_ns entry via live push";
}

/* ========================================================================
 * IdentityRotationTest — kome_rotate_identity tests
 * ======================================================================== */

class IdentityRotationTest : public ::testing::Test {
protected:
    KomeEngine *engine = nullptr;
    std::string db_path;

    void SetUp() override {
        db_path = temp_db_path("id_rotation");
        cleanup_db(db_path);

        KomeConfig cfg = {};
        cfg.path = db_path.c_str();
        ASSERT_EQ(KOME_OK, kome_open(&cfg, &engine));
    }

    void TearDown() override {
        kome_close(engine);
        cleanup_db(db_path);
    }
};

/* Rotation fails if identity is not set */
TEST_F(IdentityRotationTest, FailsWithoutIdentity) {
    uint8_t new_key[32] = {0xFF};
    EXPECT_EQ(KOME_ERR_MISUSE, kome_rotate_identity(engine, new_key, sizeof(new_key)));
}

/* After rotation, new fingerprint has the same role in all namespaces */
TEST_F(IdentityRotationTest, ACLMigratedToNewFingerprint) {
    uint8_t old_key[32];
    std::memset(old_key, 0x11, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, old_key, sizeof(old_key)));

    /* Compute old fingerprint the same way the engine does (SHA-256 of key material) */
    /* We'll use get_namespace_config to verify the ACL contents */

    /* Configure two namespaces with ACL entries for the engine's identity */
    /* First, read back the identity by writing an entry and checking the author */
    uint8_t dummy_key[] = "dk";
    uint8_t dummy_val[] = "dv";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns_a", dummy_key, 2, dummy_val, 2, &m));
    uint8_t old_fp[32];
    std::memcpy(old_fp, m.author, 32);

    /* Configure ns_a with ACL granting old fingerprint WRITE */
    KomeNamespaceACLEntry acl_a;
    std::memcpy(acl_a.fingerprint, old_fp, 32);
    acl_a.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg_a = {};
    cfg_a.name = "ns_a";
    cfg_a.acl = &acl_a;
    cfg_a.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg_a));

    /* Configure ns_b with ACL granting old fingerprint READ */
    KomeNamespaceACLEntry acl_b;
    std::memcpy(acl_b.fingerprint, old_fp, 32);
    acl_b.role = KOME_ROLE_READ;

    KomeNamespaceConfig cfg_b = {};
    cfg_b.name = "ns_b";
    cfg_b.acl = &acl_b;
    cfg_b.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg_b));

    /* Rotate identity */
    uint8_t new_key[32];
    std::memset(new_key, 0x22, 32);
    ASSERT_EQ(KOME_OK, kome_rotate_identity(engine, new_key, sizeof(new_key)));

    /* Read new fingerprint by writing a new entry */
    uint8_t dk2[] = "dk2";
    uint8_t dv2[] = "dv2";
    KomeEntryMeta m2;
    ASSERT_EQ(KOME_OK, kome_put(engine, "ns_a", dk2, 3, dv2, 3, &m2));
    uint8_t new_fp[32];
    std::memcpy(new_fp, m2.author, 32);

    /* The new fingerprint should be different from old */
    EXPECT_NE(0, std::memcmp(old_fp, new_fp, 32));

    /* ns_a ACL should now have new fingerprint with WRITE */
    KomeNamespaceConfig out_a = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "ns_a", &out_a));
    ASSERT_EQ(1u, out_a.acl_count);
    EXPECT_EQ(0, std::memcmp(out_a.acl[0].fingerprint, new_fp, 32));
    EXPECT_EQ(KOME_ROLE_WRITE, out_a.acl[0].role);
    kome_free_namespace_config(&out_a);

    /* ns_b ACL should now have new fingerprint with READ */
    KomeNamespaceConfig out_b = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "ns_b", &out_b));
    ASSERT_EQ(1u, out_b.acl_count);
    EXPECT_EQ(0, std::memcmp(out_b.acl[0].fingerprint, new_fp, 32));
    EXPECT_EQ(KOME_ROLE_READ, out_b.acl[0].role);
    kome_free_namespace_config(&out_b);
}

/* After rotation, old fingerprint no longer appears in any ACL */
TEST_F(IdentityRotationTest, OldFingerprintRemovedFromACLs) {
    uint8_t old_key[32];
    std::memset(old_key, 0x33, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, old_key, sizeof(old_key)));

    /* Get old fingerprint */
    uint8_t dk[] = "k";
    uint8_t dv[] = "v";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "test_ns", dk, 1, dv, 1, &m));
    uint8_t old_fp[32];
    std::memcpy(old_fp, m.author, 32);

    /* Configure namespace with old fingerprint */
    KomeNamespaceACLEntry acl;
    std::memcpy(acl.fingerprint, old_fp, 32);
    acl.role = KOME_ROLE_WRITE;

    KomeNamespaceConfig cfg = {};
    cfg.name = "test_ns";
    cfg.acl = &acl;
    cfg.acl_count = 1;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine, &cfg));

    /* Rotate */
    uint8_t new_key[32];
    std::memset(new_key, 0x44, 32);
    ASSERT_EQ(KOME_OK, kome_rotate_identity(engine, new_key, sizeof(new_key)));

    /* Verify old fingerprint has no role in the namespace */
    KomeNamespaceConfig out = {};
    ASSERT_EQ(KOME_OK, kome_get_namespace_config(engine, "test_ns", &out));
    for (size_t i = 0; i < out.acl_count; i++) {
        EXPECT_NE(0, std::memcmp(out.acl[i].fingerprint, old_fp, 32))
            << "Old fingerprint should not appear in ACL after rotation";
    }
    kome_free_namespace_config(&out);
}

/* Writes after rotation use the new fingerprint as author */
TEST_F(IdentityRotationTest, WritesUseNewFingerprint) {
    uint8_t old_key[32];
    std::memset(old_key, 0x55, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, old_key, sizeof(old_key)));

    /* Write before rotation */
    uint8_t k1[] = "before";
    uint8_t v1[] = "val1";
    KomeEntryMeta m1;
    ASSERT_EQ(KOME_OK, kome_put(engine, "wns", k1, 6, v1, 4, &m1));
    uint8_t old_fp[32];
    std::memcpy(old_fp, m1.author, 32);

    /* Rotate */
    uint8_t new_key[32];
    std::memset(new_key, 0x66, 32);
    ASSERT_EQ(KOME_OK, kome_rotate_identity(engine, new_key, sizeof(new_key)));

    /* Write after rotation */
    uint8_t k2[] = "after";
    uint8_t v2[] = "val2";
    KomeEntryMeta m2;
    ASSERT_EQ(KOME_OK, kome_put(engine, "wns", k2, 5, v2, 4, &m2));

    /* Author should be different from old fingerprint */
    EXPECT_NE(0, std::memcmp(m2.author, old_fp, 32));

    /* Read back the entry and confirm author matches */
    KomeEntryMeta m3;
    ASSERT_EQ(KOME_OK, kome_get_meta(engine, "wns", k2, 5, &m3));
    EXPECT_EQ(0, std::memcmp(m3.author, m2.author, 32));
}

/* Null/invalid args return MISUSE */
TEST_F(IdentityRotationTest, MisuseArgs) {
    uint8_t key[32] = {1};
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key, sizeof(key)));

    /* Null engine */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_rotate_identity(nullptr, key, sizeof(key)));
    /* Null key material */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_rotate_identity(engine, nullptr, 32));
    /* Zero length */
    EXPECT_EQ(KOME_ERR_MISUSE, kome_rotate_identity(engine, key, 0));
}

/* Two namespaces: ns1 grants B WRITE, ns2 is owner-only.
   A writes to both. Connect. B only gets ns1 entries. */
TEST_F(NamespaceSyncTest, MultipleNamespacesIndependent) {
    /* Configure ns1 with bidirectional WRITE */
    configure_ns("ns1");

    /* Configure ns2 as owner-only on A */
    KomeNamespaceConfig cfg_ns2_a = {};
    cfg_ns2_a.name = "ns2";
    cfg_ns2_a.acl = nullptr;
    cfg_ns2_a.acl_count = 0;
    ASSERT_EQ(KOME_OK, kome_configure_namespace(engine_a, &cfg_ns2_a));

    /* A writes to both namespaces */
    for (int i = 0; i < 3; i++) {
        std::string key = "mk_" + std::to_string(i);
        std::string val = "mv_" + std::to_string(i);
        KomeEntryMeta m;
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "ns1",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
        ASSERT_EQ(KOME_OK, kome_put(engine_a, "ns2",
            (const uint8_t*)key.data(), key.size(),
            (const uint8_t*)val.data(), val.size(), &m));
    }

    /* Connect */
    loopback.connect();

    /* B should have ns1 entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "mk_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_OK, kome_get_meta(engine_b, "ns1",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "B should have ns1 key: " << key;
    }

    /* B should NOT have ns2 entries */
    for (int i = 0; i < 3; i++) {
        std::string key = "mk_" + std::to_string(i);
        KomeEntryMeta meta;
        EXPECT_EQ(KOME_ERR_NOT_FOUND, kome_get_meta(engine_b, "ns2",
            (const uint8_t*)key.data(), key.size(), &meta))
            << "B should NOT have ns2 key: " << key;
    }
}
