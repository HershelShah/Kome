#include <gtest/gtest.h>
#include "kome.h"
#include "kome_util.hpp"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>

/*
 * Encryption tests.
 *
 * These tests verify that the encryption_key config path works correctly.
 * With plain SQLite (no SQLCipher), PRAGMA key is a no-op — the database
 * is NOT actually encrypted, but the code path must still succeed.
 * Actual encryption only activates when built with -DKOME_USE_SQLCIPHER=ON.
 */

class EncryptionTest : public ::testing::Test {
protected:
    std::string db_path;

    void SetUp() override {
        db_path = temp_db_path("encryption");
        cleanup_db(db_path);
    }

    void TearDown() override {
        cleanup_db(db_path);
    }
};

/* Opening with a 32-byte encryption key succeeds */
TEST_F(EncryptionTest, OpenWithEncryptionKey) {
    uint8_t key[32];
    std::memset(key, 0x42, sizeof(key));

    KomeConfig cfg = {};
    cfg.path = db_path.c_str();
    cfg.encryption_key = key;
    cfg.encryption_key_len = 32;

    KomeEngine *engine = nullptr;
    ASSERT_EQ(KOME_OK, kome_open(&cfg, &engine));
    ASSERT_NE(nullptr, engine);
    kome_close(engine);
}

/* Opening with NULL encryption key still works (backward compat) */
TEST_F(EncryptionTest, OpenWithNullKey) {
    KomeConfig cfg = {};
    cfg.path = db_path.c_str();
    cfg.encryption_key = nullptr;
    cfg.encryption_key_len = 0;

    KomeEngine *engine = nullptr;
    ASSERT_EQ(KOME_OK, kome_open(&cfg, &engine));
    ASSERT_NE(nullptr, engine);
    kome_close(engine);
}

/* Zero-init config (no encryption fields set) still works */
TEST_F(EncryptionTest, ZeroInitConfigBackwardCompat) {
    KomeConfig cfg = {};
    cfg.path = db_path.c_str();

    KomeEngine *engine = nullptr;
    ASSERT_EQ(KOME_OK, kome_open(&cfg, &engine));
    ASSERT_NE(nullptr, engine);
    kome_close(engine);
}

/* Data written with encryption key can be read back.
 * (With plain SQLite, PRAGMA key is a no-op, so this verifies the
 * code path doesn't corrupt the database.) */
TEST_F(EncryptionTest, WriteAndReadWithKey) {
    uint8_t key[32];
    std::memset(key, 0xAB, sizeof(key));

    KomeConfig cfg = {};
    cfg.path = db_path.c_str();
    cfg.encryption_key = key;
    cfg.encryption_key_len = 32;

    /* Write */
    {
        KomeEngine *engine = nullptr;
        ASSERT_EQ(KOME_OK, kome_open(&cfg, &engine));

        uint8_t id_key[32] = {1};
        ASSERT_EQ(KOME_OK, kome_set_identity(engine, id_key, sizeof(id_key)));

        const uint8_t k[] = "mykey";
        const uint8_t v[] = "myvalue";
        ASSERT_EQ(KOME_OK, kome_put(engine, "test", k, sizeof(k),
                                      v, sizeof(v), nullptr));
        kome_close(engine);
    }

    /* Read back with same key */
    {
        KomeEngine *engine = nullptr;
        ASSERT_EQ(KOME_OK, kome_open(&cfg, &engine));

        const uint8_t k[] = "mykey";
        uint8_t *value = nullptr;
        size_t value_len = 0;
        KomeEntryMeta meta = {};

        ASSERT_EQ(KOME_OK, kome_get(engine, "test", k, sizeof(k),
                                      &value, &value_len, &meta));
        ASSERT_NE(nullptr, value);
        EXPECT_EQ(sizeof("myvalue"), value_len);
        EXPECT_EQ(0, std::memcmp(value, "myvalue", value_len));
        kome_free_value(value);
        kome_close(engine);
    }
}

/* derive_db_key produces a deterministic 32-byte output */
TEST_F(EncryptionTest, DeriveDbKey) {
    uint8_t material[16] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
    uint8_t out1[32], out2[32];

    kome::derive_db_key(material, sizeof(material), out1);
    kome::derive_db_key(material, sizeof(material), out2);

    /* Same input produces same output */
    EXPECT_EQ(0, std::memcmp(out1, out2, 32));

    /* Output is non-zero (sanity check) */
    bool all_zero = true;
    for (int i = 0; i < 32; i++) {
        if (out1[i] != 0) { all_zero = false; break; }
    }
    EXPECT_FALSE(all_zero);
}

/* derive_db_key produces different output for different input */
TEST_F(EncryptionTest, DeriveDbKeyDifferentInput) {
    uint8_t mat_a[16] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
    uint8_t mat_b[16] = {16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1};
    uint8_t out_a[32], out_b[32];

    kome::derive_db_key(mat_a, sizeof(mat_a), out_a);
    kome::derive_db_key(mat_b, sizeof(mat_b), out_b);

    EXPECT_NE(0, std::memcmp(out_a, out_b, 32));
}

/*
 * NOTE: Testing that a wrong key fails to open an encrypted database
 * requires SQLCipher. With plain SQLite, PRAGMA key is a no-op and any
 * "key" will appear to work since the database is not actually encrypted.
 * That test belongs in a SQLCipher-specific integration test suite.
 */
