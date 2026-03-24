#include <gtest/gtest.h>
#include "kome.h"
#include "kome_sign.hpp"
#include "kome_util.hpp"
#include "kome_wire.hpp"
#include "kome_test_helpers.hpp"
#include <cstring>
#include <string>
#include <vector>

/* ========================================================================
   Unit tests for entry signing infrastructure (issue #24).

   The current signing scheme is a PLACEHOLDER (SHA-256 MAC) that will be
   replaced by Ed25519. These tests verify the signing infrastructure —
   wire format, storage, call sites — not the cryptographic strength.
   ======================================================================== */

/* --- Low-level sign/verify tests ---------------------------------------- */

TEST(SigningTest, SignProducesNonZeroSignature) {
    uint8_t secret[32];
    std::memset(secret, 0x42, 32);

    uint8_t value_hash[32];
    std::memset(value_hash, 0xAA, 32);

    uint8_t author[32];
    std::memset(author, 0xBB, 32);

    uint8_t sig[64] = {};
    kome::sign_entry(secret, 32, "test_ns",
                     (const uint8_t*)"key", 3,
                     value_hash, 1000000, 1, author, sig);

    EXPECT_TRUE(kome::signature_is_nonzero(sig));
}

TEST(SigningTest, SignatureDeterministic) {
    uint8_t secret[32];
    std::memset(secret, 0x42, 32);

    uint8_t value_hash[32], author[32];
    std::memset(value_hash, 0xAA, 32);
    std::memset(author, 0xBB, 32);

    uint8_t sig1[64], sig2[64];
    kome::sign_entry(secret, 32, "ns", (const uint8_t*)"k", 1,
                     value_hash, 999, 5, author, sig1);
    kome::sign_entry(secret, 32, "ns", (const uint8_t*)"k", 1,
                     value_hash, 999, 5, author, sig2);

    EXPECT_EQ(0, std::memcmp(sig1, sig2, 64));
}

TEST(SigningTest, SignatureChangesWithValue) {
    uint8_t secret[32], author[32];
    std::memset(secret, 0x42, 32);
    std::memset(author, 0xBB, 32);

    uint8_t hash1[32], hash2[32];
    std::memset(hash1, 0x11, 32);
    std::memset(hash2, 0x22, 32);

    uint8_t sig1[64], sig2[64];
    kome::sign_entry(secret, 32, "ns", (const uint8_t*)"k", 1,
                     hash1, 1000, 1, author, sig1);
    kome::sign_entry(secret, 32, "ns", (const uint8_t*)"k", 1,
                     hash2, 1000, 1, author, sig2);

    EXPECT_NE(0, std::memcmp(sig1, sig2, 64));
}

TEST(SigningTest, SignatureChangesWithKey) {
    uint8_t secret[32], author[32], value_hash[32];
    std::memset(secret, 0x42, 32);
    std::memset(author, 0xBB, 32);
    std::memset(value_hash, 0xAA, 32);

    uint8_t sig1[64], sig2[64];
    kome::sign_entry(secret, 32, "ns", (const uint8_t*)"key1", 4,
                     value_hash, 1000, 1, author, sig1);
    kome::sign_entry(secret, 32, "ns", (const uint8_t*)"key2", 4,
                     value_hash, 1000, 1, author, sig2);

    EXPECT_NE(0, std::memcmp(sig1, sig2, 64));
}

TEST(SigningTest, SignatureChangesWithSecret) {
    uint8_t secret1[32], secret2[32], author[32], value_hash[32];
    std::memset(secret1, 0x11, 32);
    std::memset(secret2, 0x22, 32);
    std::memset(author, 0xBB, 32);
    std::memset(value_hash, 0xAA, 32);

    uint8_t sig1[64], sig2[64];
    kome::sign_entry(secret1, 32, "ns", (const uint8_t*)"k", 1,
                     value_hash, 1000, 1, author, sig1);
    kome::sign_entry(secret2, 32, "ns", (const uint8_t*)"k", 1,
                     value_hash, 1000, 1, author, sig2);

    EXPECT_NE(0, std::memcmp(sig1, sig2, 64));
}

TEST(SigningTest, VerifyWithCorrectKey) {
    uint8_t secret[32], author[32], value_hash[32];
    std::memset(secret, 0x42, 32);
    std::memset(author, 0xBB, 32);
    std::memset(value_hash, 0xAA, 32);

    uint8_t sig[64];
    kome::sign_entry(secret, 32, "ns", (const uint8_t*)"k", 1,
                     value_hash, 1000, 1, author, sig);

    /* Placeholder: verify with same key (MAC scheme) */
    EXPECT_TRUE(kome::verify_entry_signature(
        secret, 32, "ns", (const uint8_t*)"k", 1,
        value_hash, 1000, 1, author, sig));
}

TEST(SigningTest, VerifyWithWrongKeyFails) {
    uint8_t secret[32], wrong[32], author[32], value_hash[32];
    std::memset(secret, 0x42, 32);
    std::memset(wrong, 0x99, 32);
    std::memset(author, 0xBB, 32);
    std::memset(value_hash, 0xAA, 32);

    uint8_t sig[64];
    kome::sign_entry(secret, 32, "ns", (const uint8_t*)"k", 1,
                     value_hash, 1000, 1, author, sig);

    EXPECT_FALSE(kome::verify_entry_signature(
        wrong, 32, "ns", (const uint8_t*)"k", 1,
        value_hash, 1000, 1, author, sig));
}

TEST(SigningTest, VerifyWithNullKeyChecksNonZero) {
    uint8_t sig_nonzero[64];
    std::memset(sig_nonzero, 0xAA, 64);

    /* NULL key -> falls back to non-zero check */
    EXPECT_TRUE(kome::verify_entry_signature(
        nullptr, 0, "ns", (const uint8_t*)"k", 1,
        sig_nonzero, 1000, 1, sig_nonzero, sig_nonzero));

    uint8_t sig_zero[64] = {};
    EXPECT_FALSE(kome::verify_entry_signature(
        nullptr, 0, "ns", (const uint8_t*)"k", 1,
        sig_zero, 1000, 1, sig_zero, sig_zero));
}

TEST(SigningTest, SignatureIsNonzero) {
    uint8_t all_zero[64] = {};
    EXPECT_FALSE(kome::signature_is_nonzero(all_zero));

    uint8_t one_bit[64] = {};
    one_bit[63] = 1;
    EXPECT_TRUE(kome::signature_is_nonzero(one_bit));
}

/* --- Integration: kome_put produces signed entries ---------------------- */

class SigningEngineTest : public ::testing::Test {
protected:
    KomeEngine *engine = nullptr;
    std::string db_path;

    void SetUp() override {
        db_path = temp_db_path("signing");
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

TEST_F(SigningEngineTest, PutProducesNonZeroSignature) {
    uint8_t key_mat[32];
    std::memset(key_mat, 0x42, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key_mat, 32));

    uint8_t key[] = "mykey";
    uint8_t value[] = "myvalue";
    KomeEntryMeta meta = {};
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 5, value, 7, &meta));

    /* Signature must be non-zero */
    EXPECT_TRUE(kome::signature_is_nonzero(meta.signature));
}

TEST_F(SigningEngineTest, PutSignatureChangesWithDifferentValue) {
    uint8_t key_mat[32];
    std::memset(key_mat, 0x42, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key_mat, 32));

    uint8_t key[] = "k";
    uint8_t val1[] = "value1";
    uint8_t val2[] = "value2";

    KomeEntryMeta meta1 = {}, meta2 = {};
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 1, val1, 6, &meta1));

    /* Overwrite with different value */
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 1, val2, 6, &meta2));

    /* Signatures must differ because value hash differs (and seq differs) */
    EXPECT_NE(0, std::memcmp(meta1.signature, meta2.signature, 64));
}

TEST_F(SigningEngineTest, PutSignatureChangesWithDifferentKey) {
    uint8_t key_mat[32];
    std::memset(key_mat, 0x42, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key_mat, 32));

    uint8_t val[] = "same_value";
    uint8_t k1[] = "key_a";
    uint8_t k2[] = "key_b";

    KomeEntryMeta meta1 = {}, meta2 = {};
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", k1, 5, val, 10, &meta1));
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", k2, 5, val, 10, &meta2));

    /* Different keys → different signatures (even with same value) */
    EXPECT_NE(0, std::memcmp(meta1.signature, meta2.signature, 64));
}

TEST_F(SigningEngineTest, DeleteProducesNonZeroSignature) {
    uint8_t key_mat[32];
    std::memset(key_mat, 0x42, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key_mat, 32));

    uint8_t key[] = "delme";
    uint8_t val[] = "data";
    KomeEntryMeta m;
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 5, val, 4, &m));

    KomeEntryMeta del_meta = {};
    ASSERT_EQ(KOME_OK, kome_delete(engine, "test", key, 5, &del_meta));
    EXPECT_TRUE(kome::signature_is_nonzero(del_meta.signature));
}

TEST_F(SigningEngineTest, GetReturnsSignature) {
    uint8_t key_mat[32];
    std::memset(key_mat, 0x42, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key_mat, 32));

    uint8_t key[] = "rk";
    uint8_t val[] = "rv";
    KomeEntryMeta write_meta = {};
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 2, val, 2, &write_meta));

    uint8_t *out = nullptr;
    size_t out_len = 0;
    KomeEntryMeta read_meta = {};
    ASSERT_EQ(KOME_OK, kome_get(engine, "test", key, 2, &out, &out_len, &read_meta));

    /* Signature from get must match what was written */
    EXPECT_EQ(0, std::memcmp(write_meta.signature, read_meta.signature, 64));
    kome_free_value(out);
}

TEST_F(SigningEngineTest, GetMetaReturnsSignature) {
    uint8_t key_mat[32];
    std::memset(key_mat, 0x42, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key_mat, 32));

    uint8_t key[] = "mk";
    uint8_t val[] = "mv";
    KomeEntryMeta write_meta = {};
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 2, val, 2, &write_meta));

    KomeEntryMeta read_meta = {};
    ASSERT_EQ(KOME_OK, kome_get_meta(engine, "test", key, 2, &read_meta));

    EXPECT_EQ(0, std::memcmp(write_meta.signature, read_meta.signature, 64));
}

TEST_F(SigningEngineTest, BatchPutProducesSignatures) {
    uint8_t key_mat[32];
    std::memset(key_mat, 0x42, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key_mat, 32));

    KomeBatchEntry entries[2];
    entries[0] = {"ns", (const uint8_t*)"k1", 2, (const uint8_t*)"v1", 2};
    entries[1] = {"ns", (const uint8_t*)"k2", 2, (const uint8_t*)"v2", 2};

    KomeEntryMeta metas[2] = {};
    ASSERT_EQ(KOME_OK, kome_put_batch(engine, entries, 2, metas));

    /* Both entries should have non-zero signatures */
    EXPECT_TRUE(kome::signature_is_nonzero(metas[0].signature));
    EXPECT_TRUE(kome::signature_is_nonzero(metas[1].signature));

    /* Different keys → different signatures */
    EXPECT_NE(0, std::memcmp(metas[0].signature, metas[1].signature, 64));
}

/* --- Wire encoding: signature survives round-trip ----------------------- */

TEST(SigningWireTest, SyncEntrySignatureRoundTrip) {
    kome::SyncEntry entry;
    entry.ns = "signed_ns";
    entry.key = {1, 2, 3};
    entry.value = {10, 20, 30};
    entry.timestamp_us = 1234567890;
    std::memset(entry.author, 0xAA, 32);
    entry.seq = 7;
    std::memset(entry.hash, 0xBB, 32);
    entry.tombstone = 0;
    /* Set a distinctive signature pattern */
    for (int i = 0; i < 64; i++)
        entry.signature[i] = (uint8_t)(i * 3 + 0x10);

    auto encoded = kome::encode_sync_entry(entry);
    ASSERT_FALSE(encoded.empty());

    kome::SyncEntry decoded;
    ASSERT_TRUE(kome::decode_sync_entry(encoded.data(), encoded.size(), &decoded));

    EXPECT_EQ(0, std::memcmp(entry.signature, decoded.signature, 64));
}

TEST(SigningWireTest, LiveEntrySignatureRoundTrip) {
    kome::SyncEntry entry;
    entry.ns = "live_ns";
    entry.key = {5};
    entry.value = {50, 60};
    entry.timestamp_us = 999;
    std::memset(entry.author, 0x11, 32);
    entry.seq = 3;
    std::memset(entry.hash, 0x22, 32);
    entry.tombstone = 0;
    std::memset(entry.signature, 0xFF, 64);

    auto encoded = kome::encode_live_entry(entry);
    ASSERT_FALSE(encoded.empty());

    kome::SyncEntry decoded;
    ASSERT_TRUE(kome::decode_live_entry(encoded.data(), encoded.size(), &decoded));

    EXPECT_EQ(0, std::memcmp(entry.signature, decoded.signature, 64));
}

TEST(SigningWireTest, BatchEntrySignatureRoundTrip) {
    std::vector<kome::SyncEntry> entries(2);
    for (int i = 0; i < 2; i++) {
        entries[i].ns = "batch_ns";
        entries[i].key = {(uint8_t)(i + 1)};
        entries[i].value = {(uint8_t)(i + 10)};
        entries[i].timestamp_us = 1000 + i;
        std::memset(entries[i].author, 0xAA + i, 32);
        entries[i].seq = i + 1;
        std::memset(entries[i].hash, 0xCC + i, 32);
        entries[i].tombstone = 0;
        std::memset(entries[i].signature, 0x30 + i, 64);
    }

    auto encoded = kome::encode_batch_entry(entries);
    ASSERT_FALSE(encoded.empty());

    std::vector<kome::SyncEntry> decoded;
    ASSERT_TRUE(kome::decode_batch_entry(encoded.data(), encoded.size(), &decoded));
    ASSERT_EQ(2u, decoded.size());

    for (int i = 0; i < 2; i++) {
        EXPECT_EQ(0, std::memcmp(entries[i].signature, decoded[i].signature, 64));
    }
}

/* --- Sync: signed entries survive replication --------------------------- */

TEST_F(SigningEngineTest, SignedEntrySurvivesSync) {
    /* Set up engine A (writer) */
    uint8_t key_a[32];
    std::memset(key_a, 0xAA, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine, key_a, 32));

    /* Write an entry on A */
    uint8_t key[] = "sync_k";
    uint8_t val[] = "sync_v";
    KomeEntryMeta write_meta = {};
    ASSERT_EQ(KOME_OK, kome_put(engine, "test", key, 6, val, 6, &write_meta));
    ASSERT_TRUE(kome::signature_is_nonzero(write_meta.signature));

    /* Set up engine B (reader) */
    std::string db2 = temp_db_path("signing_b");
    cleanup_db(db2);
    KomeConfig cfg2 = {};
    cfg2.path = db2.c_str();
    KomeEngine *engine_b = nullptr;
    ASSERT_EQ(KOME_OK, kome_open(&cfg2, &engine_b));
    uint8_t key_b[32];
    std::memset(key_b, 0xBB, 32);
    ASSERT_EQ(KOME_OK, kome_set_identity(engine_b, key_b, 32));

    /* Configure namespace ACLs so A can write and B can read */
    /* A's identity fingerprint is SHA-256(0xAA * 32) */
    uint8_t fp_a[32], fp_b[32];
    kome::sha256(key_a, 32, fp_a);
    kome::sha256(key_b, 32, fp_b);

    /* On engine A: allow B to read+write */
    KomeNamespaceACLEntry acl_a;
    std::memcpy(acl_a.fingerprint, fp_b, 32);
    acl_a.role = KOME_ROLE_WRITE;
    KomeNamespaceConfig nscfg_a = {};
    nscfg_a.name = "test";
    nscfg_a.acl = &acl_a;
    nscfg_a.acl_count = 1;
    kome_configure_namespace(engine, &nscfg_a);

    /* On engine B: allow A to write */
    KomeNamespaceACLEntry acl_b;
    std::memcpy(acl_b.fingerprint, fp_a, 32);
    acl_b.role = KOME_ROLE_WRITE;
    KomeNamespaceConfig nscfg_b = {};
    nscfg_b.name = "test";
    nscfg_b.acl = &acl_b;
    nscfg_b.acl_count = 1;
    kome_configure_namespace(engine_b, &nscfg_b);

    /* Connect via loopback transport */
    LoopbackPair lb;
    kome_attach_transport(engine, &lb.a.transport);
    kome_attach_transport(engine_b, &lb.b.transport);

    /* Set correct fingerprints on the loopback */
    std::memcpy(lb.a.fingerprint, fp_a, 32);
    std::memcpy(lb.b.fingerprint, fp_b, 32);

    lb.connect();

    /* Read the entry on B and verify the signature matches */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    KomeEntryMeta read_meta = {};
    ASSERT_EQ(KOME_OK, kome_get(engine_b, "test", key, 6, &out, &out_len, &read_meta));
    ASSERT_NE(nullptr, out);
    EXPECT_EQ(6u, out_len);
    EXPECT_EQ(0, std::memcmp(out, "sync_v", 6));

    /* The signature must survive the wire round-trip */
    EXPECT_EQ(0, std::memcmp(write_meta.signature, read_meta.signature, 64));

    kome_free_value(out);
    kome_close(engine_b);
    cleanup_db(db2);
}

/* --- Protocol version --------------------------------------------------- */

TEST(SigningTest, ProtocolVersion) {
    EXPECT_EQ(3, KOME_PROTOCOL_VERSION);
}
