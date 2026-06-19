/* crypto_test.cpp — known-answer and round-trip tests for the crypto
 * primitives underpinning M4 (satisfies T4.2's primitive-KAT requirement). */
#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <string>
#include <vector>

#include "crypto.h"
#include "sha256.h"

namespace {

std::vector<uint8_t> unhex(const std::string &s) {
    std::vector<uint8_t> out;
    for (size_t i = 0; i + 1 < s.size(); i += 2)
        out.push_back((uint8_t)std::stoi(s.substr(i, 2), nullptr, 16));
    return out;
}

std::string hex(const uint8_t *p, size_t n) {
    static const char *d = "0123456789abcdef";
    std::string s;
    for (size_t i = 0; i < n; i++) {
        s.push_back(d[p[i] >> 4]);
        s.push_back(d[p[i] & 0xf]);
    }
    return s;
}

} // namespace

/* SHA-256("abc") — FIPS 180-4. */
TEST(Crypto, Sha256Kat) {
    uint8_t out[32];
    sync_engine_detail::sha256("abc", 3, out);
    EXPECT_EQ(hex(out, 32),
              "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
}

/* HMAC-SHA256 — RFC 4231 test case 2. */
TEST(Crypto, HmacSha256Kat) {
    std::string key = "Jefe";
    std::string msg = "what do ya want for nothing?";
    uint8_t out[32];
    ke::hmac_sha256((const uint8_t *)key.data(), key.size(),
                    (const uint8_t *)msg.data(), msg.size(), out);
    EXPECT_EQ(hex(out, 32),
              "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843");
}

/* HMAC-SHA256 — RFC 4231 test case 6 (key longer than the block size). */
TEST(Crypto, HmacSha256LongKey) {
    std::vector<uint8_t> key(131, 0xaa);
    std::string msg = "Test Using Larger Than Block-Size Key - Hash Key First";
    uint8_t out[32];
    ke::hmac_sha256(key.data(), key.size(), (const uint8_t *)msg.data(),
                    msg.size(), out);
    EXPECT_EQ(hex(out, 32),
              "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54");
}

/* X25519 — RFC 7748 section 5.2 first test vector. */
TEST(Crypto, X25519Kat) {
    auto scalar = unhex(
        "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4");
    auto u = unhex(
        "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c");
    uint8_t out[32];
    ke::x25519(scalar.data(), u.data(), out);
    EXPECT_EQ(hex(out, 32),
              "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552");
}

/* BLAKE2b-512("abc") — RFC 7693 appendix A. */
TEST(Crypto, Blake2bKat) {
    uint8_t out[64];
    ke::blake2b("abc", 3, out, 64);
    EXPECT_EQ(
        hex(out, 64),
        "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1"
        "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923");
}

/* EdDSA sign/verify round-trip + tamper + wrong-key rejection. */
TEST(Crypto, EddsaSignVerify) {
    uint8_t seed[32];
    std::memset(seed, 0x5A, sizeof seed);
    ke::KeyPair kp = ke::keypair_from_seed(seed);

    std::string msg = "capability statement";
    uint8_t sig[64];
    ke::sign(kp.sign_sk.data(), msg.data(), msg.size(), sig);
    EXPECT_TRUE(ke::verify(kp.sign_pk.data(), msg.data(), msg.size(), sig));

    /* Tampered message fails. */
    std::string bad = msg + "!";
    EXPECT_FALSE(ke::verify(kp.sign_pk.data(), bad.data(), bad.size(), sig));

    /* Tampered signature fails. */
    uint8_t sig2[64];
    std::memcpy(sig2, sig, 64);
    sig2[10] ^= 0x01;
    EXPECT_FALSE(ke::verify(kp.sign_pk.data(), msg.data(), msg.size(), sig2));

    /* Wrong key fails. */
    uint8_t seed2[32];
    std::memset(seed2, 0x6B, sizeof seed2);
    ke::KeyPair kp2 = ke::keypair_from_seed(seed2);
    EXPECT_FALSE(ke::verify(kp2.sign_pk.data(), msg.data(), msg.size(), sig));
}

/* Deterministic identity: same seed -> same keys -> same site_id. */
TEST(Crypto, DeterministicIdentity) {
    uint8_t seed[32];
    std::memset(seed, 0x11, sizeof seed);
    ke::KeyPair a = ke::keypair_from_seed(seed);
    ke::KeyPair b = ke::keypair_from_seed(seed);
    EXPECT_EQ(a.sign_pk, b.sign_pk);
    EXPECT_EQ(a.dh_pk, b.dh_pk);

    uint8_t id1[32], id2[32];
    ke::site_id_from_pubkey(a.sign_pk.data(), id1);
    ke::site_id_from_pubkey(b.sign_pk.data(), id2);
    EXPECT_EQ(0, std::memcmp(id1, id2, 32));
}

/* AEAD round-trip + tamper detection (T4.3 at the primitive level). */
TEST(Crypto, AeadRoundTripAndTamper) {
    uint8_t key[32], nonce[24];
    std::memset(key, 0x01, sizeof key);
    std::memset(nonce, 0x02, sizeof nonce);
    std::string pt = "secret payload that must not leak";
    std::string ad = "associated data";

    std::vector<uint8_t> ct(pt.size());
    uint8_t mac[16];
    ke::aead_encrypt(key, nonce, (const uint8_t *)ad.data(), ad.size(),
                     (const uint8_t *)pt.data(), pt.size(), ct.data(), mac);
    EXPECT_NE(std::string((char *)ct.data(), ct.size()), pt); /* not plaintext */

    std::vector<uint8_t> rt(pt.size());
    EXPECT_TRUE(ke::aead_decrypt(key, nonce, (const uint8_t *)ad.data(),
                                 ad.size(), ct.data(), ct.size(), mac,
                                 rt.data()));
    EXPECT_EQ(std::string((char *)rt.data(), rt.size()), pt);

    /* Flip one ciphertext byte -> authentication fails. */
    std::vector<uint8_t> ct2 = ct;
    ct2[0] ^= 0x01;
    EXPECT_FALSE(ke::aead_decrypt(key, nonce, (const uint8_t *)ad.data(),
                                  ad.size(), ct2.data(), ct2.size(), mac,
                                  rt.data()));
    /* Flip the tag -> fails. */
    uint8_t mac2[16];
    std::memcpy(mac2, mac, 16);
    mac2[0] ^= 0x01;
    EXPECT_FALSE(ke::aead_decrypt(key, nonce, (const uint8_t *)ad.data(),
                                  ad.size(), ct.data(), ct.size(), mac2,
                                  rt.data()));
}

/* F4: constant-time 16-byte equality used for MAC/nonce/cookie compares. We
 * can't assert timing here, but pin the functional contract — equal vs. a
 * difference in any position (notably the last byte, where a short-circuiting
 * memcmp would diverge most). */
TEST(Crypto, ConstantTimeEq16) {
    uint8_t a[16], b[16];
    for (int i = 0; i < 16; i++) a[i] = b[i] = (uint8_t)(i * 7 + 1);
    EXPECT_TRUE(ke::ct_eq16(a, b));
    b[0] ^= 0x80; /* first-byte difference */
    EXPECT_FALSE(ke::ct_eq16(a, b));
    b[0] = a[0];
    b[15] ^= 0x01; /* last-byte difference */
    EXPECT_FALSE(ke::ct_eq16(a, b));
}
