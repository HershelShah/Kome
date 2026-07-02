/* crypto.h — thin wrapper over monocypher + our SHA-256 (M4). Internal.
 *
 * Provides the primitives the engine needs: a long-term identity keypair
 * (EdDSA signing + X25519 agreement), record signing/verification, BLAKE2b-256
 * (for site ids), X25519 DH, an AEAD (XChaCha20-Poly1305), and HMAC-SHA256 /
 * HKDF for the Noise channel. */
#ifndef SYNC_CRYPTO_H
#define SYNC_CRYPTO_H

#include <array>
#include <cstddef>
#include <cstdint>

namespace ke {

constexpr size_t kSignPkLen = 32;  /* EdDSA public key */
constexpr size_t kSignSkLen = 64;  /* EdDSA secret key (seed||public) */
constexpr size_t kDhKeyLen  = 32;  /* X25519 key */

/* A long-term identity. The signing public key defines the site identity;
 * site_id = BLAKE2b-256(sign_pk). The X25519 pair is used for the channel. */
struct KeyPair {
    std::array<uint8_t, kSignSkLen> sign_sk{};
    std::array<uint8_t, kSignPkLen> sign_pk{};
    std::array<uint8_t, kDhKeyLen>  dh_sk{};
    std::array<uint8_t, kDhKeyLen>  dh_pk{};
};

/* Deterministically derive an identity from a 32-byte seed. */
KeyPair keypair_from_seed(const uint8_t seed[32]);

/* site_id = BLAKE2b-256(signing public key). */
void site_id_from_pubkey(const uint8_t sign_pk[32], uint8_t out[32]);

/* General BLAKE2b with a chosen output length. */
void blake2b(const void *data, size_t len, uint8_t *out, size_t out_len);

/* EdDSA sign / verify (BLAKE2b-based, via monocypher core). */
void sign(const uint8_t sk[64], const void *msg, size_t len, uint8_t sig[64]);
bool verify(const uint8_t pk[32], const void *msg, size_t len, const uint8_t sig[64]);

/* X25519 Diffie-Hellman: shared = DH(my_sk, their_pk). */
void x25519(const uint8_t my_sk[32], const uint8_t their_pk[32],
            uint8_t shared[32]);
void x25519_public(const uint8_t sk[32], uint8_t pk[32]);

/* AEAD (XChaCha20-Poly1305). Returns true on successful authentication. */
void aead_encrypt(const uint8_t key[32], const uint8_t nonce[24],
                  const uint8_t *ad, size_t ad_len, const uint8_t *pt,
                  size_t pt_len, uint8_t *ct, uint8_t mac[16]);
bool aead_decrypt(const uint8_t key[32], const uint8_t nonce[24],
                  const uint8_t *ad, size_t ad_len, const uint8_t *ct,
                  size_t ct_len, const uint8_t mac[16], uint8_t *pt);

/* HMAC-SHA256 and HKDF-SHA256 (used by the Noise channel). */
void hmac_sha256(const uint8_t *key, size_t key_len, const uint8_t *msg,
                 size_t msg_len, uint8_t out[32]);

/* Fill buf with cryptographically random bytes (from the OS CSPRNG).
 * Returns false if no entropy source is available. */
bool random_bytes(uint8_t *buf, size_t len);

/* Zero a buffer in a way the compiler won't optimize away (for secrets). */
void secure_wipe(void *p, size_t n);

/* Constant-time equality for two 16-byte buffers (MAC/nonce/cookie compares):
 * runs in time independent of where the first differing byte is, so it leaks no
 * timing oracle an attacker could use to forge a tag byte-by-byte. Returns true
 * iff the buffers are equal. */
bool ct_eq16(const uint8_t a[16], const uint8_t b[16]);

} // namespace ke

#endif /* SYNC_CRYPTO_H */
