/* crypto.cpp — crypto wrapper over monocypher + our SHA-256 (M4). */
#include "crypto.h"

#include <cstdio>
#include <cstring>

#include "monocypher.h"
#include "sha256.h"

namespace ke {

using sync_engine_detail::Sha256;

void blake2b(const void *data, size_t len, uint8_t *out, size_t out_len) {
    crypto_blake2b(out, out_len, (const uint8_t *)data, len);
}

void site_id_from_pubkey(const uint8_t sign_pk[32], uint8_t out[32]) {
    crypto_blake2b(out, 32, sign_pk, 32);
}

KeyPair keypair_from_seed(const uint8_t seed[32]) {
    KeyPair kp;
    /* Derive two independent sub-seeds from the master seed. */
    uint8_t buf[33];
    std::memcpy(buf, seed, 32);

    uint8_t sign_seed[32];
    buf[32] = 0x01;
    crypto_blake2b(sign_seed, 32, buf, 33);
    crypto_eddsa_key_pair(kp.sign_sk.data(), kp.sign_pk.data(), sign_seed);
    /* crypto_eddsa_key_pair wipes sign_seed. */

    buf[32] = 0x02;
    crypto_blake2b(kp.dh_sk.data(), 32, buf, 33);
    crypto_x25519_public_key(kp.dh_pk.data(), kp.dh_sk.data());

    crypto_wipe(buf, sizeof buf);
    return kp;
}

void sign(const uint8_t sk[64], const void *msg, size_t len, uint8_t sig[64]) {
    crypto_eddsa_sign(sig, sk, (const uint8_t *)msg, len);
}

bool verify(const uint8_t pk[32], const void *msg, size_t len,
            const uint8_t sig[64]) {
    return crypto_eddsa_check(sig, pk, (const uint8_t *)msg, len) == 0;
}

void x25519(const uint8_t my_sk[32], const uint8_t their_pk[32],
            uint8_t shared[32]) {
    crypto_x25519(shared, my_sk, their_pk);
}

void x25519_public(const uint8_t sk[32], uint8_t pk[32]) {
    crypto_x25519_public_key(pk, sk);
}

void aead_encrypt(const uint8_t key[32], const uint8_t nonce[24],
                  const uint8_t *ad, size_t ad_len, const uint8_t *pt,
                  size_t pt_len, uint8_t *ct, uint8_t mac[16]) {
    crypto_aead_lock(ct, mac, key, nonce, ad, ad_len, pt, pt_len);
}

bool aead_decrypt(const uint8_t key[32], const uint8_t nonce[24],
                  const uint8_t *ad, size_t ad_len, const uint8_t *ct,
                  size_t ct_len, const uint8_t mac[16], uint8_t *pt) {
    return crypto_aead_unlock(pt, mac, key, nonce, ad, ad_len, ct, ct_len) == 0;
}

void hmac_sha256(const uint8_t *key, size_t key_len, const uint8_t *msg,
                 size_t msg_len, uint8_t out[32]) {
    uint8_t k[64];
    std::memset(k, 0, sizeof k);
    if (key_len > 64) {
        Sha256 h;
        h.update(key, key_len);
        h.finish(k); /* 32 bytes, rest stays zero */
    } else {
        std::memcpy(k, key, key_len);
    }
    uint8_t ipad[64], opad[64];
    for (int i = 0; i < 64; i++) {
        ipad[i] = k[i] ^ 0x36;
        opad[i] = k[i] ^ 0x5c;
    }
    uint8_t inner[32];
    {
        Sha256 h;
        h.update(ipad, 64);
        h.update(msg, msg_len);
        h.finish(inner);
    }
    {
        Sha256 h;
        h.update(opad, 64);
        h.update(inner, 32);
        h.finish(out);
    }
    crypto_wipe(k, sizeof k);
    crypto_wipe(ipad, sizeof ipad);
    crypto_wipe(opad, sizeof opad);
}

bool random_bytes(uint8_t *buf, size_t len) {
    FILE *f = std::fopen("/dev/urandom", "rb");
    if (!f) return false;
    size_t got = std::fread(buf, 1, len, f);
    std::fclose(f);
    return got == len;
}

} // namespace ke
