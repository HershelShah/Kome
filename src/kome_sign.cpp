#include "kome_sign.hpp"
#include "kome_util.hpp"
#include <cstring>
#include <vector>

namespace kome {

/* --- Helpers ------------------------------------------------------------- */

static inline void store64le(uint8_t out[8], uint64_t v) {
    out[0] = (uint8_t)(v);       out[1] = (uint8_t)(v >> 8);
    out[2] = (uint8_t)(v >> 16); out[3] = (uint8_t)(v >> 24);
    out[4] = (uint8_t)(v >> 32); out[5] = (uint8_t)(v >> 40);
    out[6] = (uint8_t)(v >> 48); out[7] = (uint8_t)(v >> 56);
}

void compute_entry_payload_hash(
    const char *ns, const uint8_t *key, size_t key_len,
    const uint8_t value_hash[32], uint64_t timestamp_us,
    uint64_t seq, const uint8_t author[32],
    uint8_t payload_hash_out[32])
{
    /*
     * payload_hash = SHA-256(ns || key || value_hash || timestamp_us_le || seq_le || author)
     *
     * We build the concatenation into a flat buffer and hash it in one shot.
     * Maximum size:  255 (ns) + 512 (key) + 32 + 8 + 8 + 32 = 847 bytes.
     */
    size_t ns_len = ns ? std::strlen(ns) : 0;
    size_t total = ns_len + key_len + 32 + 8 + 8 + 32;
    std::vector<uint8_t> buf(total);

    size_t off = 0;
    if (ns_len > 0) { std::memcpy(buf.data() + off, ns, ns_len);          off += ns_len; }
    if (key_len > 0) { std::memcpy(buf.data() + off, key, key_len);       off += key_len; }
    std::memcpy(buf.data() + off, value_hash, 32);                         off += 32;
    store64le(buf.data() + off, timestamp_us);                              off += 8;
    store64le(buf.data() + off, seq);                                       off += 8;
    std::memcpy(buf.data() + off, author, 32);                              off += 32;

    sha256(buf.data(), off, payload_hash_out);
}

void sign_entry(const uint8_t *secret_key, size_t secret_key_len,
                const char *ns, const uint8_t *key, size_t key_len,
                const uint8_t value_hash[32], uint64_t timestamp_us,
                uint64_t seq, const uint8_t author[32],
                uint8_t signature_out[64])
{
    /*
     * PLACEHOLDER signing scheme (will be replaced by Ed25519):
     *
     *   payload_hash = compute_entry_payload_hash(...)
     *   sig[0..32]   = SHA-256(secret_key || payload_hash)
     *   sig[32..64]  = SHA-256(payload_hash || secret_key)
     */
    uint8_t payload_hash[32];
    compute_entry_payload_hash(ns, key, key_len, value_hash,
                               timestamp_us, seq, author, payload_hash);

    /* First half: SHA-256(secret_key || payload_hash) */
    {
        std::vector<uint8_t> buf(secret_key_len + 32);
        std::memcpy(buf.data(), secret_key, secret_key_len);
        std::memcpy(buf.data() + secret_key_len, payload_hash, 32);
        sha256(buf.data(), buf.size(), signature_out);
    }

    /* Second half: SHA-256(payload_hash || secret_key) */
    {
        std::vector<uint8_t> buf(32 + secret_key_len);
        std::memcpy(buf.data(), payload_hash, 32);
        std::memcpy(buf.data() + 32, secret_key, secret_key_len);
        sha256(buf.data(), buf.size(), signature_out + 32);
    }
}

bool verify_entry_signature(const uint8_t *public_key, size_t public_key_len,
                            const char *ns, const uint8_t *key, size_t key_len,
                            const uint8_t value_hash[32], uint64_t timestamp_us,
                            uint64_t seq, const uint8_t author[32],
                            const uint8_t signature[64])
{
    /*
     * PLACEHOLDER verification:
     *
     * Since the current scheme is a symmetric MAC, real verification
     * requires the secret key (== public_key in this placeholder).
     * If we have the key, recompute and compare.
     * If we don't have the key (public_key == NULL), just check non-zero.
     *
     * When Ed25519 replaces this, verification will use the actual public
     * key and will be cryptographically sound.
     */
    if (!public_key || public_key_len == 0) {
        /* No key available — fall back to non-zero check */
        return signature_is_nonzero(signature);
    }

    /* Recompute the signature with the provided key material and compare */
    uint8_t expected[64];
    sign_entry(public_key, public_key_len,
               ns, key, key_len, value_hash,
               timestamp_us, seq, author, expected);

    /* Constant-time comparison to prevent timing attacks */
    uint8_t diff = 0;
    for (int i = 0; i < 64; i++)
        diff |= signature[i] ^ expected[i];
    return diff == 0;
}

bool signature_is_nonzero(const uint8_t signature[64]) {
    uint8_t acc = 0;
    for (int i = 0; i < 64; i++)
        acc |= signature[i];
    return acc != 0;
}

} /* namespace kome */
