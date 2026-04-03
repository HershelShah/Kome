#ifndef KOME_UTIL_HPP
#define KOME_UTIL_HPP

#include <cstdint>
#include <cstddef>

namespace kome {

/* SHA-256 — standalone, no heap allocation for messages <= 16 MiB */
void sha256(const uint8_t *data, size_t len, uint8_t out[32]);

/*
 * Derive a 32-byte database encryption key from arbitrary key material.
 * Uses SHA-256("kome-db-key" || key_material).
 * Input should already have high entropy (e.g. a random 32-byte secret).
 */
void derive_db_key(const uint8_t *key_material, size_t key_len, uint8_t out[32]);

/* Current time in microseconds */
uint64_t timestamp_us();

/* CSPRNG — reads from /dev/urandom */
void random_bytes(uint8_t *out, size_t len);

/* HMAC-SHA256 */
void hmac_sha256(const uint8_t *key, size_t key_len,
                 const uint8_t *msg, size_t msg_len,
                 uint8_t out[32]);

/* HKDF-SHA256 (RFC 5869): extract-then-expand */
void hkdf_sha256(const uint8_t *salt, size_t salt_len,
                 const uint8_t *ikm,  size_t ikm_len,
                 const uint8_t *info, size_t info_len,
                 uint8_t *out, size_t out_len);

} /* namespace kome */

#endif /* KOME_UTIL_HPP */
