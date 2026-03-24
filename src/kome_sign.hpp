#ifndef KOME_SIGN_HPP
#define KOME_SIGN_HPP

/*
 * Entry signing module — PLACEHOLDER implementation.
 *
 * This module provides the signing/verification infrastructure for Kome
 * entries.  Every local write produces a 64-byte signature that is stored
 * alongside the entry metadata, persisted in SQLite, and sent over the wire.
 *
 * IMPORTANT — PLACEHOLDER SCHEME (will be replaced by Ed25519)
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The current implementation uses SHA-256-based MAC, NOT a real digital
 * signature.  It requires knowledge of the secret key to both produce AND
 * verify signatures (symmetric, not asymmetric).  This means:
 *
 *   - A peer can prove it authored an entry ONLY if the verifier knows
 *     the peer's secret key (which defeats the purpose of public-key crypto).
 *   - For now, remote entries are NOT fully verified — we only check that
 *     the signature field is non-zero (i.e., the sender claims to have signed).
 *
 * The VALUE of this module is the infrastructure — wire format, storage
 * schema, signing/verification call sites — not the cryptographic primitive.
 * Swapping to real Ed25519 requires only replacing the two functions below.
 *
 * Placeholder scheme:
 *   payload_hash = SHA-256(ns || key || value_hash || timestamp_us_le || seq_le || author)
 *   sig[0..32]   = SHA-256(secret_key || payload_hash)
 *   sig[32..64]  = SHA-256(payload_hash || secret_key)
 */

#include <cstdint>
#include <cstddef>

namespace kome {

/*
 * Compute the canonical payload hash for an entry.
 * payload_hash = SHA-256(ns || key || value_hash || timestamp_us_le || seq_le || author)
 */
void compute_entry_payload_hash(
    const char *ns, const uint8_t *key, size_t key_len,
    const uint8_t value_hash[32], uint64_t timestamp_us,
    uint64_t seq, const uint8_t author[32],
    uint8_t payload_hash_out[32]);

/*
 * Sign an entry using the secret key (placeholder: SHA-256 MAC).
 *
 * Produces a 64-byte signature:
 *   sig[0..32]  = SHA-256(secret_key || payload_hash)
 *   sig[32..64] = SHA-256(payload_hash || secret_key)
 *
 * When Ed25519 replaces this, secret_key will be the 64-byte Ed25519
 * expanded secret key and the signature will be a proper Ed25519 signature.
 */
void sign_entry(const uint8_t *secret_key, size_t secret_key_len,
                const char *ns, const uint8_t *key, size_t key_len,
                const uint8_t value_hash[32], uint64_t timestamp_us,
                uint64_t seq, const uint8_t author[32],
                uint8_t signature_out[64]);

/*
 * Verify an entry signature.
 *
 * PLACEHOLDER: Since the current scheme is a MAC, full verification requires
 * the secret key.  When called with a peer's public key (which we don't
 * store yet), this function only checks that the signature is non-zero.
 *
 * When Ed25519 replaces this, public_key will be the 32-byte Ed25519 public
 * key and verification will be cryptographically sound.
 *
 * Returns true if the signature passes verification.
 */
bool verify_entry_signature(const uint8_t *public_key, size_t public_key_len,
                            const char *ns, const uint8_t *key, size_t key_len,
                            const uint8_t value_hash[32], uint64_t timestamp_us,
                            uint64_t seq, const uint8_t author[32],
                            const uint8_t signature[64]);

/*
 * Check whether a signature is non-zero (i.e., the entry was signed).
 * Used as a lightweight check when we don't have the peer's key for
 * full verification.
 */
bool signature_is_nonzero(const uint8_t signature[64]);

} /* namespace kome */

#endif /* KOME_SIGN_HPP */
