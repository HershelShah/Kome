/*
 * Minimal Monocypher-compatible API — vendored for Kome
 *
 * Provides:
 *   - X25519 Diffie-Hellman (Curve25519)
 *   - ChaCha20-Poly1305 AEAD
 *   - Secure memory wipe
 *
 * Public domain (CC0).  Written from the RFCs:
 *   - RFC 7748  (X25519)
 *   - RFC 7539  (ChaCha20-Poly1305)
 */
#ifndef MONOCYPHER_H
#define MONOCYPHER_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* X25519 -------------------------------------------------------------- */

/* Compute public key from secret key (clamp + base-point multiply). */
void crypto_x25519_public_key(uint8_t public_key[32],
                               const uint8_t secret_key[32]);

/* Diffie-Hellman: shared = scalar_mult(your_secret, their_public). */
void crypto_x25519(uint8_t shared_key[32],
                   const uint8_t your_secret_key[32],
                   const uint8_t their_public_key[32]);

/* ChaCha20-Poly1305 AEAD ---------------------------------------------- */

/* Encrypt + authenticate.
 * mac        : 16-byte output tag
 * cipher_text: output ciphertext (same size as plain_text)
 * key        : 32-byte key
 * nonce      : 8-byte nonce (padded to 12 internally with 4 zero bytes)
 * ad         : additional data (may be NULL if ad_size == 0)
 * plain_text : input plaintext
 * text_size  : length of plain_text / cipher_text
 */
void crypto_aead_lock(uint8_t        mac[16],
                      uint8_t       *cipher_text,
                      const uint8_t  key[32],
                      const uint8_t  nonce[8],
                      const uint8_t *ad,       size_t ad_size,
                      const uint8_t *plain_text, size_t text_size);

/* Decrypt + verify.  Returns 0 on success, -1 on authentication failure.
 * plain_text : output plaintext (same size as cipher_text)
 * key        : 32-byte key
 * nonce      : 8-byte nonce
 * mac        : 16-byte expected tag
 * ad         : additional data
 * cipher_text: input ciphertext
 * text_size  : length of cipher_text / plain_text
 */
int crypto_aead_unlock(uint8_t       *plain_text,
                       const uint8_t  key[32],
                       const uint8_t  nonce[8],
                       const uint8_t  mac[16],
                       const uint8_t *ad,         size_t ad_size,
                       const uint8_t *cipher_text, size_t text_size);

/* Utility ------------------------------------------------------------- */

/* Secure wipe (volatile, not elided by the compiler). */
void crypto_wipe(void *secret, size_t size);

#ifdef __cplusplus
}
#endif

#endif /* MONOCYPHER_H */
