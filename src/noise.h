/* noise.h — Noise XX handshake + transport channel (M4). Internal.
 *
 * Pattern: Noise_XX with X25519 DH and SHA-256 hash. The AEAD is monocypher's
 * XChaCha20-Poly1305 (24-byte nonce) rather than RFC 8439 ChaCha20-Poly1305, so
 * this is not wire-compatible with standard Noise — see DECISIONS.md. It
 * provides a mutually authenticated, forward-secret byte channel that the M3
 * reconciliation session runs inside. */
#ifndef SYNC_NOISE_H
#define SYNC_NOISE_H

#include <array>
#include <cstdint>
#include <string>

#include "crypto.h"

namespace ke {

class NoiseChannel {
public:
    NoiseChannel(bool initiator, const KeyPair &identity);

    /* Handshake pump. Feed the peer's last handshake message (empty for the
     * initiator's first call); receive the next message to send in out. Sets
     * done when the handshake is complete on this side. Returns false on a
     * malformed/forged handshake message. */
    bool step(const std::string &in, std::string &out, bool &done);
    bool done() const { return done_; }

    /* Transport encryption (only valid once done()). */
    bool encrypt(const std::string &pt, std::string &out);
    bool decrypt(const std::string &ct, std::string &pt);

    /* The peer's authenticated X25519 static public key. */
    const uint8_t *remote_static() const { return rs_.data(); }

private:
    bool      initiator_;
    int       msgidx_ = 0;
    bool      done_ = false;

    /* SymmetricState. */
    std::array<uint8_t, 32> ck_{}, h_{}, k_{};
    bool     has_key_ = false;
    uint64_t nonce_ = 0;

    /* Keys. */
    std::array<uint8_t, 32> s_sk_{}, s_pk_{}; /* local static (identity DH) */
    std::array<uint8_t, 32> e_sk_{}, e_pk_{}; /* local ephemeral */
    std::array<uint8_t, 32> re_{}, rs_{};     /* remote ephemeral / static */

    /* Transport keys after Split(). */
    std::array<uint8_t, 32> send_k_{}, recv_k_{};
    uint64_t send_nonce_ = 0, recv_nonce_ = 0;

    void mix_hash(const uint8_t *d, size_t n);
    void mix_key(const uint8_t dh[32]);
    bool encrypt_hash(const uint8_t *pt, size_t n, std::string &out);
    bool decrypt_hash(const uint8_t *ct, size_t n, std::string &pt);
    void split();
};

} // namespace ke

#endif /* SYNC_NOISE_H */
