#ifndef KOME_NOISE_HPP
#define KOME_NOISE_HPP

#include "kome_transport.hpp"
#include <cstdint>
#include <cstddef>
#include <vector>
#include <map>
#include <string>
#include <mutex>
#include <functional>

namespace kome {

/* Wire-format tag bytes for Noise messages.
 * These are chosen to not collide with existing WireMessageType values (0x01-0x07). */
static constexpr uint8_t NOISE_HANDSHAKE_TAG = 0x0F;
static constexpr uint8_t NOISE_TRANSPORT_TAG = 0x10;

/* =====================================================================
 * NoiseSession — implements the Noise XX handshake and transport crypto
 * ===================================================================== */

class NoiseSession {
public:
    enum State { INIT, HANDSHAKE_1_SENT, HANDSHAKE_2_SENT, ESTABLISHED, FAILED };

    /* Initialize as initiator or responder */
    void init_initiator(const uint8_t local_static_priv[32],
                        const uint8_t local_static_pub[32],
                        const uint8_t local_fingerprint[32]);
    void init_responder(const uint8_t local_static_priv[32],
                        const uint8_t local_static_pub[32],
                        const uint8_t local_fingerprint[32]);

    /* Handshake message generation / processing */
    std::vector<uint8_t> write_handshake_msg();
    bool read_handshake_msg(const uint8_t *data, size_t len);

    /* After ESTABLISHED: encrypt/decrypt transport messages */
    std::vector<uint8_t> encrypt(const uint8_t *plaintext, size_t len);
    bool decrypt(const uint8_t *ciphertext, size_t len,
                 std::vector<uint8_t> &plaintext_out);

    State state() const { return state_; }
    bool is_initiator() const { return is_initiator_; }
    const uint8_t* ephemeral_pub() const { return ephemeral_pub_; }
    const uint8_t* remote_fingerprint() const { return remote_fingerprint_; }

private:
    State state_ = INIT;
    bool is_initiator_ = false;

    /* Symmetric state (Noise framework) */
    uint8_t h_[32];    /* handshake hash */
    uint8_t ck_[32];   /* chaining key */
    uint8_t k_[32];    /* cipher key (during handshake) */
    bool has_key_ = false;
    uint64_t nonce_ = 0;

    /* Local keys */
    uint8_t local_static_priv_[32];
    uint8_t local_static_pub_[32];
    uint8_t local_fingerprint_[32];
    uint8_t ephemeral_priv_[32];
    uint8_t ephemeral_pub_[32];

    /* Remote keys */
    uint8_t remote_static_pub_[32];
    uint8_t remote_ephemeral_pub_[32];
    uint8_t remote_fingerprint_[32];

    /* Transport keys (after Split) */
    uint8_t send_key_[32];
    uint8_t recv_key_[32];
    uint64_t send_nonce_ = 0;
    uint64_t recv_nonce_ = 0;

    /* Noise operations */
    void initialize_symmetric(const char *protocol_name);
    void mix_hash(const uint8_t *data, size_t len);
    void mix_key(const uint8_t *ikm, size_t len);
    std::vector<uint8_t> encrypt_and_hash(const uint8_t *plaintext, size_t len);
    bool decrypt_and_hash(const uint8_t *ciphertext, size_t len,
                          std::vector<uint8_t> &out);
    void split();
};

/* =====================================================================
 * KomeNoiseTransport — decorator transport that wraps any KomeTransportAdapter
 * ===================================================================== */

class KomeNoiseTransport : public KomeTransportAdapter {
public:
    KomeNoiseTransport(KomeTransportAdapter *inner,
                       const uint8_t static_priv[32],
                       const uint8_t static_pub[32],
                       const uint8_t fingerprint[32]);

    void send(const uint8_t *peer_fp, const uint8_t *data, size_t len) override;

    /* Override base class callback setters so the sync manager's callbacks
     * go to our upper layer (after Noise decryption) */
    void set_recv_callback(RecvCallback cb) override { upper_recv_cb_ = std::move(cb); }
    void set_peer_callback(PeerCallback cb) override { upper_peer_cb_ = std::move(cb); }

private:
    KomeTransportAdapter *inner_;
    uint8_t static_priv_[32];
    uint8_t static_pub_[32];
    uint8_t fingerprint_[32];

    std::recursive_mutex sessions_mu_;
    std::map<std::string, NoiseSession> sessions_;    /* keyed by peer fingerprint (raw 32 bytes) */
    std::map<std::string, std::vector<std::vector<uint8_t>>> pending_; /* queued sends */

    RecvCallback upper_recv_cb_ = nullptr;
    PeerCallback upper_peer_cb_ = nullptr;

    void on_inner_recv(const uint8_t *peer_fp, const uint8_t *data, size_t len);
    void on_inner_peer(const uint8_t *peer_fp, int connected);
    void start_handshake(const std::string &fp_key, const uint8_t *peer_fp);
    void flush_pending(const std::string &fp_key, const uint8_t *peer_fp);

    static std::string make_fp_key(const uint8_t *fp) {
        return std::string((const char*)fp, 32);
    }
};

} /* namespace kome */

#endif /* KOME_NOISE_HPP */
