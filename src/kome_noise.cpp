#include "kome_noise.hpp"
#include "kome_util.hpp"
extern "C" {
#include "monocypher.h"
}
#include <cstring>
#include <cassert>
#include <algorithm>

namespace kome {

/* =====================================================================
 * NoiseSession implementation
 * ===================================================================== */

static constexpr const char *NOISE_PROTOCOL_NAME =
    "Noise_XX_25519_ChaChaPoly_SHA256";

void NoiseSession::initialize_symmetric(const char *protocol_name)
{
    size_t name_len = std::strlen(protocol_name);
    if (name_len <= 32) {
        std::memset(h_, 0, 32);
        std::memcpy(h_, protocol_name, name_len);
    } else {
        sha256((const uint8_t*)protocol_name, name_len, h_);
    }
    std::memcpy(ck_, h_, 32);
    std::memset(k_, 0, 32);
    has_key_ = false;
    nonce_ = 0;
}

void NoiseSession::mix_hash(const uint8_t *data, size_t len)
{
    /* h = SHA-256(h || data) */
    std::vector<uint8_t> buf(32 + len);
    std::memcpy(buf.data(), h_, 32);
    if (data && len > 0)
        std::memcpy(buf.data() + 32, data, len);
    sha256(buf.data(), buf.size(), h_);
}

void NoiseSession::mix_key(const uint8_t *ikm, size_t len)
{
    /* HKDF(ck, ikm) -> (ck, k)
     * ck = first 32 bytes of HKDF output
     * k  = next 32 bytes of HKDF output */
    uint8_t out[64];
    hkdf_sha256(ck_, 32, ikm, len, nullptr, 0, out, 64);
    std::memcpy(ck_, out, 32);
    std::memcpy(k_, out + 32, 32);
    has_key_ = true;
    nonce_ = 0;
    crypto_wipe(out, 64);
}

std::vector<uint8_t> NoiseSession::encrypt_and_hash(const uint8_t *plaintext, size_t len)
{
    if (!has_key_) {
        /* No key yet: "encrypt" = pass through, but still mix_hash */
        std::vector<uint8_t> ct(plaintext, plaintext + len);
        mix_hash(plaintext, len);
        return ct;
    }

    /* AEAD encrypt with key k_, nonce, and h_ as AD */
    std::vector<uint8_t> ct(len + 16); /* ciphertext + 16-byte tag */
    uint8_t nonce_bytes[8];
    for (int i = 0; i < 8; i++)
        nonce_bytes[i] = (uint8_t)(nonce_ >> (i * 8));

    crypto_aead_lock(ct.data() + len,       /* mac (tag) at the end */
                     ct.data(),              /* ciphertext */
                     k_,                     /* key */
                     nonce_bytes,            /* nonce */
                     h_, 32,                 /* AD = handshake hash */
                     plaintext, len);        /* plaintext */
    nonce_++;

    /* mix_hash the ciphertext + tag */
    mix_hash(ct.data(), ct.size());
    return ct;
}

bool NoiseSession::decrypt_and_hash(const uint8_t *ciphertext, size_t len,
                                     std::vector<uint8_t> &out)
{
    if (!has_key_) {
        /* No key yet: "decrypt" = pass through, but still mix_hash */
        out.assign(ciphertext, ciphertext + len);
        mix_hash(ciphertext, len);
        return true;
    }

    if (len < 16) return false;
    size_t pt_len = len - 16;

    uint8_t nonce_bytes[8];
    for (int i = 0; i < 8; i++)
        nonce_bytes[i] = (uint8_t)(nonce_ >> (i * 8));

    out.resize(pt_len);
    int rc = crypto_aead_unlock(out.data(),           /* plaintext */
                                k_,                    /* key */
                                nonce_bytes,           /* nonce */
                                ciphertext + pt_len,   /* mac (tag) */
                                h_, 32,                /* AD */
                                ciphertext, pt_len);   /* ciphertext */
    if (rc != 0) {
        out.clear();
        return false;
    }
    nonce_++;

    /* mix_hash the ciphertext + tag (the full input) */
    mix_hash(ciphertext, len);
    return true;
}

void NoiseSession::split()
{
    /* HKDF(ck, "") -> (k1, k2) */
    uint8_t out[64];
    hkdf_sha256(ck_, 32, nullptr, 0, nullptr, 0, out, 64);

    if (is_initiator_) {
        std::memcpy(send_key_, out, 32);
        std::memcpy(recv_key_, out + 32, 32);
    } else {
        std::memcpy(recv_key_, out, 32);
        std::memcpy(send_key_, out + 32, 32);
    }
    send_nonce_ = 0;
    recv_nonce_ = 0;
    crypto_wipe(out, 64);
}

/* --- Init ------------------------------------------------------------ */

void NoiseSession::init_initiator(const uint8_t local_static_priv[32],
                                   const uint8_t local_static_pub[32],
                                   const uint8_t local_fingerprint[32])
{
    is_initiator_ = true;
    state_ = INIT;
    std::memcpy(local_static_priv_, local_static_priv, 32);
    std::memcpy(local_static_pub_, local_static_pub, 32);
    std::memcpy(local_fingerprint_, local_fingerprint, 32);
    std::memset(remote_static_pub_, 0, 32);
    std::memset(remote_ephemeral_pub_, 0, 32);
    std::memset(remote_fingerprint_, 0, 32);

    /* Generate ephemeral keypair */
    random_bytes(ephemeral_priv_, 32);
    crypto_x25519_public_key(ephemeral_pub_, ephemeral_priv_);

    initialize_symmetric(NOISE_PROTOCOL_NAME);
}

void NoiseSession::init_responder(const uint8_t local_static_priv[32],
                                   const uint8_t local_static_pub[32],
                                   const uint8_t local_fingerprint[32])
{
    is_initiator_ = false;
    state_ = INIT;
    std::memcpy(local_static_priv_, local_static_priv, 32);
    std::memcpy(local_static_pub_, local_static_pub, 32);
    std::memcpy(local_fingerprint_, local_fingerprint, 32);
    std::memset(remote_static_pub_, 0, 32);
    std::memset(remote_ephemeral_pub_, 0, 32);
    std::memset(remote_fingerprint_, 0, 32);

    /* Generate ephemeral keypair */
    random_bytes(ephemeral_priv_, 32);
    crypto_x25519_public_key(ephemeral_pub_, ephemeral_priv_);

    initialize_symmetric(NOISE_PROTOCOL_NAME);
}

/* --- write_handshake_msg --------------------------------------------- */

std::vector<uint8_t> NoiseSession::write_handshake_msg()
{
    std::vector<uint8_t> msg;

    if (is_initiator_ && state_ == INIT) {
        /* Message 1 (initiator -> responder): -> e
         * Send ephemeral public key (32 bytes) */
        msg.insert(msg.end(), ephemeral_pub_, ephemeral_pub_ + 32);
        mix_hash(ephemeral_pub_, 32);
        state_ = HANDSHAKE_1_SENT;
    }
    else if (!is_initiator_ && state_ == HANDSHAKE_1_SENT) {
        /* Message 2 (responder -> initiator): <- e, ee, s, es
         * 1. Send responder ephemeral (e) */
        msg.insert(msg.end(), ephemeral_pub_, ephemeral_pub_ + 32);
        mix_hash(ephemeral_pub_, 32);

        /* 2. DH ee: mix_key(DH(e_resp, e_init)) */
        uint8_t dh_result[32];
        crypto_x25519(dh_result, ephemeral_priv_, remote_ephemeral_pub_);
        mix_key(dh_result, 32);
        crypto_wipe(dh_result, 32);

        /* 3. Send static (s) encrypted: encrypt_and_hash(s) */
        auto enc_s = encrypt_and_hash(local_static_pub_, 32);
        msg.insert(msg.end(), enc_s.begin(), enc_s.end());

        /* 4. DH es: mix_key(DH(s_resp, e_init)) */
        crypto_x25519(dh_result, local_static_priv_, remote_ephemeral_pub_);
        mix_key(dh_result, 32);
        crypto_wipe(dh_result, 32);

        /* 5. Send fingerprint as encrypted payload */
        auto enc_fp = encrypt_and_hash(local_fingerprint_, 32);
        msg.insert(msg.end(), enc_fp.begin(), enc_fp.end());

        state_ = HANDSHAKE_2_SENT;
    }
    else if (is_initiator_ && state_ == HANDSHAKE_2_SENT) {
        /* Message 3 (initiator -> responder): -> s, se
         * 1. Send static (s) encrypted */
        auto enc_s = encrypt_and_hash(local_static_pub_, 32);
        msg.insert(msg.end(), enc_s.begin(), enc_s.end());

        /* 2. DH se: mix_key(DH(s_init, e_resp)) */
        uint8_t dh_result[32];
        crypto_x25519(dh_result, local_static_priv_, remote_ephemeral_pub_);
        mix_key(dh_result, 32);
        crypto_wipe(dh_result, 32);

        /* 3. Send fingerprint as encrypted payload */
        auto enc_fp = encrypt_and_hash(local_fingerprint_, 32);
        msg.insert(msg.end(), enc_fp.begin(), enc_fp.end());

        /* 4. Split to derive transport keys */
        split();
        state_ = ESTABLISHED;
    }

    return msg;
}

/* --- read_handshake_msg ---------------------------------------------- */

bool NoiseSession::read_handshake_msg(const uint8_t *data, size_t len)
{
    if (!is_initiator_ && state_ == INIT) {
        /* Message 1 (from initiator): -> e
         * Expect exactly 32 bytes: ephemeral public key */
        if (len != 32) { state_ = FAILED; return false; }

        std::memcpy(remote_ephemeral_pub_, data, 32);
        mix_hash(data, 32);

        /* Responder marks that msg 1 has been "sent" (i.e., received from
         * initiator's perspective). We transition to HANDSHAKE_1_SENT so
         * write_handshake_msg knows to produce message 2. */
        state_ = HANDSHAKE_1_SENT;
        return true;
    }
    else if (is_initiator_ && state_ == HANDSHAKE_1_SENT) {
        /* Message 2 (from responder): <- e, ee, s, es
         * Format: [32: e_resp][48: enc(s_resp)][48: enc(fingerprint)]
         * Total: 32 + 48 + 48 = 128 bytes */
        if (len != 128) { state_ = FAILED; return false; }

        size_t off = 0;

        /* 1. Read responder ephemeral (e) */
        std::memcpy(remote_ephemeral_pub_, data + off, 32);
        mix_hash(data + off, 32);
        off += 32;

        /* 2. DH ee */
        uint8_t dh_result[32];
        crypto_x25519(dh_result, ephemeral_priv_, remote_ephemeral_pub_);
        mix_key(dh_result, 32);
        crypto_wipe(dh_result, 32);

        /* 3. Decrypt static (s) — 48 bytes (32 + 16 tag) */
        std::vector<uint8_t> dec_s;
        if (!decrypt_and_hash(data + off, 48, dec_s)) { state_ = FAILED; return false; }
        if (dec_s.size() != 32) { state_ = FAILED; return false; }
        std::memcpy(remote_static_pub_, dec_s.data(), 32);
        off += 48;

        /* 4. DH es */
        crypto_x25519(dh_result, ephemeral_priv_, remote_static_pub_);
        mix_key(dh_result, 32);
        crypto_wipe(dh_result, 32);

        /* 5. Decrypt fingerprint — 48 bytes (32 + 16 tag) */
        std::vector<uint8_t> dec_fp;
        if (!decrypt_and_hash(data + off, 48, dec_fp)) { state_ = FAILED; return false; }
        if (dec_fp.size() != 32) { state_ = FAILED; return false; }
        std::memcpy(remote_fingerprint_, dec_fp.data(), 32);
        off += 48;

        /* Initiator is now ready to send message 3. We mark state as
         * HANDSHAKE_2_SENT from the session's perspective (msg 2 received). */
        state_ = HANDSHAKE_2_SENT;
        return true;
    }
    else if (!is_initiator_ && state_ == HANDSHAKE_2_SENT) {
        /* Message 3 (from initiator): -> s, se
         * Format: [48: enc(s_init)][48: enc(fingerprint)]
         * Total: 48 + 48 = 96 bytes */
        if (len != 96) { state_ = FAILED; return false; }

        size_t off = 0;

        /* 1. Decrypt static (s) */
        std::vector<uint8_t> dec_s;
        if (!decrypt_and_hash(data + off, 48, dec_s)) { state_ = FAILED; return false; }
        if (dec_s.size() != 32) { state_ = FAILED; return false; }
        std::memcpy(remote_static_pub_, dec_s.data(), 32);
        off += 48;

        /* 2. DH se */
        uint8_t dh_result[32];
        crypto_x25519(dh_result, ephemeral_priv_, remote_static_pub_);
        mix_key(dh_result, 32);
        crypto_wipe(dh_result, 32);

        /* 3. Decrypt fingerprint */
        std::vector<uint8_t> dec_fp;
        if (!decrypt_and_hash(data + off, 48, dec_fp)) { state_ = FAILED; return false; }
        if (dec_fp.size() != 32) { state_ = FAILED; return false; }
        std::memcpy(remote_fingerprint_, dec_fp.data(), 32);
        off += 48;

        /* 4. Split */
        split();
        state_ = ESTABLISHED;
        return true;
    }

    state_ = FAILED;
    return false;
}

/* --- Transport encrypt/decrypt --------------------------------------- */

std::vector<uint8_t> NoiseSession::encrypt(const uint8_t *plaintext, size_t len)
{
    /* Encrypt with send_key_ and send_nonce_ */
    uint8_t nonce_bytes[8];
    for (int i = 0; i < 8; i++)
        nonce_bytes[i] = (uint8_t)(send_nonce_ >> (i * 8));

    std::vector<uint8_t> ct(len + 16);
    crypto_aead_lock(ct.data() + len,   /* mac */
                     ct.data(),         /* ciphertext */
                     send_key_,         /* key */
                     nonce_bytes,       /* nonce */
                     nullptr, 0,        /* no AD */
                     plaintext, len);
    send_nonce_++;
    return ct;
}

bool NoiseSession::decrypt(const uint8_t *ciphertext, size_t len,
                            std::vector<uint8_t> &plaintext_out)
{
    if (len < 16) return false;
    size_t pt_len = len - 16;

    uint8_t nonce_bytes[8];
    for (int i = 0; i < 8; i++)
        nonce_bytes[i] = (uint8_t)(recv_nonce_ >> (i * 8));

    plaintext_out.resize(pt_len);
    int rc = crypto_aead_unlock(plaintext_out.data(),
                                recv_key_,
                                nonce_bytes,
                                ciphertext + pt_len, /* mac */
                                nullptr, 0,
                                ciphertext, pt_len);
    if (rc != 0) {
        plaintext_out.clear();
        return false;
    }
    recv_nonce_++;
    return true;
}

/* =====================================================================
 * KomeNoiseTransport implementation
 *
 * The transport uses "both-initiate" with collision resolution:
 * - On peer connect, both sides create an initiator session and send msg 1
 * - When a side receives msg 1 while in HANDSHAKE_1_SENT state,
 *   it's a simultaneous open. Resolve by comparing ephemeral keys:
 *   the side with the LOWER ephemeral key stays as initiator,
 *   the other side resets as responder.
 * ===================================================================== */

KomeNoiseTransport::KomeNoiseTransport(KomeTransportAdapter *inner,
                                         const uint8_t static_priv[32],
                                         const uint8_t static_pub[32],
                                         const uint8_t fingerprint[32])
    : inner_(inner)
{
    std::memcpy(static_priv_, static_priv, 32);
    std::memcpy(static_pub_, static_pub, 32);
    std::memcpy(fingerprint_, fingerprint, 32);

    /* Wire our callbacks to the inner transport */
    inner_->set_recv_callback([this](const uint8_t *peer_fp,
                                      const uint8_t *data, size_t len) {
        on_inner_recv(peer_fp, data, len);
    });
    inner_->set_peer_callback([this](const uint8_t *peer_fp, int connected) {
        on_inner_peer(peer_fp, connected);
    });
}

void KomeNoiseTransport::send(const uint8_t *peer_fp,
                               const uint8_t *data, size_t len)
{
    std::lock_guard<std::recursive_mutex> lock(sessions_mu_);
    std::string key = make_fp_key(peer_fp);

    auto it = sessions_.find(key);
    if (it != sessions_.end() && it->second.state() == NoiseSession::ESTABLISHED) {
        /* Encrypt and send */
        auto ct = it->second.encrypt(data, len);
        std::vector<uint8_t> wire(1 + ct.size());
        wire[0] = NOISE_TRANSPORT_TAG;
        std::memcpy(wire.data() + 1, ct.data(), ct.size());
        inner_->send(peer_fp, wire.data(), wire.size());
    } else {
        /* Session not established yet — queue the message */
        pending_[key].push_back(std::vector<uint8_t>(data, data + len));
    }
}

void KomeNoiseTransport::on_inner_recv(const uint8_t *peer_fp,
                                        const uint8_t *data, size_t len)
{
    if (len < 1) return;

    uint8_t tag = data[0];

    if (tag == NOISE_HANDSHAKE_TAG) {
        /* Handshake message: 0x0F + phase(1 byte) + payload */
        if (len < 3) return;
        uint8_t phase = data[1];
        const uint8_t *payload = data + 2;
        size_t payload_len = len - 2;

        std::lock_guard<std::recursive_mutex> lock(sessions_mu_);
        std::string key = make_fp_key(peer_fp);

        auto it = sessions_.find(key);
        if (it == sessions_.end()) {
            /* No session yet (e.g. we got msg 1 before our peer_cb fired).
             * Create a responder session on the fly. */
            if (phase == 1 && payload_len == 32) {
                NoiseSession session;
                session.init_responder(static_priv_, static_pub_, fingerprint_);
                sessions_[key] = session;
                it = sessions_.find(key);
            } else {
                return;
            }
        }

        NoiseSession &session = it->second;

        /* Detect simultaneous open: we sent msg 1 (initiator in HANDSHAKE_1_SENT)
         * and received msg 1 from the peer (phase 1, 32 bytes = ephemeral key).
         * Resolve: compare our ephemeral key with theirs. Lower key stays
         * as initiator, the other resets as responder. */
        if (phase == 1 && payload_len == 32 &&
            session.state() == NoiseSession::HANDSHAKE_1_SENT &&
            session.is_initiator()) {

            /* We both sent msg 1. Compare ephemeral public keys. */
            int cmp = std::memcmp(session.ephemeral_pub(), payload, 32);
            if (cmp < 0) {
                /* Our ephemeral key is lower — we stay as initiator.
                 * The peer will yield. Ignore their msg 1. */
                return;
            } else {
                /* Their ephemeral key is lower — they stay as initiator.
                 * We must reset as responder and process their msg 1. */
                session.init_responder(static_priv_, static_pub_, fingerprint_);

                /* Now process their msg 1 */
                if (!session.read_handshake_msg(payload, payload_len)) {
                    session = NoiseSession();
                    return;
                }
                /* Write msg 2 as responder */
                auto resp = session.write_handshake_msg();
                if (!resp.empty()) {
                    std::vector<uint8_t> wire(2 + resp.size());
                    wire[0] = NOISE_HANDSHAKE_TAG;
                    wire[1] = 2;
                    std::memcpy(wire.data() + 2, resp.data(), resp.size());
                    inner_->send(peer_fp, wire.data(), wire.size());
                }
                return;
            }
        }

        if (!session.read_handshake_msg(payload, payload_len)) {
            session = NoiseSession();
            return;
        }

        /* If session needs to write a response, do it */
        if (session.state() != NoiseSession::ESTABLISHED &&
            session.state() != NoiseSession::FAILED) {
            auto resp = session.write_handshake_msg();
            if (!resp.empty()) {
                uint8_t resp_phase = phase + 1;
                std::vector<uint8_t> wire(2 + resp.size());
                wire[0] = NOISE_HANDSHAKE_TAG;
                wire[1] = resp_phase;
                std::memcpy(wire.data() + 2, resp.data(), resp.size());
                inner_->send(peer_fp, wire.data(), wire.size());
            }
        }

        if (session.state() == NoiseSession::ESTABLISHED) {
            if (upper_peer_cb_)
                upper_peer_cb_(peer_fp, 1);
            flush_pending(key, peer_fp);
        }
    }
    else if (tag == NOISE_TRANSPORT_TAG) {
        if (len < 1 + 16) return;

        std::lock_guard<std::recursive_mutex> lock(sessions_mu_);
        std::string key = make_fp_key(peer_fp);

        auto it = sessions_.find(key);
        if (it == sessions_.end() || it->second.state() != NoiseSession::ESTABLISHED)
            return;

        std::vector<uint8_t> plaintext;
        if (it->second.decrypt(data + 1, len - 1, plaintext)) {
            if (upper_recv_cb_)
                upper_recv_cb_(peer_fp, plaintext.data(), plaintext.size());
        }
    }
    else {
        /* Non-Noise message (e.g. raw sync protocol 0x01-0x07 injected
         * directly into the inner transport). Pass through to upper layer
         * unmodified for backward compatibility and testability. */
        if (upper_recv_cb_)
            upper_recv_cb_(peer_fp, data, len);
    }
}

void KomeNoiseTransport::on_inner_peer(const uint8_t *peer_fp, int connected)
{
    if (connected) {
        std::lock_guard<std::recursive_mutex> lock(sessions_mu_);
        std::string key = make_fp_key(peer_fp);

        /* If there's already an established (or in-progress) session,
         * don't reset it. This handles synchronous transports where both
         * sides' peer callbacks fire in sequence, and the first callback
         * may complete the entire handshake before the second fires. */
        auto existing = sessions_.find(key);
        if (existing != sessions_.end() &&
            existing->second.state() != NoiseSession::FAILED) {
            /* Session already exists and is healthy. If already ESTABLISHED,
             * just fire the upper peer callback. */
            if (existing->second.state() == NoiseSession::ESTABLISHED) {
                if (upper_peer_cb_)
                    upper_peer_cb_(peer_fp, 1);
            }
            return;
        }

        /* Both sides always start as initiator. Collision is resolved
         * in on_inner_recv when both msg 1s cross. */
        NoiseSession session;
        session.init_initiator(static_priv_, static_pub_, fingerprint_);
        sessions_[key] = session;
        start_handshake(key, peer_fp);
    } else {
        std::lock_guard<std::recursive_mutex> lock(sessions_mu_);
        std::string key = make_fp_key(peer_fp);
        sessions_.erase(key);
        pending_.erase(key);

        if (upper_peer_cb_)
            upper_peer_cb_(peer_fp, 0);
    }
}

void KomeNoiseTransport::start_handshake(const std::string &fp_key,
                                          const uint8_t *peer_fp)
{
    auto it = sessions_.find(fp_key);
    if (it == sessions_.end()) return;

    auto msg = it->second.write_handshake_msg();
    if (!msg.empty()) {
        std::vector<uint8_t> wire(2 + msg.size());
        wire[0] = NOISE_HANDSHAKE_TAG;
        wire[1] = 1; /* phase 1 */
        std::memcpy(wire.data() + 2, msg.data(), msg.size());
        inner_->send(peer_fp, wire.data(), wire.size());
    }
}

void KomeNoiseTransport::flush_pending(const std::string &fp_key,
                                        const uint8_t *peer_fp)
{
    auto pit = pending_.find(fp_key);
    if (pit == pending_.end()) return;

    auto it = sessions_.find(fp_key);
    if (it == sessions_.end() || it->second.state() != NoiseSession::ESTABLISHED) return;

    for (auto &msg : pit->second) {
        auto ct = it->second.encrypt(msg.data(), msg.size());
        std::vector<uint8_t> wire(1 + ct.size());
        wire[0] = NOISE_TRANSPORT_TAG;
        std::memcpy(wire.data() + 1, ct.data(), ct.size());
        inner_->send(peer_fp, wire.data(), wire.size());
    }
    pending_.erase(pit);
}

} /* namespace kome */
