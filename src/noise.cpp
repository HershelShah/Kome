/* noise.cpp — Noise XX handshake + transport channel (M4). */
#include "noise.h"

#include <cstring>

#include "sha256.h"

namespace ke {

using sync_engine_detail::Sha256;

namespace {

void nonce24(uint64_t n, uint8_t out[24]) {
    std::memset(out, 0, 24);
    for (int i = 0; i < 8; i++) out[i] = (uint8_t)(n >> (i * 8));
}

/* HKDF-SHA256 producing two 32-byte outputs (Noise's MixKey / Split). */
void hkdf2(const uint8_t ck[32], const uint8_t *ikm, size_t ilen,
           uint8_t o1[32], uint8_t o2[32]) {
    uint8_t temp[32];
    hmac_sha256(ck, 32, ikm, ilen, temp);
    uint8_t one = 0x01;
    hmac_sha256(temp, 32, &one, 1, o1);
    uint8_t buf[33];
    std::memcpy(buf, o1, 32);
    buf[32] = 0x02;
    hmac_sha256(temp, 32, buf, 33, o2);
}

} // namespace

NoiseChannel::NoiseChannel(bool initiator, const KeyPair &id)
    : initiator_(initiator) {
    s_sk_ = id.dh_sk;
    s_pk_ = id.dh_pk;
    sign_sk_ = id.sign_sk;
    sign_pk_ = id.sign_pk;
    /* InitializeSymmetric("Noise_XX_25519_XChaChaPoly_SHA256"): name <= 32
     * bytes? It is 33, so h = SHA256(name). */
    static const char *name = "Noise_XX_25519_XChaChaPoly_SHA256";
    size_t nlen = std::strlen(name);
    if (nlen <= 32) {
        std::memset(h_.data(), 0, 32);
        std::memcpy(h_.data(), name, nlen);
    } else {
        sync_engine_detail::sha256(name, nlen, h_.data());
    }
    ck_ = h_;
}

void NoiseChannel::mix_hash(const uint8_t *d, size_t n) {
    Sha256 hh;
    hh.update(h_.data(), 32);
    hh.update(d, n);
    hh.finish(h_.data());
}

void NoiseChannel::mix_key(const uint8_t dh[32]) {
    uint8_t o1[32], o2[32];
    hkdf2(ck_.data(), dh, 32, o1, o2);
    std::memcpy(ck_.data(), o1, 32);
    std::memcpy(k_.data(), o2, 32);
    has_key_ = true;
    nonce_ = 0;
}

bool NoiseChannel::encrypt_hash(const uint8_t *pt, size_t n, std::string &out) {
    if (!has_key_) {
        out.assign((const char *)pt, n);
        mix_hash(pt, n);
        return true;
    }
    uint8_t nn[24];
    nonce24(nonce_++, nn);
    std::string body(n, '\0');
    uint8_t mac[16];
    aead_encrypt(k_.data(), nn, h_.data(), 32, pt, n,
                 (uint8_t *)body.data(), mac);
    out = body;
    out.append((const char *)mac, 16);
    mix_hash((const uint8_t *)out.data(), out.size());
    return true;
}

bool NoiseChannel::decrypt_hash(const uint8_t *ct, size_t n, std::string &pt) {
    if (!has_key_) {
        pt.assign((const char *)ct, n);
        mix_hash(ct, n);
        return true;
    }
    if (n < 16) return false;
    size_t blen = n - 16;
    uint8_t nn[24];
    nonce24(nonce_++, nn);
    std::string body(blen, '\0');
    if (!aead_decrypt(k_.data(), nn, h_.data(), 32, ct, blen, ct + blen,
                      (uint8_t *)body.data()))
        return false;
    pt = body;
    mix_hash(ct, n); /* hash the ciphertext (incl. tag) */
    return true;
}

void NoiseChannel::split() {
    final_h_ = h_; /* transcript hash, identical on both ends */
    uint8_t o1[32], o2[32];
    hkdf2(ck_.data(), nullptr, 0, o1, o2);
    if (initiator_) {
        std::memcpy(send_k_.data(), o1, 32);
        std::memcpy(recv_k_.data(), o2, 32);
    } else {
        std::memcpy(send_k_.data(), o2, 32);
        std::memcpy(recv_k_.data(), o1, 32);
    }
}

bool NoiseChannel::step(const std::string &in, std::string &out, bool &done) {
    out.clear();
    done = false;
    const uint8_t *p = (const uint8_t *)in.data();
    size_t n = in.size();

    if (initiator_) {
        if (msgidx_ == 0) {
            /* -> e */
            if (!random_bytes(e_sk_.data(), 32)) return false;
            x25519_public(e_sk_.data(), e_pk_.data());
            out.assign((const char *)e_pk_.data(), 32);
            mix_hash(e_pk_.data(), 32);
            msgidx_ = 1;
            return true;
        }
        if (msgidx_ == 1) {
            /* <- e, ee, s, es */
            if (n < 32 + 48) return false;
            std::memcpy(re_.data(), p, 32);
            mix_hash(re_.data(), 32);
            uint8_t dh[32];
            x25519(e_sk_.data(), re_.data(), dh);
            mix_key(dh);
            std::string rs_pt;
            if (!decrypt_hash(p + 32, 48, rs_pt) || rs_pt.size() != 32)
                return false;
            std::memcpy(rs_.data(), rs_pt.data(), 32);
            x25519(e_sk_.data(), rs_.data(), dh); /* es: initiator e * remote s */
            mix_key(dh);
            /* -> s, se */
            if (!encrypt_hash(s_pk_.data(), 32, out)) return false;
            x25519(s_sk_.data(), re_.data(), dh); /* se: initiator s * remote e */
            mix_key(dh);
            split();
            done_ = true;
            done = true;
            return true;
        }
        return false;
    }

    /* responder */
    if (msgidx_ == 0) {
        /* <- e ; -> e, ee, s, es */
        if (n < 32) return false;
        std::memcpy(re_.data(), p, 32);
        mix_hash(re_.data(), 32);
        if (!random_bytes(e_sk_.data(), 32)) return false;
        x25519_public(e_sk_.data(), e_pk_.data());
        out.assign((const char *)e_pk_.data(), 32);
        mix_hash(e_pk_.data(), 32);
        uint8_t dh[32];
        x25519(e_sk_.data(), re_.data(), dh);
        mix_key(dh);
        std::string cs;
        if (!encrypt_hash(s_pk_.data(), 32, cs)) return false;
        out += cs;
        x25519(s_sk_.data(), re_.data(), dh); /* es: responder s * remote e */
        mix_key(dh);
        msgidx_ = 1;
        return true;
    }
    if (msgidx_ == 1) {
        /* <- s, se */
        if (n < 48) return false;
        std::string rs_pt;
        if (!decrypt_hash(p, 48, rs_pt) || rs_pt.size() != 32) return false;
        std::memcpy(rs_.data(), rs_pt.data(), 32);
        uint8_t dh[32];
        x25519(e_sk_.data(), rs_.data(), dh); /* se: responder e * remote s */
        mix_key(dh);
        split();
        done_ = true;
        done = true;
        return true;
    }
    return false;
}

bool NoiseChannel::encrypt(const std::string &pt, std::string &out) {
    if (!done_) return false;
    uint8_t nn[24];
    nonce24(send_nonce_++, nn);
    std::string body(pt.size(), '\0');
    uint8_t mac[16];
    aead_encrypt(send_k_.data(), nn, nullptr, 0,
                 (const uint8_t *)pt.data(), pt.size(),
                 (uint8_t *)body.data(), mac);
    out = body;
    out.append((const char *)mac, 16);
    return true;
}

bool NoiseChannel::decrypt(const std::string &ct, std::string &pt) {
    if (!done_ || ct.size() < 16) return false;
    size_t blen = ct.size() - 16;
    uint8_t nn[24];
    nonce24(recv_nonce_, nn); /* peek; advance only on a successful auth */
    std::string body(blen, '\0');
    if (!aead_decrypt(recv_k_.data(), nn, nullptr, 0,
                      (const uint8_t *)ct.data(), blen,
                      (const uint8_t *)ct.data() + blen,
                      (uint8_t *)body.data()))
        return false; /* forged/corrupt frame: do NOT desync the counter */
    recv_nonce_++;
    pt = body;
    return true;
}

namespace {
const char *kBindLabel = "kome-channel-bind-v1";
}

bool NoiseChannel::make_identity_proof(std::string &out) {
    if (!done_) return false;
    std::string msg = kBindLabel;
    msg.append((const char *)final_h_.data(), final_h_.size());
    uint8_t sig[64];
    sign(sign_sk_.data(), msg.data(), msg.size(), sig);
    out.assign((const char *)sign_pk_.data(), sign_pk_.size());
    out.append((const char *)sig, 64);
    return true;
}

bool NoiseChannel::verify_identity_proof(const std::string &in,
                                         uint8_t peer_sign_pk[32]) {
    if (!done_ || in.size() != 96) return false;
    const uint8_t *pk = (const uint8_t *)in.data();
    const uint8_t *sig = pk + 32;
    std::string msg = kBindLabel;
    msg.append((const char *)final_h_.data(), final_h_.size());
    if (!verify(pk, msg.data(), msg.size(), sig)) return false;
    std::memcpy(peer_sign_pk, pk, 32);
    return true;
}

void NoiseChannel::reliability_key(uint8_t out[32]) const {
    /* Both peers share final_h_ (the transcript hash at Split), so HMAC over a
     * label yields the same key on both sides — independent of the directional
     * transport keys. */
    static const char *kRelLabel = "kome-reliability-mac-v1";
    hmac_sha256(final_h_.data(), 32, (const uint8_t *)kRelLabel,
                std::strlen(kRelLabel), out);
}

} // namespace ke
