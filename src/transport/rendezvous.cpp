/* rendezvous.cpp — rendezvous registry + UDP service (M5). */
#include "transport/rendezvous.h"

#include <cstring>
#include <string>

#include "codec.h"  /* ke::put_varint / ke::get_varint */
#include "crypto.h" /* random_bytes / sign / verify */

namespace ke {

namespace {
constexpr char kRegister = 'R';  /* 'R' | 32 me                          */
constexpr char kChallenge = 'C'; /* 'C' | 16 nonce         (server->me)  */
constexpr char kRegAuth = 'U';   /* 'U' | 32 me | 16 nonce | 64 sig      */
constexpr char kAck = 'A';       /* 'A'                                  */
constexpr char kLookup = 'L';    /* 'L' | 32 target                      */
constexpr char kPeer = 'P';      /* 'P' | found(1) | varint ip | port(2) */
constexpr size_t kMaxPending = 4096;

std::string endpoint_key(const Endpoint &e) {
    return e.ip + ":" + std::to_string(e.port);
}

void put_endpoint(std::string &o, const Endpoint &ep) {
    put_varint(o, ep.ip.size());
    o += ep.ip;
    o.push_back((char)(ep.port & 0xff));
    o.push_back((char)(ep.port >> 8));
}
bool get_endpoint(const uint8_t *&p, const uint8_t *end, Endpoint &ep) {
    uint64_t l = 0;
    if (!get_varint(p, end, l)) return false;
    /* Guard the bound against l+2 wrapping around (l is attacker-controlled). */
    uint64_t avail = (uint64_t)(end - p);
    if (avail < 2 || avail - 2 < l) return false;
    ep.ip.assign((const char *)p, (size_t)l);
    p += l;
    ep.port = (uint16_t)((uint8_t)p[0] | ((uint8_t)p[1] << 8));
    p += 2;
    return true;
}
} // namespace

void Rendezvous::issue_challenge(const std::string &endpoint,
                                 const uint8_t nonce[16],
                                 const std::string &pkkey) {
    if (pending_.size() >= kMaxPending && !pending_.count(endpoint))
        pending_.erase(pending_.begin());
    Pending pe;
    std::memcpy(pe.nonce.data(), nonce, 16);
    pe.pkkey = pkkey;
    pending_[endpoint] = pe;
}

bool Rendezvous::consume_challenge(const std::string &endpoint,
                                   const uint8_t nonce[16],
                                   const std::string &pkkey) {
    auto it = pending_.find(endpoint);
    if (it == pending_.end()) return false;
    bool ok = it->second.pkkey == pkkey &&
              std::memcmp(it->second.nonce.data(), nonce, 16) == 0;
    pending_.erase(it);
    return ok;
}

bool rendezvous_server_step(Rendezvous &rdv, UdpSocket &sock, int timeout_ms) {
    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.empty()) return true;

    if (dg[0] == kRegister && dg.size() >= 1 + 32) {
        /* Challenge the registrant to prove it owns this key (and is at this
         * address) before recording the mapping — otherwise anyone could point
         * a victim's key at an arbitrary endpoint. */
        uint8_t nonce[16];
        if (!random_bytes(nonce, 16)) return true;
        rdv.issue_challenge(endpoint_key(from), nonce,
                            std::string((const char *)dg.data() + 1, 32));
        std::string ch(1, kChallenge);
        ch.append((const char *)nonce, 16);
        sock.send_to(from, ch);
    } else if (dg[0] == kRegAuth && dg.size() >= 1 + 32 + 16 + 64) {
        const uint8_t *me = (const uint8_t *)dg.data() + 1;
        const uint8_t *nonce = me + 32;
        const uint8_t *sig = nonce + 16;
        std::string pkkey((const char *)me, 32);
        /* The nonce must match the one we sent to this endpoint, and the
         * signature must verify under `me` — so the registrant holds me's
         * signing secret and received the challenge at its claimed address. */
        if (rdv.consume_challenge(endpoint_key(from), nonce, pkkey) &&
            verify(me, nonce, 16, sig)) {
            rdv.set(me, from);
            std::string ack(1, kAck);
            sock.send_to(from, ack);
        }
    } else if (dg[0] == kLookup && dg.size() >= 1 + 32) {
        Endpoint ep;
        bool found = rdv.get((const uint8_t *)dg.data() + 1, ep);
        std::string reply(1, kPeer);
        reply.push_back(found ? 1 : 0);
        if (found) put_endpoint(reply, ep);
        sock.send_to(from, reply);
    }
    return true;
}

bool rendezvous_register(UdpSocket &sock, const Endpoint &server,
                         const KeyPair &id, int timeout_ms) {
    /* Step 1: request to register; the server replies with a challenge nonce. */
    std::string m(1, kRegister);
    m.append((const char *)id.sign_pk.data(), 32);
    if (!sock.send_to(server, m)) return false;
    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.size() != 1 + 16 || dg[0] != kChallenge) return false;

    /* Step 2: sign the nonce with our signing secret to prove key ownership. */
    uint8_t sig[64];
    sign(id.sign_sk.data(), dg.data() + 1, 16, sig);
    std::string a(1, kRegAuth);
    a.append((const char *)id.sign_pk.data(), 32);
    a.append(dg.data() + 1, 16);
    a.append((const char *)sig, 64);
    if (!sock.send_to(server, a)) return false;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    return !dg.empty() && dg[0] == kAck;
}

bool rendezvous_lookup(UdpSocket &sock, const Endpoint &server,
                       const uint8_t target[32], Endpoint &out, int timeout_ms) {
    std::string m(1, kLookup);
    m.append((const char *)target, 32);
    if (!sock.send_to(server, m)) return false;
    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.size() < 2 || dg[0] != kPeer || dg[1] != 1) return false;
    const uint8_t *p = (const uint8_t *)dg.data() + 2;
    const uint8_t *end = (const uint8_t *)dg.data() + dg.size();
    return get_endpoint(p, end, out);
}

} // namespace ke
