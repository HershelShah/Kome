/* rendezvous.cpp — rendezvous registry + UDP service (M5). */
#include "transport/rendezvous.h"

#include <cstring>
#include <string>

#include "codec.h"  /* ke::put_varint / ke::get_varint */
#include "crypto.h" /* random_bytes / sign / verify */

namespace ke {

namespace {
constexpr char kRegister = 'R';    /* 'R' | 32 me                          */
constexpr char kRzChallenge = 'C'; /* 'C' | 16 cookie        (server->me)  */
constexpr char kRegAuth = 'U';     /* 'U' | 32 me | 16 cookie | 64 sig     */
constexpr char kRzAck = 'A';       /* 'A'                                  */
constexpr char kLookup = 'L';      /* 'L' | 32 target                      */
constexpr char kLookupAuth = 'M';  /* 'M' | 32 target | 16 cookie          */
constexpr char kPeer = 'P';        /* 'P' | found(1) | varint ip | port(2) */

std::string rz_endpoint_key(const Endpoint &e) {
    return e.ip + ":" + std::to_string(e.port);
}

/* Cookie context: purpose byte (domain-separates REGISTER from LOOKUP so one
 * cookie can't be redeemed as the other), the key (fixed 32), then the observed
 * endpoint (variable, last). */
std::string cookie_ctx(char purpose, const std::string &endpoint,
                       const uint8_t key[32]) {
    std::string c;
    c.reserve(1 + 32 + endpoint.size());
    c.push_back(purpose);
    c.append((const char *)key, 32);
    c += endpoint;
    return c;
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

bool Rendezvous::register_cookie(const std::string &endpoint,
                                 const uint8_t key[32], uint8_t out[16]) {
    return cookies_.issue(cookie_ctx('R', endpoint, key), out);
}
bool Rendezvous::register_cookie_valid(const std::string &endpoint,
                                       const uint8_t key[32],
                                       const uint8_t presented[16]) {
    return cookies_.verify(cookie_ctx('R', endpoint, key), presented);
}
bool Rendezvous::lookup_cookie(const std::string &endpoint, const uint8_t key[32],
                               uint8_t out[16]) {
    return cookies_.issue(cookie_ctx('L', endpoint, key), out);
}
bool Rendezvous::lookup_cookie_valid(const std::string &endpoint,
                                     const uint8_t key[32],
                                     const uint8_t presented[16]) {
    return cookies_.verify(cookie_ctx('L', endpoint, key), presented);
}

bool rendezvous_server_step(Rendezvous &rdv, UdpSocket &sock, int timeout_ms) {
    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.empty()) return true;

    if (dg[0] == kRegister && dg.size() >= 1 + 32) {
        /* Challenge the registrant to prove it owns this key (and is at this
         * address) before recording the mapping — otherwise anyone could point
         * a victim's key at an arbitrary endpoint. The cookie is stateless (F5). */
        const uint8_t *me = (const uint8_t *)dg.data() + 1;
        uint8_t cookie[16];
        if (!rdv.register_cookie(rz_endpoint_key(from), me, cookie)) return true;
        std::string ch(1, kRzChallenge);
        ch.append((const char *)cookie, 16);
        sock.send_to(from, ch);
    } else if (dg[0] == kRegAuth && dg.size() >= 1 + 32 + 16 + 64) {
        const uint8_t *me = (const uint8_t *)dg.data() + 1;
        const uint8_t *cookie = me + 32;
        const uint8_t *sig = cookie + 16;
        /* The cookie must be one we'd issue for this endpoint+key (return-
         * routability), and the signature must verify under `me` over that
         * cookie — so the registrant holds me's signing secret and received the
         * challenge at its claimed address. */
        if (rdv.register_cookie_valid(rz_endpoint_key(from), me, cookie) &&
            verify(me, cookie, 16, sig)) {
            rdv.set(me, from);
            std::string ack(1, kRzAck);
            sock.send_to(from, ack);
        }
    } else if (dg[0] == kLookup && dg.size() >= 1 + 32) {
        /* Return-routability: challenge the requester at its claimed address
         * before revealing/reflecting any endpoint, so a spoofed source can't use
         * the rendezvous as a reflector/amplifier (F1). Stateless cookie (F5). */
        const uint8_t *target = (const uint8_t *)dg.data() + 1;
        uint8_t cookie[16];
        if (!rdv.lookup_cookie(rz_endpoint_key(from), target, cookie)) return true;
        std::string ch(1, kRzChallenge);
        ch.append((const char *)cookie, 16);
        sock.send_to(from, ch);
    } else if (dg[0] == kLookupAuth && dg.size() >= 1 + 32 + 16) {
        const uint8_t *target = (const uint8_t *)dg.data() + 1;
        const uint8_t *cookie = target + 32;
        /* Only a requester that received the challenge at its claimed address can
         * echo a valid cookie, so we now answer it (no reflection). */
        if (rdv.lookup_cookie_valid(rz_endpoint_key(from), target, cookie)) {
            Endpoint ep;
            bool found = rdv.get(target, ep);
            std::string reply(1, kPeer);
            reply.push_back(found ? 1 : 0);
            if (found) put_endpoint(reply, ep);
            sock.send_to(from, reply);
        }
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
    if (dg.size() != 1 + 16 || dg[0] != kRzChallenge) return false;

    /* Step 2: sign the nonce with our signing secret to prove key ownership. */
    uint8_t sig[64];
    sign(id.sign_sk.data(), dg.data() + 1, 16, sig);
    std::string a(1, kRegAuth);
    a.append((const char *)id.sign_pk.data(), 32);
    a.append(dg.data() + 1, 16);
    a.append((const char *)sig, 64);
    if (!sock.send_to(server, a)) return false;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    return !dg.empty() && dg[0] == kRzAck;
}

bool rendezvous_lookup(UdpSocket &sock, const Endpoint &server,
                       const uint8_t target[32], Endpoint &out, int timeout_ms) {
    /* Step 1: ask to look up; the server replies with a return-routability nonce. */
    std::string m(1, kLookup);
    m.append((const char *)target, 32);
    if (!sock.send_to(server, m)) return false;
    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.size() != 1 + 16 || dg[0] != kRzChallenge) return false;

    /* Step 2: echo the nonce from our real address; only then does the server
     * answer (so it never reflects a reply to a spoofed source). */
    std::string a(1, kLookupAuth);
    a.append((const char *)target, 32);
    a.append(dg.data() + 1, 16);
    if (!sock.send_to(server, a)) return false;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.size() < 2 || dg[0] != kPeer || dg[1] != 1) return false;
    const uint8_t *p = (const uint8_t *)dg.data() + 2;
    const uint8_t *end = (const uint8_t *)dg.data() + dg.size();
    return get_endpoint(p, end, out);
}

} // namespace ke
