/* rendezvous.cpp — rendezvous registry + UDP service (M5). */
#include "transport/rendezvous.h"

#include <cstring>

#include "codec.h" /* ke::put_varint / ke::get_varint */

namespace ke {

namespace {
constexpr char kRegister = 'R'; /* 'R' | 32 me                     */
constexpr char kAck = 'A';      /* 'A'                             */
constexpr char kLookup = 'L';   /* 'L' | 32 target                 */
constexpr char kPeer = 'P';     /* 'P' | found(1) | varint ip | port(2) */

void put_endpoint(std::string &o, const Endpoint &ep) {
    put_varint(o, ep.ip.size());
    o += ep.ip;
    o.push_back((char)(ep.port & 0xff));
    o.push_back((char)(ep.port >> 8));
}
bool get_endpoint(const uint8_t *&p, const uint8_t *end, Endpoint &ep) {
    uint64_t l = 0;
    if (!get_varint(p, end, l)) return false;
    if ((uint64_t)(end - p) < l + 2) return false;
    ep.ip.assign((const char *)p, (size_t)l);
    p += l;
    ep.port = (uint16_t)((uint8_t)p[0] | ((uint8_t)p[1] << 8));
    p += 2;
    return true;
}
} // namespace

bool rendezvous_server_step(Rendezvous &rdv, UdpSocket &sock, int timeout_ms) {
    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.empty()) return true;

    if (dg[0] == kRegister && dg.size() >= 1 + 32) {
        /* Record the observed (reflexive) source endpoint. */
        rdv.set((const uint8_t *)dg.data() + 1, from);
        std::string ack(1, kAck);
        sock.send_to(from, ack);
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
                         const uint8_t me[32], int timeout_ms) {
    std::string m(1, kRegister);
    m.append((const char *)me, 32);
    if (!sock.send_to(server, m)) return false;
    std::string dg;
    Endpoint from;
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
