/* relay.cpp — blind store-and-forward relay + UDP service (M5). */
#include "transport/relay.h"

#include <cstring>

#include "codec.h" /* ke::put_varint / ke::get_varint */

namespace ke {

void Relay::send(const uint8_t dst[32], const std::string &blob) {
    mailbox_[key(dst)].push_back(blob);
}

void Relay::fetch(const uint8_t pk[32], std::vector<std::string> &out) {
    auto it = mailbox_.find(key(pk));
    if (it == mailbox_.end()) return;
    while (!it->second.empty()) {
        out.push_back(it->second.front());
        it->second.pop_front();
    }
}

size_t Relay::queued(const uint8_t dst[32]) const {
    auto it = mailbox_.find(key(dst));
    return it == mailbox_.end() ? 0 : it->second.size();
}

namespace {
constexpr char kSend = 'S';     /* 'S' | 32 dst | blob          */
constexpr char kFetch = 'F';    /* 'F' | 32 me                  */
constexpr char kDeliver = 'D';  /* 'D' | varint n | (varint+blob)* */
} // namespace

bool relay_server_step(Relay &relay, UdpSocket &sock, int timeout_ms) {
    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.empty()) return true;

    if (dg[0] == kSend && dg.size() >= 1 + 32) {
        relay.send((const uint8_t *)dg.data() + 1, dg.substr(33));
    } else if (dg[0] == kFetch && dg.size() >= 1 + 32) {
        std::vector<std::string> blobs;
        relay.fetch((const uint8_t *)dg.data() + 1, blobs);
        std::string reply(1, kDeliver);
        put_varint(reply, blobs.size());
        for (auto &b : blobs) {
            put_varint(reply, b.size());
            reply += b;
        }
        sock.send_to(from, reply);
    }
    return true;
}

bool relay_client_send(UdpSocket &sock, const Endpoint &server,
                       const uint8_t dst[32], const std::string &blob) {
    std::string m(1, kSend);
    m.append((const char *)dst, 32);
    m += blob;
    return sock.send_to(server, m);
}

bool relay_client_fetch(UdpSocket &sock, const Endpoint &server,
                        const uint8_t me[32], std::vector<std::string> &out,
                        int timeout_ms) {
    std::string m(1, kFetch);
    m.append((const char *)me, 32);
    if (!sock.send_to(server, m)) return false;

    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.empty() || dg[0] != kDeliver) return false;

    const uint8_t *p = (const uint8_t *)dg.data() + 1;
    const uint8_t *end = (const uint8_t *)dg.data() + dg.size();
    uint64_t n = 0;
    if (!get_varint(p, end, n)) return false;
    for (uint64_t i = 0; i < n; i++) {
        uint64_t l = 0;
        if (!get_varint(p, end, l)) return false;
        if ((uint64_t)(end - p) < l) return false;
        out.emplace_back((const char *)p, (size_t)l);
        p += l;
    }
    return true;
}

} // namespace ke
