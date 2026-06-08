/* relay.cpp — blind store-and-forward relay + UDP service (M5). */
#include "transport/relay.h"

#include <cstring>

#include "codec.h"  /* ke::put_varint / ke::get_varint */
#include "crypto.h" /* random_bytes for the return-routability nonce */

namespace ke {

namespace {
/* Memory bounds (a relay accepts SENDs from anyone, so it must be capped). */
constexpr size_t kMaxBlobBytes  = 1u << 16;   /* 64 KiB (one datagram)      */
constexpr size_t kMaxKeyBytes   = 1u << 20;   /* 1 MiB queued per destination */
constexpr size_t kMaxKeyBlobs   = 256;        /* blobs queued per destination */
constexpr size_t kMaxTotalBytes = 64u << 20;  /* 64 MiB across all mailboxes  */
constexpr size_t kMaxKeys       = 4096;       /* distinct destinations        */
constexpr size_t kMaxPending    = 4096;       /* outstanding fetch challenges */
} // namespace

void Relay::send(const uint8_t dst[32], const std::string &blob) {
    if (blob.empty() || blob.size() > kMaxBlobBytes) return;
    std::string k = key(dst);
    auto it = mailbox_.find(k);
    if (it == mailbox_.end()) {
        if (mailbox_.size() >= kMaxKeys) return; /* too many destinations */
        it = mailbox_.emplace(k, Mailbox{}).first;
    }
    Mailbox &mb = it->second;
    /* Evict the oldest queued blobs until this one fits the per-key caps. */
    while (!mb.blobs.empty() &&
           (mb.blobs.size() >= kMaxKeyBlobs ||
            mb.bytes + blob.size() > kMaxKeyBytes)) {
        size_t n = mb.blobs.front().size();
        mb.blobs.pop_front();
        mb.bytes -= n;
        total_bytes_ -= n;
    }
    if (mb.bytes + blob.size() > kMaxKeyBytes ||
        total_bytes_ + blob.size() > kMaxTotalBytes) {
        if (mb.blobs.empty()) mailbox_.erase(it);
        return;
    }
    mb.bytes += blob.size();
    total_bytes_ += blob.size();
    mb.blobs.push_back(blob);
}

void Relay::fetch(const uint8_t pk[32], std::vector<std::string> &out) {
    auto it = mailbox_.find(key(pk));
    if (it == mailbox_.end()) return;
    Mailbox &mb = it->second;
    while (!mb.blobs.empty()) {
        out.push_back(std::move(mb.blobs.front()));
        mb.blobs.pop_front();
    }
    total_bytes_ -= mb.bytes;
    mailbox_.erase(it); /* empty mailbox: reclaim */
}

size_t Relay::queued(const uint8_t dst[32]) const {
    auto it = mailbox_.find(key(dst));
    return it == mailbox_.end() ? 0 : it->second.blobs.size();
}

void Relay::issue_challenge(const std::string &endpoint, const uint8_t nonce[16],
                            const std::string &dstkey) {
    if (pending_.size() >= kMaxPending && !pending_.count(endpoint))
        pending_.erase(pending_.begin()); /* bound the pending set */
    Pending p;
    std::memcpy(p.nonce.data(), nonce, 16);
    p.dstkey = dstkey;
    pending_[endpoint] = p;
}

bool Relay::consume_challenge(const std::string &endpoint,
                              const uint8_t nonce[16],
                              const std::string &dstkey) {
    auto it = pending_.find(endpoint);
    if (it == pending_.end()) return false;
    bool ok = it->second.dstkey == dstkey &&
              std::memcmp(it->second.nonce.data(), nonce, 16) == 0;
    pending_.erase(it); /* single-use */
    return ok;
}

namespace {
constexpr char kSend = 'S';      /* 'S' | 32 dst | blob                  */
constexpr char kFetch = 'F';     /* 'F' | 32 me                          */
constexpr char kChallenge = 'C'; /* 'C' | 16 nonce         (relay->me)   */
constexpr char kFetchAuth = 'A'; /* 'A' | 32 me | 16 nonce               */
constexpr char kDeliver = 'D';   /* 'D' | varint n | (varint+blob)*      */

std::string endpoint_key(const Endpoint &e) {
    return e.ip + ":" + std::to_string(e.port);
}

void deliver(Relay &relay, UdpSocket &sock, const Endpoint &from,
             const uint8_t *me) {
    std::vector<std::string> blobs;
    relay.fetch(me, blobs);
    std::string reply(1, kDeliver);
    put_varint(reply, blobs.size());
    for (auto &b : blobs) {
        put_varint(reply, b.size());
        reply += b;
    }
    sock.send_to(from, reply);
}
} // namespace

bool relay_server_step(Relay &relay, UdpSocket &sock, int timeout_ms) {
    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.empty()) return true;

    if (dg[0] == kSend && dg.size() >= 1 + 32) {
        relay.send((const uint8_t *)dg.data() + 1, dg.substr(33));
    } else if (dg[0] == kFetch && dg.size() >= 1 + 32) {
        /* Don't deliver yet: challenge the requester at its claimed address so a
         * spoofed source can't trigger a (large) reflected delivery. */
        uint8_t nonce[16];
        if (!random_bytes(nonce, 16)) return true;
        relay.issue_challenge(endpoint_key(from), nonce,
                              std::string((const char *)dg.data() + 1, 32));
        std::string ch(1, kChallenge);
        ch.append((const char *)nonce, 16);
        sock.send_to(from, ch);
    } else if (dg[0] == kFetchAuth && dg.size() >= 1 + 32 + 16) {
        const uint8_t *me = (const uint8_t *)dg.data() + 1;
        const uint8_t *nonce = me + 32;
        if (relay.consume_challenge(endpoint_key(from), nonce,
                                    std::string((const char *)me, 32)))
            deliver(relay, sock, from, me);
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
    /* Step 1: ask to fetch; the relay replies with a return-routability nonce. */
    std::string m(1, kFetch);
    m.append((const char *)me, 32);
    if (!sock.send_to(server, m)) return false;

    std::string dg;
    Endpoint from;
    if (!sock.recv(dg, from, timeout_ms)) return false;
    if (dg.size() != 1 + 16 || dg[0] != kChallenge) return false;

    /* Step 2: echo the nonce; only we (at our real address) received it. */
    std::string a(1, kFetchAuth);
    a.append((const char *)me, 32);
    a.append(dg.data() + 1, 16);
    if (!sock.send_to(server, a)) return false;

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
