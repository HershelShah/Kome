/* relay.h — blind store-and-forward relay (M5). Internal.
 *
 * Forwards opaque ciphertext blobs addressed by destination public key. It has
 * no key material and no decryption path, so it cannot read what it carries
 * (privacy invariant). Blobs for an offline destination are queued (FIFO) until
 * the destination fetches them — store-and-forward for offline peers. This is
 * the relay's core logic; a network service wraps it with a socket. */
#ifndef SYNC_RELAY_H
#define SYNC_RELAY_H

#include <array>
#include <cstdint>
#include <deque>
#include <map>
#include <string>
#include <vector>

#include "transport/cookie.h"
#include "transport/udp.h"

namespace ke {

class Relay {
public:
    /* Queue an opaque blob for delivery to dst (32-byte public key). Oversized
     * blobs are dropped; per-destination and global caps bound memory (oldest
     * queued blobs are evicted to make room). When the distinct-destination cap
     * is hit, the least-recently-used mailbox is evicted so a one-time spray of
     * junk destination keys can't permanently block new peers (F6). */
    void send(const uint8_t dst[32], const std::string &blob);

    /* Drain (in order) the blobs waiting for pk; appends to out. */
    void fetch(const uint8_t pk[32], std::vector<std::string> &out);

    /* Number of blobs currently queued for dst. */
    size_t queued(const uint8_t dst[32]) const;

    /* Number of distinct destination mailboxes currently held (for tests). */
    size_t mailboxes() const { return mailbox_.size(); }

    /* Stateless return-routability cookie for a FETCH from `endpoint` for key
     * `key`. `issue` returns the cookie to send as the challenge; `valid` checks
     * a presented cookie. Only a requester that received the challenge at the
     * endpoint it claimed can echo a valid cookie, defeating spoofed-source
     * reflection — with no server-side per-request state to exhaust (F5). */
    bool fetch_cookie(const std::string &endpoint, const uint8_t key[32],
                      uint8_t out[16]);
    bool fetch_cookie_valid(const std::string &endpoint, const uint8_t key[32],
                            const uint8_t presented[16]);

private:
    static std::string key(const uint8_t pk[32]) {
        return std::string((const char *)pk, 32);
    }
    struct Mailbox {
        std::deque<std::string> blobs;
        size_t                  bytes = 0;
        uint64_t                seq = 0; /* last-access order; 0 == not in lru_ */
    };
    /* Mark a mailbox most-recently-used (maintains the lru_ index). */
    void touch(std::map<std::string, Mailbox>::iterator it);

    std::map<std::string, Mailbox> mailbox_;
    std::map<uint64_t, std::string> lru_; /* seq -> mailbox key, ascending */
    uint64_t                       access_seq_ = 0;
    size_t                         total_bytes_ = 0;

    Cookies cookies_;
};

/* ---- UDP relay service (wraps the blind Relay core) -------------------- */

/* Process one incoming relay request on sock (SEND queues; FETCH replies with
 * the requester's queued blobs). Returns true if a datagram was handled. */
bool relay_server_step(Relay &relay, UdpSocket &sock, int timeout_ms);

/* Client: queue an opaque blob for dst at the relay `server`. */
bool relay_client_send(UdpSocket &sock, const Endpoint &server,
                       const uint8_t dst[32], const std::string &blob);

/* Client: fetch blobs addressed to me from `server`; appends to out. */
bool relay_client_fetch(UdpSocket &sock, const Endpoint &server,
                        const uint8_t me[32], std::vector<std::string> &out,
                        int timeout_ms);

} // namespace ke

#endif /* SYNC_RELAY_H */
