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

#include "transport/udp.h"

namespace ke {

class Relay {
public:
    /* Queue an opaque blob for delivery to dst (32-byte public key). Oversized
     * blobs are dropped; per-destination and global caps bound memory (oldest
     * queued blobs are evicted to make room). */
    void send(const uint8_t dst[32], const std::string &blob);

    /* Drain (in order) the blobs waiting for pk; appends to out. */
    void fetch(const uint8_t pk[32], std::vector<std::string> &out);

    /* Number of blobs currently queued for dst. */
    size_t queued(const uint8_t dst[32]) const;

    /* Return-routability: record a challenge nonce issued to a requester at
     * `endpoint` (for destination key dstkey), and later check a presented
     * nonce. Only a requester that actually receives the challenge (i.e. is at
     * the endpoint it claimed) can present it back, which defeats spoofed-source
     * reflection. The pending set is bounded. */
    void issue_challenge(const std::string &endpoint, const uint8_t nonce[16],
                         const std::string &dstkey);
    bool consume_challenge(const std::string &endpoint, const uint8_t nonce[16],
                           const std::string &dstkey);

private:
    static std::string key(const uint8_t pk[32]) {
        return std::string((const char *)pk, 32);
    }
    struct Mailbox {
        std::deque<std::string> blobs;
        size_t                  bytes = 0;
    };
    std::map<std::string, Mailbox> mailbox_;
    size_t                         total_bytes_ = 0;

    struct Pending {
        std::array<uint8_t, 16> nonce{};
        std::string             dstkey;
    };
    std::map<std::string, Pending> pending_; /* endpoint -> challenge */
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
