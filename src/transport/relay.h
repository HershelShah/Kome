/* relay.h — blind store-and-forward relay (M5). Internal.
 *
 * Forwards opaque ciphertext blobs addressed by destination public key. It has
 * no key material and no decryption path, so it cannot read what it carries
 * (privacy invariant). Blobs for an offline destination are queued (FIFO) until
 * the destination fetches them — store-and-forward for offline peers. This is
 * the relay's core logic; a network service wraps it with a socket. */
#ifndef SYNC_RELAY_H
#define SYNC_RELAY_H

#include <cstdint>
#include <deque>
#include <map>
#include <string>
#include <vector>

#include "transport/udp.h"

namespace ke {

class Relay {
public:
    /* Queue an opaque blob for delivery to dst (32-byte public key). */
    void send(const uint8_t dst[32], const std::string &blob);

    /* Drain (in order) the blobs waiting for pk; appends to out. */
    void fetch(const uint8_t pk[32], std::vector<std::string> &out);

    /* Number of blobs currently queued for dst. */
    size_t queued(const uint8_t dst[32]) const;

private:
    static std::string key(const uint8_t pk[32]) {
        return std::string((const char *)pk, 32);
    }
    std::map<std::string, std::deque<std::string>> mailbox_;
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
