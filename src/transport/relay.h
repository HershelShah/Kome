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

} // namespace ke

#endif /* SYNC_RELAY_H */
