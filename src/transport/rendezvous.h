/* rendezvous.h — rendezvous registry + UDP service (M5). Internal.
 *
 * Maps a peer's signing public key to the endpoint the server *observed* it
 * from (its reflexive address), and answers lookups so two peers can learn
 * each other's endpoints to attempt a direct connection. The rendezvous never
 * sees plaintext and holds no authority over data — it only brokers endpoints. */
#ifndef SYNC_RENDEZVOUS_H
#define SYNC_RENDEZVOUS_H

#include <array>
#include <cstdint>
#include <map>
#include <string>

#include "crypto.h" /* KeyPair for the ownership-proof register */
#include "transport/udp.h"

namespace ke {

class Rendezvous {
public:
    void set(const uint8_t pk[32], const Endpoint &ep) {
        reg_[std::string((const char *)pk, 32)] = ep;
    }
    bool get(const uint8_t pk[32], Endpoint &out) const {
        auto it = reg_.find(std::string((const char *)pk, 32));
        if (it == reg_.end()) return false;
        out = it->second;
        return true;
    }

    /* Ownership-proof challenge: record a nonce issued to a registrant at
     * `endpoint` for key `pkkey`, then check a presented nonce. Bounded. */
    void issue_challenge(const std::string &endpoint, const uint8_t nonce[16],
                         const std::string &pkkey);
    bool consume_challenge(const std::string &endpoint, const uint8_t nonce[16],
                           const std::string &pkkey);

private:
    std::map<std::string, Endpoint> reg_;
    struct Pending {
        std::array<uint8_t, 16> nonce{};
        std::string             pkkey;
    };
    std::map<std::string, Pending> pending_; /* endpoint -> challenge */
};

/* Process one request: REGISTER starts an ownership-proof challenge;
 * REGISTER-AUTH (with a valid signature) records the sender's observed
 * endpoint; LOOKUP replies with a target's endpoint (if known). Returns true if
 * a datagram was handled. */
bool rendezvous_server_step(Rendezvous &rdv, UdpSocket &sock, int timeout_ms);

/* Client: register our identity's endpoint, proving we own the key by signing
 * the server's challenge with our signing secret. */
bool rendezvous_register(UdpSocket &sock, const Endpoint &server,
                         const KeyPair &id, int timeout_ms);

/* Client: look up a peer's endpoint. Returns true and fills out on success. */
bool rendezvous_lookup(UdpSocket &sock, const Endpoint &server,
                       const uint8_t target[32], Endpoint &out, int timeout_ms);

} // namespace ke

#endif /* SYNC_RENDEZVOUS_H */
