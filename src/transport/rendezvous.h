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
#include "transport/cookie.h"
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

    /* Stateless return-routability cookies for REGISTER and LOOKUP. `issue`
     * returns the cookie to send as the challenge; `valid` checks a presented
     * one. Binding the cookie to the requester's observed endpoint defeats
     * spoofed-source reflection, with no per-request server state to exhaust
     * (F5). REGISTER and LOOKUP cookies are domain-separated so one can't be
     * redeemed as the other. */
    bool register_cookie(const std::string &endpoint, const uint8_t key[32],
                         uint8_t out[16]);
    bool register_cookie_valid(const std::string &endpoint, const uint8_t key[32],
                               const uint8_t presented[16]);
    bool lookup_cookie(const std::string &endpoint, const uint8_t key[32],
                       uint8_t out[16]);
    bool lookup_cookie_valid(const std::string &endpoint, const uint8_t key[32],
                             const uint8_t presented[16]);

private:
    std::map<std::string, Endpoint> reg_;
    Cookies                         cookies_;
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
