/* connection.h — connect-and-sync core + connection manager (M5). Internal.
 *
 * Runs a Noise XX handshake + reliability layer + range-reconciliation session
 * over a pluggable per-peer datagram transport, and a ConnectionManager that
 * discovers a peer via rendezvous and tries a direct path before falling back
 * to the relay. */
#ifndef SYNC_CONNECTION_H
#define SYNC_CONNECTION_H

#include <array>
#include <cstdint>
#include <cstring>
#include <deque>
#include <string>
#include <vector>

#include "transport/relay.h"
#include "transport/udp.h"
#include "sync_engine.h"

namespace ke {

/* An opaque-datagram transport to a single peer. */
struct PeerTransport {
    virtual ~PeerTransport() = default;
    virtual bool send(const std::string &dg) = 0;
    /* Receive one datagram (false on timeout). */
    virtual bool recv(std::string &dg, int timeout_ms) = 0;
};

/* Handshake (Noise XX) + run one reconciliation cycle over t to convergence.
 * Returns true if the handshake completed and the session settled before
 * total_timeout_ms. */
bool connect_and_sync(sync_engine *e, PeerTransport &t, bool initiator,
                      int total_timeout_ms);

/* Direct UDP path: datagrams go straight to the peer's endpoint. */
struct DirectTransport : PeerTransport {
    UdpSocket *sock = nullptr;
    Endpoint   peer;
    bool send(const std::string &dg) override { return sock->send_to(peer, dg); }
    bool recv(std::string &dg, int timeout_ms) override {
        Endpoint from;
        return sock->recv(dg, from, timeout_ms);
    }
};

/* Relay path: datagrams are forwarded by destination pubkey through a relay,
 * and received by polling the relay for our queue (store-and-forward). */
struct RelayTransport : PeerTransport {
    UdpSocket              *sock = nullptr;
    Endpoint                relay;
    std::array<uint8_t, 32> peer_pk{};
    std::array<uint8_t, 32> my_pk{};
    std::deque<std::string> inbox;

    bool send(const std::string &dg) override {
        return relay_client_send(*sock, relay, peer_pk.data(), dg);
    }
    bool recv(std::string &dg, int timeout_ms) override {
        if (inbox.empty()) {
            std::vector<std::string> got;
            relay_client_fetch(*sock, relay, my_pk.data(), got, timeout_ms);
            for (auto &g : got) inbox.push_back(std::move(g));
        }
        if (inbox.empty()) return false;
        dg = inbox.front();
        inbox.pop_front();
        return true;
    }
};

/* Outcome of a connection attempt. */
enum class ConnResult { Direct, Relay, Failed };

/* Tries a direct path first, then falls back to the relay. (Peer discovery via
 * rendezvous is a separate step — see transport/rendezvous.h — whose result is
 * passed in as direct_ep.) Uses one persistent socket for both paths. */
class ConnectionManager {
public:
    sync_engine            *engine = nullptr;
    UdpSocket              *sock = nullptr; /* persistent listening socket */
    bool                    have_relay = false;
    Endpoint                relay;
    std::array<uint8_t, 32> my_pk{};

    /* direct_ep: a known peer endpoint to try directly (or NULL to skip
     * straight to relay). Returns which path (if any) achieved convergence. */
    ConnResult sync_with(const uint8_t peer_pk[32], bool initiator,
                         const Endpoint *direct_ep, int direct_ms, int relay_ms);
};

} // namespace ke

#endif /* SYNC_CONNECTION_H */
