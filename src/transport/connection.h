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
#include <memory>
#include <string>
#include <vector>

#include "noise.h"
#include "transport/relay.h"
#include "transport/reliable.h"
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

/* The per-peer secure state machine: a Noise XX handshake, the transcript-bound
 * identity proof, and capability-scoped range reconciliation, over one peer.
 * Non-blocking and transport-agnostic — it consumes opaque inbound datagrams
 * and emits opaque outbound datagrams; the caller owns the socket and routes
 * them. Both connect_and_sync (one peer, one cycle) and the mesh daemon (N
 * peers, repeated cycles) drive instances of this.
 *
 * gossip_interval_ms == 0: run one reconcile cycle, then quiesce (the
 *   connect_and_sync semantics — settle once the link goes idle).
 * gossip_interval_ms  > 0: keep gossiping — the initiator starts a fresh,
 *   re-snapshotted reconcile cycle every interval; the responder re-snapshots
 *   each cycle. This is how newly-learned data propagates multi-hop. */
class SecurePeerSession {
public:
    SecurePeerSession(sync_engine *e, bool initiator,
                      uint32_t gossip_interval_ms);
    ~SecurePeerSession();

    SecurePeerSession(const SecurePeerSession &) = delete;
    SecurePeerSession &operator=(const SecurePeerSession &) = delete;

    /* Initiator: produce the first handshake datagram (no-op for a responder). */
    void start(uint64_t now_mono, std::vector<std::string> &out);
    /* Feed one inbound datagram; append any outbound datagrams to `out`.
     * Advances handshake -> identity proof -> reconcile as appropriate. */
    void on_datagram(const std::string &dg, uint64_t now_mono,
                     std::vector<std::string> &out);
    /* Time-driven work: reliability retransmits/acks, and (in gossip mode) start
     * a fresh reconcile cycle when idle and the interval has elapsed. */
    void poll(uint64_t now_mono, std::vector<std::string> &out);
    /* Re-handshake from scratch (use when a peer is detected to have restarted). */
    void reset(uint64_t now_mono, std::vector<std::string> &out);

    bool handshake_done() const;   /* Noise XX complete on this side */
    bool authenticated() const;    /* peer's identity proof verified */
    bool idle() const;             /* reliability link fully drained */
    bool failed() const;           /* handshake step or proof verification failed */
    uint64_t last_progress() const { return last_progress_; }
    const uint8_t *peer_pk() const { return peer_pk_.data(); } /* valid once authenticated */

private:
    bool pump_(const uint8_t *in, size_t in_len); /* step+drain session; true if it emitted */
    void send_proof_();
    void enable_after_handshake_();
    void begin_cycle_();                           /* (re)begin a scoped reconcile session */
    void kick_(uint64_t now);                      /* initiator: begin a cycle + send first FP */
    void drain_(uint64_t now, std::vector<std::string> &out);

    sync_engine                  *e_;
    bool                          initiator_;
    uint32_t                      interval_;
    std::unique_ptr<NoiseChannel> chan_;
    ReliableLink                  link_;
    sync_session                 *sess_ = nullptr;
    bool                          proof_sent_ = false;
    bool                          peer_ok_ = false;
    bool                          failed_ = false;
    bool                          sess_done_ = false; /* current cycle drained to empty */
    /* Engine gens when sess_ began — two loose counters, not a ke::GenPair,
     * so this header keeps sync_engine opaque (no engine.hpp include);
     * compared with || at the cycle boundary in poll(). */
    uint64_t                      sess_content_gen_ = 0;
    uint64_t                      sess_scope_gen_ = 0;
    std::array<uint8_t, 32>       peer_pk_{};
    uint64_t                      last_kick_ = 0;
    uint64_t                      last_progress_ = 0;
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
