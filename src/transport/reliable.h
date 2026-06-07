/* reliable.h — reliability layer over an unreliable datagram link (M5).
 * Internal.
 *
 * Turns a lossy / reordering / duplicating datagram channel into a reliable,
 * in-order message stream. Stop-and-wait with sequence numbers, cumulative
 * acks, and timed retransmission — which matches the one-message-in-flight
 * reconciliation protocol that runs on top. Pump-style (no callbacks): the
 * caller moves datagrams between peers and advances the clock. */
#ifndef SYNC_RELIABLE_H
#define SYNC_RELIABLE_H

#include <cstdint>
#include <deque>
#include <string>
#include <vector>

namespace ke {

class ReliableLink {
public:
    /* Queue an application message for reliable, ordered delivery. */
    void send(const std::string &msg);

    /* Feed one incoming datagram; append any fully-delivered application
     * messages (in order) to `delivered`. Returns true if the datagram made
     * genuine progress (delivered a message or acked our outstanding send) —
     * a liveness signal callers can use to detect a silent/restarted peer. */
    bool on_datagram(const std::string &dg, std::vector<std::string> &delivered);

    /* Collect datagrams to transmit now: freshly queued data plus any
     * retransmission whose ack is overdue, plus pending acks. */
    void poll(std::vector<std::string> &out, uint64_t now_ms);

    /* True when nothing is queued, outstanding, or awaiting ack. */
    bool idle() const;

    /* Retransmission timeout, milliseconds. */
    static constexpr uint64_t kRtoMs = 50;

private:
    /* Outbound: stop-and-wait. */
    std::deque<std::string> outbox_;       /* messages not yet sent */
    bool        in_flight_ = false;        /* a DATA awaiting its ACK */
    uint32_t    send_seq_ = 0;             /* seq of the in-flight DATA */
    std::string in_flight_payload_;
    uint64_t    last_tx_ms_ = 0;

    /* Inbound. */
    uint32_t    recv_seq_ = 0;             /* next expected DATA seq */
    bool        ack_pending_ = false;
    uint32_t    ack_seq_ = 0;
};

} // namespace ke

#endif /* SYNC_RELIABLE_H */
