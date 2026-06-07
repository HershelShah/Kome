/* reliable.cpp — stop-and-wait reliability over datagrams (M5). */
#include "transport/reliable.h"

#include <cstring>

namespace ke {

namespace {
constexpr uint8_t kData = 0;
constexpr uint8_t kAck = 1;

std::string frame(uint8_t type, uint32_t seq, const std::string &payload) {
    std::string d;
    d.push_back((char)type);
    for (int i = 0; i < 4; i++) d.push_back((char)(seq >> (i * 8)));
    d += payload;
    return d;
}

bool parse(const std::string &dg, uint8_t &type, uint32_t &seq,
           std::string &payload) {
    if (dg.size() < 5) return false;
    type = (uint8_t)dg[0];
    seq = 0;
    for (int i = 0; i < 4; i++)
        seq |= (uint32_t)(uint8_t)dg[1 + i] << (i * 8);
    payload.assign(dg.data() + 5, dg.size() - 5);
    return true;
}
} // namespace

void ReliableLink::send(const std::string &msg) { outbox_.push_back(msg); }

bool ReliableLink::on_datagram(const std::string &dg,
                               std::vector<std::string> &delivered) {
    uint8_t type;
    uint32_t seq;
    std::string payload;
    if (!parse(dg, type, seq, payload)) return false;

    bool progress = false;
    if (type == kData) {
        if (seq == recv_seq_) {
            delivered.push_back(payload);
            recv_seq_++;
            progress = true;
        }
        /* Always (re-)ack the highest in-order seq we have, so a lost ack or a
         * duplicate DATA is handled. ack the last accepted seq. */
        ack_pending_ = true;
        ack_seq_ = recv_seq_ - 1;
    } else if (type == kAck) {
        if (in_flight_ && seq == send_seq_) {
            in_flight_ = false;
            in_flight_payload_.clear();
            send_seq_++;
            progress = true;
        }
    }
    return progress;
}

void ReliableLink::poll(std::vector<std::string> &out, uint64_t now_ms) {
    /* Pending ack first. */
    if (ack_pending_) {
        out.push_back(frame(kAck, ack_seq_, std::string()));
        ack_pending_ = false;
    }
    /* Start a new send if the channel is free. */
    if (!in_flight_ && !outbox_.empty()) {
        in_flight_payload_ = outbox_.front();
        outbox_.pop_front();
        in_flight_ = true;
        out.push_back(frame(kData, send_seq_, in_flight_payload_));
        last_tx_ms_ = now_ms;
        return;
    }
    /* Retransmit if the ack is overdue. */
    if (in_flight_ && now_ms - last_tx_ms_ >= kRtoMs) {
        out.push_back(frame(kData, send_seq_, in_flight_payload_));
        last_tx_ms_ = now_ms;
    }
}

bool ReliableLink::idle() const {
    return !in_flight_ && outbox_.empty() && !ack_pending_;
}

} // namespace ke
