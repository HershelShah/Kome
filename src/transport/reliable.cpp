/* reliable.cpp — stop-and-wait reliability over datagrams (M5). */
#include "transport/reliable.h"

#include <cstring>

#include "byteorder.h"
#include "crypto.h" /* hmac_sha256 for the frame MAC */

namespace ke {

namespace {
constexpr uint8_t kData = 0;
constexpr uint8_t kAck = 1;
constexpr size_t kMacLen = 16;

/* Datagram: [auth:1][type:1][seq:u32le][payload] then, when auth!=0, a 16-byte
 * HMAC-SHA256 tag over everything before it. */
std::string frame(uint8_t type, uint32_t seq, const std::string &payload,
                  bool mac, const uint8_t key[32]) {
    std::string d;
    d.push_back(mac ? 1 : 0);
    d.push_back((char)type);
    put_u32le(d, seq);
    d += payload;
    if (mac) {
        uint8_t tag[32];
        hmac_sha256(key, 32, (const uint8_t *)d.data(), d.size(), tag);
        d.append((const char *)tag, kMacLen);
    }
    return d;
}

/* Parse and (when flagged) authenticate. Sets authed = whether the frame
 * carried a valid MAC. An authenticated frame requires the key; an unauthen-
 * ticated frame parses fine here — on_datagram then refuses to let it *change
 * state* once the link is keyed (so stale handshake-phase duplicates are still
 * accepted, but a forged seq/ack at the live position is rejected). */
bool parse(const std::string &dg, bool keyed, const uint8_t key[32],
           uint8_t &type, uint32_t &seq, std::string &payload, bool &authed) {
    if (dg.size() < 6) return false;
    bool macd = (uint8_t)dg[0] != 0;
    size_t body = dg.size();
    if (macd) {
        if (!keyed || dg.size() < 6 + kMacLen) return false;
        body = dg.size() - kMacLen;
        uint8_t tag[32];
        hmac_sha256(key, 32, (const uint8_t *)dg.data(), body, tag);
        if (std::memcmp(tag, dg.data() + body, kMacLen) != 0) return false;
    }
    authed = macd;
    type = (uint8_t)dg[1];
    seq = read_u32le((const uint8_t *)dg.data() + 2);
    payload.assign(dg.data() + 6, body - 6);
    return true;
}
} // namespace

void ReliableLink::enable_mac(const uint8_t key[32]) {
    std::memcpy(mac_key_.data(), key, 32);
    keyed_ = true;
}

void ReliableLink::send(const std::string &msg) {
    outbox_.emplace_back(msg, keyed_); /* authenticate per enqueue-time state */
}

bool ReliableLink::on_datagram(const std::string &dg,
                               std::vector<std::string> &delivered) {
    uint8_t type;
    uint32_t seq;
    std::string payload;
    bool authed = false;
    if (!parse(dg, keyed_, mac_key_.data(), type, seq, payload, authed))
        return false;

    bool progress = false;
    if (type == kData) {
        bool advances = (seq == recv_seq_);
        /* Once keyed, only an authenticated frame may advance our stream; an
         * unauthenticated frame at the live seq could be forged. Stale plain
         * duplicates (seq != recv_seq_) are still accepted and re-acked, which
         * lets the last handshake-phase frames settle across the key boundary. */
        if (keyed_ && !authed && advances) return false;
        if (advances) {
            delivered.push_back(payload);
            recv_seq_++;
            progress = true;
        }
        ack_pending_ = true;
        ack_seq_ = recv_seq_ - 1;
    } else if (type == kAck) {
        bool clears = (in_flight_ && seq == send_seq_);
        if (keyed_ && !authed && clears) return false; /* forged ack */
        if (clears) {
            in_flight_ = false;
            in_flight_payload_.clear();
            send_seq_++;
            progress = true;
        }
    }
    return progress;
}

void ReliableLink::poll(std::vector<std::string> &out, uint64_t now_ms) {
    const uint8_t *k = mac_key_.data();
    /* Pending ack first (authenticated once the link is keyed). */
    if (ack_pending_) {
        out.push_back(frame(kAck, ack_seq_, std::string(), keyed_, k));
        ack_pending_ = false;
    }
    /* Start a new send if the channel is free. */
    if (!in_flight_ && !outbox_.empty()) {
        in_flight_payload_ = outbox_.front().first;
        in_flight_mac_ = outbox_.front().second;
        outbox_.pop_front();
        in_flight_ = true;
        out.push_back(frame(kData, send_seq_, in_flight_payload_, in_flight_mac_, k));
        last_tx_ms_ = now_ms;
        return;
    }
    /* Retransmit if the ack is overdue. */
    if (in_flight_ && now_ms - last_tx_ms_ >= kRtoMs) {
        out.push_back(frame(kData, send_seq_, in_flight_payload_, in_flight_mac_, k));
        last_tx_ms_ = now_ms;
    }
}

bool ReliableLink::idle() const {
    return !in_flight_ && outbox_.empty() && !ack_pending_;
}

} // namespace ke
