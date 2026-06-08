/* ws.h — RFC 6455 WebSocket transport (server + client). Internal.
 *
 * Lets a node speak WebSocket so a browser (or another node) can connect: the
 * HTTP Upgrade handshake, masked/unmasked binary framing, fragmentation, and
 * ping/close control frames. Presents the same datagram-shaped send/recv as the
 * other transports, so the reconciliation stack runs over it unchanged. */
#ifndef SYNC_WS_H
#define SYNC_WS_H

#include <cstdint>
#include <string>

#include "transport/tcp.h"

namespace ke {

/* Sec-WebSocket-Accept for a given Sec-WebSocket-Key (base64(SHA1(key+GUID))).
 * Exposed so it can be checked against the RFC 6455 example vector. */
std::string ws_accept_key(const std::string &key);

class WsStream {
public:
    TcpStream tcp; /* the underlying connection (connect/accept into this) */

    /* Server side: read the client's Upgrade request and reply 101. */
    bool server_handshake(int timeout_ms);
    /* Client side (browser-style): send the Upgrade request and verify 101. */
    bool client_handshake(const std::string &host, int timeout_ms);

    /* One binary message per call. send masks iff this side is the client
     * (per RFC 6455). recv reassembles fragmentation and answers pings. */
    bool send_frame(const std::string &msg);
    bool recv_frame(std::string &out, int timeout_ms);

private:
    bool      is_client_ = false;
    std::string rx_;       /* raw bytes not yet parsed into frames */
    std::string assembling_; /* payload of a fragmented message in progress */
    uint8_t   assembling_op_ = 0;
    bool      in_message_ = false;
};

/* Parse one WebSocket frame from buf[0,len). Returns 1 and fills fin/op,
 * the unmasked payload, and consumed on a complete frame; 0 if more bytes are
 * needed; -1 on a protocol violation (length exceeds the cap / would overflow
 * the size math). Pure (no socket, no state) so it is unit- and fuzz-testable. */
int ws_parse_frame(const uint8_t *buf, size_t len, bool &fin, uint8_t &op,
                   std::string &payload, size_t &consumed);

} // namespace ke

#endif /* SYNC_WS_H */
