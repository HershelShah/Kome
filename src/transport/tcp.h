/* tcp.h — minimal loopback TCP stream with message framing.
 *
 * TCP is a byte stream, so messages are length-prefixed ([4-byte LE len][bytes])
 * and reassembled on receive. This exposes the same datagram-shaped
 * send/recv-one-message interface as UDP, so the transport-agnostic stack
 * (reliability layer, Noise channel, reconciliation session, connect_and_sync)
 * runs over TCP unchanged. */
#ifndef SYNC_TCP_H
#define SYNC_TCP_H

#include <cstdint>
#include <string>

#include "transport/udp.h" /* Endpoint */

namespace ke {

class TcpStream {
public:
    TcpStream() = default;
    ~TcpStream();
    TcpStream(const TcpStream &) = delete;
    TcpStream &operator=(const TcpStream &) = delete;

    /* Connect to ep (blocking handshake, then non-blocking I/O). */
    bool connect_to(const Endpoint &ep);
    /* Take ownership of an already-connected fd (e.g. from accept). */
    void adopt(int fd);
    void close();
    int fd() const { return fd_; }

    /* Send one length-prefixed message (sends it in full). */
    bool send_frame(const std::string &msg);
    /* Receive exactly one reassembled message; false on timeout/close. */
    bool recv_frame(std::string &out, int timeout_ms);

    /* Raw byte I/O (used by the WebSocket layer, which has its own framing). */
    bool send_all(const char *p, size_t n);
    bool recv_into(std::string &buf, int timeout_ms); /* appends; false=timeout/close */

private:
    bool extract(std::string &out);
    int         fd_ = -1;
    std::string rx_; /* reassembly buffer */
};

class TcpListener {
public:
    ~TcpListener();
    bool open(const char *ip, uint16_t port);
    Endpoint local() const { return local_; }
    /* Accept one connection into out; false on timeout. */
    bool accept(TcpStream &out, int timeout_ms);
    void close();

private:
    int      fd_ = -1;
    Endpoint local_;
};

} // namespace ke

#endif /* SYNC_TCP_H */
