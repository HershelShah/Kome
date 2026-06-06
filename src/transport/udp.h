/* udp.h — minimal UDP datagram socket (M5). Internal.
 *
 * A thin wrapper over a non-blocking UDP socket: bind, learn the local
 * endpoint, send to / receive from a peer endpoint. The reliability layer and
 * Noise channel run on top; this just moves datagrams. */
#ifndef SYNC_UDP_H
#define SYNC_UDP_H

#include <cstdint>
#include <string>

namespace ke {

struct Endpoint {
    std::string ip;
    uint16_t    port = 0;
    bool operator==(const Endpoint &o) const {
        return ip == o.ip && port == o.port;
    }
};

class UdpSocket {
public:
    UdpSocket() = default;
    ~UdpSocket();
    UdpSocket(const UdpSocket &) = delete;
    UdpSocket &operator=(const UdpSocket &) = delete;

    /* Bind to bind_ip:port (port 0 = ephemeral). Returns false on error. */
    bool open(const char *bind_ip, uint16_t port);
    void close();

    Endpoint local() const { return local_; }
    int      fd() const { return fd_; }

    bool send_to(const Endpoint &dst, const std::string &data);
    /* Receive one datagram into out (with sender in from). timeout_ms < 0 waits
     * indefinitely; 0 polls. Returns false on timeout/error. */
    bool recv(std::string &out, Endpoint &from, int timeout_ms);

private:
    int      fd_ = -1;
    Endpoint local_;
};

} // namespace ke

#endif /* SYNC_UDP_H */
