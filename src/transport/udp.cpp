/* udp.cpp — minimal UDP datagram socket (M5). */
#include "transport/udp.h"

#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>

#include <cstring>

namespace ke {

UdpSocket::~UdpSocket() { close(); }

void UdpSocket::close() {
    if (fd_ >= 0) {
        ::close(fd_);
        fd_ = -1;
    }
}

bool UdpSocket::open(const char *bind_ip, uint16_t port) {
    fd_ = ::socket(AF_INET, SOCK_DGRAM, 0);
    if (fd_ < 0) return false;

    int flags = fcntl(fd_, F_GETFL, 0);
    fcntl(fd_, F_SETFL, flags | O_NONBLOCK);

    sockaddr_in addr;
    std::memset(&addr, 0, sizeof addr);
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    if (inet_pton(AF_INET, bind_ip ? bind_ip : "127.0.0.1", &addr.sin_addr) != 1) {
        close();
        return false;
    }
    if (::bind(fd_, (sockaddr *)&addr, sizeof addr) != 0) {
        close();
        return false;
    }
    socklen_t len = sizeof addr;
    if (getsockname(fd_, (sockaddr *)&addr, &len) != 0) {
        close();
        return false;
    }
    char buf[INET_ADDRSTRLEN];
    inet_ntop(AF_INET, &addr.sin_addr, buf, sizeof buf);
    local_.ip = buf;
    local_.port = ntohs(addr.sin_port);
    return true;
}

bool UdpSocket::send_to(const Endpoint &dst, const std::string &data) {
    if (fd_ < 0) return false;
    sockaddr_in addr;
    std::memset(&addr, 0, sizeof addr);
    addr.sin_family = AF_INET;
    addr.sin_port = htons(dst.port);
    if (inet_pton(AF_INET, dst.ip.c_str(), &addr.sin_addr) != 1) return false;
    ssize_t n = ::sendto(fd_, data.data(), data.size(), 0, (sockaddr *)&addr,
                         sizeof addr);
    return n == (ssize_t)data.size();
}

bool UdpSocket::recv(std::string &out, Endpoint &from, int timeout_ms) {
    if (fd_ < 0) return false;
    struct pollfd pfd;
    pfd.fd = fd_;
    pfd.events = POLLIN;
    int r = ::poll(&pfd, 1, timeout_ms);
    if (r <= 0) return false;

    char buf[65536];
    sockaddr_in addr;
    socklen_t alen = sizeof addr;
    ssize_t n = ::recvfrom(fd_, buf, sizeof buf, 0, (sockaddr *)&addr, &alen);
    if (n < 0) return false;
    out.assign(buf, (size_t)n);
    char ip[INET_ADDRSTRLEN];
    inet_ntop(AF_INET, &addr.sin_addr, ip, sizeof ip);
    from.ip = ip;
    from.port = ntohs(addr.sin_port);
    return true;
}

} // namespace ke
