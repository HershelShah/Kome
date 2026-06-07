/* tcp.cpp — loopback TCP stream with length-prefix framing. */
#include "transport/tcp.h"

#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>

namespace ke {

namespace {
void set_nonblock(int fd) {
    int fl = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, fl | O_NONBLOCK);
}
} // namespace

TcpStream::~TcpStream() { close(); }

void TcpStream::close() {
    if (fd_ >= 0) { ::close(fd_); fd_ = -1; }
    rx_.clear();
}

void TcpStream::adopt(int fd) {
    close();
    fd_ = fd;
    int one = 1;
    setsockopt(fd_, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
    set_nonblock(fd_);
}

bool TcpStream::connect_to(const Endpoint &ep) {
    int fd = ::socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return false;
    sockaddr_in a;
    std::memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons(ep.port);
    if (inet_pton(AF_INET, ep.ip.c_str(), &a.sin_addr) != 1) { ::close(fd); return false; }
    if (::connect(fd, (sockaddr *)&a, sizeof a) != 0) { ::close(fd); return false; }
    adopt(fd);
    return true;
}

bool TcpStream::send_all(const char *p, size_t n) {
    if (fd_ < 0) return false;
    size_t off = 0;
    while (off < n) {
        ssize_t w = ::send(fd_, p + off, n - off, MSG_NOSIGNAL);
        if (w > 0) { off += (size_t)w; continue; }
        if (w < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
            struct pollfd pf{fd_, POLLOUT, 0};
            ::poll(&pf, 1, 1000);
            continue;
        }
        return false; /* closed / error */
    }
    return true;
}

bool TcpStream::recv_into(std::string &buf, int timeout_ms) {
    if (fd_ < 0) return false;
    struct pollfd p{fd_, POLLIN, 0};
    if (::poll(&p, 1, timeout_ms) <= 0) return false;
    char tmp[65536];
    ssize_t n = ::recv(fd_, tmp, sizeof tmp, 0);
    if (n <= 0) return false;
    buf.append(tmp, (size_t)n);
    return true;
}

bool TcpStream::send_frame(const std::string &msg) {
    std::string buf;
    uint32_t n = (uint32_t)msg.size();
    for (int i = 0; i < 4; i++) buf.push_back((char)(n >> (i * 8)));
    buf += msg;
    return send_all(buf.data(), buf.size());
}

bool TcpStream::extract(std::string &out) {
    if (rx_.size() < 4) return false;
    uint32_t len = (uint8_t)rx_[0] | ((uint8_t)rx_[1] << 8) |
                   ((uint8_t)rx_[2] << 16) | ((uint32_t)(uint8_t)rx_[3] << 24);
    if (rx_.size() < 4 + (size_t)len) return false;
    out.assign(rx_.data() + 4, len);
    rx_.erase(0, 4 + (size_t)len);
    return true;
}

bool TcpStream::recv_frame(std::string &out, int timeout_ms) {
    if (fd_ < 0) return false;
    if (extract(out)) return true; /* already buffered */
    char tmp[65536];
    for (;;) {
        struct pollfd p{fd_, POLLIN, 0};
        if (::poll(&p, 1, timeout_ms) <= 0) return false; /* timeout */
        ssize_t n = ::recv(fd_, tmp, sizeof tmp, 0);
        if (n <= 0) return false; /* peer closed / error */
        rx_.append(tmp, (size_t)n);
        if (extract(out)) return true;
        /* partial frame — poll again for the rest */
    }
}

TcpListener::~TcpListener() { close(); }

void TcpListener::close() {
    if (fd_ >= 0) { ::close(fd_); fd_ = -1; }
}

bool TcpListener::open(const char *ip, uint16_t port) {
    fd_ = ::socket(AF_INET, SOCK_STREAM, 0);
    if (fd_ < 0) return false;
    int one = 1;
    setsockopt(fd_, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    sockaddr_in a;
    std::memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons(port);
    if (inet_pton(AF_INET, ip ? ip : "127.0.0.1", &a.sin_addr) != 1) { close(); return false; }
    if (::bind(fd_, (sockaddr *)&a, sizeof a) != 0) { close(); return false; }
    if (::listen(fd_, 8) != 0) { close(); return false; }
    socklen_t len = sizeof a;
    getsockname(fd_, (sockaddr *)&a, &len);
    char buf[INET_ADDRSTRLEN];
    inet_ntop(AF_INET, &a.sin_addr, buf, sizeof buf);
    local_.ip = buf;
    local_.port = ntohs(a.sin_port);
    return true;
}

bool TcpListener::accept(TcpStream &out, int timeout_ms) {
    if (fd_ < 0) return false;
    struct pollfd p{fd_, POLLIN, 0};
    if (::poll(&p, 1, timeout_ms) <= 0) return false;
    int c = ::accept(fd_, nullptr, nullptr);
    if (c < 0) return false;
    out.adopt(c);
    return true;
}

} // namespace ke
