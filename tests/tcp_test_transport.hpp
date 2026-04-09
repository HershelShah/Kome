#ifndef TCP_TEST_TRANSPORT_HPP
#define TCP_TEST_TRANSPORT_HPP

/**
 * @file tcp_test_transport.hpp
 * @brief Minimal TCP transport for integration testing.
 *
 * Two TcpTestNode instances connect via localhost TCP. Each runs a
 * background recv thread that reads length-prefixed messages and
 * dispatches to the KomeTransport recv callback.
 *
 * Wire format per message: [4-byte big-endian length][payload]
 *
 * This is TEST-ONLY code — not part of the library.
 */

#include "kome.h"
#include <cstdint>
#include <cstring>
#include <string>
#include <thread>
#include <atomic>
#include <mutex>
#include <functional>

#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <fcntl.h>

struct TcpTestNode {
    KomeTransport transport;
    uint8_t       fingerprint[32] = {};
    uint8_t       peer_fingerprint[32] = {};

    void (*recv_cb)(void *ud, const uint8_t *peer_fp,
                    const uint8_t *data, size_t len) = nullptr;
    void *recv_ud = nullptr;
    void (*peer_cb)(void *ud, const uint8_t *peer_fp, int connected) = nullptr;
    void *peer_ud = nullptr;

    int           conn_fd = -1;
    std::thread   recv_thread;
    std::atomic<bool> running{false};
    std::mutex    send_mu;

    ~TcpTestNode() { stop(); }

    void stop() {
        running.store(false);
        /* shutdown() unblocks the recv thread's blocking recv() call */
        if (conn_fd >= 0) shutdown(conn_fd, SHUT_RDWR);
        if (recv_thread.joinable()) recv_thread.join();
        /* Close fd only after the recv thread has exited */
        if (conn_fd >= 0) { close(conn_fd); conn_fd = -1; }
    }

    void start_recv() {
        running.store(true);
        recv_thread = std::thread([this]() {
            uint8_t hdr[4];
            while (running.load()) {
                /* Read 4-byte length header */
                if (!read_exact(hdr, 4)) break;
                uint32_t len = ((uint32_t)hdr[0] << 24) | ((uint32_t)hdr[1] << 16) |
                               ((uint32_t)hdr[2] << 8)  | (uint32_t)hdr[3];
                if (len > 16 * 1024 * 1024) break; /* sanity */

                std::vector<uint8_t> buf(len);
                if (!read_exact(buf.data(), len)) break;

                if (recv_cb)
                    recv_cb(recv_ud, peer_fingerprint, buf.data(), buf.size());
            }
        });
    }

    bool read_exact(uint8_t *buf, size_t len) {
        size_t got = 0;
        while (got < len && running.load()) {
            ssize_t n = ::recv(conn_fd, buf + got, len - got, 0);
            if (n <= 0) return false;
            got += (size_t)n;
        }
        return got == len;
    }

    void send_msg(const uint8_t *data, size_t len) {
        std::lock_guard<std::mutex> lock(send_mu);
        if (conn_fd < 0) return;
        uint8_t hdr[4] = {
            (uint8_t)(len >> 24), (uint8_t)(len >> 16),
            (uint8_t)(len >> 8),  (uint8_t)len
        };
        ::send(conn_fd, hdr, 4, MSG_NOSIGNAL);
        ::send(conn_fd, data, len, MSG_NOSIGNAL);
    }
};

/* C-style function pointers for KomeTransport */
static void tcp_send(KomeTransport *t, const uint8_t * /*peer_fp*/,
                     const uint8_t *data, size_t len) {
    auto *node = static_cast<TcpTestNode*>(t->user_data);
    node->send_msg(data, len);
}

static void tcp_set_recv(KomeTransport *t,
    void (*cb)(void *ud, const uint8_t *peer_fp, const uint8_t *data, size_t len),
    void *ud) {
    auto *node = static_cast<TcpTestNode*>(t->user_data);
    node->recv_cb = cb;
    node->recv_ud = ud;
}

static void tcp_set_peer(KomeTransport *t,
    void (*cb)(void *ud, const uint8_t *peer_fp, int connected),
    void *ud) {
    auto *node = static_cast<TcpTestNode*>(t->user_data);
    node->peer_cb = cb;
    node->peer_ud = ud;
}

/**
 * @brief Connect two TcpTestNode instances via localhost TCP.
 *
 * `server` listens on an ephemeral port, `client` connects.
 * Both start background recv threads. Returns the port used.
 */
inline int tcp_connect_pair(TcpTestNode &server, TcpTestNode &client) {
    /* Set up transport function pointers */
    auto setup = [](TcpTestNode &n) {
        n.transport.send = tcp_send;
        n.transport.set_recv_callback = tcp_set_recv;
        n.transport.set_peer_callback = tcp_set_peer;
        n.transport.user_data = &n;
    };
    setup(server);
    setup(client);

    /* Server: listen on ephemeral port */
    int listen_fd = socket(AF_INET, SOCK_STREAM, 0);
    int opt = 1;
    setsockopt(listen_fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));

    struct sockaddr_in addr = {};
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = 0; /* kernel picks a port */
    bind(listen_fd, (struct sockaddr*)&addr, sizeof(addr));
    listen(listen_fd, 1);

    /* Get assigned port */
    socklen_t alen = sizeof(addr);
    getsockname(listen_fd, (struct sockaddr*)&addr, &alen);
    int port = ntohs(addr.sin_port);

    /* Client: connect */
    int cli_fd = socket(AF_INET, SOCK_STREAM, 0);
    struct sockaddr_in srv_addr = {};
    srv_addr.sin_family = AF_INET;
    srv_addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    srv_addr.sin_port = htons(port);
    connect(cli_fd, (struct sockaddr*)&srv_addr, sizeof(srv_addr));

    /* Server: accept */
    int srv_fd = accept(listen_fd, nullptr, nullptr);
    close(listen_fd);

    /* Wire up */
    server.conn_fd = srv_fd;
    client.conn_fd = cli_fd;
    std::memcpy(server.peer_fingerprint, client.fingerprint, 32);
    std::memcpy(client.peer_fingerprint, server.fingerprint, 32);

    /* Start recv threads */
    server.start_recv();
    client.start_recv();

    return port;
}

/**
 * @brief Fire peer-connected callbacks on both sides.
 *
 * Call this AFTER kome_attach_transport() on both engines,
 * so the sync manager's callbacks are registered.
 */
inline void tcp_fire_connected(TcpTestNode &a, TcpTestNode &b) {
    if (a.peer_cb) a.peer_cb(a.peer_ud, b.fingerprint, 1);
    if (b.peer_cb) b.peer_cb(b.peer_ud, a.fingerprint, 1);
}

#endif /* TCP_TEST_TRANSPORT_HPP */
