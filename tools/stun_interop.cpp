/* stun_interop.cpp — drive the engine's real STUN client against a *public*
 * STUN server over the real internet, and print the reflexive (public) endpoint
 * it learns. This is a genuine M5 interop check: it proves src/transport/stun
 * speaks RFC 5389 well enough to talk to third-party infrastructure, and that
 * UDP egress + reflexive-address discovery work end-to-end — not a loopback sim.
 *
 *   stun_interop [host] [port]      # default stun.l.google.com 19302
 *
 * Exit 0 if a reflexive endpoint was learned, 1 otherwise. */
#include <arpa/inet.h>
#include <netdb.h>

#include <cstdio>
#include <cstring>
#include <string>

#include "transport/stun.h"
#include "transport/udp.h"

using namespace ke;

/* Resolve host:port to a numeric IPv4 string (our UDP layer is AF_INET). */
static bool resolve_v4(const char *host, const char *port, std::string &ip) {
    addrinfo hints{};
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_DGRAM;
    addrinfo *res = nullptr;
    if (getaddrinfo(host, port, &hints, &res) != 0 || !res) return false;
    char buf[INET_ADDRSTRLEN];
    auto *sin = (sockaddr_in *)res->ai_addr;
    inet_ntop(AF_INET, &sin->sin_addr, buf, sizeof buf);
    ip = buf;
    freeaddrinfo(res);
    return true;
}

int main(int argc, char **argv) {
    const char *host = argc > 1 ? argv[1] : "stun.l.google.com";
    const char *port = argc > 2 ? argv[2] : "19302";

    Endpoint server;
    if (!resolve_v4(host, port, server.ip)) {
        fprintf(stderr, "resolve %s failed\n", host);
        return 1;
    }
    server.port = (uint16_t)atoi(port);
    printf("STUN server: %s -> %s:%u\n", host, server.ip.c_str(), server.port);

    UdpSocket sock;
    if (!sock.open("0.0.0.0", 0)) {
        fprintf(stderr, "bind failed\n");
        return 1;
    }
    printf("local socket: udp/%u\n", sock.local().port);

    uint8_t txid[12];
    std::string req;
    stun_build_request(txid, req);

    /* Retry a few times — UDP can drop. */
    for (int attempt = 1; attempt <= 4; attempt++) {
        if (!sock.send_to(server, req)) {
            fprintf(stderr, "send failed\n");
            return 1;
        }
        std::string resp;
        Endpoint from;
        if (sock.recv(resp, from, 2000)) {
            Endpoint mapped;
            if (stun_parse_response(resp, txid, mapped)) {
                printf("reflexive (public) endpoint: %s:%u\n", mapped.ip.c_str(),
                       mapped.port);
                printf("PASS: real STUN interop over the internet (attempt %d, "
                       "%zu-byte response)\n",
                       attempt, resp.size());
                return 0;
            }
            fprintf(stderr, "got %zu bytes but not a parseable binding success\n",
                    resp.size());
        } else {
            fprintf(stderr, "no response (attempt %d), retrying...\n", attempt);
        }
    }
    fprintf(stderr, "FAIL: no STUN binding response (egress blocked or server "
                    "unreachable)\n");
    return 1;
}
