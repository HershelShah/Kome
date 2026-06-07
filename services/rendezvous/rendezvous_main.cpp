/* rendezvous_main.cpp — standalone rendezvous daemon (M5).
 *
 *   rendezvousd --listen 9002
 *
 * Brokers peer endpoints (pubkey -> reflexive address); never sees plaintext. */
#include <cstdio>
#include <cstdlib>
#include <string>

#include "transport/rendezvous.h"
#include "transport/udp.h"

int main(int argc, char **argv) {
    int port = 9002;
    for (int i = 1; i < argc; i++)
        if (std::string(argv[i]) == "--listen" && i + 1 < argc)
            port = atoi(argv[++i]);

    ke::UdpSocket sock;
    if (!sock.open("0.0.0.0", (uint16_t)port)) {
        fprintf(stderr, "rendezvousd: bind %d failed\n", port);
        return 1;
    }
    printf("rendezvousd: listening on udp/%d (endpoint broker)\n",
           sock.local().port);
    fflush(stdout);

    ke::Rendezvous rdv;
    for (;;) rendezvous_server_step(rdv, sock, 1000);
    return 0;
}
