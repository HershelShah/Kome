/* relay_main.cpp — standalone blind store-and-forward relay daemon (M5).
 *
 *   relayd --listen 9001
 *
 * Forwards opaque ciphertext blobs by destination pubkey; never decrypts. */
#include <cstdio>
#include <cstdlib>
#include <string>

#include "transport/relay.h"
#include "transport/udp.h"

int main(int argc, char **argv) {
    int port = 9001;
    for (int i = 1; i < argc; i++)
        if (std::string(argv[i]) == "--listen" && i + 1 < argc)
            port = atoi(argv[++i]);

    ke::UdpSocket sock;
    if (!sock.open("0.0.0.0", (uint16_t)port)) {
        fprintf(stderr, "relayd: bind %d failed\n", port);
        return 1;
    }
    printf("relayd: listening on udp/%d (blind store-and-forward)\n",
           sock.local().port);
    fflush(stdout);

    ke::Relay relay;
    for (;;) relay_server_step(relay, sock, 1000);
    return 0;
}
