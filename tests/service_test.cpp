/* service_test.cpp — loopback tests for the relay + rendezvous UDP services.
 * The server side runs in a background thread; the client protocol is driven
 * over real localhost UDP. (Cross-network behaviour needs a real multi-host
 * environment; this validates the wire protocols and core logic.) */
#include <gtest/gtest.h>

#include <unistd.h>

#include <atomic>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

#include "transport/relay.h"
#include "transport/rendezvous.h"
#include "transport/udp.h"

using namespace ke;

namespace {
void fill(uint8_t pk[32], uint8_t v) { std::memset(pk, v, 32); }
}

/* ---- Relay service: blind store-and-forward over UDP -------------------- */
TEST(Service, RelayLoopback) {
    UdpSocket server;
    ASSERT_TRUE(server.open("127.0.0.1", 0));
    Endpoint sep = server.local();

    Relay relay;
    std::atomic<bool> stop{false};
    std::thread th([&] {
        while (!stop.load()) relay_server_step(relay, server, 50);
    });

    UdpSocket a, b;
    ASSERT_TRUE(a.open("127.0.0.1", 0));
    ASSERT_TRUE(b.open("127.0.0.1", 0));
    uint8_t pkB[32];
    fill(pkB, 0xBB);

    /* A queues two opaque blobs for B while B is "offline". */
    std::string secret = "ciphertext-for-B";
    ASSERT_TRUE(relay_client_send(a, sep, pkB, secret));
    ASSERT_TRUE(relay_client_send(a, sep, pkB, "second-blob"));

    /* B later fetches them (retry to absorb cross-socket UDP races). */
    std::vector<std::string> got;
    for (int i = 0; i < 50 && got.size() < 2; i++) {
        relay_client_fetch(b, sep, pkB, got, 100);
        if (got.size() < 2) usleep(10 * 1000);
    }
    ASSERT_EQ(got.size(), 2u);
    EXPECT_EQ(got[0], secret);
    EXPECT_EQ(got[1], "second-blob");

    stop.store(true);
    th.join();
}

/* ---- Rendezvous service: endpoint broker over UDP ---------------------- */
TEST(Service, RendezvousLoopback) {
    UdpSocket server;
    ASSERT_TRUE(server.open("127.0.0.1", 0));
    Endpoint sep = server.local();

    Rendezvous rdv;
    std::atomic<bool> stop{false};
    std::thread th([&] {
        while (!stop.load()) rendezvous_server_step(rdv, server, 50);
    });

    UdpSocket a, b;
    ASSERT_TRUE(a.open("127.0.0.1", 0));
    ASSERT_TRUE(b.open("127.0.0.1", 0));
    /* Real keypairs: registration now proves key ownership by signing the
     * server's challenge, so the registered key must match the signing key. */
    uint8_t seedA[32], seedB[32];
    fill(seedA, 0x1A);
    fill(seedB, 0x1B);
    KeyPair idA = keypair_from_seed(seedA);
    KeyPair idB = keypair_from_seed(seedB);

    ASSERT_TRUE(rendezvous_register(a, sep, idA, 500));
    ASSERT_TRUE(rendezvous_register(b, sep, idB, 500));

    /* A looks up B and learns the reflexive endpoint the server observed. */
    Endpoint outB;
    ASSERT_TRUE(rendezvous_lookup(a, sep, idB.sign_pk.data(), outB, 500));
    EXPECT_EQ(outB.ip, std::string("127.0.0.1"));
    EXPECT_EQ(outB.port, b.local().port);

    /* Unknown peer is not found. */
    uint8_t pkC[32];
    fill(pkC, 0xCC);
    Endpoint outC;
    EXPECT_FALSE(rendezvous_lookup(a, sep, pkC, outC, 300));

    stop.store(true);
    th.join();
}

/* S6b: registering a key requires proving ownership — an attacker that doesn't
 * hold the key's signing secret cannot bind a victim's key to its endpoint. */
TEST(Service, RendezvousRejectsForgedRegistration) {
    UdpSocket server;
    ASSERT_TRUE(server.open("127.0.0.1", 0));
    Endpoint sep = server.local();
    Rendezvous rdv;
    std::atomic<bool> stop{false};
    std::thread th([&] { while (!stop.load()) rendezvous_server_step(rdv, server, 50); });

    uint8_t seedV[32], seedA[32];
    fill(seedV, 0x2A);
    fill(seedA, 0x2B);
    KeyPair victim = keypair_from_seed(seedV);
    KeyPair attacker = keypair_from_seed(seedA);

    UdpSocket atk;
    ASSERT_TRUE(atk.open("127.0.0.1", 0));

    /* Attacker requests to register the VICTIM's key... */
    std::string reg(1, 'R');
    reg.append((const char *)victim.sign_pk.data(), 32);
    ASSERT_TRUE(atk.send_to(sep, reg));
    std::string dg; Endpoint from;
    ASSERT_TRUE(atk.recv(dg, from, 500));
    ASSERT_EQ(dg[0], 'C'); /* challenge */

    /* ...but signs the nonce with ITS OWN key (it lacks the victim's secret). */
    uint8_t sig[64];
    sign(attacker.sign_sk.data(), dg.data() + 1, 16, sig);
    std::string ra(1, 'U');
    ra.append((const char *)victim.sign_pk.data(), 32);
    ra.append(dg.data() + 1, 16);
    ra.append((const char *)sig, 64);
    ASSERT_TRUE(atk.send_to(sep, ra));

    /* The server must reject it: the victim's key is not bound. */
    Endpoint out;
    EXPECT_FALSE(rendezvous_lookup(atk, sep, victim.sign_pk.data(), out, 400))
        << "forged registration was accepted";

    stop.store(true);
    th.join();
}
