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
    uint8_t pkA[32], pkB[32];
    fill(pkA, 0xAA);
    fill(pkB, 0xBB);

    ASSERT_TRUE(rendezvous_register(a, sep, pkA, 500));
    ASSERT_TRUE(rendezvous_register(b, sep, pkB, 500));

    /* A looks up B and learns the reflexive endpoint the server observed. */
    Endpoint outB;
    ASSERT_TRUE(rendezvous_lookup(a, sep, pkB, outB, 500));
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
