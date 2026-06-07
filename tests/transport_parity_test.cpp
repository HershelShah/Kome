/* transport_parity_test.cpp — run the full sync stack (Noise + reliability +
 * reconciliation via connect_and_sync) over BOTH UDP and TCP, with identical
 * scenarios and assertions, to prove every transport-agnostic code path works
 * over TCP with UDP parity. A TCP-only test then exercises large messages that
 * exceed the UDP datagram limit (a documented boundary, not a bug). */
#include "cluster.hpp"

#include <gtest/gtest.h>

#include <atomic>
#include <random>
#include <string>
#include <thread>

#include "transport/connection.h"
#include "transport/tcp.h"
#include "transport/udp.h"

using namespace cluster;

namespace {
/* PeerTransport over a framed TCP stream. */
struct TcpTransport : ke::PeerTransport {
    ke::TcpStream *s = nullptr;
    bool send(const std::string &dg) override { return s->send_frame(dg); }
    bool recv(std::string &dg, int t) override { return s->recv_frame(dg, t); }
};
} // namespace

class TransportParity : public ::testing::TestWithParam<const char *> {
protected:
    /* UDP backing */
    ke::UdpSocket usa, usb;
    ke::DirectTransport uta, utb;
    /* TCP backing */
    ke::TcpListener listener;
    ke::TcpStream tc_client, tc_server;
    TcpTransport tta, ttb;

    ke::PeerTransport *ta = nullptr; /* A's side (initiator) */
    ke::PeerTransport *tb = nullptr; /* B's side (responder) */

    void SetUp() override {
        if (std::string(GetParam()) == "udp") {
            ASSERT_TRUE(usa.open("127.0.0.1", 0));
            ASSERT_TRUE(usb.open("127.0.0.1", 0));
            uta.sock = &usa; uta.peer = usb.local();
            utb.sock = &usb; utb.peer = usa.local();
            ta = &uta; tb = &utb;
        } else {
            ASSERT_TRUE(listener.open("127.0.0.1", 0));
            ASSERT_TRUE(tc_client.connect_to(listener.local()));
            ASSERT_TRUE(listener.accept(tc_server, 1000));
            tta.s = &tc_client; ttb.s = &tc_server;
            ta = &tta; tb = &ttb;
        }
    }

    /* Run a full encrypted reconcile between a and b over the chosen transport. */
    bool sync_over_transport(sync_engine *a, sync_engine *b) {
        std::atomic<bool> ra{false}, rb{false};
        std::thread A([&] { ra = ke::connect_and_sync(a, *ta, true, 10000); });
        std::thread Bt([&] { rb = ke::connect_and_sync(b, *tb, false, 10000); });
        A.join(); Bt.join();
        return ra.load() && rb.load();
    }
};

INSTANTIATE_TEST_SUITE_P(Transports, TransportParity,
                         ::testing::Values("udp", "tcp"),
                         [](const auto &i) { return std::string(i.param); });

/* Independent writes on both sides converge. */
TEST_P(TransportParity, BasicConverge) {
    sync_engine *a = make(1), *b = make(2);
    std::mt19937 ra(10), rb(20);
    for (int i = 0; i < 30; i++) {
        put(a, "ns", "a" + std::to_string(i), "f", "v" + std::to_string(ra() % 99));
        put(b, "ns", "b" + std::to_string(i), "f", "v" + std::to_string(rb() % 99));
    }
    ASSERT_TRUE(sync_over_transport(a, b));
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(record_count(a), 60);
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* Same-cell conflict resolves to one deterministic winner on both sides. */
TEST_P(TransportParity, Conflict) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "ns", "cell", "f", "from-A");
    put(b, "ns", "cell", "f", "from-B");
    ASSERT_TRUE(sync_over_transport(a, b));
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(get(a, "ns", "cell", "f"), get(b, "ns", "cell", "f"));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* Delete dominates a concurrent edit (causal-length set) across the transport. */
TEST_P(TransportParity, DeleteVsEdit) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "ns", "e", "f1", "init");
    replicate(a, b);              /* shared base (in-process) */
    del(a, "ns", "e");
    put(b, "ns", "e", "f2", "edit");
    ASSERT_TRUE(sync_over_transport(a, b));
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_FALSE(exists(a, "ns", "e"));
    EXPECT_FALSE(exists(b, "ns", "e"));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* Binary value with embedded NULs round-trips over the transport. */
TEST_P(TransportParity, BinaryValue) {
    sync_engine *a = make(1), *b = make(2);
    std::string bin = std::string("a\0b\0c", 5) + std::string(2000, '\xab');
    put(a, "ns", "bin", "f", bin);
    ASSERT_TRUE(sync_over_transport(a, b));
    EXPECT_EQ(get(b, "ns", "bin", "f"), bin);
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* Moderate dataset (UDP-datagram-safe) converges to the union. */
TEST_P(TransportParity, ManyEntities) {
    sync_engine *a = make(1), *b = make(2);
    for (int i = 0; i < 100; i++) {
        put(a, "ns", "a" + std::to_string(i), "f", "x");
        put(b, "ns", "b" + std::to_string(i), "f", "y");
    }
    ASSERT_TRUE(sync_over_transport(a, b));
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(record_count(a), 200);
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* One empty side bootstraps fully from the other. */
TEST_P(TransportParity, EmptyVsFull) {
    sync_engine *a = make(1), *b = make(2);
    for (int i = 0; i < 60; i++) put(a, "ns", "e" + std::to_string(i), "f", "v");
    ASSERT_TRUE(sync_over_transport(a, b));
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(record_count(b), 60);
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ---- TCP-only: messages larger than a UDP datagram --------------------- *
 * The UDP transport sends each reconcile message as one datagram, so it is
 * bounded by the ~64 KB UDP limit; TCP's framed stream is not. This exercises
 * a 256 KB value and a large empty-vs-full batch that UDP could not carry. */
TEST(TransportTcp, LargeMessages) {
    ke::TcpListener listener;
    ASSERT_TRUE(listener.open("127.0.0.1", 0));
    ke::TcpStream client, server;
    ASSERT_TRUE(client.connect_to(listener.local()));
    ASSERT_TRUE(listener.accept(server, 1000));
    TcpTransport ta; ta.s = &client;
    TcpTransport tb; tb.s = &server;

    sync_engine *a = make(1), *b = make(2);
    std::string big(256 * 1024, 'Z');
    big[100000] = '\0';
    put(a, "ns", "huge", "f", big);
    for (int i = 0; i < 1500; i++) put(a, "ns", "e" + std::to_string(i), "f", "x");

    std::atomic<bool> ra{false}, rb{false};
    std::thread A([&] { ra = ke::connect_and_sync(a, ta, true, 15000); });
    std::thread Bt([&] { rb = ke::connect_and_sync(b, tb, false, 15000); });
    A.join(); Bt.join();

    EXPECT_TRUE(ra.load());
    EXPECT_TRUE(rb.load());
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(get(b, "ns", "huge", "f"), big); /* 256 KB value intact */
    EXPECT_EQ(record_count(b), 1501);
    sync_engine_destroy(a); sync_engine_destroy(b);
}
