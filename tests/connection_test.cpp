/* connection_test.cpp — connect-and-sync over a direct path and over the
 * relay, plus the connection manager's direct→relay fallback. Encrypted
 * reconcile runs end-to-end over real localhost UDP (server logic in threads).
 * Cross-network/NAT behaviour needs a real multi-host environment. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <atomic>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

#include "cluster.hpp"
#include "engine.hpp"
#include "transport/connection.h"
#include "transport/relay.h"
#include "transport/udp.h"

using namespace ke;

namespace {
using cluster::B;
using cluster::seed_from;
sync_engine *make(uint32_t s) { return sync_engine_create(seed_from(s).data()); }
void put(sync_engine *e, const std::string &ent, const std::string &val) {
    sync_engine_set(e, B(std::string("ns")), 2, B(ent), ent.size(),
                    B(std::string("f")), 1, B(val), val.size());
}
std::array<uint8_t, SYNC_DIGEST_LEN> digest(sync_engine *e) {
    std::array<uint8_t, SYNC_DIGEST_LEN> d{};
    sync_engine_digest(e, d.data());
    return d;
}
} // namespace

/* ---- Direct path ------------------------------------------------------- */
TEST(Connection, DirectPath) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "a1", "x");
    put(b, "b1", "y");

    UdpSocket sa, sb;
    ASSERT_TRUE(sa.open("127.0.0.1", 0));
    ASSERT_TRUE(sb.open("127.0.0.1", 0));
    DirectTransport ta; ta.sock = &sa; ta.peer = sb.local();
    DirectTransport tb; tb.sock = &sb; tb.peer = sa.local();

    std::atomic<bool> ra{false}, rb{false};
    std::thread A([&] { ra = connect_and_sync(a, ta, true, 5000); });
    std::thread Bt([&] { rb = connect_and_sync(b, tb, false, 5000); });
    A.join(); Bt.join();

    EXPECT_TRUE(ra.load());
    EXPECT_TRUE(rb.load());
    EXPECT_EQ(digest(a), digest(b));
    int present = 0;
    sync_engine_exists(a, B(std::string("ns")), 2, B(std::string("b1")), 2, &present);
    EXPECT_EQ(present, 1); /* A learned B's record over the direct path */
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ---- S1: identity-bound channel enforces read scoping ------------------- */
/* A owns namespace "secret"; an authenticated peer with no read delegation must
 * NOT receive it over connect_and_sync, while an open namespace still syncs.
 * Pre-fix the live path used an unscoped session and shipped every namespace. */
TEST(Connection, ReadScopingEnforcedOverTransport) {
    sync_engine *a = make(1), *b = make(2);

    sync_capability *root =
        sync_capability_root(a, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_EQ(sync_engine_grant(a, root), SYNC_OK); /* A owns "secret" */
    sync_capability_free(root);
    ASSERT_EQ(sync_engine_set(a, B(std::string("secret")), 6, B(std::string("s1")),
                              2, B(std::string("f")), 1, B(std::string("v")), 1),
              SYNC_OK);
    ASSERT_EQ(sync_engine_set(a, B(std::string("pub")), 3, B(std::string("p1")), 2,
                              B(std::string("f")), 1, B(std::string("v")), 1),
              SYNC_OK); /* open namespace */

    UdpSocket sa, sb;
    ASSERT_TRUE(sa.open("127.0.0.1", 0));
    ASSERT_TRUE(sb.open("127.0.0.1", 0));
    DirectTransport ta; ta.sock = &sa; ta.peer = sb.local();
    DirectTransport tb; tb.sock = &sb; tb.peer = sa.local();

    std::atomic<bool> ra{false}, rb{false};
    std::thread A([&] { ra = connect_and_sync(a, ta, true, 5000); });
    std::thread Bt([&] { rb = connect_and_sync(b, tb, false, 5000); });
    A.join(); Bt.join();
    EXPECT_TRUE(ra.load());
    EXPECT_TRUE(rb.load());

    int sec = 0, pub = 0;
    sync_engine_exists(b, B(std::string("secret")), 6, B(std::string("s1")), 2, &sec);
    sync_engine_exists(b, B(std::string("pub")), 3, B(std::string("p1")), 2, &pub);
    EXPECT_EQ(sec, 0) << "read-scoping bypassed: peer received a restricted namespace";
    EXPECT_EQ(pub, 1) << "open namespace should have synced";

    sync_engine_destroy(a); sync_engine_destroy(b);
}
TEST(Connection, RelayPath) {
    UdpSocket server;
    ASSERT_TRUE(server.open("127.0.0.1", 0));
    Endpoint sep = server.local();
    Relay relay;
    std::atomic<bool> stop{false};
    std::thread srv([&] { while (!stop.load()) relay_server_step(relay, server, 50); });

    sync_engine *a = make(1), *b = make(2);
    put(a, "a1", "x");
    put(b, "b1", "y");
    uint8_t pka[32], pkb[32];
    sync_engine_identity(a, pka);
    sync_engine_identity(b, pkb);

    UdpSocket sa, sb;
    ASSERT_TRUE(sa.open("127.0.0.1", 0));
    ASSERT_TRUE(sb.open("127.0.0.1", 0));
    RelayTransport ta; ta.sock = &sa; ta.relay = sep;
    std::memcpy(ta.peer_pk.data(), pkb, 32); std::memcpy(ta.my_pk.data(), pka, 32);
    RelayTransport tb; tb.sock = &sb; tb.relay = sep;
    std::memcpy(tb.peer_pk.data(), pka, 32); std::memcpy(tb.my_pk.data(), pkb, 32);

    std::atomic<bool> ra{false}, rb{false};
    std::thread A([&] { ra = connect_and_sync(a, ta, true, 8000); });
    std::thread Bt([&] { rb = connect_and_sync(b, tb, false, 8000); });
    A.join(); Bt.join();

    stop.store(true); srv.join();
    EXPECT_TRUE(ra.load());
    EXPECT_TRUE(rb.load());
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ---- Connection manager: direct fails -> relay fallback ---------------- */
TEST(Connection, ManagerRelayFallback) {
    UdpSocket server;
    ASSERT_TRUE(server.open("127.0.0.1", 0));
    Endpoint sep = server.local();
    Relay relay;
    std::atomic<bool> stop{false};
    std::thread srv([&] { while (!stop.load()) relay_server_step(relay, server, 50); });

    sync_engine *a = make(1), *b = make(2);
    put(a, "a1", "x");
    put(b, "b1", "y");
    uint8_t pka[32], pkb[32];
    sync_engine_identity(a, pka);
    sync_engine_identity(b, pkb);

    UdpSocket sa, sb;
    ASSERT_TRUE(sa.open("127.0.0.1", 0));
    ASSERT_TRUE(sb.open("127.0.0.1", 0));

    ConnectionManager ma; ma.engine = a; ma.sock = &sa; ma.have_relay = true;
    ma.relay = sep; std::memcpy(ma.my_pk.data(), pka, 32);
    ConnectionManager mb; mb.engine = b; mb.sock = &sb; mb.have_relay = true;
    mb.relay = sep; std::memcpy(mb.my_pk.data(), pkb, 32);

    Endpoint bogus{"127.0.0.1", 1}; /* nothing listens here -> direct times out */

    std::atomic<int> resA{-1}, resB{-1};
    std::thread A([&] {
        resA = (int)ma.sync_with(pkb, /*initiator=*/true, &bogus, 700, 8000);
    });
    std::thread Bt([&] {
        resB = (int)mb.sync_with(pka, /*initiator=*/false, nullptr, 0, 8000);
    });
    A.join(); Bt.join();
    stop.store(true); srv.join();

    EXPECT_EQ(resA.load(), (int)ConnResult::Relay) << "A should fall back to relay";
    EXPECT_EQ(resB.load(), (int)ConnResult::Relay);
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}
