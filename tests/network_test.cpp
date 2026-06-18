/* network_test.cpp — M5 acceptance tests that run in-container.
 *
 *   T5.1 LAN direct  — two engines converge over real localhost UDP.
 *   T5.8 Reliability — convergence over a lossy/reordering/duplicating link.
 *
 * STUN (T5.2), relay store-and-forward / blindness (T5.5, T5.7) and the NAT
 * simulator (T5.4) are in relay_test.cpp. IPv6 preference (T5.9) and kernel
 * NAT hole-punching (T5.3) need an environment this sandbox lacks (no IPv6
 * bind, no ip/iptables) — see DECISIONS.md. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <unistd.h>

#include <array>
#include <chrono>
#include <cstring>
#include <random>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "sync_drive.hpp"
#include "transport/reliable.h"
#include "transport/stun.h"
#include "transport/udp.h"

namespace {

using synctest::Medium;
using synctest::converge;

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
using cluster::B;

std::array<uint8_t, SYNC_SEED_LEN> seed_from(uint8_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (auto &b : s) b = v;
    return s;
}

Digest digest(sync_engine *e) {
    Digest d{};
    EXPECT_EQ(sync_engine_digest(e, d.data()), SYNC_OK);
    return d;
}

void populate(sync_engine *e, std::mt19937 &rng, int n) {
    for (int i = 0; i < n; i++) {
        std::string ent = "e" + std::to_string(i);
        std::string val = "v" + std::to_string(rng() % 1000);
        sync_engine_set(e, B(std::string("ns")), 2, B(ent), ent.size(),
                        B(std::string("f")), 1, B(val), val.size());
    }
}

int exists(sync_engine *e, const std::string &ns, const std::string &ent) {
    int p = 0;
    sync_engine_exists(e, B(ns), ns.size(), B(ent), ent.size(), &p);
    return p;
}

Digest baseline_union(sync_engine *a, sync_engine *b) {
    sync_engine *u = sync_engine_create(seed_from(0xEE).data());
    for (sync_engine *e : {a, b}) {
        sync_change *recs = nullptr; size_t n = 0;
        sync_engine_export(e, &recs, &n);
        for (size_t i = 0; i < n; i++) sync_engine_apply(u, &recs[i]);
        sync_changes_free(recs, n);
    }
    Digest d = digest(u);
    sync_engine_destroy(u);
    return d;
}

/* In-process medium that drops, duplicates, and reorders datagrams. */
struct LossySim : Medium {
    std::mt19937 rng{12345};
    std::vector<std::string> q[2]; /* q[0] -> deliverable to A, q[1] -> to B */
    void send(int from, const std::string &dg) override {
        int to = 1 - from;
        if (rng() % 100 < 20) return;            /* 20% drop */
        q[to].push_back(dg);
        if (rng() % 6 == 0) q[to].push_back(dg); /* duplicate */
    }
    bool recv(int to, std::string &dg) override {
        if (q[to].empty()) return false;
        size_t i = rng() % q[to].size();         /* deliver out of order */
        dg = q[to][i];
        q[to].erase(q[to].begin() + i);
        return true;
    }
};

/* Real localhost UDP medium. */
struct UdpMedium : Medium {
    ke::UdpSocket *sock[2];
    ke::Endpoint   ep[2];
    void send(int from, const std::string &dg) override {
        sock[from]->send_to(ep[1 - from], dg);
    }
    bool recv(int to, std::string &dg) override {
        ke::Endpoint f;
        return sock[to]->recv(dg, f, 0);
    }
};


} // namespace

/* ---- T5.1 LAN direct (real localhost UDP) ------------------------------ */
TEST(Network, LanDirectUdp) {
    auto sa = seed_from(0x51), sb = seed_from(0x52);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    std::mt19937 ra(1), rb(2);
    populate(a, ra, 30);
    populate(b, rb, 30);
    Digest oracle = baseline_union(a, b);

    ke::UdpSocket sca, scb;
    ASSERT_TRUE(sca.open("127.0.0.1", 0));
    ASSERT_TRUE(scb.open("127.0.0.1", 0));
    UdpMedium m;
    m.sock[0] = &sca; m.sock[1] = &scb;
    m.ep[0] = sca.local(); m.ep[1] = scb.local();

    ASSERT_TRUE(converge(a, b, m, /*virtual_clock=*/false, /*max_iters=*/20000));
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(digest(a), oracle);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T5.2 STUN binding (against a local test STUN server) -------------- */
TEST(Network, StunBinding) {
    ke::UdpSocket server, client;
    ASSERT_TRUE(server.open("127.0.0.1", 0));
    ASSERT_TRUE(client.open("127.0.0.1", 0));

    uint8_t txid[12];
    std::string req;
    ke::stun_build_request(txid, req);
    ASSERT_TRUE(client.send_to(server.local(), req));

    /* Server: reflect the observed sender endpoint. */
    std::string in;
    ke::Endpoint from;
    ASSERT_TRUE(server.recv(in, from, 1000));
    uint8_t stxid[12];
    ASSERT_TRUE(ke::stun_parse_request(in, stxid));
    std::string resp;
    ke::stun_build_response(stxid, from, resp);
    ASSERT_TRUE(server.send_to(from, resp));

    /* Client learns its reflexive endpoint. */
    std::string rin;
    ke::Endpoint rf;
    ASSERT_TRUE(client.recv(rin, rf, 1000));
    ke::Endpoint mapped;
    ASSERT_TRUE(ke::stun_parse_response(rin, txid, mapped));
    EXPECT_EQ(mapped.ip, std::string("127.0.0.1"));
    EXPECT_EQ(mapped.port, client.local().port);
}

/* ---- T5.6 Reconnection after a network change -------------------------- */
TEST(Network, ReconnectionResumesSync) {
    auto sa = seed_from(0x55), sb = seed_from(0x56);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    std::mt19937 ra(5), rb(6);
    populate(a, ra, 20);
    populate(b, rb, 20);

    /* Initial connection over UDP. */
    ke::UdpSocket sca, scb;
    ASSERT_TRUE(sca.open("127.0.0.1", 0));
    ASSERT_TRUE(scb.open("127.0.0.1", 0));
    {
        UdpMedium m;
        m.sock[0] = &sca; m.sock[1] = &scb;
        m.ep[0] = sca.local(); m.ep[1] = scb.local();
        ASSERT_TRUE(converge(a, b, m, false, 20000));
    }
    EXPECT_EQ(digest(a), digest(b));

    /* Simulate a network change on A: its socket gets a new local endpoint. */
    sca.close();
    ke::UdpSocket sca2;
    ASSERT_TRUE(sca2.open("127.0.0.1", 0));

    /* New offline writes while disconnected. */
    for (int i = 0; i < 10; i++) {
        std::string ent = "post-" + std::to_string(i);
        sync_engine_set(a, B(std::string("ns")), 2, B(ent), ent.size(),
                        B(std::string("f")), 1, B(std::string("new")), 3);
    }
    Digest oracle = baseline_union(a, b);

    /* Re-establish over the new endpoint and resume sync. */
    {
        UdpMedium m;
        m.sock[0] = &sca2; m.sock[1] = &scb;
        m.ep[0] = sca2.local(); m.ep[1] = scb.local();
        ASSERT_TRUE(converge(a, b, m, false, 20000));
    }
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(digest(a), oracle);
    EXPECT_EQ(exists(a, "ns", "post-3"), 1);
    EXPECT_EQ(exists(b, "ns", "post-3"), 1);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T5.8 Reliability layer (lossy datagram link) ---------------------- */
TEST(Network, ReliabilityOverLossyLink) {
    auto sa = seed_from(0x53), sb = seed_from(0x54);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    std::mt19937 ra(3), rb(4);
    populate(a, ra, 25);
    populate(b, rb, 25);
    Digest oracle = baseline_union(a, b);

    LossySim m;
    ASSERT_TRUE(converge(a, b, m, /*virtual_clock=*/true, /*max_iters=*/200000));
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(digest(a), oracle);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- S6c: reliability-layer authentication ------------------------------ */
/* Once keyed (post-handshake), an authenticated frame is delivered, but a
 * forged/unauthenticated frame at the live sequence — the seq/ack-desync
 * attack — is rejected. */
TEST(Reliable, MacRejectsForgedFrameOnceKeyed) {
    uint8_t key[32];
    for (int i = 0; i < 32; i++) key[i] = (uint8_t)i;

    ke::ReliableLink a, b;
    a.enable_mac(key);
    b.enable_mac(key);

    a.send("hello");
    std::vector<std::string> dgs;
    a.poll(dgs, 0);
    ASSERT_FALSE(dgs.empty());
    std::string data = dgs.back(); /* authenticated DATA frame */

    std::vector<std::string> del;
    EXPECT_TRUE(b.on_datagram(data, del)); /* authentic -> delivered */
    ASSERT_EQ(del.size(), 1u);
    EXPECT_EQ(del[0], "hello");

    /* Forged plain DATA at the live seq (flag=0,type=0,seq=0,payload). */
    ke::ReliableLink victim;
    victim.enable_mac(key);
    std::string forged(6, '\0');
    forged += "evil";
    std::vector<std::string> d2;
    EXPECT_FALSE(victim.on_datagram(forged, d2)) << "forged plain frame accepted";
    EXPECT_TRUE(d2.empty());

    /* A frame with a corrupted MAC is rejected. */
    std::string tampered = data;
    tampered[tampered.size() - 1] ^= 0x01;
    ke::ReliableLink v2;
    v2.enable_mac(key);
    std::vector<std::string> d3;
    EXPECT_FALSE(v2.on_datagram(tampered, d3)) << "bad-MAC frame accepted";
    EXPECT_TRUE(d3.empty());
}

/* Helper: assemble a reliability frame [auth:1][type:1][seq:u32le][payload]. */
static std::string mk_frame(uint8_t auth, uint8_t type, uint32_t seq,
                            const std::string &payload = "") {
    std::string d;
    d.push_back((char)auth);
    d.push_back((char)type);
    for (int i = 0; i < 4; i++) d.push_back((char)(seq >> (i * 8)));
    d += payload;
    return d;
}

/* F7: once keyed, an unauthenticated DATA frame at or ahead of the live seq is
 * forgery/noise — it must be dropped WITHOUT eliciting an ACK, so a spoofing
 * injector can't farm one ACK per datagram (amplification). A genuine stale
 * plain duplicate (seq < recv_seq_) is still re-acked so the handshake settles. */
TEST(Reliable, KeyedLinkDoesNotAckUnauthenticatedFutureFrame) {
    uint8_t key[32];
    for (int i = 0; i < 32; i++) key[i] = (uint8_t)(i + 3);

    ke::ReliableLink b;
    b.enable_mac(key);

    /* Forged plain DATA at a FUTURE seq (type=0/kData, seq=7, recv_seq_==0). */
    std::vector<std::string> del;
    EXPECT_FALSE(b.on_datagram(mk_frame(0, 0, 7, "evil"), del));
    EXPECT_TRUE(del.empty());

    /* No ACK may be queued for it (no amplification). */
    std::vector<std::string> out;
    b.poll(out, 0);
    EXPECT_TRUE(out.empty()) << "keyed link acked an unauthenticated future frame";
}

/* F8: a non-advancing DATA arriving before any in-order data (recv_seq_==0) must
 * NOT produce a cumulative ack at all. The old code underflowed recv_seq_-1 to
 * 0xFFFFFFFF (a harmless never-matching sentinel); naively clamping that to 0
 * would instead ack seq 0, which a sender at send_seq_==0 reads as delivery of
 * its first (never-delivered) frame — silent data loss. The fix is to stay
 * silent until something is delivered in order. */
TEST(Reliable, NoAckBeforeAnyInOrderDelivery) {
    ke::ReliableLink b; /* not keyed (settling phase) */
    std::vector<std::string> del;
    /* Plain DATA at a future seq=5 while recv_seq_==0: non-advancing. */
    EXPECT_FALSE(b.on_datagram(mk_frame(0, 0, 5, "x"), del));
    EXPECT_TRUE(del.empty());

    std::vector<std::string> out;
    b.poll(out, 0);
    EXPECT_TRUE(out.empty()) << "acked before any in-order delivery (spurious ack)";

    /* The in-order frame (seq=0) is delivered and now legitimately acked at 0. */
    EXPECT_TRUE(b.on_datagram(mk_frame(0, 0, 0, "hi"), del));
    ASSERT_EQ(del.size(), 1u);
    out.clear();
    b.poll(out, 0);
    ASSERT_FALSE(out.empty());
    const std::string &ack = out.front();
    ASSERT_GE(ack.size(), 6u);
    EXPECT_EQ((uint8_t)ack[1], 1); /* kAck */
    uint32_t ack_seq = (uint8_t)ack[2] | ((uint8_t)ack[3] << 8) |
                       ((uint8_t)ack[4] << 16) | ((uint32_t)(uint8_t)ack[5] << 24);
    EXPECT_EQ(ack_seq, 0u);
}
