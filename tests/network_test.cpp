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

#include "transport/reliable.h"
#include "transport/udp.h"

namespace {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

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

uint64_t now_ms() {
    using namespace std::chrono;
    return (uint64_t)duration_cast<milliseconds>(
               steady_clock::now().time_since_epoch())
        .count();
}

/* A datagram medium between endpoint 0 (A) and endpoint 1 (B). */
struct Medium {
    virtual ~Medium() = default;
    virtual void send(int from, const std::string &dg) = 0;
    virtual bool recv(int to, std::string &dg) = 0;
};

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

/* Drive two engines to convergence over a datagram medium using the
 * reliability layer. virtual_clock advances time deterministically (lossy
 * sim); otherwise it uses the real clock with a short sleep (UDP). */
bool converge(sync_engine *a, sync_engine *b, Medium &m, bool virtual_clock,
              int max_iters) {
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    ke::ReliableLink la, lb;

    auto feed = [&](sync_session *s, ke::ReliableLink &l,
                    const std::string &msg) {
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(s, (const uint8_t *)msg.data(), msg.size(), &o, &ol,
                          &d);
        if (ol) l.send(std::string((char *)o, ol));
        if (o) sync_free(o);
    };

    { /* initiator's first message */
        uint8_t *o = nullptr; size_t ol = 0; int d = 0;
        sync_session_step(sa, nullptr, 0, &o, &ol, &d);
        if (ol) la.send(std::string((char *)o, ol));
        if (o) sync_free(o);
    }

    uint64_t now = virtual_clock ? 0 : now_ms();
    int quiet = 0;
    bool ok = false;
    for (int iter = 0; iter < max_iters; iter++) {
        now = virtual_clock ? now + 100 : now_ms();
        bool work = false;

        std::vector<std::string> dgs;
        la.poll(dgs, now);
        for (auto &d : dgs) { m.send(0, d); work = true; }
        dgs.clear();
        lb.poll(dgs, now);
        for (auto &d : dgs) { m.send(1, d); work = true; }

        std::string dg;
        while (m.recv(0, dg)) {
            work = true;
            std::vector<std::string> del;
            la.on_datagram(dg, del);
            for (auto &msg : del) feed(sa, la, msg);
        }
        while (m.recv(1, dg)) {
            work = true;
            std::vector<std::string> del;
            lb.on_datagram(dg, del);
            for (auto &msg : del) feed(sb, lb, msg);
        }

        /* Quiescence: no datagrams moved and both links have nothing pending
         * (no data in flight, no queued sends, no pending acks). */
        if (!work && la.idle() && lb.idle()) {
            if (++quiet > 5) { ok = true; break; }
        } else {
            quiet = 0;
        }
        if (!virtual_clock) usleep(500);
    }
    sync_session_end(sa);
    sync_session_end(sb);
    return ok;
}

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
