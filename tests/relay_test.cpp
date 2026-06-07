/* relay_test.cpp — M5 relay + NAT-traversal acceptance tests.
 *
 *   T5.3 Cone-NAT punch       — two full-cone NATs hole-punch and converge.
 *   T5.4 Symmetric-NAT relay  — symmetric NATs fail to punch, fall back to
 *                               relay, and still converge.
 *   T5.5 Store-and-forward    — A sends while B is offline; B later fetches.
 *   T5.7 Relay blindness      — the relay carries only ciphertext.
 *
 * NAT behaviour is modelled by an in-process simulator (the plan permits a NAT
 * simulator in place of Linux netns, which this sandbox lacks). */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <map>
#include <random>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "engine.hpp"
#include "noise.h"
#include "sync_drive.hpp"
#include "transport/relay.h"

using synctest::Medium;
using synctest::converge;

namespace {

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
bool handshake(ke::NoiseChannel &ci, ke::NoiseChannel &cr) {
    std::string msg, out;
    bool d = false;
    if (!ci.step("", out, d)) return false;
    msg = out;
    if (!cr.step(msg, out, d)) return false;
    msg = out;
    if (!ci.step(msg, out, d)) return false;
    msg = out;
    if (!cr.step(msg, out, d)) return false;
    return ci.done() && cr.done();
}

/* ---- userspace NAT simulator ------------------------------------------- */
enum Nat { CONE, SYM };

struct SimNet {
    Nat nat[2];
    std::string stun = "STUN";
    struct Map { int owner; std::string allowed; bool cone; };
    std::map<std::string, Map> reg;
    std::vector<std::pair<std::string, std::string>> inbox[2];

    std::string srcmap(int h, const std::string &dst) {
        if (nat[h] == CONE) return "H" + std::to_string(h);
        return "H" + std::to_string(h) + ">" + dst;
    }
    void ensure_map(int h, const std::string &dst) {
        std::string s = srcmap(h, dst);
        Map m;
        m.owner = h;
        m.cone = (nat[h] == CONE);
        m.allowed = m.cone ? "" : dst;
        reg[s] = m;
    }
    /* Reflexive endpoint as learned via STUN. */
    std::string reflexive(int h) {
        ensure_map(h, stun);
        return srcmap(h, stun);
    }
    void send(int h, const std::string &dst, const std::string &payload) {
        ensure_map(h, dst);
        std::string src = srcmap(h, dst);
        auto it = reg.find(dst);
        if (it == reg.end()) return;
        const Map &dm = it->second;
        if (!(dm.cone || dm.allowed == src)) return; /* NAT filters it */
        inbox[dm.owner].push_back({src, payload});
    }
    bool recv(int h, std::string &payload) {
        if (inbox[h].empty()) return false;
        payload = inbox[h].front().second;
        inbox[h].erase(inbox[h].begin());
        return true;
    }
};

/* Medium that routes datagrams through the NAT simulator (direct path). */
struct SimMedium : Medium {
    SimNet *net;
    std::string peer_ep[2]; /* endpoint each side sends to */
    void send(int from, const std::string &dg) override {
        net->send(from, peer_ep[from], dg);
    }
    bool recv(int to, std::string &dg) override { return net->recv(to, dg); }
};

/* Medium that routes datagrams through the relay, addressed by pubkey. */
struct RelayMedium : Medium {
    ke::Relay *relay;
    std::array<uint8_t, 32> pub[2];
    std::vector<std::string> buf[2];
    void send(int from, const std::string &dg) override {
        relay->send(pub[1 - from].data(), dg); /* to the peer */
    }
    bool recv(int to, std::string &dg) override {
        if (buf[to].empty()) relay->fetch(pub[to].data(), buf[to]);
        if (buf[to].empty()) return false;
        dg = buf[to].front();
        buf[to].erase(buf[to].begin());
        return true;
    }
};

/* Try to hole-punch: both sides probe the other's reflexive endpoint. Returns
 * true if probes are delivered both ways (a usable direct path). */
bool try_punch(SimNet &net, const std::string &ra, const std::string &rb) {
    for (int i = 0; i < 4; i++) {
        net.send(0, rb, "probe-a");
        net.send(1, ra, "probe-b");
    }
    std::string p;
    bool a_reachable = net.recv(0, p); /* B's probe reached A */
    bool b_reachable = net.recv(1, p); /* A's probe reached B */
    /* drain */
    while (net.recv(0, p)) {}
    while (net.recv(1, p)) {}
    return a_reachable && b_reachable;
}

} // namespace

/* ---- T5.3 Cone-NAT hole punching --------------------------------------- */
TEST(Relay, ConeNatPunch) {
    auto sa = seed_from(0x61), sb = seed_from(0x62);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    std::mt19937 ra(1), rb(2);
    populate(a, ra, 20);
    populate(b, rb, 20);

    SimNet net;
    net.nat[0] = CONE;
    net.nat[1] = CONE;
    std::string ea = net.reflexive(0), eb = net.reflexive(1);

    ASSERT_TRUE(try_punch(net, ea, eb)) << "full-cone punch should succeed";

    SimMedium m;
    m.net = &net;
    m.peer_ep[0] = eb;
    m.peer_ep[1] = ea;
    ASSERT_TRUE(converge(a, b, m, /*virtual_clock=*/true, 100000));
    EXPECT_EQ(digest(a), digest(b));

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T5.4 Symmetric-NAT relay fallback --------------------------------- */
TEST(Relay, SymmetricNatRelayFallback) {
    auto sa = seed_from(0x63), sb = seed_from(0x64);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    std::mt19937 ra(3), rb(4);
    populate(a, ra, 20);
    populate(b, rb, 20);

    SimNet net;
    net.nat[0] = SYM;
    net.nat[1] = SYM;
    std::string ea = net.reflexive(0), eb = net.reflexive(1);

    ASSERT_FALSE(try_punch(net, ea, eb)) << "symmetric punch must fail";

    /* Fall back to the relay. */
    ke::Relay relay;
    RelayMedium m;
    m.relay = &relay;
    sync_engine_identity(a, m.pub[0].data());
    sync_engine_identity(b, m.pub[1].data());
    ASSERT_TRUE(converge(a, b, m, /*virtual_clock=*/true, 100000));
    EXPECT_EQ(digest(a), digest(b));

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T5.5 Store-and-forward -------------------------------------------- */
TEST(Relay, StoreAndForward) {
    auto sa = seed_from(0x65), sb = seed_from(0x66);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    std::mt19937 ra(5);
    populate(a, ra, 15);

    /* Both online briefly to establish the encrypted channel. */
    ke::NoiseChannel ci(true, a->identity);
    ke::NoiseChannel cr(false, b->identity);
    ASSERT_TRUE(handshake(ci, cr));

    ke::Relay relay;
    uint8_t bpub[SYNC_PUBKEY_LEN];
    sync_engine_identity(b, bpub);

    /* B is offline: A pushes each record as an encrypted blob to the relay. */
    sync_change *recs = nullptr;
    size_t n = 0;
    sync_engine_export(a, &recs, &n);
    for (size_t i = 0; i < n; i++) {
        size_t len = sync_change_encode(&recs[i], nullptr, 0);
        std::vector<uint8_t> enc(len);
        sync_change_encode(&recs[i], enc.data(), enc.size());
        std::string blob;
        ASSERT_TRUE(ci.encrypt(std::string((char *)enc.data(), enc.size()), blob));
        relay.send(bpub, blob);
    }
    sync_changes_free(recs, n);
    EXPECT_EQ(relay.queued(bpub), n);

    /* B comes online later and drains the queue, decrypting in order. */
    std::vector<std::string> blobs;
    relay.fetch(bpub, blobs);
    EXPECT_EQ(blobs.size(), n);
    for (auto &blob : blobs) {
        std::string pt;
        ASSERT_TRUE(cr.decrypt(blob, pt));
        sync_change out;
        size_t consumed = 0;
        ASSERT_EQ(sync_change_decode((const uint8_t *)pt.data(), pt.size(), &out,
                                     &consumed),
                  SYNC_OK);
        EXPECT_EQ(sync_engine_apply(b, &out), SYNC_OK);
        sync_change_free_decoded(&out);
    }

    /* B now holds A's data. */
    for (int i = 0; i < 15; i++)
        EXPECT_EQ(exists(b, "ns", "e" + std::to_string(i)), 1);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T5.7 Relay blindness ---------------------------------------------- */
TEST(Relay, Blindness) {
    auto sa = seed_from(0x67), sb = seed_from(0x68);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    ke::NoiseChannel ci(true, a->identity);
    ke::NoiseChannel cr(false, b->identity);
    ASSERT_TRUE(handshake(ci, cr));

    std::string secret = "TOP-SECRET-PLAINTEXT-MARKER-0xDEADBEEF";
    std::string blob;
    ASSERT_TRUE(ci.encrypt(secret, blob));

    ke::Relay relay;
    uint8_t bpub[SYNC_PUBKEY_LEN];
    sync_engine_identity(b, bpub);
    relay.send(bpub, blob);

    std::vector<std::string> got;
    relay.fetch(bpub, got);
    ASSERT_EQ(got.size(), 1u);
    /* The relay carries ciphertext: the plaintext marker never appears. */
    EXPECT_EQ(got[0].find(secret), std::string::npos);
    EXPECT_NE(got[0], secret);
    /* Only the intended recipient's channel can recover it. */
    std::string pt;
    ASSERT_TRUE(cr.decrypt(got[0], pt));
    EXPECT_EQ(pt, secret);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}
