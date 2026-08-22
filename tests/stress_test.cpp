/* stress_test.cpp — opt-in (-DSYNC_STRESS=ON) adversarial / large-scale probes.
 * In-process and deterministic (fixed-seed std::mt19937, no real sockets), so it
 * is reproducible and CI-gateable. Leads with the two scenarios that exercise
 * this branch's changes: the max-access capability fixpoint and the per-peer
 * scoped-snapshot cache under contention/churn. Sizes are modest by default
 * (≈couple minutes total); the kKnob constants below scale heavier runs. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <unistd.h>

#include <algorithm>
#include <array>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <deque>
#include <functional>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "capability.h"
#include "cluster.hpp"
#include "engine.hpp"
#include "tempdir.hpp"
#include "transport/connection.h"

using namespace ke;
using Pk = std::array<uint8_t, SYNC_PUBKEY_LEN>;
using clk = std::chrono::steady_clock;

/* RSS-based leak/footprint assertions are only meaningful without a sanitizer:
 * ASan/TSan deliberately add redzones, quarantine frees, and never return memory
 * to the OS, so RSS balloons regardless of leaks. Detect ASan/TSan (clang via
 * __has_feature, gcc via __SANITIZE_*); the metrics still print, only the
 * assertions are gated. UBSan leaves the allocator alone, so it is not excluded. */
#if defined(__has_feature)
#  if __has_feature(address_sanitizer) || __has_feature(thread_sanitizer)
#    define KOME_SANITIZED 1
#  endif
#endif
#if defined(__SANITIZE_ADDRESS__) || defined(__SANITIZE_THREAD__)
#  define KOME_SANITIZED 1
#endif
#if defined(__linux__) && !defined(KOME_SANITIZED)
#  define KOME_RSS_CHECKS 1
#else
#  define KOME_RSS_CHECKS 0
#endif

namespace {

double ms_since(clk::time_point t) {
    return std::chrono::duration<double, std::milli>(clk::now() - t).count();
}

#ifdef __linux__
size_t rss_kb() {
    FILE *f = std::fopen("/proc/self/statm", "r");
    if (!f) return 0;
    long total = 0, resident = 0;
    if (std::fscanf(f, "%ld %ld", &total, &resident) != 2) resident = 0;
    std::fclose(f);
    return (size_t)resident * ((size_t)sysconf(_SC_PAGESIZE) / 1024);
}
#else
size_t rss_kb() { return 0; }
#endif

/* ---- impairing in-process secure mesh ---------------------------------- */
/* A mesh of SecurePeerSession endpoints over a virtual clock, with a lossy /
 * duplicating / reordering / partitionable channel. Models what the real daemon
 * sees on a bad network, exercising the reliability layer + reconcile end to
 * end. (Modeled on the Mesh in securemesh_test.cpp, with impairment added.) */
struct Endp {
    SecurePeerSession       sps;
    int                     node;
    Endp                   *peer = nullptr;
    int                     peer_node = -1;
    std::deque<std::string> inbox;
    Endp(sync_engine *e, bool initiator, uint32_t iv, int n)
        : sps(e, initiator, iv), node(n) {}
};

struct InFlight { Endp *dst; std::string dg; uint64_t at; };

struct ImpairMesh {
    std::vector<sync_engine *>         eng;
    std::vector<std::unique_ptr<Endp>> ends;
    std::vector<InFlight>              wire;
    uint32_t                           interval;
    uint64_t                           now = 1000;
    std::mt19937                       rng{0xC0FFEE};
    std::uniform_real_distribution<double> U{0.0, 1.0};
    double                             loss = 0.0, dup = 0.0;
    uint32_t                           latency = 5, jitter = 0;
    std::function<bool(int, int)>      linked = [](int, int) { return true; };
    uint64_t                           dgrams = 0, bytes = 0;

    explicit ImpairMesh(uint32_t iv) : interval(iv) {}
    ~ImpairMesh() {
        ends.clear(); /* sessions hold sync_session*; free before engines */
        for (auto *e : eng) sync_engine_destroy(e);
    }

    sync_engine *add(uint32_t seed) { eng.push_back(cluster::make(seed)); return eng.back(); }

    void connect(int i, int j) {
        uint8_t pi[32], pj[32];
        sync_engine_identity(eng[i], pi);
        sync_engine_identity(eng[j], pj);
        bool i_init = std::memcmp(pi, pj, 32) < 0;
        auto a = std::make_unique<Endp>(eng[i], i_init, interval, i);
        auto b = std::make_unique<Endp>(eng[j], !i_init, interval, j);
        a->peer = b.get(); a->peer_node = j;
        b->peer = a.get(); b->peer_node = i;
        ends.push_back(std::move(a)); ends.push_back(std::move(b));
    }
    void ring() { int n = (int)eng.size(); for (int i = 0; i < n; i++) connect(i, (i + 1) % n); }
    void full() { int n = (int)eng.size(); for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) connect(i, j); }

    void emit(Endp *e, std::vector<std::string> &out) {
        for (auto &dg : out) {
            dgrams++; bytes += dg.size();
            if (!linked(e->node, e->peer_node)) continue; /* partitioned */
            if (U(rng) < loss) continue;                  /* dropped */
            uint64_t at = now + latency + (jitter ? rng() % jitter : 0);
            wire.push_back({e->peer, dg, at});
            if (U(rng) < dup)
                wire.push_back({e->peer, dg, at + (jitter ? rng() % jitter : 0)});
        }
        out.clear();
    }
    void start() {
        std::vector<std::string> out;
        for (auto &e : ends) { e->sps.start(now, out); emit(e.get(), out); }
    }
    /* Model a clean restart of every node: fresh sessions and fresh sockets, so
     * no stale in-flight datagram from the previous channel is delivered to the
     * new handshake (which would be rejected as garbage). */
    void restart_all() {
        wire.clear();
        std::vector<std::string> out;
        for (auto &e : ends) {
            e->inbox.clear();
            e->sps.reset(now, out);
            emit(e.get(), out);
        }
    }
    void deliver_matured() {
        std::vector<InFlight> keep;
        keep.reserve(wire.size());
        for (auto &m : wire) {
            if (m.at <= now) m.dst->inbox.push_back(std::move(m.dg));
            else keep.push_back(std::move(m));
        }
        wire.swap(keep);
    }
    void round() {
        now += 40;
        std::vector<std::string> out;
        for (auto &e : ends) { e->sps.poll(now, out); emit(e.get(), out); }
        deliver_matured();
        for (auto &e : ends) {
            std::deque<std::string> local;
            local.swap(e->inbox);
            for (auto &dg : local) { e->sps.on_datagram(dg, now, out); emit(e.get(), out); }
        }
    }
    bool converge(int cap) {
        for (int r = 0; r < cap; r++) { round(); if (cluster::all_converged(eng)) return true; }
        return cluster::all_converged(eng);
    }
};

/* Build a depth-`d` R|W delegation chain (owner -> e1 -> ... -> ed) and grant the
 * whole chain into `enforcer`. Returns the deepest subject's public key. */
Pk build_chain(sync_engine *enforcer, uint32_t base, int d, const char *ns) {
    std::vector<sync_engine *> es;
    for (int i = 0; i <= d; i++) es.push_back(cluster::make(base + (uint32_t)i));
    std::vector<Pk> pk(d + 1);
    for (int i = 0; i <= d; i++) sync_engine_identity(es[i], pk[i].data());

    std::vector<sync_capability *> caps;
    sync_capability *parent =
        sync_capability_root(es[0], ns, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_engine_grant(enforcer, parent);
    caps.push_back(parent);
    for (int i = 0; i < d; i++) {
        sync_capability *c = sync_capability_delegate(
            es[i], parent, pk[i + 1].data(), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);
        sync_engine_grant(enforcer, c);
        caps.push_back(c);
        parent = c;
    }
    for (auto *c : caps) sync_capability_free(c);
    for (auto *e : es) sync_engine_destroy(e);
    return pk[d];
}

double time_authorize(sync_engine *e, const Pk &pk, const char *ns, int iters) {
    auto s = clk::now();
    volatile int acc = 0;
    for (int i = 0; i < iters; i++) acc += cap_authorize_write(e, pk.data(), ns);
    (void)acc;
    return ms_since(s) / iters;
}

/* A collision-free, time-sortable message id. */
std::string smid(uint64_t t, int who, int seq) {
    char b[64];
    std::snprintf(b, sizeof b, "%013llu-u%d-%05d", (unsigned long long)t, who, seq);
    return b;
}
/* Present message ids in `ns`, sorted (= chronological for time-sortable ids). */
std::vector<std::string> present_ids(sync_engine *e, const std::string &ns) {
    std::vector<std::string> out;
    sync_change *r = nullptr; size_t n = 0;
    sync_engine_export(e, &r, &n);
    for (size_t i = 0; i < n; i++) {
        if (r[i].kind != SYNC_CHANGE_EXISTENCE || r[i].causal_length != 1) continue;
        std::string rns((const char *)r[i].ns, r[i].ns_len);
        if (rns == ns) out.emplace_back((const char *)r[i].entity, r[i].entity_len);
    }
    sync_changes_free(r, n);
    std::sort(out.begin(), out.end());
    return out;
}

} // namespace

/* ============================ scenarios ================================== */

/* #1 — the max-access fixpoint stays correct and ~linear on deep / wide / cyclic
 * delegation graphs near the ingest bound. */
TEST(Stress, CapabilityGraphScales) {
    {   /* linearity: time per authorize at depth D vs 2D */
        sync_engine *v1 = cluster::make(1'000'000);
        sync_engine *v2 = cluster::make(2'000'000);
        Pk leaf1 = build_chain(v1, 10'000, 400, "ns");
        Pk leaf2 = build_chain(v2, 20'000, 800, "ns");
        double t400 = time_authorize(v1, leaf1, "ns", 2000);
        double t800 = time_authorize(v2, leaf2, "ns", 2000);
        std::printf("  authorize: depth400=%.4f ms  depth800=%.4f ms\n", t400, t800);
        EXPECT_EQ(cap_authorize_write(v1, leaf1.data(), "ns"), SYNC_OK);
        EXPECT_EQ(cap_authorize_write(v2, leaf2.data(), "ns"), SYNC_OK);
        EXPECT_LT(t800, 4.0 * t400 + 0.05) << "authorization is super-linear in chain depth";
        sync_engine_destroy(v1); sync_engine_destroy(v2);
    }
    {   /* deep chain near the bound completes and is correct */
        sync_engine *v = cluster::make(3'000'000);
        Pk leaf = build_chain(v, 30'000, 2000, "ns");
        auto s = clk::now();
        EXPECT_EQ(cap_authorize_write(v, leaf.data(), "ns"), SYNC_OK);
        double ms = ms_since(s);
        std::printf("  depth-2000 authorize: %.4f ms\n", ms);
        EXPECT_LT(ms, 50.0) << "deep-chain authorize too slow";
        sync_engine_destroy(v);
    }
    {   /* wide star: owner delegates directly to many subjects */
        const int N = 1000;
        sync_engine *owner = cluster::make(4'000'000);
        sync_engine *v = cluster::make(4'000'001);
        sync_capability *root =
            sync_capability_root(owner, "ns", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        sync_engine_grant(v, root);
        std::mt19937 rng{7};
        Pk probe{};
        for (int i = 0; i < N; i++) {
            Pk sub{}; for (auto &b : sub) b = (uint8_t)rng();
            sync_capability *c = sync_capability_delegate(
                owner, root, sub.data(), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);
            sync_engine_grant(v, c); sync_capability_free(c);
            if (i == N / 2) probe = sub;
        }
        EXPECT_EQ(cap_authorize_write(v, probe.data(), "ns"), SYNC_OK);
        sync_capability_free(root);
        sync_engine_destroy(owner); sync_engine_destroy(v);
    }
    {   /* cycle: e0 -> e1 -> e0 must terminate */
        sync_engine *e0 = cluster::make(5'000'000), *e1 = cluster::make(5'000'001);
        sync_engine *v = cluster::make(5'000'002);
        Pk p0{}, p1{}; sync_engine_identity(e0, p0.data()); sync_engine_identity(e1, p1.data());
        sync_capability *root =
            sync_capability_root(e0, "ns", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        sync_capability *d01 = sync_capability_delegate(
            e0, root, p1.data(), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);
        sync_capability *d10 = sync_capability_delegate(
            e1, d01, p0.data(), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);
        for (auto *c : {root, d01, d10}) sync_engine_grant(v, c);
        EXPECT_EQ(cap_authorize_write(v, p1.data(), "ns"), SYNC_OK); /* terminates */
        for (auto *c : {root, d01, d10}) sync_capability_free(c);
        sync_engine_destroy(e0); sync_engine_destroy(e1); sync_engine_destroy(v);
    }
}

/* #2 — many writers hammering ONE cell over a gossiping mesh converge once writes
 * stop (no wedge); the scoped cache is inert here because every write advances
 * content_gen. */
TEST(Stress, HighContentionConverges) {
    const int K = 8, WRITE_ROUNDS = 1500;
    ImpairMesh m(/*interval=*/120);
    for (int i = 0; i < K; i++) m.add(700 + (uint32_t)i);
    m.full();
    m.start();
    for (int r = 0; r < WRITE_ROUNDS; r++) {
        m.round();
        if (r % 4 == 0)
            for (int i = 0; i < K; i++)
                cluster::put(m.eng[i], "c", "cell", "v",
                             "n" + std::to_string(i) + "r" + std::to_string(r));
    }
    auto s = clk::now();
    bool ok = m.converge(3000);
    EXPECT_TRUE(ok) << "contended mesh failed to converge after writes stopped";
    std::printf("  contention: converged=%d in %.0f ms after %d write-rounds\n",
                ok, ms_since(s), WRITE_ROUNDS);
    std::string v0 = cluster::get(m.eng[0], "c", "cell", "v");
    for (int i = 1; i < K; i++)
        EXPECT_EQ(cluster::get(m.eng[i], "c", "cell", "v"), v0) << "cell disagreement at " << i;
}

/* #3 — the per-peer scoped-snapshot cache stays bounded under many distinct peers
 * between writes, and repeated reconnect (churn) re-converges every time. */
TEST(Stress, PeerChurnAndScopeCache) {
    {   /* scope-cache bound: many distinct peers scoped against one hub, no
         * writes in between (cache should cap, not grow without bound). */
        sync_engine *hub = cluster::make(900);
        for (int i = 0; i < 500; i++)
            cluster::put(hub, "open", "e" + std::to_string(i), "f", "v");
        size_t before = rss_kb();
        std::mt19937 rng{3};
        for (int k = 0; k < 4000; k++) {
            Pk peer{}; for (auto &b : peer) b = (uint8_t)rng();
            sync_session *s = sync_session_begin_scoped(hub, 1, peer.data());
            ASSERT_NE(s, nullptr);
            sync_session_end(s);
        }
        size_t after = rss_kb();
        std::printf("  scope-cache: RSS %zu -> %zu KB over 4000 distinct peers\n", before, after);
#if KOME_RSS_CHECKS
        /* Open-namespace peers must alias the single shared snapshot, not cache a
         * full O(N) copy each — so 4000 distinct peers cost ~nothing. */
        EXPECT_LT(after, before + 20 * 1024) << "scoped_cache grows per distinct peer";
#endif
        sync_engine_destroy(hub);
    }
    {   /* churn: repeated clean restarts must re-converge every time, with new
         * data written between restarts. */
        ImpairMesh m(/*interval=*/120);
        m.add(901); m.add(902);
        m.connect(0, 1);
        m.start();
        bool all_ok = true;
        for (int cycle = 0; cycle < 20; cycle++) {
            cluster::put(m.eng[0], "open", "a" + std::to_string(cycle), "f", "x");
            cluster::put(m.eng[1], "open", "b" + std::to_string(cycle), "f", "y");
            m.restart_all();
            all_ok = all_ok && m.converge(800);
        }
        EXPECT_TRUE(all_ok) << "reconnect churn failed to re-converge";
    }
}

/* #4 — large dataset: digest, scoped-snapshot build, export, and durable reopen
 * replay all complete in sane time; reopened state matches. */
TEST(Stress, DataScale) {
    const int N_MEM = 200'000, N_DISK = 20'000;
    {   /* in-memory hot paths over a big dataset */
        sync_engine *e = cluster::make(1234);
        auto s = clk::now();
        for (int i = 0; i < N_MEM; i++)
            cluster::put(e, "ns", "e" + std::to_string(i), "f", "v" + std::to_string(i));
        double t_seed = ms_since(s);

        uint8_t dg[SYNC_DIGEST_LEN];
        s = clk::now(); sync_engine_digest(e, dg); double t_digest = ms_since(s);

        Pk peer{}; for (auto &b : peer) b = 0xAB;
        s = clk::now();
        sync_session *sess = sync_session_begin_scoped(e, 1, peer.data());
        double t_snap = ms_since(s);
        sync_session_end(sess);

        std::printf("  %d recs: seed=%.0f digest=%.1f snapshot=%.1f ms  RSS=%zu KB\n",
                    N_MEM, t_seed, t_digest, t_snap, rss_kb());
        EXPECT_LT(t_digest, 2000.0);
        EXPECT_LT(t_snap, 2000.0);
        sync_engine_destroy(e);
    }
    {   /* durable reopen (cold start = log replay) */
        synctest::TempDir dir;
        std::string path = dir.file("scale.db");
        auto seed = cluster::seed_from(77);
        sync_engine *e = sync_engine_open(path.c_str(), seed.data());
        ASSERT_NE(e, nullptr);
        for (int i = 0; i < N_DISK; i++)
            cluster::put(e, "ns", "e" + std::to_string(i), "f", "v");
        sync_engine_flush(e);
        sync_engine_destroy(e);

        auto s = clk::now();
        sync_engine *re = sync_engine_open(path.c_str(), seed.data());
        double t_replay = ms_since(s);
        ASSERT_NE(re, nullptr);
        std::printf("  reopen %d recs: replay=%.0f ms\n", N_DISK, t_replay);
        EXPECT_TRUE(cluster::exists(re, "ns", "e0"));
        EXPECT_TRUE(cluster::exists(re, "ns", "e" + std::to_string(N_DISK - 1)));
        sync_engine_destroy(re);
    }
}

/* #5 — a large mesh converges; report rounds and total bytes (amplification). */
TEST(Stress, LargeMeshConverges) {
    const int N = 64;
    {   /* one writer, ring topology */
        ImpairMesh m(/*interval=*/100);
        for (int i = 0; i < N; i++) m.add(2000 + (uint32_t)i);
        m.ring();
        cluster::put(m.eng[0], "open", "seed", "f", "v");
        m.start();
        int rounds = 0;
        bool ok = false;
        for (; rounds < 1200 && !ok; rounds++) { m.round(); ok = cluster::all_converged(m.eng); }
        EXPECT_TRUE(ok) << "ring mesh did not converge";
        std::printf("  ring N=%d: converged in %d rounds, %.1f MB on the wire\n",
                    N, rounds, m.bytes / 1e6);
    }
    {   /* every node writes one record, ring topology */
        ImpairMesh m(/*interval=*/100);
        for (int i = 0; i < N; i++) m.add(3000 + (uint32_t)i);
        m.ring();
        for (int i = 0; i < N; i++) cluster::put(m.eng[i], "open", "e" + std::to_string(i), "f", "v");
        m.start();
        bool ok = m.converge(1500);
        EXPECT_TRUE(ok) << "N-writer ring mesh did not converge";
        EXPECT_EQ(cluster::record_count(m.eng[0]), N);
    }
}

/* #6 — flooding is bounded: a flood of signed-junk delegations cannot grow the
 * cap store without limit, and unauthorized / far-future records are rejected
 * without poisoning the clock. */
TEST(Stress, ByzantineFloodBounded) {
    {   /* cap-ingest flood */
        sync_engine *owner = cluster::make(6000);
        sync_engine *victim = cluster::make(6001);
        sync_capability *root =
            sync_capability_root(owner, "x", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        const int FLOOD = 6000;
        std::vector<std::string> blobs;
        blobs.reserve(FLOOD);
        std::mt19937 rng{11};
        for (int i = 0; i < FLOOD; i++) {
            Pk sub{}; for (auto &b : sub) b = (uint8_t)rng();
            sync_capability *d =
                sync_capability_delegate(owner, root, sub.data(), SYNC_ACCESS_READ, 0);
            ASSERT_NE(d, nullptr);
            int n = sync_capability_encode(d, nullptr, 0);
            std::string blob(n, '\0');
            sync_capability_encode(d, (uint8_t *)blob.data(), blob.size());
            blobs.push_back(std::move(blob));
            sync_capability_free(d);
        }
        cap_ingest_delegations(victim, blobs);
        ASSERT_NE(victim->caps, nullptr);
        std::printf("  cap flood: %d offered, store holds %zu\n", FLOOD, victim->caps->size());
        EXPECT_LE(victim->caps->size(), (size_t)4096) << "cap store not bounded";
        sync_capability_free(root);
        sync_engine_destroy(owner); sync_engine_destroy(victim);
    }
    {   /* a volume of far-future unauthorized writes are all rejected and never
         * poison the engine's clock. */
        const uint64_t kFar = 4'000'000'000'000ull;
        sync_engine *owner = cluster::make(6100);
        sync_engine *v = cluster::make(6101);
        sync_capability *root =
            sync_capability_root(owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        sync_engine_grant(v, root);
        const std::string ns = "nsA", f = "f", val = "junk";
        auto attacker = cluster::seed_from(9999); /* holds no capability for nsA */
        int rejected = 0;
        for (int i = 0; i < 200; i++) {
            std::string ent = "e" + std::to_string(i);
            sync_change c; std::memset(&c, 0, sizeof c);
            c.kind = SYNC_CHANGE_REGISTER;
            c.ns = cluster::B(ns); c.ns_len = ns.size();
            c.entity = cluster::B(ent); c.entity_len = ent.size();
            c.field = cluster::B(f); c.field_len = f.size();
            c.value = cluster::B(val); c.value_len = val.size();
            c.hlc.physical = kFar; c.hlc.logical = 0;
            sync_change_sign(&c, attacker.data());
            if (sync_engine_apply(v, &c) != SYNC_OK) rejected++;
        }
        EXPECT_EQ(rejected, 200) << "far-future unauthorized writes not all rejected";
        /* v's own subsequent write must carry a real timestamp, not the future. */
        cluster::put(v, "open", "honest", "f", "x");
        sync_change *recs = nullptr; size_t n = 0;
        sync_engine_export(v, &recs, &n);
        for (size_t i = 0; i < n; i++) {
            if (recs[i].kind == SYNC_CHANGE_REGISTER) {
                EXPECT_LT(recs[i].hlc.physical, kFar) << "clock poisoned by a rejected record";
            }
        }
        sync_changes_free(recs, n);
        sync_capability_free(root);
        sync_engine_destroy(owner); sync_engine_destroy(v);
    }
}

/* #7 — heavy loss/reorder/dup still converges (reliability recovers), a partition
 * isolates writes until healed, and a long soak does not leak. */
TEST(Stress, ImpairedChannelConverges) {
    {   /* impaired ring converges */
        ImpairMesh m(/*interval=*/100);
        for (int i = 0; i < 5; i++) m.add(8000 + (uint32_t)i);
        m.loss = 0.30; m.dup = 0.10; m.jitter = 20;
        m.ring();
        for (int i = 0; i < 5; i++) cluster::put(m.eng[i], "open", "e" + std::to_string(i), "f", "v");
        m.start();
        bool ok = m.converge(4000);
        EXPECT_TRUE(ok) << "did not converge under 30% loss + reorder + dup";
        std::printf("  impaired ring: converged=%d\n", ok);
    }
    {   /* partition then heal */
        ImpairMesh m(/*interval=*/100);
        for (int i = 0; i < 5; i++) m.add(8100 + (uint32_t)i);
        m.ring();
        m.start();
        m.converge(400); /* settle initial empty state */
        /* split {0,1,2} | {3,4} */
        m.linked = [](int a, int b) { return (a < 3) == (b < 3); };
        cluster::put(m.eng[0], "open", "from0", "f", "v");
        cluster::put(m.eng[4], "open", "from4", "f", "v");
        for (int r = 0; r < 600; r++) m.round();
        EXPECT_TRUE(cluster::exists(m.eng[1], "open", "from0"));
        EXPECT_FALSE(cluster::exists(m.eng[4], "open", "from0")) << "partition leaked";
        EXPECT_FALSE(cluster::exists(m.eng[0], "open", "from4")) << "partition leaked";
        /* heal */
        m.linked = [](int, int) { return true; };
        bool ok = m.converge(1500);
        EXPECT_TRUE(ok) << "did not converge after partition healed";
        EXPECT_TRUE(cluster::exists(m.eng[4], "open", "from0"));
        EXPECT_TRUE(cluster::exists(m.eng[0], "open", "from4"));
    }
    {   /* soak: many idle/gossip cycles must not leak */
        ImpairMesh m(/*interval=*/100);
        for (int i = 0; i < 4; i++) m.add(8200 + (uint32_t)i);
        m.ring();
        cluster::put(m.eng[0], "open", "x", "f", "v");
        m.start();
        m.converge(400);
        size_t before = rss_kb();
        for (int r = 0; r < 20000; r++) m.round();
        size_t after = rss_kb();
        std::printf("  soak 20000 rounds: RSS %zu -> %zu KB\n", before, after);
#if KOME_RSS_CHECKS
        EXPECT_LT(after, before + 20 * 1024) << "RSS grew during steady-state soak (leak?)";
#endif
    }
}

/* #8 (messaging) — a busy group chat: every member sends a stream of messages
 * while the mesh gossips; after it settles every member holds every message and
 * agrees on one chronological order (no loss, consistent order at scale). */
TEST(Stress, MessagingHighVolumeNoLossInOrder) {
    const int K = 6, M = 40; /* 240 messages */
    ImpairMesh m(/*interval=*/120);
    for (int i = 0; i < K; i++) m.add(5200 + (uint32_t)i);
    m.full();
    m.start();
    uint64_t t = 1;
    for (int k = 0; k < M; k++) {
        for (int i = 0; i < K; i++)
            cluster::put(m.eng[i], "chat", smid(t++, i, k), "body", "m"); /* unique ids */
        for (int r = 0; r < 3; r++) m.round(); /* interleave gossip with sends */
    }
    bool ok = m.converge(3000);
    EXPECT_TRUE(ok) << "high-volume chat failed to converge";
    auto o0 = present_ids(m.eng[0], "chat");
    EXPECT_EQ((int)o0.size(), K * M) << "messages lost under load";
    bool ordered = true;
    for (int i = 1; i < K; i++) ordered = ordered && (present_ids(m.eng[i], "chat") == o0);
    EXPECT_TRUE(ordered) << "members disagree on message order at scale";
    std::printf("  chat: %d members x %d = %d delivered, identical order=%d, %.1f MB wire\n",
                K, M, (int)o0.size(), ordered, m.bytes / 1e6);
}

/* #9 (messaging) — a new device cold-joins a conversation with a large backlog
 * and receives the whole history, in order. */
TEST(Stress, MessagingBacklogColdJoinOrdered) {
    const int BACKLOG = 4000;
    ImpairMesh m(/*interval=*/100);
    m.add(5300); m.add(5301);
    for (int i = 0; i < BACKLOG; i++)
        cluster::put(m.eng[0], "chat", smid((uint64_t)(1000 + i), 0, i), "body", "m");
    m.connect(0, 1);
    m.start();
    auto t0 = clk::now();
    bool ok = m.converge(4000);
    double ms = ms_since(t0);
    EXPECT_TRUE(ok) << "cold-join backlog did not converge";
    auto ob = present_ids(m.eng[1], "chat");
    EXPECT_EQ((int)ob.size(), BACKLOG) << "backlog messages lost on join";
    EXPECT_TRUE(std::is_sorted(ob.begin(), ob.end())) << "backlog delivered out of order";
    std::printf("  backlog cold-join: %d msgs in %.0f ms\n", BACKLOG, ms);
}
