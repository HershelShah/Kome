/* multinode_test.cpp — convergence across many nodes (scaling).
 *
 * N independent engines, each seeded with its own data, gossip by pairwise
 * range-reconciliation over a topology until the entire network converges to a
 * single digest. Exercises multi-hop anti-entropy: data authored on one node
 * reaches every other node through intermediaries. Scales N up and reports the
 * rounds-to-converge. */
#include "sync_engine.h"

#include "cluster.hpp"

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <iostream>
#include <random>
#include <string>
#include <vector>

namespace {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
using cluster::B;
using cluster::seed_from;

Digest digest(sync_engine *e) {
    Digest d{};
    EXPECT_EQ(sync_engine_digest(e, d.data()), SYNC_OK);
    return d;
}

/* Fully reconcile two engines via the in-process session pump (bidirectional;
 * both end holding the union). */
void reconcile_pair(sync_engine *a, sync_engine *b) {
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);

    uint8_t *out = nullptr;
    size_t ol = 0;
    int done = 0;
    sync_session_step(sa, nullptr, 0, &out, &ol, &done);
    std::vector<uint8_t> msg(out, out + ol);
    if (out) sync_free(out);

    sync_session *turn = sb, *other = sa;
    int empties = (ol == 0) ? 1 : 0;
    for (int i = 0; i < 100000; i++) {
        out = nullptr; ol = 0; done = 0;
        sync_session_step(turn, msg.data(), msg.size(), &out, &ol, &done);
        std::vector<uint8_t> next(out, out + ol);
        if (out) sync_free(out);
        empties = (ol == 0) ? empties + 1 : 0;
        if (empties >= 2) break;
        msg.swap(next);
        std::swap(turn, other);
    }
    sync_session_end(sa);
    sync_session_end(sb);
}

struct Net {
    std::vector<sync_engine *> nodes;
    explicit Net(int n) {
        for (int i = 0; i < n; i++)
            nodes.push_back(sync_engine_create(seed_from(0x1000 + i).data()));
    }
    ~Net() {
        for (auto *e : nodes) sync_engine_destroy(e);
    }
    int size() const { return (int)nodes.size(); }

    /* Each node writes `k` records into a shared namespace, keyed uniquely. */
    void seed_data(int k, std::mt19937 &rng) {
        for (int i = 0; i < size(); i++)
            for (int j = 0; j < k; j++) {
                std::string ent = "n" + std::to_string(i) + "_e" + std::to_string(j);
                std::string val = "v" + std::to_string(rng() % 100000);
                sync_engine_set(nodes[i], B(std::string("ns")), 2, B(ent),
                                ent.size(), B(std::string("f")), 1, B(val),
                                val.size());
            }
    }

    bool converged() {
        if (nodes.empty()) return true;
        Digest first = digest(nodes[0]);
        for (int i = 1; i < size(); i++)
            if (digest(nodes[i]) != first) return false;
        return true;
    }

    /* Run gossip rounds over a set of edges until convergence or the cap. */
    int gossip(const std::vector<std::pair<int, int>> &edges, int max_rounds) {
        int rounds = 0;
        while (!converged() && rounds < max_rounds) {
            for (auto &e : edges) reconcile_pair(nodes[e.first], nodes[e.second]);
            rounds++;
        }
        return rounds;
    }
};

std::vector<std::pair<int, int>> ring_edges(int n) {
    std::vector<std::pair<int, int>> e;
    for (int i = 0; i < n; i++) e.push_back({i, (i + 1) % n});
    return e;
}

/* Hub-and-spokes: node 0 is the hub, reconciling with every other node. */
std::vector<std::pair<int, int>> star_edges(int n) {
    std::vector<std::pair<int, int>> e;
    for (int i = 1; i < n; i++) e.push_back({0, i});
    return e;
}

/* Connected random mesh: a spanning tree (guarantees connectivity) plus a
 * sprinkling of extra random edges. Deterministic given `rng`. */
std::vector<std::pair<int, int>> mesh_edges(int n, std::mt19937 &rng) {
    std::vector<std::pair<int, int>> e;
    for (int i = 1; i < n; i++) e.push_back({(int)(rng() % i), i});
    for (int i = 0; i < n; i++)
        e.push_back({(int)(rng() % n), (int)(rng() % n)});
    return e;
}

/* Set up an enforced namespace: node 0 owns `ns`, every node enforces it (holds
 * the root) and carries its own write delegation. Each node then writes one
 * record it is authorized for. Authorization for *other* nodes' records must be
 * obtained purely by capabilities gossiped during sync. */
void setup_enforced(Net &net, const char *ns) {
    sync_engine *owner = net.nodes[0];
    sync_capability *root =
        sync_capability_root(owner, ns, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    for (int i = 0; i < net.size(); i++) {
        EXPECT_EQ(sync_engine_grant(net.nodes[i], root), SYNC_OK); /* all enforce */
        uint8_t pk[SYNC_PUBKEY_LEN];
        sync_engine_identity(net.nodes[i], pk);
        sync_capability *d =
            sync_capability_delegate(owner, root, pk, SYNC_ACCESS_WRITE, 0);
        EXPECT_EQ(sync_engine_grant(net.nodes[i], d), SYNC_OK); /* carries own cap */
        sync_capability_free(d);
    }
    sync_capability_free(root);

    std::string nss(ns);
    for (int i = 0; i < net.size(); i++) {
        std::string ent = "rec" + std::to_string(i);
        sync_engine_set(net.nodes[i], B(nss), nss.size(), B(ent), ent.size(),
                        B(std::string("f")), 1, B(ent), ent.size());
    }
}

} // namespace

/* ---- Ring topology, scaling N ------------------------------------------ */
TEST(MultiNode, RingScaling) {
    for (int n : {3, 5, 10, 25, 50}) {
        std::mt19937 rng(100 + n);
        Net net(n);
        net.seed_data(2, rng);
        ASSERT_FALSE(net.converged()) << "n=" << n << " trivially converged";

        /* A ring has diameter ~n/2, so multi-hop propagation needs ~n/2
         * rounds; cap generously. */
        int rounds = net.gossip(ring_edges(n), n + 5);
        EXPECT_TRUE(net.converged()) << "ring n=" << n << " did not converge";
        std::cout << "  [ring]   N=" << n << " converged in " << rounds
                  << " rounds (records/node=" << (n * 2) << ")\n";
    }

    /* Optional larger run: SYNC_SCALE_N=<int> to push the scale up. */
    if (const char *env = getenv("SYNC_SCALE_N")) {
        int n = atoi(env);
        if (n > 1) {
            std::mt19937 rng(999);
            Net net(n);
            net.seed_data(2, rng);
            int rounds = net.gossip(ring_edges(n), n + 5);
            EXPECT_TRUE(net.converged()) << "ring n=" << n << " did not converge";
            std::cout << "  [ring]   N=" << n << " converged in " << rounds
                      << " rounds (total records=" << (n * n * 2) << ")\n";
        }
    }
}

/* ---- Enforced namespace at scale (capabilities gossiped during sync) --- */
TEST(MultiNode, EnforcedRingWithCapabilities) {
    std::vector<int> sizes = {5, 10, 25};
    if (const char *env = getenv("SYNC_SCALE_N")) {
        int n = atoi(env);
        if (n > 1) sizes.push_back(n);
    }
    for (int n : sizes) {
        Net net(n);
        setup_enforced(net, "secure");

        int rounds = net.gossip(ring_edges(n), n + 5);
        EXPECT_TRUE(net.converged()) << "enforced ring n=" << n << " diverged";

        /* Every node ended up with every node's record — all authorized purely
         * via capabilities exchanged during gossip (no out-of-band grants). */
        int total_present = 0;
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++) {
                std::string ent = "rec" + std::to_string(j);
                int p = 0;
                sync_engine_exists(net.nodes[i], B(std::string("secure")), 6,
                                   B(ent), ent.size(), &p);
                total_present += p;
            }
        EXPECT_EQ(total_present, n * n)
            << "enforced ring n=" << n << ": some authorized records were dropped";
        std::cout << "  [enforced] N=" << n << " converged in " << rounds
                  << " rounds, all " << (n * n) << " (node x record) present\n";
    }
}

/* ---- Star topology (hub and spokes) ------------------------------------ */
TEST(MultiNode, StarTopology) {
    const int n = 30;
    std::mt19937 rng(7);
    Net net(n);
    net.seed_data(2, rng);

    int rounds = net.gossip(star_edges(n), 10);
    EXPECT_TRUE(net.converged());
    std::cout << "  [star]   N=" << n << " converged in " << rounds
              << " rounds\n";
}

/* ---- Random connected mesh --------------------------------------------- */
TEST(MultiNode, RandomMesh) {
    const int n = 40;
    std::mt19937 rng(42);
    Net net(n);
    net.seed_data(3, rng);

    int rounds = net.gossip(mesh_edges(n, rng), n + 5);
    EXPECT_TRUE(net.converged());
    std::cout << "  [mesh]   N=" << n << " converged in " << rounds
              << " rounds\n";
}

/* ---- Writes during gossip, then settle --------------------------------- */
TEST(MultiNode, ChurnThenConverge) {
    const int n = 12;
    std::mt19937 rng(11);
    Net net(n);
    net.seed_data(1, rng);
    auto edges = ring_edges(n);

    /* Gossip while new writes keep arriving. */
    for (int t = 0; t < 8; t++) {
        for (int i = 0; i < n; i++) {
            std::string ent = "churn" + std::to_string(t) + "_" + std::to_string(i);
            sync_engine_set(net.nodes[i], B(std::string("ns")), 2, B(ent),
                            ent.size(), B(std::string("f")), 1,
                            B(std::string("x")), 1);
        }
        for (auto &e : edges) reconcile_pair(net.nodes[e.first], net.nodes[e.second]);
    }
    /* Stop writing; gossip must drive everyone to the same state. */
    int rounds = net.gossip(edges, n + 5);
    EXPECT_TRUE(net.converged());
    std::cout << "  [churn]  N=" << n << " settled in " << rounds
              << " rounds after writes stopped\n";
}

/* ---- Powers-of-two scaling sweep: N = 2, 4, 8, 16, 32, 64 -------------- *
 * One parameterized case per N, so each network size is reported (and can
 * fail) independently. At every N we drive convergence across all three
 * topologies — ring (worst-case diameter), star (hub fan-out), and a random
 * connected mesh — and the enforced-namespace case where authorization for
 * every peer's writes must be obtained purely from capabilities gossiped
 * during sync. This is the multi-node acceptance sweep up to 64 nodes. */
class MultiNodeScale : public ::testing::TestWithParam<int> {};

TEST_P(MultiNodeScale, AllTopologiesConverge) {
    const int n = GetParam();

    {
        std::mt19937 rng(2000 + n);
        Net net(n);
        net.seed_data(2, rng);
        ASSERT_FALSE(net.converged()) << "n=" << n << " trivially converged";
        /* Ring diameter is ~n/2, so propagation needs ~n/2 rounds; cap at n+5. */
        int rounds = net.gossip(ring_edges(n), n + 5);
        EXPECT_TRUE(net.converged()) << "ring n=" << n << " did not converge";
        std::cout << "  [ring]   N=" << n << " converged in " << rounds
                  << " rounds\n";
    }
    {
        std::mt19937 rng(3000 + n);
        Net net(n);
        net.seed_data(2, rng);
        /* Star gathers at the hub then redistributes: ~2 rounds regardless of N. */
        int rounds = net.gossip(star_edges(n), 8);
        EXPECT_TRUE(net.converged()) << "star n=" << n << " did not converge";
        std::cout << "  [star]   N=" << n << " converged in " << rounds
                  << " rounds\n";
    }
    {
        std::mt19937 rng(4000 + n);
        Net net(n);
        net.seed_data(2, rng);
        int rounds = net.gossip(mesh_edges(n, rng), n + 5);
        EXPECT_TRUE(net.converged()) << "mesh n=" << n << " did not converge";
        std::cout << "  [mesh]   N=" << n << " converged in " << rounds
                  << " rounds\n";
    }
    {
        /* Enforced namespace: every node holds the root + its own write cap;
         * authorization for other nodes' records arrives only via gossip. */
        Net net(n);
        setup_enforced(net, "secure");
        int rounds = net.gossip(ring_edges(n), n + 5);
        EXPECT_TRUE(net.converged()) << "enforced ring n=" << n << " diverged";
        int total_present = 0;
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++) {
                std::string ent = "rec" + std::to_string(j);
                int p = 0;
                sync_engine_exists(net.nodes[i], B(std::string("secure")), 6,
                                   B(ent), ent.size(), &p);
                total_present += p;
            }
        EXPECT_EQ(total_present, n * n)
            << "enforced n=" << n << ": some authorized records were dropped";
        std::cout << "  [enforced] N=" << n << " converged in " << rounds
                  << " rounds, all " << (n * n) << " (node x record) present\n";
    }
}

INSTANTIATE_TEST_SUITE_P(PowersOfTwo, MultiNodeScale,
                         ::testing::Values(2, 4, 8, 16, 32, 64),
                         [](const ::testing::TestParamInfo<int> &info) {
                             return "N" + std::to_string(info.param);
                         });
