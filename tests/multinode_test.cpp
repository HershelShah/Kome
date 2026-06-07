/* multinode_test.cpp — convergence across many nodes (scaling).
 *
 * N independent engines, each seeded with its own data, gossip by pairwise
 * range-reconciliation over a topology until the entire network converges to a
 * single digest. Exercises multi-hop anti-entropy: data authored on one node
 * reaches every other node through intermediaries. Scales N up and reports the
 * rounds-to-converge. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <iostream>
#include <random>
#include <string>
#include <vector>

namespace {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

std::array<uint8_t, SYNC_SEED_LEN> seed_from(uint32_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (size_t i = 0; i < s.size(); i++) s[i] = (uint8_t)(v >> ((i % 4) * 8));
    return s;
}

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

/* ---- Star topology (hub and spokes) ------------------------------------ */
TEST(MultiNode, StarTopology) {
    const int n = 30;
    std::mt19937 rng(7);
    Net net(n);
    net.seed_data(2, rng);

    std::vector<std::pair<int, int>> edges;
    for (int i = 1; i < n; i++) edges.push_back({0, i}); /* hub = node 0 */

    int rounds = net.gossip(edges, 10);
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

    /* Spanning tree (guarantees connectivity) + extra random edges. */
    std::vector<std::pair<int, int>> edges;
    for (int i = 1; i < n; i++) edges.push_back({(int)(rng() % i), i});
    for (int i = 0; i < n; i++)
        edges.push_back({(int)(rng() % n), (int)(rng() % n)});

    int rounds = net.gossip(edges, n + 5);
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
