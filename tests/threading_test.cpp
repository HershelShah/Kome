/* threading_test.cpp — M6 threading contract (T6.3).
 *
 * Threading contract: a single sync_engine (or sync_session) is NOT internally
 * synchronized — one engine must be used by one thread at a time, or guarded by
 * the caller. Distinct engines are fully independent: the library holds no
 * global mutable state. This test validates that invariant by driving many
 * independent engines concurrently; run under ThreadSanitizer it must be clean.
 */
#include "sync_engine.h"

#include "cluster.hpp"

#include <gtest/gtest.h>

#include <array>
#include <atomic>
#include <cstring>
#include <random>
#include <thread>
#include <vector>

namespace {
using cluster::B;
using cluster::seed_from;
} // namespace

/* Each thread owns its engines end-to-end; nothing is shared between threads. */
TEST(Threading, IndependentEnginesNoSharedState) {
    const int kThreads = 8;
    std::atomic<int> converged{0};
    std::vector<std::thread> ts;

    for (int t = 0; t < kThreads; t++) {
        ts.emplace_back([t, &converged]() {
            std::mt19937 rng(1000 + t);
            auto sa = seed_from(0x1000 + t), sb = seed_from(0x2000 + t);
            sync_engine *a = sync_engine_create(sa.data());
            sync_engine *b = sync_engine_create(sb.data());

            for (int i = 0; i < 50; i++) {
                std::string ent = "e" + std::to_string(rng() % 10);
                std::string val = "v" + std::to_string(rng() % 100);
                sync_engine *target = (rng() % 2) ? a : b;
                sync_engine_set(target, B(std::string("ns")), 2, B(ent),
                                ent.size(), B(std::string("f")), 1, B(val),
                                val.size());
            }

            /* Reconcile via the full-state path (each engine local to this
             * thread). */
            for (int round = 0; round < 2; round++) {
                for (auto pair : {std::make_pair(a, b), std::make_pair(b, a)}) {
                    sync_change *recs = nullptr;
                    size_t n = 0;
                    sync_engine_export(pair.first, &recs, &n);
                    for (size_t i = 0; i < n; i++)
                        sync_engine_apply(pair.second, &recs[i]);
                    sync_changes_free(recs, n);
                }
            }

            uint8_t da[SYNC_DIGEST_LEN], db[SYNC_DIGEST_LEN];
            sync_engine_digest(a, da);
            sync_engine_digest(b, db);
            if (std::memcmp(da, db, SYNC_DIGEST_LEN) == 0) converged++;

            sync_engine_destroy(a);
            sync_engine_destroy(b);
        });
    }
    for (auto &th : ts) th.join();
    EXPECT_EQ(converged.load(), kThreads);
}
