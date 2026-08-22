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
#include "log_frames.hpp" /* fsync counter (durable-engines race pin) */
#include "tempdir.hpp"

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

/* Independent DURABLE engines driven from independent threads must be just as
 * clean: the storage layer's only process-global mutable state is the
 * debug/test fsync counter (ke::storage_fsync_count), which every durable
 * write path increments — a plain uint64_t there is a data race the moment
 * two durable engines fsync concurrently, invisible to the in-memory test
 * above. Run under TSan this pins the counter's atomicity; natively the
 * exact final count also proves relaxed increments lose nothing. */
TEST(Threading, IndependentDurableEnginesNoSharedState) {
    const int kThreads = 4;
    const int kSetsPerThread = 100; /* ~30 KB/log: stays under the 64 KiB
                                     * auto-compact floor, so every set is
                                     * exactly one fsync'd frame */
    synctest::TempDir dir;
    synctest::fsync_reset();
    std::vector<std::thread> ts;
    for (int t = 0; t < kThreads; t++) {
        ts.emplace_back([t, &dir]() {
            std::string db = dir.file("durable_" + std::to_string(t) + ".db");
            auto sd = seed_from(0x3000 + t);
            sync_engine *e = sync_engine_open(db.c_str(), sd.data());
            if (!e) return; /* asserted via the fsync arithmetic below */
            for (int i = 0; i < kSetsPerThread; i++) {
                std::string ent = "e" + std::to_string(i);
                cluster::put(e, "ns", ent, "f", "v");
            }
            sync_engine_destroy(e);
        });
    }
    for (auto &th : ts) th.join();
    /* Per engine: 1 frame for the fresh log's schema+seed stamp, then one
     * frame per set. An engine that failed to open, a lost (raced) counter
     * increment, or an unexpected auto-compaction all break the sum. */
    EXPECT_EQ(synctest::fsync_count(),
              (uint64_t)kThreads * (1u + kSetsPerThread));
}
