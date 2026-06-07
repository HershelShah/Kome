/* scenario_test.cpp — a matrix of real-life situations, each asserting data
 * correctness (convergence + the *right* values, no lost updates, no rollback).
 * See docs/SCENARIOS.md for the full matrix and coverage map.
 *
 * Groups:
 *   Conflict   — concurrent edits resolve deterministically & losslessly
 *   Lifecycle  — add/delete/re-add across nodes (causal-length set)
 *   Ordering   — stale writes never roll back; merge order doesn't matter
 *   Timing     — clock skew still converges deterministically
 *   Topology   — transitive multi-hop, cluster merge, fresh-node bootstrap
 *   Liveness   — writes during an active sync are safe & eventually consistent
 *   Data       — binary/large values and many entities round-trip intact
 */
#include "cluster.hpp"

#include <gtest/gtest.h>

#include <string>
#include <vector>

using namespace cluster;

/* ===================== Conflict ========================================= */

/* Concurrent edits to DIFFERENT fields of the same entity must both survive. */
TEST(Scenario, FieldLevelConcurrentEditsNoLostUpdate) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "ns", "user", "name", "Alice");
    sync2(a, b); /* both know the entity */

    put(a, "ns", "user", "email", "alice@x");   /* concurrent... */
    put(b, "ns", "user", "phone", "555");        /* ...different fields */
    sync2(a, b);

    for (sync_engine *e : {a, b}) {
        EXPECT_EQ(get(e, "ns", "user", "name"), "Alice");
        EXPECT_EQ(get(e, "ns", "user", "email"), "alice@x");
        EXPECT_EQ(get(e, "ns", "user", "phone"), "555");
    }
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* N writers hit the same cell concurrently → one deterministic winner,
 * independent of the order the conflicting records are merged. */
TEST(Scenario, NWayConflictOrderIndependent) {
    std::vector<sync_engine *> w;
    for (int i = 0; i < 4; i++) {
        w.push_back(make(100 + i));
        put(w[i], "ns", "cell", "v", "writer-" + std::to_string(i));
    }
    /* Merge the four conflicting writes in opposite orders into two replicas. */
    sync_engine *p = make(900), *q = make(901);
    for (int i = 0; i < 4; i++) replicate(w[i], p);
    for (int i = 3; i >= 0; i--) replicate(w[i], q);

    EXPECT_EQ(get(p, "ns", "cell", "v"), get(q, "ns", "cell", "v"));
    EXPECT_EQ(digest(p), digest(q)) << "multi-way conflict is order-dependent";

    sync_engine_destroy(p); sync_engine_destroy(q);
    for (auto *e : w) sync_engine_destroy(e);
}

/* Two replicas independently create the same entity → one present entity. */
TEST(Scenario, ConcurrentAddAdd) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "ns", "e", "fa", "x");
    put(b, "ns", "e", "fb", "y");
    sync2(a, b);
    EXPECT_TRUE(exists(a, "ns", "e"));
    EXPECT_TRUE(exists(b, "ns", "e"));
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* Two replicas delete the same entity → converges absent, idempotently. */
TEST(Scenario, ConcurrentDeleteDelete) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "ns", "e", "f", "v");
    sync2(a, b);
    del(a, "ns", "e");
    del(b, "ns", "e");
    sync2(a, b);
    EXPECT_FALSE(exists(a, "ns", "e"));
    EXPECT_FALSE(exists(b, "ns", "e"));
    EXPECT_EQ(digest(a), digest(b));
    sync2(a, b); /* re-sync is a no-op */
    EXPECT_FALSE(exists(a, "ns", "e"));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ===================== Lifecycle (causal-length set) ==================== */

/* Delete on one node, concurrent field edit on another, then re-add. */
TEST(Scenario, DeleteVsEditThenReAdd) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "ns", "e", "f1", "init");
    sync2(a, b); /* both present */

    del(a, "ns", "e");                     /* A deletes (causal_length -> even) */
    put(b, "ns", "e", "f2", "edit");        /* B concurrently edits a field */
    sync2(a, b);
    EXPECT_FALSE(exists(a, "ns", "e")) << "delete should dominate concurrent edit";
    EXPECT_FALSE(exists(b, "ns", "e"));
    EXPECT_EQ(digest(a), digest(b));

    put(a, "ns", "e", "f1", "reborn");      /* re-add */
    sync2(a, b);
    EXPECT_TRUE(exists(a, "ns", "e"));
    EXPECT_TRUE(exists(b, "ns", "e"));
    EXPECT_EQ(get(b, "ns", "e", "f1"), "reborn");
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ===================== Ordering ======================================== */

/* A newer value is never overwritten by a later-delivered older one,
 * regardless of the order the two writes arrive. */
TEST(Scenario, StaleWriteDoesNotRollBack) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "ns", "x", "present", "y");  /* make entity x present */
    put(b, "ns", "x", "present", "y");

    /* a: newer then older. */
    apply_register(a, "ns", "x", "f", "new", 2000, 0, 7);
    apply_register(a, "ns", "x", "f", "old", 1000, 0, 7);
    EXPECT_EQ(get(a, "ns", "x", "f"), "new");

    /* b: older then newer (opposite delivery order). */
    apply_register(b, "ns", "x", "f", "old", 1000, 0, 7);
    apply_register(b, "ns", "x", "f", "new", 2000, 0, 7);
    EXPECT_EQ(get(b, "ns", "x", "f"), "new");

    /* And it stays "new" after they reconcile. */
    sync2(a, b);
    EXPECT_EQ(get(a, "ns", "x", "f"), "new");
    EXPECT_EQ(get(b, "ns", "x", "f"), "new");
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ===================== Timing ========================================== */

/* Nodes with badly skewed clocks still converge deterministically; the
 * higher-timestamp write wins its cell (expected, self-correcting). */
TEST(Scenario, ClockSkewConverges) {
    sync_engine *future = make(1), *normal = make(2), *past = make(3);

    /* future node stamps a far-future time; past node a far-past time. */
    apply_register(future, "ns", "cell", "v", "from-future", 4000000000000ull, 0, 50);
    put(normal, "ns", "cell", "v", "from-normal");           /* ~now */
    apply_register(past, "ns", "cell", "v", "from-past", 1000, 0, 52);

    /* Each node also has unique data, to confirm nothing is lost. */
    put(future, "ns", "uf", "v", "f");
    put(normal, "ns", "un", "v", "n");
    put(past, "ns", "up", "v", "p");

    std::vector<sync_engine *> g = {future, normal, past};
    gossip(g);
    EXPECT_TRUE(all_converged(g));

    /* The far-future write wins the contested cell everywhere. */
    for (auto *e : g) EXPECT_EQ(get(e, "ns", "cell", "v"), "from-future");
    /* No unique data lost despite the skew. */
    for (auto *e : g) {
        EXPECT_TRUE(exists(e, "ns", "uf"));
        EXPECT_TRUE(exists(e, "ns", "un"));
        EXPECT_TRUE(exists(e, "ns", "up"));
    }
    destroy(g);
}

/* ===================== Topology ======================================== */

/* Data reaches a node it is never directly connected to (A-B-C-D chain). */
TEST(Scenario, TransitiveChainPropagation) {
    sync_engine *a = make(1), *b = make(2), *c = make(3), *d = make(4);
    put(a, "ns", "from-a", "v", "1");
    put(d, "ns", "from-d", "v", "2");

    /* Only adjacent links ever talk. */
    sync2(a, b); sync2(b, c); sync2(c, d); /* forward sweep */
    sync2(c, d); sync2(b, c); sync2(a, b); /* backward sweep */

    EXPECT_TRUE(exists(d, "ns", "from-a")) << "A's data did not reach D";
    EXPECT_TRUE(exists(a, "ns", "from-d")) << "D's data did not reach A";
    std::vector<sync_engine *> g = {a, b, c, d};
    EXPECT_TRUE(all_converged(g));
    destroy(g);
}

/* Two independently-converged clusters merge into the union. */
TEST(Scenario, TwoClustersMerge) {
    std::vector<sync_engine *> c1 = {make(1), make(2), make(3)};
    std::vector<sync_engine *> c2 = {make(4), make(5), make(6)};
    for (int i = 0; i < 3; i++) {
        put(c1[i], "ns", "c1e" + std::to_string(i), "v", "x");
        put(c2[i], "ns", "c2e" + std::to_string(i), "v", "y");
    }
    gossip(c1);
    gossip(c2);

    /* Bridge the two clusters with a single link, then settle everyone. */
    sync2(c1[2], c2[0]);
    std::vector<sync_engine *> all = {c1[0], c1[1], c1[2], c2[0], c2[1], c2[2]};
    gossip(all);
    EXPECT_TRUE(all_converged(all));
    for (auto *e : all)
        for (int i = 0; i < 3; i++) {
            EXPECT_TRUE(exists(e, "ns", "c1e" + std::to_string(i)));
            EXPECT_TRUE(exists(e, "ns", "c2e" + std::to_string(i)));
        }
    destroy(all);
}

/* A fresh empty node joins an established cluster and bootstraps fully. */
TEST(Scenario, FreshNodeBootstrap) {
    std::vector<sync_engine *> g = {make(1), make(2), make(3)};
    for (int i = 0; i < 3; i++) put(g[i], "ns", "e" + std::to_string(i), "v", "x");
    gossip(g);

    sync_engine *fresh = make(99);
    sync2(fresh, g[0]); /* one bootstrap contact */
    for (int i = 0; i < 3; i++)
        EXPECT_TRUE(exists(fresh, "ns", "e" + std::to_string(i)))
            << "fresh node missed e" << i;
    EXPECT_EQ(digest(fresh), digest(g[0]));
    sync_engine_destroy(fresh);
    destroy(g);
}

/* ===================== Liveness ======================================== */

/* Writes that happen while a sync session is in flight are not lost or
 * corrupted; a subsequent session reconciles them. */
TEST(Scenario, WritesDuringActiveSync) {
    sync_engine *a = make(1), *b = make(2);
    put(a, "ns", "A1", "v", "1");
    put(b, "ns", "B1", "v", "1");

    /* Drive a session partway, inject writes mid-flight, then finish it. */
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    uint8_t *out = nullptr; size_t ol = 0; int done = 0;
    sync_session_step(sa, nullptr, 0, &out, &ol, &done);
    std::vector<uint8_t> msg(out, out + ol);
    if (out) sync_free(out);
    sync_session *turn = sb, *other = sa;
    bool injected = false;
    int empties = (ol == 0) ? 1 : 0;
    for (int i = 0; i < 100000; i++) {
        if (i == 1 && !injected) {            /* mid-flight writes */
            put(a, "ns", "A2", "v", "2");
            put(b, "ns", "B2", "v", "2");
            injected = true;
        }
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

    /* A fresh session settles whatever the in-flight one didn't carry. */
    sync2(a, b);
    for (sync_engine *e : {a, b}) {
        EXPECT_TRUE(exists(e, "ns", "A1"));
        EXPECT_TRUE(exists(e, "ns", "A2"));
        EXPECT_TRUE(exists(e, "ns", "B1"));
        EXPECT_TRUE(exists(e, "ns", "B2"));
    }
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ===================== Data shapes ===================================== */

/* Binary values with embedded NULs and a large value round-trip through sync. */
TEST(Scenario, BinaryAndLargeValues) {
    sync_engine *a = make(1), *b = make(2);
    std::string binv = std::string("\x00\x01\x02\x00\xff", 5) + std::string("\x00mid\x00", 5);
    std::string bigv(200000, 'Z');
    bigv[100000] = '\0';
    put(a, "ns", "bin", "f", binv);
    put(a, "ns", "big", "f", bigv);
    sync2(a, b);
    EXPECT_EQ(get(b, "ns", "bin", "f"), binv);
    EXPECT_EQ(get(b, "ns", "big", "f"), bigv);
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* Many distinct entities from two nodes merge to the full union. */
TEST(Scenario, ManyEntitiesConverge) {
    sync_engine *a = make(1), *b = make(2);
    const int k = 500;
    for (int i = 0; i < k; i++) {
        put(a, "ns", "a" + std::to_string(i), "v", "x");
        put(b, "ns", "b" + std::to_string(i), "v", "y");
    }
    sync2(a, b);
    EXPECT_EQ(record_count(a), 2 * k);
    EXPECT_EQ(record_count(b), 2 * k);
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}
