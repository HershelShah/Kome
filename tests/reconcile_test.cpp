/* reconcile_test.cpp — M3 acceptance tests (T3.1-T3.7).
 *
 * Codec round-trip + golden vector, then range-based reconciliation checked
 * against the full-state oracle: correctness, difference-proportional and
 * sublinear transfer, round-trip count, edge topologies, and robustness to
 * reordered/duplicated messages. */
#include "sync_engine.h"

#include "cluster.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cmath>
#include <cstring>
#include <deque>
#include <random>
#include <string>
#include <vector>

namespace {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
using cluster::B;

std::array<uint8_t, SYNC_SITE_ID_LEN> site_from(uint8_t seed) {
    std::array<uint8_t, SYNC_SITE_ID_LEN> s{};
    for (auto &b : s) b = seed;
    return s;
}

Digest digest(sync_engine *e) {
    Digest d{};
    EXPECT_EQ(sync_engine_digest(e, d.data()), SYNC_OK);
    return d;
}

struct OwnedChange {
    uint8_t kind = 0;
    std::string ns, entity, field, value;
    uint64_t causal_length = 0;
    sync_hlc hlc{};
    std::array<uint8_t, SYNC_PUBKEY_LEN> author{};
    std::array<uint8_t, SYNC_SIG_LEN>    signature{};
};

std::vector<OwnedChange> export_owned(sync_engine *e) {
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_EQ(sync_engine_export(e, &recs, &n), SYNC_OK);
    std::vector<OwnedChange> out;
    for (size_t i = 0; i < n; i++) {
        OwnedChange o;
        o.kind = recs[i].kind;
        o.ns.assign((const char *)recs[i].ns, recs[i].ns_len);
        o.entity.assign((const char *)recs[i].entity, recs[i].entity_len);
        if (recs[i].field) o.field.assign((const char *)recs[i].field, recs[i].field_len);
        if (recs[i].value) o.value.assign((const char *)recs[i].value, recs[i].value_len);
        o.causal_length = recs[i].causal_length;
        o.hlc = recs[i].hlc;
        std::memcpy(o.author.data(), recs[i].author, SYNC_PUBKEY_LEN);
        std::memcpy(o.signature.data(), recs[i].signature, SYNC_SIG_LEN);
        out.push_back(std::move(o));
    }
    sync_changes_free(recs, n);
    return out;
}

void apply_owned(sync_engine *e, const OwnedChange &o) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = o.kind;
    c.ns = B(o.ns); c.ns_len = o.ns.size();
    c.entity = B(o.entity); c.entity_len = o.entity.size();
    c.field = B(o.field); c.field_len = o.field.size();
    c.value = B(o.value); c.value_len = o.value.size();
    c.causal_length = o.causal_length;
    c.hlc = o.hlc;
    std::memcpy(c.author, o.author.data(), SYNC_PUBKEY_LEN);
    std::memcpy(c.signature, o.signature.data(), SYNC_SIG_LEN);
    EXPECT_EQ(sync_engine_apply(e, &c), SYNC_OK);
}

/* Full-state oracle: union of a and b applied into a fresh engine. */
Digest baseline_union(sync_engine *a, sync_engine *b) {
    auto sa = site_from(0xEE);
    sync_engine *u = sync_engine_create(sa.data());
    for (auto &o : export_owned(a)) apply_owned(u, o);
    for (auto &o : export_owned(b)) apply_owned(u, o);
    Digest d = digest(u);
    sync_engine_destroy(u);
    return d;
}

size_t full_state_bytes(sync_engine *e) {
    size_t total = 0;
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_EQ(sync_engine_export(e, &recs, &n), SYNC_OK);
    for (size_t i = 0; i < n; i++) total += sync_change_encode(&recs[i], nullptr, 0);
    sync_changes_free(recs, n);
    return total;
}

struct DriveResult {
    int rounds = 0;       /* non-empty messages exchanged */
    size_t bytes = 0;     /* total bytes across all messages */
    bool finished = false;
};

/* In-process driver: pump messages between two sessions until both quiesce. */
DriveResult drive(sync_engine *a, sync_engine *b, int cap = 2000) {
    DriveResult r;
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    EXPECT_NE(sa, nullptr);
    EXPECT_NE(sb, nullptr);

    uint8_t *out = nullptr;
    size_t outlen = 0;
    int done = 0;

    /* Initiator's first message. */
    EXPECT_EQ(sync_session_step(sa, nullptr, 0, &out, &outlen, &done), SYNC_OK);
    std::vector<uint8_t> msg(out, out + outlen);
    if (out) sync_free(out);
    r.bytes += outlen;
    if (outlen) r.rounds++;

    sync_session *turn = sb, *other = sa;
    int empties = (outlen == 0) ? 1 : 0;
    int iters = 0;
    for (; iters < cap; iters++) {
        out = nullptr; outlen = 0; done = 0;
        EXPECT_EQ(sync_session_step(turn, msg.data(), msg.size(), &out, &outlen,
                                    &done),
                  SYNC_OK);
        r.bytes += outlen;
        if (outlen) r.rounds++;
        std::vector<uint8_t> next(out, out + outlen);
        if (out) sync_free(out);
        empties = (outlen == 0) ? empties + 1 : 0;
        if (empties >= 2) { r.finished = true; break; }
        msg.swap(next);
        std::swap(turn, other);
    }
    sync_session_end(sa);
    sync_session_end(sb);
    return r;
}

/* Lossy driver: a queue of (target, message) with random delivery order and
 * message duplication, to exercise robustness (T3.7). */
bool drive_lossy(sync_engine *a, sync_engine *b, std::mt19937 &rng,
                 int cap = 50000) {
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    EXPECT_NE(sa, nullptr);
    EXPECT_NE(sb, nullptr);

    struct Item { sync_session *tgt; std::vector<uint8_t> msg; };
    std::deque<Item> q;

    uint8_t *out = nullptr;
    size_t outlen = 0;
    int done = 0;
    EXPECT_EQ(sync_session_step(sa, nullptr, 0, &out, &outlen, &done), SYNC_OK);
    if (outlen) q.push_back({sb, std::vector<uint8_t>(out, out + outlen)});
    if (out) sync_free(out);

    int iters = 0;
    bool finished = false;
    for (; iters < cap; iters++) {
        if (q.empty()) { finished = true; break; }
        /* Random delivery order (reorder). */
        size_t idx = rng() % q.size();
        Item it = q[idx];
        q.erase(q.begin() + idx);

        out = nullptr; outlen = 0; done = 0;
        EXPECT_EQ(sync_session_step(it.tgt, it.msg.data(), it.msg.size(), &out,
                                    &outlen, &done),
                  SYNC_OK);
        if (outlen) {
            sync_session *next = (it.tgt == sa) ? sb : sa;
            std::vector<uint8_t> m(out, out + outlen);
            q.push_back({next, m});
            /* Duplicate sometimes. */
            if (rng() % 4 == 0) q.push_back({next, m});
        }
        if (out) sync_free(out);
    }
    sync_session_end(sa);
    sync_session_end(sb);
    return finished;
}

void populate(sync_engine *e, std::mt19937 &rng, int entities, int fields) {
    for (int i = 0; i < entities; i++) {
        std::string ent = "entity-" + std::to_string(i);
        for (int f = 0; f < fields; f++) {
            std::string field = "f" + std::to_string(f);
            std::string val = "v" + std::to_string(rng() % 100000);
            sync_engine_set(e, B(std::string("ns")), 2, B(ent), ent.size(),
                            B(field), field.size(), B(val), val.size());
        }
    }
}

} // namespace

/* ---- T3.1 Codec round-trip (randomized) -------------------------------- */
TEST(Reconcile, CodecRoundTrip) {
    std::mt19937 rng(0xC0DEC);
    for (int trial = 0; trial < 500; trial++) {
        sync_change c;
        std::memset(&c, 0, sizeof c);
        std::string ns = "ns" + std::to_string(rng() % 10);
        std::string ent = "e" + std::to_string(rng() % 50);
        c.ns = B(ns); c.ns_len = ns.size();
        c.entity = B(ent); c.entity_len = ent.size();

        bool reg = rng() % 2;
        std::string field, value;
        if (reg) {
            c.kind = SYNC_CHANGE_REGISTER;
            field = (rng() % 5 == 0) ? std::string() : ("f" + std::to_string(rng() % 5));
            /* values: empty, plain, and binary with embedded NULs */
            int vk = rng() % 3;
            if (vk == 0) value = "";
            else if (vk == 1) value = "value" + std::to_string(rng());
            else { value = std::string("a\0b\0c", 5); value.push_back((char)(rng() & 0xff)); }
            c.field = B(field); c.field_len = field.size();
            c.value = B(value); c.value_len = value.size();
            c.hlc.physical = ((uint64_t)rng() << 20) ^ rng();
            c.hlc.logical = rng();
        } else {
            c.kind = SYNC_CHANGE_EXISTENCE;
            c.causal_length = ((uint64_t)rng() << 16) ^ rng();
        }
        for (int i = 0; i < (int)SYNC_PUBKEY_LEN; i++) c.author[i] = (uint8_t)rng();
        for (int i = 0; i < (int)SYNC_SIG_LEN; i++) c.signature[i] = (uint8_t)rng();

        size_t need = sync_change_encode(&c, nullptr, 0);
        ASSERT_GT(need, 0u);
        std::vector<uint8_t> buf(need);
        ASSERT_EQ(sync_change_encode(&c, buf.data(), buf.size()), need);

        sync_change out;
        size_t consumed = 0;
        ASSERT_EQ(sync_change_decode(buf.data(), buf.size(), &out, &consumed),
                  SYNC_OK);
        EXPECT_EQ(consumed, need);
        EXPECT_EQ(out.kind, c.kind);
        EXPECT_EQ(std::string((char *)out.ns, out.ns_len), ns);
        EXPECT_EQ(std::string((char *)out.entity, out.entity_len), ent);
        if (reg) {
            EXPECT_EQ(std::string((char *)out.field, out.field_len), field);
            EXPECT_EQ(std::string((char *)out.value, out.value_len), value);
            EXPECT_EQ(out.hlc.physical, c.hlc.physical);
            EXPECT_EQ(out.hlc.logical, c.hlc.logical);
        } else {
            EXPECT_EQ(out.causal_length, c.causal_length);
        }
        EXPECT_EQ(0, std::memcmp(out.author, c.author, SYNC_PUBKEY_LEN));
        EXPECT_EQ(0, std::memcmp(out.signature, c.signature, SYNC_SIG_LEN));
        sync_change_free_decoded(&out);
    }
}

/* ---- T3.2 Codec golden vector (endianness-stable) ---------------------- */
TEST(Reconcile, CodecGoldenVector) {
    /* Existence (codec v2): ver=02 kind=00 ns="n" ent="e" cl=3 (LE u64)
     * author=0xAA*32 signature=0xCC*64. */
    {
        std::vector<uint8_t> golden = {0x02, 0x00, 0x01, 0x6E, 0x01, 0x65,
                                       0x03, 0x00, 0x00, 0x00, 0x00, 0x00,
                                       0x00, 0x00};
        for (int i = 0; i < (int)SYNC_PUBKEY_LEN; i++) golden.push_back(0xAA);
        for (int i = 0; i < (int)SYNC_SIG_LEN; i++) golden.push_back(0xCC);

        sync_change c;
        std::memset(&c, 0, sizeof c);
        c.kind = SYNC_CHANGE_EXISTENCE;
        c.ns = (const uint8_t *)"n"; c.ns_len = 1;
        c.entity = (const uint8_t *)"e"; c.entity_len = 1;
        c.causal_length = 3;
        std::memset(c.author, 0xAA, SYNC_PUBKEY_LEN);
        std::memset(c.signature, 0xCC, SYNC_SIG_LEN);
        std::vector<uint8_t> buf(256);
        size_t n = sync_change_encode(&c, buf.data(), buf.size());
        ASSERT_EQ(n, golden.size());
        EXPECT_EQ(0, std::memcmp(buf.data(), golden.data(), n));

        sync_change out;
        size_t consumed = 0;
        ASSERT_EQ(sync_change_decode(golden.data(), golden.size(), &out,
                                     &consumed),
                  SYNC_OK);
        EXPECT_EQ(out.kind, SYNC_CHANGE_EXISTENCE);
        EXPECT_EQ(out.causal_length, 3u);
        sync_change_free_decoded(&out);
    }
    /* Register (codec v2): ... field="f" value="v" phys=2 log=1
     * author=0xAA*32 signature=0xCC*64. */
    {
        std::vector<uint8_t> golden = {0x02, 0x01, 0x01, 0x6E, 0x01, 0x65,
                                       0x01, 0x66, 0x01, 0x76,
                                       0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                       0x01, 0x00, 0x00, 0x00};
        for (int i = 0; i < (int)SYNC_PUBKEY_LEN; i++) golden.push_back(0xAA);
        for (int i = 0; i < (int)SYNC_SIG_LEN; i++) golden.push_back(0xCC);

        sync_change c;
        std::memset(&c, 0, sizeof c);
        c.kind = SYNC_CHANGE_REGISTER;
        c.ns = (const uint8_t *)"n"; c.ns_len = 1;
        c.entity = (const uint8_t *)"e"; c.entity_len = 1;
        c.field = (const uint8_t *)"f"; c.field_len = 1;
        c.value = (const uint8_t *)"v"; c.value_len = 1;
        c.hlc.physical = 2; c.hlc.logical = 1;
        std::memset(c.author, 0xAA, SYNC_PUBKEY_LEN);
        std::memset(c.signature, 0xCC, SYNC_SIG_LEN);

        std::vector<uint8_t> buf(256);
        size_t n = sync_change_encode(&c, buf.data(), buf.size());
        ASSERT_EQ(n, golden.size());
        EXPECT_EQ(0, std::memcmp(buf.data(), golden.data(), n));

        sync_change out;
        size_t consumed = 0;
        ASSERT_EQ(sync_change_decode(golden.data(), golden.size(), &out,
                                     &consumed),
                  SYNC_OK);
        EXPECT_EQ(std::string((char *)out.value, out.value_len), "v");
        EXPECT_EQ(out.hlc.physical, 2u);
        sync_change_free_decoded(&out);
    }
}

/* ---- T3.3 Correctness vs oracle ---------------------------------------- */
TEST(Reconcile, CorrectnessVsOracle) {
    for (int trial = 0; trial < 40; trial++) {
        std::mt19937 ra(1000 + trial * 2), rb(1000 + trial * 2 + 1);
        auto sa = site_from(0x0A), sb = site_from(0x0B);
        sync_engine *a = sync_engine_create(sa.data());
        sync_engine *b = sync_engine_create(sb.data());

        /* Shared base then independent edits. */
        std::mt19937 rbase(trial);
        populate(a, rbase, 20, 2);
        for (auto &o : export_owned(a)) apply_owned(b, o);
        populate(a, ra, 10, 2);
        populate(b, rb, 10, 2);

        Digest oracle = baseline_union(a, b);
        DriveResult dr = drive(a, b);
        EXPECT_TRUE(dr.finished);
        EXPECT_EQ(digest(a), digest(b));
        EXPECT_EQ(digest(a), oracle);

        sync_engine_destroy(a);
        sync_engine_destroy(b);
    }
}

/* ---- T3.4 Difference-proportional transfer ----------------------------- */
TEST(Reconcile, DifferenceProportionalTransfer) {
    std::mt19937 rng(42);
    auto sa = site_from(0x0A), sb = site_from(0x0B);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());

    populate(a, rng, 1000, 2); /* ~3000 elements */
    for (auto &o : export_owned(a)) apply_owned(b, o);

    /* Diverge in k cells. */
    const int k = 10;
    for (int i = 0; i < k; i++) {
        std::string ent = "entity-" + std::to_string(i * 50);
        std::string val = "CHANGED" + std::to_string(i);
        sync_engine_set(b, B(std::string("ns")), 2, B(ent), ent.size(),
                        B(std::string("f0")), 2, B(val), val.size());
    }

    size_t full = full_state_bytes(a);
    DriveResult dr = drive(a, b);
    EXPECT_TRUE(dr.finished);
    EXPECT_EQ(digest(a), digest(b));

    /* Transfer must be a small fraction of full state. */
    EXPECT_LT(dr.bytes * 4, full)
        << "transferred " << dr.bytes << " of full " << full;

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T3.5 Round-trips ~ log16(n) --------------------------------------- */
TEST(Reconcile, RoundTripsLogarithmic) {
    for (int n : {256, 1024, 4096}) {
        std::mt19937 ra(7), rb(8);
        auto sa = site_from(0x0A), sb = site_from(0x0B);
        sync_engine *a = sync_engine_create(sa.data());
        sync_engine *b = sync_engine_create(sb.data());

        /* Fully disjoint worst case drives the deepest recursion. */
        populate(a, ra, n, 1);
        for (int i = 0; i < n; i++) {
            std::string ent = "other-" + std::to_string(i);
            std::string val = "v" + std::to_string(rb() % 1000);
            sync_engine_set(b, B(std::string("ns")), 2, B(ent), ent.size(),
                            B(std::string("f0")), 2, B(val), val.size());
        }

        DriveResult dr = drive(a, b);
        EXPECT_TRUE(dr.finished);
        EXPECT_EQ(digest(a), digest(b));

        double log16 = std::log((double)n) / std::log(16.0);
        /* Generous bound: a small constant times the recursion depth. */
        EXPECT_LT(dr.rounds, (int)(8 * log16 + 30))
            << "n=" << n << " rounds=" << dr.rounds;

        sync_engine_destroy(a);
        sync_engine_destroy(b);
    }
}

/* ---- T3.6 Edge topologies ---------------------------------------------- */
TEST(Reconcile, EdgeIdentical) {
    std::mt19937 rng(11);
    auto sa = site_from(0x0A), sb = site_from(0x0B);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    populate(a, rng, 500, 2);
    for (auto &o : export_owned(a)) apply_owned(b, o);

    DriveResult dr = drive(a, b);
    EXPECT_TRUE(dr.finished);
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_LT(dr.bytes, 1000u) << "identical replicas transferred too much";

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

TEST(Reconcile, EdgeEmptyVsFull) {
    std::mt19937 rng(12);
    auto sa = site_from(0x0A), sb = site_from(0x0B);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    populate(a, rng, 300, 2);

    Digest oracle = baseline_union(a, b);
    DriveResult dr = drive(a, b);
    EXPECT_TRUE(dr.finished);
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(digest(a), oracle);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

TEST(Reconcile, EdgeDisjoint) {
    auto sa = site_from(0x0A), sb = site_from(0x0B);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    for (int i = 0; i < 200; i++) {
        std::string ea = "A-" + std::to_string(i), eb = "B-" + std::to_string(i);
        sync_engine_set(a, B(std::string("ns")), 2, B(ea), ea.size(),
                        B(std::string("f")), 1, B(std::string("x")), 1);
        sync_engine_set(b, B(std::string("ns")), 2, B(eb), eb.size(),
                        B(std::string("f")), 1, B(std::string("y")), 1);
    }
    Digest oracle = baseline_union(a, b);
    DriveResult dr = drive(a, b);
    EXPECT_TRUE(dr.finished);
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(digest(a), oracle);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T3.7 Message robustness (reorder + duplicate) --------------------- */
TEST(Reconcile, MessageRobustness) {
    for (int trial = 0; trial < 10; trial++) {
        std::mt19937 ra(500 + trial), rb(900 + trial), loss(13 + trial);
        auto sa = site_from(0x0A), sb = site_from(0x0B);
        sync_engine *a = sync_engine_create(sa.data());
        sync_engine *b = sync_engine_create(sb.data());

        std::mt19937 rbase(trial);
        populate(a, rbase, 40, 2);
        for (auto &o : export_owned(a)) apply_owned(b, o);
        populate(a, ra, 15, 2);
        populate(b, rb, 15, 2);

        Digest oracle = baseline_union(a, b);
        bool finished = drive_lossy(a, b, loss);
        EXPECT_TRUE(finished) << "lossy drive did not quiesce";
        EXPECT_EQ(digest(a), digest(b));
        EXPECT_EQ(digest(a), oracle);

        sync_engine_destroy(a);
        sync_engine_destroy(b);
    }
}

/* The session snapshot is cached on the engine (keyed by a state generation);
 * this pins that writes/deletes between syncs invalidate it, so a second sync
 * reflects the new state. A missing invalidation would leave the second sync
 * reconciling a stale snapshot and silently failing to propagate. */
TEST(Reconcile, SnapshotCacheInvalidatesOnWrite) {
    sync_engine *a = cluster::make(0x70);
    sync_engine *b = cluster::make(0x71);

    cluster::put(a, "ns", "x", "f", "1");
    cluster::sync2(a, b); /* builds + caches a's snapshot */
    EXPECT_TRUE(cluster::exists(b, "ns", "x"));

    /* Write AFTER the first sync: the cache must be rebuilt next time. */
    cluster::put(a, "ns", "y", "f", "2");
    cluster::sync2(a, b);
    EXPECT_TRUE(cluster::exists(b, "ns", "y")) << "stale snapshot: write not synced";

    /* Overwrite an existing cell, then sync: value must update. */
    cluster::put(a, "ns", "x", "f", "updated");
    cluster::sync2(a, b);
    EXPECT_EQ(cluster::get(b, "ns", "x", "f"), "updated");

    /* Delete, then sync: removal must propagate. */
    cluster::del(a, "ns", "y");
    cluster::sync2(a, b);
    EXPECT_FALSE(cluster::exists(b, "ns", "y")) << "stale snapshot: delete not synced";

    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a);
    sync_engine_destroy(b);
}
