/* convergence_test.cpp — the M1 regression oracle.
 *
 * Verifies the semilattice properties of the convergent core: order
 * independence, idempotence, two-way convergence, delete vs concurrent edit,
 * LWW determinism, re-add after delete, HLC receive monotonicity, and
 * tombstone/value independence. Re-run by every later milestone; never weaken.
 *
 * All randomized tests use fixed seeds and, on failure, print the seed and the
 * diverging digests so a failure is reproducible (T1.8). */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstring>
#include <random>
#include <string>
#include <vector>

namespace {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;

/* A self-owning copy of a change record, so we can shuffle / duplicate freely. */
struct OwnedChange {
    uint8_t     kind = 0;
    std::string ns, entity, field, value;
    uint64_t    causal_length = 0;
    sync_hlc    hlc{};
    std::array<uint8_t, SYNC_PUBKEY_LEN> author{};
    std::array<uint8_t, SYNC_SIG_LEN>    signature{};
};

OwnedChange own(const sync_change &c) {
    OwnedChange o;
    o.kind = c.kind;
    o.ns.assign((const char *)c.ns, c.ns_len);
    o.entity.assign((const char *)c.entity, c.entity_len);
    if (c.field) o.field.assign((const char *)c.field, c.field_len);
    if (c.value) o.value.assign((const char *)c.value, c.value_len);
    o.causal_length = c.causal_length;
    o.hlc = c.hlc;
    std::memcpy(o.author.data(), c.author, SYNC_PUBKEY_LEN);
    std::memcpy(o.signature.data(), c.signature, SYNC_SIG_LEN);
    return o;
}

sync_change view(const OwnedChange &o) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = o.kind;
    c.ns = (const uint8_t *)o.ns.data();       c.ns_len = o.ns.size();
    c.entity = (const uint8_t *)o.entity.data(); c.entity_len = o.entity.size();
    c.field = (const uint8_t *)o.field.data();  c.field_len = o.field.size();
    c.value = (const uint8_t *)o.value.data();  c.value_len = o.value.size();
    c.causal_length = o.causal_length;
    c.hlc = o.hlc;
    std::memcpy(c.author, o.author.data(), SYNC_PUBKEY_LEN);
    std::memcpy(c.signature, o.signature.data(), SYNC_SIG_LEN);
    return c;
}

Digest digest(sync_engine *e) {
    Digest d{};
    EXPECT_EQ(sync_engine_digest(e, d.data()), SYNC_OK);
    return d;
}

std::vector<OwnedChange> export_owned(sync_engine *e) {
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_EQ(sync_engine_export(e, &recs, &n), SYNC_OK);
    std::vector<OwnedChange> out;
    out.reserve(n);
    for (size_t i = 0; i < n; i++) out.push_back(own(recs[i]));
    sync_changes_free(recs, n);
    return out;
}

void apply_owned(sync_engine *e, const OwnedChange &o) {
    sync_change c = view(o);
    EXPECT_EQ(sync_engine_apply(e, &c), SYNC_OK);
}

/* Replicate the entire state of `from` into `into`. */
void replicate(sync_engine *from, sync_engine *into) {
    for (auto &o : export_owned(from)) apply_owned(into, o);
}

std::array<uint8_t, SYNC_SITE_ID_LEN> site_from(uint8_t seed) {
    std::array<uint8_t, SYNC_SITE_ID_LEN> s{};
    for (auto &b : s) b = seed;
    return s;
}

const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

/* Drive a sequence of random local ops against an engine. Small key space so
 * keys collide across replicas. */
void random_ops(sync_engine *e, std::mt19937 &rng, int count) {
    const char *nss[] = {"a", "b"};
    for (int i = 0; i < count; i++) {
        std::string ns = nss[rng() % 2];
        std::string ent = "e" + std::to_string(rng() % 6);
        if (rng() % 5 == 0) {
            sync_engine_delete(e, B(ns), ns.size(), B(ent), ent.size());
        } else {
            std::string field = "f" + std::to_string(rng() % 3);
            std::string val = "v" + std::to_string(rng() % 100);
            sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(),
                            B(field), field.size(), B(val), val.size());
        }
    }
}

} // namespace

/* ---- T1.1 Order-independence + idempotence ----------------------------- */
TEST(Convergence, OrderIndependenceAndIdempotence) {
    const unsigned seed = 0x11111111u;
    std::mt19937 gen(seed);

    /* Build a fixed record set from a source replica. */
    auto src_site = site_from(0x01);
    sync_engine *src = sync_engine_create(src_site.data());
    random_ops(src, gen, 200);
    std::vector<OwnedChange> recs = export_owned(src);
    sync_engine_destroy(src);

    Digest reference{};
    bool have_ref = false;

    for (int trial = 0; trial < 300; trial++) {
        std::mt19937 trng(seed + trial);
        std::vector<OwnedChange> order = recs;
        /* Insert arbitrary duplicates. */
        size_t dups = order.size() / 4;
        for (size_t k = 0; k < dups && !recs.empty(); k++)
            order.push_back(recs[trng() % recs.size()]);
        std::shuffle(order.begin(), order.end(), trng);

        auto site = site_from(0x02);
        sync_engine *e = sync_engine_create(site.data());
        for (auto &o : order) apply_owned(e, o);
        Digest d = digest(e);
        sync_engine_destroy(e);

        if (!have_ref) {
            reference = d;
            have_ref = true;
        } else {
            ASSERT_EQ(d, reference)
                << "order-dependence at trial " << trial << " seed " << seed;
        }
    }
}

/* ---- T1.2 Two-way convergence ------------------------------------------ */
TEST(Convergence, TwoWayConvergence) {
    const unsigned base = 0x22222222u;
    for (int trial = 0; trial < 300; trial++) {
        std::mt19937 ra(base + trial * 2);
        std::mt19937 rb(base + trial * 2 + 1);

        auto sa = site_from(0x0A), sb = site_from(0x0B);
        sync_engine *a = sync_engine_create(sa.data());
        sync_engine *b = sync_engine_create(sb.data());

        random_ops(a, ra, 40);
        random_ops(b, rb, 40);

        /* Exchange all records both ways. */
        replicate(a, b);
        replicate(b, a);
        /* A second round is a no-op if convergent. */
        replicate(a, b);
        replicate(b, a);

        ASSERT_EQ(digest(a), digest(b))
            << "divergence at trial " << trial << " base seed " << base;

        sync_engine_destroy(a);
        sync_engine_destroy(b);
    }
}

/* ---- T1.3 Delete vs concurrent edit ------------------------------------ */
TEST(Convergence, DeleteVsConcurrentEdit) {
    auto sa = site_from(0x0A), sb = site_from(0x0B);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());

    std::string ns = "n", ent = "x", f1 = "f1", f2 = "f2";
    /* Both start with the entity present. */
    sync_engine_set(a, B(ns), 1, B(ent), 1, B(f1), 2, B("init"), 4);
    replicate(a, b);

    /* Concurrent: A deletes the entity, B edits a different field. */
    sync_engine_delete(a, B(ns), 1, B(ent), 1);
    sync_engine_set(b, B(ns), 1, B(ent), 1, B(f2), 2, B("edit"), 4);

    /* Converge in both orders by exchanging everything twice. */
    replicate(a, b);
    replicate(b, a);
    replicate(a, b);
    replicate(b, a);

    ASSERT_EQ(digest(a), digest(b));

    int ea = 1, eb = 1;
    sync_engine_exists(a, B(ns), 1, B(ent), 1, &ea);
    sync_engine_exists(b, B(ns), 1, B(ent), 1, &eb);
    /* Delete (causal_length -> 2) dominates the concurrent edit (stays 1). */
    EXPECT_EQ(ea, 0);
    EXPECT_EQ(eb, 0);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T1.4 LWW determinism ---------------------------------------------- */
TEST(Convergence, LwwDeterminism) {
    auto sa = site_from(0x0A), sb = site_from(0x0B); /* B's site_id is larger */
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());

    std::string ns = "n", ent = "x", f = "f";
    sync_engine_set(a, B(ns), 1, B(ent), 1, B(f), 1, B("AAA"), 3);
    sync_engine_set(b, B(ns), 1, B(ent), 1, B(f), 1, B("BBB"), 3);

    /* Apply in opposite orders on each replica. */
    replicate(a, b); /* b now sees a's write */
    replicate(b, a); /* a now sees b's write */

    ASSERT_EQ(digest(a), digest(b)) << "LWW merge order dependence";

    uint8_t *va = nullptr, *vb = nullptr;
    size_t la = 0, lb = 0;
    ASSERT_EQ(sync_engine_get(a, B(ns), 1, B(ent), 1, B(f), 1, &va, &la), SYNC_OK);
    ASSERT_EQ(sync_engine_get(b, B(ns), 1, B(ent), 1, B(f), 1, &vb, &lb), SYNC_OK);
    ASSERT_EQ(la, lb);
    EXPECT_EQ(0, std::memcmp(va, vb, la)) << "replicas chose different winners";
    sync_free(va);
    sync_free(vb);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T1.5 Re-add after delete ------------------------------------------ */
TEST(Convergence, ReAddAfterDelete) {
    auto s = site_from(0x0A);
    sync_engine *e = sync_engine_create(s.data());
    std::string ns = "n", ent = "x", f = "f";

    auto present = [&]() {
        int p = 0;
        sync_engine_exists(e, B(ns), 1, B(ent), 1, &p);
        return p;
    };

    sync_engine_set(e, B(ns), 1, B(ent), 1, B(f), 1, B("1"), 1); /* cl=1 */
    EXPECT_EQ(present(), 1);
    sync_engine_delete(e, B(ns), 1, B(ent), 1); /* cl=2 */
    EXPECT_EQ(present(), 0);
    sync_engine_set(e, B(ns), 1, B(ent), 1, B(f), 1, B("2"), 1); /* cl=3 */
    EXPECT_EQ(present(), 1);

    /* Converges when replicated to a fresh replica. */
    auto s2 = site_from(0x0B);
    sync_engine *e2 = sync_engine_create(s2.data());
    replicate(e, e2);
    EXPECT_EQ(digest(e), digest(e2));
    int p2 = 0;
    sync_engine_exists(e2, B(ns), 1, B(ent), 1, &p2);
    EXPECT_EQ(p2, 1);

    sync_engine_destroy(e);
    sync_engine_destroy(e2);
}

/* ---- T1.6 HLC receive monotonicity ------------------------------------- */
TEST(Convergence, HlcReceiveMonotonicity) {
    auto s = site_from(0x0A);
    sync_engine *e = sync_engine_create(s.data());
    std::string ns = "n", ent = "x", f = "f";

    /* Apply a remote register with a far-future physical clock, signed by a
     * different identity. */
    sync_change remote;
    std::memset(&remote, 0, sizeof remote);
    remote.kind = SYNC_CHANGE_REGISTER;
    remote.ns = B(ns); remote.ns_len = ns.size();
    remote.entity = B(ent); remote.entity_len = ent.size();
    remote.field = B(f); remote.field_len = f.size();
    remote.value = (const uint8_t *)"remote"; remote.value_len = 6;
    remote.hlc.physical = (uint64_t)4000000000000ull; /* far future ms */
    remote.hlc.logical = 5;
    auto rseed = site_from(0xFF);
    ASSERT_EQ(sync_change_sign(&remote, rseed.data()), SYNC_OK);
    ASSERT_EQ(sync_engine_apply(e, &remote), SYNC_OK);

    /* A subsequent local write to the same cell must win (strictly greater HLC). */
    sync_engine_set(e, B(ns), 1, B(ent), 1, B(f), 1, B("local"), 5);

    uint8_t *v = nullptr;
    size_t l = 0;
    ASSERT_EQ(sync_engine_get(e, B(ns), 1, B(ent), 1, B(f), 1, &v, &l), SYNC_OK);
    ASSERT_EQ(std::string((char *)v, l), "local")
        << "local write after a future remote did not win";
    sync_free(v);

    /* Confirm the exported register's HLC strictly exceeds the remote's. */
    for (auto &o : export_owned(e)) {
        if (o.kind == SYNC_CHANGE_REGISTER && o.field == f) {
            bool greater = (o.hlc.physical > remote.hlc.physical) ||
                           (o.hlc.physical == remote.hlc.physical &&
                            o.hlc.logical > remote.hlc.logical);
            EXPECT_TRUE(greater) << "HLC not monotonic on receive";
        }
    }

    sync_engine_destroy(e);
}

/* ---- T1.7 Tombstone/value independence --------------------------------- */
TEST(Convergence, TombstoneValueIndependence) {
    auto sa = site_from(0x0A), sb = site_from(0x0B);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    std::string ns = "n", ent = "x", f = "f";

    sync_engine_set(a, B(ns), 1, B(ent), 1, B(f), 1, B("val"), 3);
    sync_engine_delete(a, B(ns), 1, B(ent), 1);

    replicate(a, b);

    /* get/exists filter on presence. */
    uint8_t *v = nullptr;
    size_t l = 0;
    EXPECT_EQ(sync_engine_get(a, B(ns), 1, B(ent), 1, B(f), 1, &v, &l),
              SYNC_ERR_NOTFOUND);
    int p = 1;
    sync_engine_exists(a, B(ns), 1, B(ent), 1, &p);
    EXPECT_EQ(p, 0);

    /* But the register is retained under the tombstone and shipped in export. */
    bool found_reg = false;
    for (auto &o : export_owned(a))
        if (o.kind == SYNC_CHANGE_REGISTER && o.field == f && o.value == "val")
            found_reg = true;
    EXPECT_TRUE(found_reg) << "register lost under tombstone";

    /* Both replicas agree on tombstone AND stored register. */
    EXPECT_EQ(digest(a), digest(b));

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- ABI sanity -------------------------------------------------------- */
TEST(Convergence, AbiVersion) {
    EXPECT_EQ(sync_abi_version(), SYNC_ABI_VERSION);
}
