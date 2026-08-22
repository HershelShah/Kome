/* gen_split_test.cpp — Phase 1 (gen-split) merge-gate tests.
 *
 * state_gen was split into two independent invalidation counters
 * (engine.hpp): content_gen (the element set changed: write / delete /
 * accepted apply / tombstone GC) and scope_gen (who may read or write
 * changed: grant / revoke / wire ingest). The payoff under test: a
 * capability change no longer discards the O(N) unscoped reconcile
 * snapshot (pointer identity + byte-stable fingerprints), while per-peer
 * scoped visibility still refreshes on capability changes alone — with
 * ZERO content writes in between, so nothing but scope_gen can carry the
 * invalidation. White-box access to engine internals (content_gen,
 * scope_gen, recon_cache, scoped_cache) follows the storage_test
 * precedent of including internal headers. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "engine.hpp"  /* white-box: gens + snapshot caches */
#include "tempdir.hpp" /* MEMFS-safe under WASM: NODERAWFS maps /tmp for the
                          test runner exactly as in resilience_test.cpp */

namespace {

using cluster::B;
using synctest::TempDir;

/* The initiator's first session message (whole-range fingerprint, with the
 * engine's capabilities/revocations attached in front). */
std::string first_message(sync_engine *e) {
    sync_session *s = sync_session_begin(e, 1);
    EXPECT_NE(s, nullptr);
    if (!s) return "";
    uint8_t *o = nullptr;
    size_t ol = 0;
    int d = 0;
    EXPECT_SYNC_OK(sync_session_step(s, nullptr, 0, &o, &ol, &d));
    std::string m((const char *)o, ol);
    if (o) sync_free(o);
    sync_session_end(s);
    return m;
}

/* Minimal LEB128 reader (codec.cpp put_varint's inverse), local on purpose:
 * the test must not lean on the codec it is checking the wire against. */
bool read_varint(const uint8_t *&p, const uint8_t *end, uint64_t &v) {
    v = 0;
    for (int shift = 0; p < end && shift < 64; shift += 7) {
        uint8_t byte = *p++;
        v |= (uint64_t)(byte & 0x7f) << shift;
        if (!(byte & 0x80)) return true;
    }
    return false;
}

/* Offset of the descriptor section in a session message. The wire form is
 * [caps][revs][descriptors] (reconcile.cpp encode_message) and a grant grows
 * the leading caps block, so the fingerprint comparison must skip the two
 * varint-counted blocks and compare only the descriptor bytes. npos on
 * malformed input. */
size_t descriptor_offset(const std::string &m) {
    const uint8_t *base = (const uint8_t *)m.data();
    const uint8_t *p = base, *end = base + m.size();
    for (int block = 0; block < 2; block++) { /* caps, then revocations */
        uint64_t cnt = 0;
        if (!read_varint(p, end, cnt)) return std::string::npos;
        for (uint64_t i = 0; i < cnt; i++) {
            uint64_t len = 0;
            if (!read_varint(p, end, len)) return std::string::npos;
            if ((uint64_t)(end - p) < len) return std::string::npos;
            p += len;
        }
    }
    return (size_t)(p - base);
}

/* One full read-scoped reconcile cycle, both sides scoped to the peer's
 * identity (cluster::sync2's pump with sync_session_begin_scoped, the
 * messaging_test/circles_test pattern). */
bool scoped_sync(sync_engine *a, sync_engine *b) {
    uint8_t apk[SYNC_PUBKEY_LEN], bpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(a, apk);
    sync_engine_identity(b, bpk);
    sync_session *sa = sync_session_begin_scoped(a, 1, bpk);
    sync_session *sb = sync_session_begin_scoped(b, 0, apk);
    if (!sa || !sb) {
        sync_session_end(sa);
        sync_session_end(sb);
        return false;
    }
    uint8_t *o = nullptr;
    size_t ol = 0;
    int d = 0;
    sync_session_step(sa, nullptr, 0, &o, &ol, &d);
    std::vector<uint8_t> msg(o, o + ol);
    if (o) sync_free(o);
    sync_session *turn = sb, *other = sa;
    int empties = (ol == 0) ? 1 : 0;
    for (int i = 0; i < 100000 && empties < 2; i++) {
        o = nullptr;
        ol = 0;
        d = 0;
        sync_session_step(turn, msg.data(), msg.size(), &o, &ol, &d);
        std::vector<uint8_t> next(o, o + ol);
        if (o) sync_free(o);
        empties = (ol == 0) ? empties + 1 : 0;
        msg.swap(next);
        std::swap(turn, other);
    }
    sync_session_end(sa);
    sync_session_end(sb);
    return true;
}

/* Whether an entity appears in the exported state at all (a tombstone is
 * still exported as an existence record; a GC'd entity is not). From
 * storage_test's TombstoneGcOnCompaction. */
bool has_entity(sync_engine *e, const char *ent) {
    sync_change *r = nullptr;
    size_t n = 0;
    EXPECT_SYNC_OK(sync_engine_export(e, &r, &n));
    bool found = false;
    for (size_t i = 0; i < n; i++)
        if (std::string((char *)r[i].entity, r[i].entity_len) == ent)
            found = true;
    sync_changes_free(r, n);
    return found;
}

/* Apply an already-expired tombstone for ns/"old": present=false asserted at
 * physical=1 (epoch), signed by `seed`'s identity — kTombstoneTtlMs behind any
 * realistic clock, so the next gc_tombstones purges it (storage_test's
 * TombstoneGcOnCompaction pattern). */
void apply_expired_tombstone(sync_engine *e, uint32_t seed) {
    const std::string ns = "ns", ent = "old";
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_EXISTENCE;
    c.ns = B(ns);
    c.ns_len = ns.size();
    c.entity = B(ent);
    c.entity_len = ent.size();
    c.causal_length = 0; /* present = false */
    c.hlc.physical = 1;
    c.hlc.logical = 0;
    auto s = cluster::seed_from(seed);
    ASSERT_SYNC_OK(sync_change_sign(&c, s.data()));
    ASSERT_SYNC_OK(sync_engine_apply(e, &c));
}

/* ---- The unscoped snapshot survives a capability change ------------------ */
/* A grant bumps scope_gen only; the unscoped snapshot is a pure function of
 * e->ns and is keyed on content_gen alone, so the cached ReconSnapshot object
 * must survive by pointer identity and be reused by the next session. */
TEST(GenSplit, GrantPreservesUnscopedSnapshot) {
    sync_engine *e = cluster::make(0x41);
    cluster::put(e, "secret", "s1", "f", "v");
    cluster::put(e, "open", "p1", "f", "v");

    /* Build (and cache) the unscoped snapshot. */
    {
        sync_session *s = sync_session_begin(e, 1);
        ASSERT_NE(s, nullptr);
        sync_session_end(s);
    }
    /* Hold a reference so a rebuilt snapshot could never reuse this address —
     * pointer equality below therefore means "the same object", not "an
     * allocator coincidence". */
    std::shared_ptr<const ke::ReconSnapshot> keep = e->recon_cache;
    const void *p0 = keep.get();
    ASSERT_NE(p0, nullptr);
    const uint64_t c0 = e->content_gen;
    const uint64_t s0 = e->scope_gen;

    sync_capability *root =
        sync_capability_root(e, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(e, root));

    EXPECT_EQ(e->scope_gen, s0 + 1) << "grant must bump scope_gen";
    EXPECT_EQ(e->content_gen, c0) << "grant must not touch content_gen";
    EXPECT_EQ((const void *)e->recon_cache.get(), p0)
        << "grant discarded the cached unscoped snapshot";

    /* The next session must reuse the cached snapshot, not rebuild it. */
    {
        sync_session *s = sync_session_begin(e, 1);
        ASSERT_NE(s, nullptr);
        sync_session_end(s);
    }
    EXPECT_EQ((const void *)e->recon_cache.get(), p0)
        << "session_begin after a grant rebuilt the still-valid snapshot";

    sync_capability_free(root);
    sync_engine_destroy(e);
}

/* ---- ...and the wire bytes prove it -------------------------------------- */
/* The first session message is [caps][revs][descriptors], and grants grow the
 * caps block — so the whole message legitimately changes across a grant. The
 * invariant is that the descriptor section (the whole-range fingerprint) is
 * byte-identical: gens are never serialized and no byte-producing routine
 * reads them. */
TEST(GenSplit, FirstFingerprintBytesStableAcrossGrant) {
    sync_engine *e = cluster::make(0x42);
    /* Engage the capability system before the baseline so both messages carry
     * a non-empty caps block (the parse below skips real content each time). */
    sync_capability *root =
        sync_capability_root(e, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(e, root));
    cluster::put(e, "secret", "s1", "f", "v");
    cluster::put(e, "open", "p1", "f", "v");

    std::string m1 = first_message(e);
    ASSERT_FALSE(m1.empty());

    /* Grant a read delegation: the caps block grows, the content does not. */
    uint8_t sub[SYNC_PUBKEY_LEN];
    std::memset(sub, 0x42, sizeof sub);
    sync_capability *d =
        sync_capability_delegate(e, root, sub, SYNC_ACCESS_READ, 0);
    ASSERT_NE(d, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(e, d));

    std::string m2 = first_message(e);
    ASSERT_FALSE(m2.empty());

    size_t o1 = descriptor_offset(m1);
    size_t o2 = descriptor_offset(m2);
    ASSERT_NE(o1, std::string::npos);
    ASSERT_NE(o2, std::string::npos);
    ASSERT_LT(o1, m1.size());
    ASSERT_LT(o2, m2.size());
    /* Non-vacuity: the grant really did grow the leading blocks — comparing
     * whole messages would (correctly) fail, so the skip is load-bearing. */
    EXPECT_GT(o2, o1) << "second grant did not grow the caps block";
    EXPECT_NE(m1, m2) << "expected the raw messages to differ by the caps block";

    EXPECT_EQ(m1.substr(o1), m2.substr(o2))
        << "descriptor section (fingerprint bytes) changed across a grant";

    sync_capability_free(root);
    sync_capability_free(d);
    sync_engine_destroy(e);
}

/* ---- The inverse: a write really does rebuild ---------------------------- */
TEST(GenSplit, WriteRebuildsSnapshot) {
    sync_engine *e = cluster::make(0x43);
    cluster::put(e, "ns", "e1", "f", "v");
    {
        sync_session *s = sync_session_begin(e, 1);
        ASSERT_NE(s, nullptr);
        sync_session_end(s);
    }
    std::shared_ptr<const ke::ReconSnapshot> keep = e->recon_cache;
    ASSERT_NE(keep.get(), nullptr);
    const uint64_t c0 = e->content_gen;
    const uint64_t s0 = e->scope_gen;

    cluster::put(e, "ns", "e2", "f", "v");
    EXPECT_EQ(e->content_gen, c0 + 1) << "a set must bump content_gen";
    EXPECT_EQ(e->scope_gen, s0) << "a set must not touch scope_gen";

    {
        sync_session *s = sync_session_begin(e, 1);
        ASSERT_NE(s, nullptr);
        sync_session_end(s);
    }
    EXPECT_NE(e->recon_cache.get(), keep.get())
        << "stale snapshot served after a content write";

    /* And the rebuilt snapshot is itself cached (stable until the next write). */
    const void *p1 = e->recon_cache.get();
    {
        sync_session *s = sync_session_begin(e, 1);
        ASSERT_NE(s, nullptr);
        sync_session_end(s);
    }
    EXPECT_EQ((const void *)e->recon_cache.get(), p1);

    sync_engine_destroy(e);
}

/* ---- Scoped visibility refreshes on a grant alone ------------------------ */
/* Between the two cycles there is NO content write on the owner: the newly
 * granted namespace becomes visible purely because the grant's scope_gen bump
 * invalidates the cached per-peer scoped snapshot. */
TEST(GenSplit, GrantRefreshesScopedSession) {
    sync_engine *a = cluster::make(0x51); /* owner/enforcer */
    sync_engine *b = cluster::make(0x52); /* peer */
    uint8_t bpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(b, bpk);

    sync_capability *root =
        sync_capability_root(a, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(a, root));
    cluster::put(a, "secret", "s1", "f", "v");
    cluster::put(a, "open", "p1", "f", "v");

    /* Cycle 1: b may read "open" only; a caches b's scoped snapshot. */
    ASSERT_TRUE(scoped_sync(a, b));
    EXPECT_TRUE(cluster::exists(b, "open", "p1"));
    EXPECT_FALSE(cluster::exists(b, "secret", "s1"));
    ASSERT_FALSE(a->scoped_cache.empty())
        << "per-peer scoped cache not engaged: the refresh below would be vacuous";

    const uint64_t c0 = a->content_gen;
    const uint64_t s0 = a->scope_gen;
    sync_capability *readB =
        sync_capability_delegate(a, root, bpk, SYNC_ACCESS_READ, 0);
    ASSERT_NE(readB, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(a, readB));
    EXPECT_EQ(a->scope_gen, s0 + 1);
    EXPECT_EQ(a->content_gen, c0);

    /* Cycle 2, zero content writes in between: the grant alone must have
     * dropped the cached scope, so "secret" is now served. */
    ASSERT_TRUE(scoped_sync(a, b));
    EXPECT_TRUE(cluster::exists(b, "secret", "s1"))
        << "grant did not refresh the cached per-peer scope";
    EXPECT_EQ(a->content_gen, c0)
        << "test bug: a content write crept in — the refresh above proves nothing";

    sync_capability_free(root);
    sync_capability_free(readB);
    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- Scoped visibility refreshes on a revoke alone (security direction) -- */
/* After the revoke — again with zero content writes — a fresh peer holding the
 * revoked identity must NOT be served the namespace. If the revoke failed to
 * bump scope_gen, ensure_scoped_cache would hit the stale grant-era cache
 * entry (which includes "secret") and leak it. */
TEST(GenSplit, RevokeDropsCachedScope) {
    sync_engine *a = cluster::make(0x61); /* owner/enforcer */
    sync_engine *b = cluster::make(0x62); /* peer, delegated READ */
    uint8_t bpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(b, bpk);

    sync_capability *root =
        sync_capability_root(a, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(a, root));
    sync_capability *readB =
        sync_capability_delegate(a, root, bpk, SYNC_ACCESS_READ, 0);
    ASSERT_NE(readB, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(a, readB));
    cluster::put(a, "secret", "s1", "f", "v");
    cluster::put(a, "open", "p1", "f", "v");

    /* Grant-era cycle: b reads "secret"; a caches b's (open) scope. */
    ASSERT_TRUE(scoped_sync(a, b));
    EXPECT_TRUE(cluster::exists(b, "secret", "s1"));
    ASSERT_FALSE(a->scoped_cache.empty())
        << "per-peer scoped cache not engaged: the drop below would be vacuous";

    const uint64_t c0 = a->content_gen;
    const uint64_t s0 = a->scope_gen;
    ASSERT_SYNC_OK(sync_engine_revoke(a, "secret", bpk));
    EXPECT_EQ(a->scope_gen, s0 + 1);
    EXPECT_EQ(a->content_gen, c0);

    /* A fresh, empty engine with b's identity syncs. Zero content writes since
     * the grant-era cycle: only the revoke's scope_gen bump can have dropped
     * the cached scope that contained "secret". */
    sync_engine *b2 = cluster::make(0x62); /* same identity as b */
    ASSERT_TRUE(scoped_sync(a, b2));
    EXPECT_TRUE(cluster::exists(b2, "open", "p1"));
    EXPECT_FALSE(cluster::exists(b2, "secret", "s1"))
        << "revoked peer was served from the stale cached scope";
    EXPECT_EQ(a->content_gen, c0)
        << "test bug: a content write crept in — the cut-off above proves nothing";

    sync_capability_free(root);
    sync_capability_free(readB);
    sync_engine_destroy(a);
    sync_engine_destroy(b);
    sync_engine_destroy(b2);
}

/* ---- Digest invariance --------------------------------------------------- */
/* Invariant guard, not a discriminator: sync_engine_digest never covered
 * capabilities, so this pins that the gen-split did not accidentally wire a
 * gen (or any capability state) into a byte-producing routine. */
TEST(GenSplit, DigestUnchangedByGrant) {
    sync_engine *e = cluster::make(0x44);
    cluster::put(e, "secret", "s1", "f", "v");
    cluster::put(e, "open", "p1", "f", "v");
    cluster::Digest d0 = cluster::digest(e);

    sync_capability *root =
        sync_capability_root(e, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(e, root));
    EXPECT_EQ(cluster::digest(e), d0) << "digest changed across a grant";

    uint8_t sub[SYNC_PUBKEY_LEN];
    std::memset(sub, 0x24, sizeof sub);
    sync_capability *d =
        sync_capability_delegate(e, root, sub, SYNC_ACCESS_READ, 0);
    ASSERT_NE(d, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(e, d));
    EXPECT_EQ(cluster::digest(e), d0) << "digest changed across a delegation";

    ASSERT_SYNC_OK(sync_engine_revoke(e, "secret", sub));
    EXPECT_EQ(cluster::digest(e), d0) << "digest changed across a revoke";

    sync_capability_free(root);
    sync_capability_free(d);
    sync_engine_destroy(e);
}

/* ---- Tombstone GC is a content change (direct compact path) -------------- */
/* gc_tombstones (storage.cpp) erases entities from the element universe, so it
 * must bump content_gen — and only content_gen — or the cached reconcile
 * snapshot would keep serving GC'd entities. Store-backed via TempDir, which
 * is MEMFS-safe under the WASM leg (NODERAWFS, resilience_test's pattern). */
TEST(GenSplit, CompactTombstoneGcBumpsContent) {
    TempDir dir;
    std::string db = dir.file("gc.db");
    auto site = cluster::seed_from(0x71);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    cluster::put(e, "ns", "live", "f", "v"); /* live entity -> kept */
    apply_expired_tombstone(e, 0x72);
    ASSERT_TRUE(has_entity(e, "old"));

    const uint64_t c0 = e->content_gen;
    const uint64_t s0 = e->scope_gen;
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK); /* forces gc_tombstones */

    EXPECT_FALSE(has_entity(e, "old")) << "expired tombstone not purged";
    EXPECT_TRUE(has_entity(e, "live"));
    EXPECT_EQ(e->content_gen, c0 + 1)
        << "tombstone GC removed entities without bumping content_gen";
    EXPECT_EQ(e->scope_gen, s0) << "tombstone GC is content, not scope";

    /* Control: a compaction with nothing to purge must not bump either gen. */
    const uint64_t c1 = e->content_gen;
    ASSERT_EQ(sync_engine_compact(e), SYNC_OK);
    EXPECT_EQ(e->content_gen, c1) << "no-removal GC must not bump content_gen";
    EXPECT_EQ(e->scope_gen, s0);

    sync_engine_destroy(e);
}

/* ---- Tombstone GC is a content change (mid-session batch_commit path) ---- */
/* gc_tombstones is also reached mid-session: apply_records (reconcile.cpp)
 * stages a multi-record batch, and Storage::batch_commit runs maybe_compact
 * once the log outgrows its threshold — compacting (and GC'ing) between two
 * reconcile messages while the session is in flight. The classification must
 * hold on that path too. The transfer volume below (~240 records, 2 KiB
 * values) is sized to push the fresh log well past the 64 KiB compaction
 * threshold several times over. */
TEST(GenSplit, BatchCommitTombstoneGcBumpsContent) {
    TempDir dir;
    std::string db = dir.file("batchgc.db");
    auto site = cluster::seed_from(0x73);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    apply_expired_tombstone(e, 0x74);
    ASSERT_TRUE(has_entity(e, "old"));

    /* An in-memory feeder with enough bulk that the session's batched applies
     * grow the store past the compaction threshold mid-session. */
    sync_engine *src = cluster::make(0x75);
    const int kEntities = 120;
    const std::string big(2048, 'x');
    for (int i = 0; i < kEntities; i++)
        cluster::put(src, "bulk", "e" + std::to_string(i), "f", big);

    const uint64_t c0 = e->content_gen;
    const uint64_t s0 = e->scope_gen;
    cluster::sync2(src, e);

    /* The GC ran without any explicit sync_engine_compact call — the only
     * route is batch_commit -> maybe_compact -> compact -> gc_tombstones. */
    EXPECT_FALSE(has_entity(e, "old"))
        << "batch_commit-triggered compaction did not GC the expired tombstone";
    EXPECT_TRUE(cluster::exists(e, "bulk", "e0"));
    EXPECT_TRUE(cluster::exists(e, "bulk", "e" + std::to_string(kEntities - 1)));

    /* Exact accounting: each of src's records (one existence + one register
     * per entity) is accepted exactly once (re-deliveries are dominated ->
     * no bump), plus exactly one bump from the mid-session GC removal. */
    EXPECT_EQ(e->content_gen, c0 + 2u * kEntities + 1)
        << "mid-session gc_tombstones misclassified or miscounted";
    EXPECT_EQ(e->scope_gen, s0) << "tombstone GC is content, not scope";

    sync_engine_destroy(src);
    sync_engine_destroy(e);
}

} // namespace
