/* scoped_view_test.cpp — Phase 5 (scoped-range-views) merge-gate tests.
 *
 * A peer whose read scope depends on a capability expiry used to be excluded
 * from the per-peer snapshot cache entirely, so every gossip cycle — idle,
 * converged ones included — re-encoded its whole visible set. Such a peer now
 * reconciles over a ReconView: an immutable set of base-index ranges into the
 * engine's shared unscoped snapshot, plus prefix sums over those ranges, cached
 * until the earliest capability expiry it depends on.
 *
 * Scope enforcement therefore rests on index arithmetic rather than on the
 * denied bytes being physically absent from the session's snapshot, so these
 * tests attack that seam directly: wire parity against a dense engine holding
 * exactly the visible subset, adversarial bounds that deliberately span denied
 * namespaces, and the reply-amplification bound (which must be sized from the
 * visible count, never the base). White-box access to the engine's caches
 * follows the gen_split_test/storage_test precedent of including internal
 * headers. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <chrono>
#include <cstring>
#include <memory>
#include <string>
#include <thread>
#include <vector>

#include "capability.h"
#include "cluster.hpp"
#include "engine.hpp"    /* white-box: gens + the two per-peer caches */
#include "recon_wire.hpp"/* the adversarial message vehicle (§3.5 fix 4) */
#include "reconcile.h"   /* kBuckets, for the derived reply bound */

namespace {

using cluster::B;

/* ~2096: far enough out that a finite-expiry capability stays usable for the
 * whole run, while still being finite (so the scope is deadline-bearing). */
constexpr uint64_t kFarFuture = 4000000000000ull;

sync_engine *make(uint32_t seed) { return cluster::make(seed); }

void identity(sync_engine *e, uint8_t out[SYNC_PUBKEY_LEN]) {
    sync_engine_identity(e, out);
}

/* `owner` mints a root for `ns` and `v` accepts it: from here on v enforces
 * that namespace. The caller owns the returned capability. */
sync_capability *own_ns(sync_engine *owner, sync_engine *v, const char *ns) {
    sync_capability *root =
        sync_capability_root(owner, ns, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    EXPECT_NE(root, nullptr);
    EXPECT_SYNC_OK(sync_engine_grant(v, root));
    return root;
}

/* Delegate READ on `root` to `pk`, expiring at `expiry` (0 == never), and
 * install it in v. The caller owns the returned capability. */
sync_capability *grant_read(sync_engine *owner, sync_engine *v,
                            const sync_capability *root,
                            const uint8_t pk[SYNC_PUBKEY_LEN],
                            uint64_t expiry) {
    sync_capability *d =
        sync_capability_delegate(owner, root, pk, SYNC_ACCESS_READ, expiry);
    EXPECT_NE(d, nullptr);
    EXPECT_SYNC_OK(sync_engine_grant(v, d));
    return d;
}

void put(sync_engine *e, const std::string &ns, const std::string &ent,
         const std::string &field, const std::string &val) {
    cluster::put(e, ns, ent, field, val);
}

/* Apply every record exported from src into target, optionally only those in
 * `only_ns`. Seeding two engines from the SAME exported signed records is what
 * makes their element hashes — which cover the author signature — comparable
 * (§3.5 fix 5); two engines that independently "write the same data" never
 * agree on a fingerprint. */
void apply_from(sync_engine *target, sync_engine *src,
                const std::string &only_ns = std::string()) {
    sync_change *recs = nullptr;
    size_t n = 0;
    ASSERT_SYNC_OK(sync_engine_export(src, &recs, &n));
    for (size_t i = 0; i < n; i++) {
        if (!only_ns.empty() &&
            (recs[i].ns_len != only_ns.size() ||
             std::memcmp(recs[i].ns, only_ns.data(), only_ns.size()) != 0))
            continue;
        EXPECT_SYNC_OK(sync_engine_apply(target, &recs[i]));
    }
    sync_changes_free(recs, n);
}

/* Minimal LEB128 reader (codec.cpp put_varint's inverse), local on purpose:
 * the wire assertions must not lean on the codec they are checking. */
bool read_varint(const uint8_t *&p, const uint8_t *end, uint64_t &v) {
    v = 0;
    for (int shift = 0; p < end && shift < 64; shift += 7) {
        uint8_t byte = *p++;
        v |= (uint64_t)(byte & 0x7f) << shift;
        if (!(byte & 0x80)) return true;
    }
    return false;
}

/* Offset of the descriptor section of a session message: the wire form is
 * [caps][revocations][descriptors], and only the descriptors are comparable
 * across engines (a scoped engine attaches capabilities, a bare one does not).
 *
 * SCOPE OF THE LEAK ASSERTIONS IN THIS FILE, stated here once because every one
 * of them goes through this function: read scoping governs the RECONCILIATION
 * ELEMENT SET — the records, their count, and every fingerprint derived from
 * them. It does not govern the [caps]/[revocations] blocks, which are delegation
 * gossip: sync_session_step exports the engine's capability and revocation
 * blobs wholesale on the first message it sends (reconcile.cpp), and those blobs
 * do name namespaces the peer may not read. That is pre-existing, deliberate
 * (a peer must learn delegations to authorize records authored by keys it has
 * not been told about, and revocations must propagate replica-to-replica), and
 * unchanged by this phase. Stripping those two blocks here is therefore not a
 * convenience: it is the boundary of what "no denied existence, bytes, count or
 * fingerprint" claims. A namespace NAME can appear in a capability blob; nothing
 * about its CONTENT may appear anywhere. */
size_t descriptor_offset(const std::string &m) {
    const uint8_t *base = (const uint8_t *)m.data();
    const uint8_t *p = base, *end = base + m.size();
    for (int block = 0; block < 2; block++) {
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

std::string descriptors_of(const std::string &m) {
    size_t off = descriptor_offset(m);
    EXPECT_NE(off, std::string::npos);
    if (off == std::string::npos) return std::string();
    return m.substr(off);
}

/* Number of descriptors a message carries. */
size_t descriptor_count(const std::string &m) {
    size_t off = descriptor_offset(m);
    EXPECT_NE(off, std::string::npos);
    if (off == std::string::npos) return 0;
    const uint8_t *p = (const uint8_t *)m.data() + off;
    const uint8_t *end = (const uint8_t *)m.data() + m.size();
    uint64_t n = 0;
    EXPECT_TRUE(read_varint(p, end, n));
    return (size_t)n;
}

/* Step `s` with `in`, then keep stepping with no input until it stops emitting,
 * so a reply queued across several messages is fully collected. */
std::vector<std::string> feed(sync_session *s, const std::string &in) {
    std::vector<std::string> msgs;
    const uint8_t *ip = in.empty() ? nullptr : (const uint8_t *)in.data();
    uint8_t *o = nullptr;
    size_t   ol = 0;
    int      d = 0;
    EXPECT_SYNC_OK(sync_session_step(s, ip, in.size(), &o, &ol, &d));
    if (ol) msgs.emplace_back((const char *)o, ol);
    if (o) sync_free(o);
    for (int i = 0; i < 4096 && ol != 0; i++) {
        o = nullptr;
        ol = 0;
        d = 0;
        EXPECT_SYNC_OK(sync_session_step(s, nullptr, 0, &o, &ol, &d));
        if (ol) msgs.emplace_back((const char *)o, ol);
        if (o) sync_free(o);
    }
    return msgs;
}

/* Pump two already-begun sessions to quiescence (security_test's `drive`). */
bool drive(sync_session *sa, sync_session *sb) {
    uint8_t *out = nullptr;
    size_t   outlen = 0;
    int      done = 0;
    EXPECT_SYNC_OK(sync_session_step(sa, nullptr, 0, &out, &outlen, &done));
    std::vector<uint8_t> msg(out, out + outlen);
    if (out) sync_free(out);
    sync_session *turn = sb, *other = sa;
    int empties = (outlen == 0) ? 1 : 0;
    for (int i = 0; i < 2000; i++) {
        out = nullptr;
        outlen = 0;
        done = 0;
        EXPECT_SYNC_OK(
            sync_session_step(turn, msg.data(), msg.size(), &out, &outlen, &done));
        std::vector<uint8_t> next(out, out + outlen);
        if (out) sync_free(out);
        empties = (outlen == 0) ? empties + 1 : 0;
        if (empties >= 2) return true;
        msg.swap(next);
        std::swap(turn, other);
    }
    return false;
}

/* Begin and end an unscoped session, which builds the engine's shared unscoped
 * snapshot. This selects which of the two view representations a
 * deadline-bearing peer gets (§3.5 fix 3 — the measured gate in build_view):
 *   warm base -> the view RANGES over the shared unscoped snapshot, which
 *                physically contains every denied element;
 *   cold base -> the view owns a private filtered snapshot spanned by one
 *                range, and the deadline cache works exactly the same way.
 * Every scope assertion in this file has to hold in both, so the tests that
 * care run their body twice. */
void warm_base(sync_engine *e) {
    sync_session *s = sync_session_begin(e, 1);
    EXPECT_NE(s, nullptr);
    sync_session_end(s);
}

/* True if `needle` appears anywhere in `hay` (sentinel scan over raw wire
 * bytes: a denied record leaks whether or not it decodes as a record). */
bool contains(const std::string &hay, const std::string &needle) {
    return hay.find(needle) != std::string::npos;
}

/* A counted reference to the peer's cached view. Tests compare identity through
 * this rather than through a bare pointer: dropping the last reference and then
 * allocating a fresh view very often reuses the same address, so a raw-pointer
 * comparison can report "same object" for two different objects (ABA). Holding
 * the shared_ptr keeps the old object alive, so a rebuild is guaranteed to land
 * somewhere else. shared_ptr<const ReconView> copies fine with ReconView
 * incomplete — the deleter was type-erased when it was created. */
std::shared_ptr<const ke::ReconView> hold_view(sync_engine *e) {
    if (e->scoped_view_cache.empty()) return nullptr;
    return e->scoped_view_cache.begin()->second;
}

/* ---- T1 wire parity ----------------------------------------------------- */
/* A range view must be indistinguishable on the wire from a dense snapshot of
 * exactly the visible elements: same fingerprints, same derived bucket bounds,
 * same descriptor bytes. Both engines are seeded from the SAME exported signed
 * records (§3.5 fix 5) — element hashes cover the author's signature, so two
 * engines that independently write "the same" data can never match. */
void wire_parity_body(bool shared_base) {
    SCOPED_TRACE(shared_base ? "view over the shared unscoped base"
                             : "view over its own filtered base");
    sync_engine *owner = make(0xA1);  /* author of every record + capabilities */
    sync_engine *scoped = make(0xA2); /* enforcer serving a restricted peer */
    sync_engine *dense = make(0xA3);  /* holds exactly the visible subset */
    sync_engine *peer = make(0xA4);
    uint8_t ppk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);

    /* Enough visible elements (9 entities x 2 = 18) that the responder splits
     * into buckets rather than answering with one leaf, so the comparison
     * covers derived bucket bounds and per-bucket fingerprints too. */
    for (int i = 0; i < 9; i++) {
        put(owner, "vis", "e" + std::to_string(i), "f", "v" + std::to_string(i));
        put(owner, "hid", "e" + std::to_string(i), "f", "s" + std::to_string(i));
    }

    sync_capability *rvis = own_ns(owner, scoped, "vis");
    sync_capability *rhid = own_ns(owner, scoped, "hid");
    /* Finite expiry => the peer's scope is deadline-bearing => the view path. */
    sync_capability *dvis = grant_read(owner, scoped, rvis, ppk, kFarFuture);

    apply_from(scoped, owner);          /* both namespaces */
    apply_from(dense, owner, "vis");    /* the visible subset, same records */

    if (shared_base) warm_base(scoped);
    ASSERT_EQ(scoped->recon_cache != nullptr, shared_base)
        << "test bug: the intended view representation is not the one under test";

    /* (a) the initiator's opening whole-range fingerprint. */
    sync_session *ss = sync_session_begin_scoped(scoped, 1, ppk);
    sync_session *ds = sync_session_begin(dense, 1);
    ASSERT_NE(ss, nullptr);
    ASSERT_NE(ds, nullptr);
    std::vector<std::string> smsg = feed(ss, "");
    std::vector<std::string> dmsg = feed(ds, "");
    ASSERT_EQ(smsg.size(), 1u);
    ASSERT_EQ(dmsg.size(), 1u);
    EXPECT_EQ(descriptors_of(smsg[0]), descriptors_of(dmsg[0]))
        << "scoped view's opening fingerprint differs from a dense engine "
           "holding exactly the visible subset";
    sync_session_end(ss);
    sync_session_end(ds);

    /* (b) the responder's split: same crafted whole-range mismatch to both. */
    std::string probe = recon_wire::message(
        {recon_wire::mismatching_fp(recon_wire::Bound::neg(),
                                    recon_wire::Bound::pos())});
    ss = sync_session_begin_scoped(scoped, 0, ppk);
    ds = sync_session_begin(dense, 0);
    ASSERT_NE(ss, nullptr);
    ASSERT_NE(ds, nullptr);
    smsg = feed(ss, probe);
    dmsg = feed(ds, probe);
    ASSERT_FALSE(smsg.empty()) << "the crafted mismatch elicited no reply: the "
                                  "parity check below would be vacuous";
    ASSERT_EQ(smsg.size(), dmsg.size());
    for (size_t i = 0; i < smsg.size(); i++)
        EXPECT_EQ(descriptors_of(smsg[i]), descriptors_of(dmsg[i]))
            << "scoped view's split descriptors differ from the dense engine's "
               "at message " << i;
    /* And the split really happened (16 buckets, not one leaf). */
    EXPECT_GT(descriptor_count(smsg[0]), 1u);
    sync_session_end(ss);
    sync_session_end(ds);

    sync_capability_free(rvis);
    sync_capability_free(rhid);
    sync_capability_free(dvis);
    sync_engine_destroy(owner);
    sync_engine_destroy(scoped);
    sync_engine_destroy(dense);
    sync_engine_destroy(peer);
}

TEST(ScopedView, WireParityWithDenseSubset) {
    wire_parity_body(/*shared_base=*/false);
    wire_parity_body(/*shared_base=*/true);
}

/* ---- T2 the cache actually caches --------------------------------------- */
/* Two consecutive begins for a deadline-bearing peer, with nothing changed in
 * between, must serve the SAME view object — that pointer identity is the whole
 * point of the phase (an idle, converged link costs one map lookup and one
 * deadline compare instead of a full re-encode). The GenPair guard must still
 * fire on a content write. */
TEST(ScopedView, CachedUntilDeadlinePointerIdentity) {
    sync_engine *owner = make(0xB1);
    sync_engine *v = make(0xB2);
    sync_engine *peer = make(0xB3);
    uint8_t ppk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);

    sync_capability *root = own_ns(owner, v, "s");
    sync_capability *rd = grant_read(owner, v, root, ppk, kFarFuture);
    put(v, "s", "e1", "f", "x");
    put(v, "open", "o1", "f", "y");

    sync_session *s1 = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(s1, nullptr);
    ASSERT_EQ(v->scoped_view_cache.size(), 1u)
        << "a deadline-bearing peer must be served from the view cache";
    EXPECT_TRUE(v->scoped_cache.empty())
        << "a deadline-bearing peer must not be filed in the snapshot cache";
    /* Held by shared_ptr, not by address: see hold_view. */
    std::shared_ptr<const ke::ReconView> p0 = hold_view(v);
    ASSERT_NE(p0, nullptr);
    sync_session_end(s1);

    sync_session *s2 = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(s2, nullptr);
    EXPECT_EQ(hold_view(v), p0)
        << "the view was rebuilt with no state change and no deadline passed";
    sync_session_end(s2);

    /* The GenPair guard is independent of the deadline and still fires. */
    const uint64_t sg = v->scope_gen;
    put(v, "open", "o2", "f", "z");
    EXPECT_EQ(v->scope_gen, sg) << "test bug: that write must be content-only";
    sync_session *s3 = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(s3, nullptr);
    EXPECT_NE(hold_view(v), p0) << "a content write did not invalidate the view";
    sync_session_end(s3);

    sync_capability_free(root);
    sync_capability_free(rd);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(peer);
}

/* ---- T2b the source an in-flight session holds is frozen ---------------- */
/* Snapshot immutability for in-flight sessions is a hard invariant of the
 * project, and this phase moves a whole class of sessions off the snapshot the
 * invariant was written for and onto a ReconView -- which owns nothing but
 * indices into a base snapshot the engine is free to throw away underneath it.
 * A write mid-session evicts and replaces exactly that base.
 *
 * Two things make this test able to see that, and both are load-bearing:
 *
 *  (1) The in-flight sessions are RESPONDERS stepped with an empty LEAF over
 *      the whole range, so the reply is a HAVE carrying the visible RECORDS —
 *      i.e. it dereferences `base->snap[base_index(v)]` for every visible
 *      element. An initiator's opening message would not: it carries one
 *      whole-space fingerprint, which ReconView answers out of `cum`/`visible`
 *      alone (vsum(0) and vsum(visible) both short-circuit without touching
 *      `base`), so it is byte-identical for ANY base — live, replaced or freed.
 *  (2) The mid-flight write GROWS THE DENIED NAMESPACE, which sorts before the
 *      visible one, so every base index of the visible range SHIFTS. Appending
 *      to the visible namespace instead would leave range.lo where it was and a
 *      view resolving against the new base would still read the right elements.
 *      With the shift, a view that consulted the engine's current base would
 *      answer with DENIED records — caught below by both the byte-for-byte
 *      comparison and the sentinel scan.
 *
 * (Under ASan the "after" step is additionally a use-after-free probe on the
 * view's base, since `early`/`late` are by then its only owners.) */
TEST(ScopedView, InFlightViewSurvivesTheWriteThatEvictsIt) {
    sync_engine *owner = make(0xB4);
    sync_engine *v = make(0xB5);
    sync_engine *peer = make(0xB6);
    uint8_t ppk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);

    /* "hid" sorts before "vis": growing it shifts the visible range's base
     * offsets. */
    const std::string kSentinel = "SENTINEL-HIDDEN-PAYLOAD";
    put(owner, "hid", "h0", "f", kSentinel + "-0");
    put(owner, "vis", "e0", "f", "VIS-VAL-0");
    put(owner, "vis", "e1", "f", "VIS-VAL-1");
    sync_capability *rv = own_ns(owner, v, "vis");
    sync_capability *rh = own_ns(owner, v, "hid");
    sync_capability *dv = grant_read(owner, v, rv, ppk, kFarFuture);
    apply_from(v, owner);
    /* Shared base: the view then holds nothing but ranges into the very object
     * the write below replaces. */
    warm_base(v);
    ASSERT_NE(v->recon_cache, nullptr);

    /* Responders (see (1) above), and the message that makes them emit records. */
    const std::string ask = recon_wire::message({recon_wire::empty_leaf(
        recon_wire::Bound::neg(), recon_wire::Bound::pos())});
    sync_session *early = sync_session_begin_scoped(v, 0, ppk);
    sync_session *late = sync_session_begin_scoped(v, 0, ppk);
    ASSERT_NE(early, nullptr);
    ASSERT_NE(late, nullptr);
    ASSERT_EQ(v->scoped_view_cache.size(), 1u);
    std::shared_ptr<const ke::ReconView> v0 = hold_view(v);
    ASSERT_NE(v0, nullptr);

    std::vector<std::string> em = feed(early, ask);
    ASSERT_FALSE(em.empty());
    {   /* The reply really carries records, or every assertion below is vacuous. */
        bool saw0 = false, saw1 = false;
        for (const auto &m : em) {
            saw0 |= contains(m, "VIS-VAL-0");
            saw1 |= contains(m, "VIS-VAL-1");
        }
        ASSERT_TRUE(saw0 && saw1)
            << "the probe elicited no visible records: this test would compare "
               "two fingerprints that never dereference the view's base";
    }

    /* The write, then a rebuild of the shared base by an unrelated unscoped
     * consumer. Between them the engine drops BOTH of the objects the two
     * in-flight sessions are reconciling over: the cached view (evicted by the
     * GenPair guard) and the base snapshot it ranges into. `early` and `late`
     * are then the only remaining owners — which is precisely the situation the
     * shared_ptr sources exist for.
     *
     * Two writes, each doing a different job: the DENIED one shifts the visible
     * range's base offsets (see (2) above), the VISIBLE one makes the write
     * observable to a session begun afterwards (non-vacuity, at the bottom). */
    const void *base_before = (const void *)v->recon_cache.get();
    put(owner, "hid", "h1", "f", kSentinel + "-1");
    put(owner, "hid", "h2", "f", kSentinel + "-2");
    put(owner, "vis", "e2", "f", "VIS-VAL-2");
    apply_from(v, owner);
    warm_base(v);
    ASSERT_NE((const void *)v->recon_cache.get(), base_before)
        << "the write did not REPLACE the shared base. Either it did not land "
           "at all (a test bug) or ensure_cache rewrote the cached snapshot in "
           "place (an implementation regression: in-flight sessions hold that "
           "object by shared_ptr precisely so it is never mutated under them)";
    {
        sync_session *probe = sync_session_begin_scoped(v, 0, ppk);
        ASSERT_NE(probe, nullptr);
        EXPECT_NE(hold_view(v), v0)
            << "the write did not evict the cached view either";
        sync_session_end(probe);
    }

    std::vector<std::string> lm = feed(late, ask);
    ASSERT_EQ(lm.size(), em.size())
        << "a session in flight across a write changed its reply shape";
    for (size_t i = 0; i < lm.size(); i++)
        EXPECT_EQ(descriptors_of(lm[i]), descriptors_of(em[i]))
            << "a session in flight across a write did not keep the source it "
               "was begun on, at message " << i;
    /* Stated directly, so the failure names the consequence: a view that
     * resolved against the replaced base would emit the denied namespace's
     * records, because the visible range's base offsets moved. */
    for (const auto &m : lm) {
        EXPECT_FALSE(contains(m, kSentinel))
            << "an in-flight view resolved against a base that had shifted "
               "under it and emitted DENIED records";
        EXPECT_FALSE(contains(m, "VIS-VAL-2"))
            << "an in-flight view picked up an element written after it began";
    }

    /* Non-vacuity: the write really is observable — a session begun after it
     * answers differently. Without this the equality above would hold on an
     * engine that simply never changes. */
    sync_session *fresh = sync_session_begin_scoped(v, 0, ppk);
    ASSERT_NE(fresh, nullptr);
    std::vector<std::string> fm = feed(fresh, ask);
    ASSERT_FALSE(fm.empty());
    bool saw_new = false;
    for (const auto &m : fm) saw_new |= contains(m, "VIS-VAL-2");
    EXPECT_TRUE(saw_new)
        << "the write was invisible even to a session begun after it: the "
           "immutability assertions above prove nothing";
    for (const auto &m : fm)
        EXPECT_FALSE(contains(m, kSentinel))
            << "the denied namespace leaked into a freshly begun session";

    sync_session_end(early);
    sync_session_end(late);
    sync_session_end(fresh);
    for (sync_capability *c : {rv, rh, dv}) sync_capability_free(c);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(peer);
}

/* ---- T2c a revoke drops the cached VIEW, not just the cached snapshot --- */
/* The scope_gen half of the view cache's invalidation, which is what cuts off a
 * REVOKED peer whose read-scoped view is already cached. Every other revocation
 * test in the suite (GenSplit.RevokeDropsCachedScope, SecureMesh.
 * RevokeMidSyncCutsOff) delegates with expiry 0, so its peer is classified
 * deadline == UINT64_MAX and filed under `scoped_cache` — those tests never
 * touch `scoped_view_cache` at all. Here the delegation carries a FINITE
 * expiry, so the peer is on the view path, and the revoke is the only thing
 * that happens: zero content writes across it, so only a scope-driven
 * invalidation can drop the grant-era view.
 *
 * The second peer exists to pin the invalidation as MAP-WIDE: a scope bump must
 * drop every cached view, not just the revoked peer's entry (which would
 * otherwise be replaced on its next begin for the wrong reason and hide the
 * bug). */
TEST(ScopedView, RevokeDropsCachedView) {
    sync_engine *a = make(0x91);  /* owner and enforcer */
    sync_engine *b = make(0x92);  /* peer, READ on "secret" with a finite expiry */
    sync_engine *c = make(0x93);  /* second view-path peer, never revoked */
    uint8_t bpk[SYNC_PUBKEY_LEN], cpk[SYNC_PUBKEY_LEN];
    identity(b, bpk);
    identity(c, cpk);

    sync_capability *root = own_ns(a, a, "secret");
    sync_capability *sroot = own_ns(a, a, "shared");
    sync_capability *rb = grant_read(a, a, root, bpk, kFarFuture);
    sync_capability *rc = grant_read(a, a, sroot, cpk, kFarFuture);
    put(a, "secret", "s1", "f", "secret-value");
    put(a, "shared", "h1", "f", "shared-value");
    put(a, "open", "p1", "f", "open-value");

    /* Grant-era cycle: b genuinely reads "secret", and it is genuinely the VIEW
     * cache it is served from. */
    {
        sync_session *sa = sync_session_begin_scoped(a, 1, bpk);
        sync_session *sb = sync_session_begin(b, 0);
        ASSERT_NE(sa, nullptr);
        ASSERT_NE(sb, nullptr);
        ASSERT_TRUE(drive(sa, sb));
        sync_session_end(sa);
        sync_session_end(sb);
    }
    EXPECT_TRUE(cluster::exists(b, "secret", "s1"))
        << "the grant-era cycle did not deliver the namespace: the cut-off "
           "below would prove nothing";
    { /* c takes the view path too, so the map holds two entries. */
        sync_session *sc = sync_session_begin_scoped(a, 1, cpk);
        ASSERT_NE(sc, nullptr);
        sync_session_end(sc);
    }
    ASSERT_EQ(a->scoped_view_cache.size(), 2u)
        << "a finite-expiry delegation must put the peer on the VIEW path — "
           "otherwise this test exercises the same map the permanent-delegation "
           "revocation tests already cover";
    ASSERT_TRUE(a->scoped_cache.empty())
        << "a deadline-bearing peer must not be filed in the snapshot cache";

    const uint64_t c0 = a->content_gen;
    const uint64_t s0 = a->scope_gen;
    ASSERT_SYNC_OK(sync_engine_revoke(a, "secret", bpk));
    EXPECT_EQ(a->scope_gen, s0 + 1) << "a revoke must bump scope_gen";
    EXPECT_EQ(a->content_gen, c0)
        << "test bug: a revoke must not bump content_gen, or the view would be "
           "dropped by the content half of the guard and the scope half would "
           "stay untested";

    /* One begin for b. If the scope bump cleared the map, c's grant-era entry
     * went with it and only b's rebuild is left; if it cleared nothing (or only
     * the snapshot cache), c's stale entry is still there. */
    {
        sync_session *sa = sync_session_begin_scoped(a, 1, bpk);
        ASSERT_NE(sa, nullptr);
        sync_session_end(sa);
    }
    EXPECT_EQ(a->scoped_view_cache.size(), 1u)
        << "the scope bump did not clear the view cache: a grant-era view for "
           "an untouched peer survived a capability change";

    /* And the security consequence, end to end: a fresh engine holding b's
     * identity must receive "open" and NOT "secret". Zero content writes have
     * happened since the grant-era cycle, so only the revoke's scope bump can
     * have dropped the view that contained "secret". */
    sync_engine *b2 = make(0x92); /* same identity as b */
    sync_session *sv = sync_session_begin_scoped(a, 1, bpk);
    sync_session *sp = sync_session_begin(b2, 0);
    ASSERT_NE(sv, nullptr);
    ASSERT_NE(sp, nullptr);
    ASSERT_TRUE(drive(sv, sp));
    sync_session_end(sv);
    sync_session_end(sp);
    EXPECT_TRUE(cluster::exists(b2, "open", "p1"));
    EXPECT_FALSE(cluster::exists(b2, "secret", "s1"))
        << "a revoked peer was served from a stale cached VIEW";
    EXPECT_EQ(a->content_gen, c0)
        << "test bug: a content write crept in — the cut-off above proves "
           "nothing";

    for (sync_capability *cap : {root, sroot, rb, rc}) sync_capability_free(cap);
    sync_engine_destroy(a);
    sync_engine_destroy(b);
    sync_engine_destroy(c);
    sync_engine_destroy(b2);
}


/* ---- T3 the deadline evicts on its own ---------------------------------- */
/* Capability expiry moves no counter, so the deadline — not a generation bump —
 * has to be what drops the entry. With zero writes and zero capability changes
 * across the expiry, the peer must lose the namespace anyway. */
TEST(ScopedView, DeadlineEvictsWithoutStateGenBump) {
    sync_engine *owner = make(0xC1);
    sync_engine *v = make(0xC2);
    sync_engine *peer = make(0xC3);
    uint8_t ppk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);

    sync_capability *root = own_ns(owner, v, "s");
    sync_capability *rd =
        grant_read(owner, v, root, ppk, ke::now_ms() + 300 /* expires soon */);
    put(v, "s", "e1", "f", "x");

    sync_session *s1 = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(s1, nullptr);
    ASSERT_EQ(v->scoped_view_cache.size(), 1u);
    std::shared_ptr<const ke::ReconView> p0 = hold_view(v);
    ASSERT_NE(p0, nullptr);
    sync_session_end(s1);
    const ke::GenPair g0 = v->gens();

    std::this_thread::sleep_for(std::chrono::milliseconds(450)); /* cross it */

    sync_session *s2 = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(s2, nullptr);
    EXPECT_EQ(v->gens(), g0)
        << "test bug: a state change crept in — the eviction proves nothing";
    EXPECT_TRUE(v->scoped_view_cache.empty())
        << "the expired view was served (or re-cached) past its deadline";
    /* Nothing in "s" is readable now, and the peer's scope is time-stable again
     * (no usable expiring capability is left), so it files under the snapshot
     * cache with an empty visible set. */
    ASSERT_EQ(v->scoped_cache.size(), 1u);
    sync_session_end(s2);

    /* End to end: a fresh peer engine must receive nothing at all. */
    sync_engine *p2 = make(0xC3); /* same identity */
    sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
    sync_session *sp = sync_session_begin(p2, 0);
    ASSERT_TRUE(drive(sv, sp));
    sync_session_end(sv);
    sync_session_end(sp);
    EXPECT_FALSE(cluster::exists(p2, "s", "e1"))
        << "a namespace was served after its read capability expired";

    sync_capability_free(root);
    sync_capability_free(rd);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(peer);
    sync_engine_destroy(p2);
}

/* ---- T4 adversarial bounds ---------------------------------------------- */
/* Scope is now enforced by index arithmetic over a shared base snapshot that
 * physically contains the denied bytes. A peer that asks about ranges spanning
 * a denied namespace — with bounds no honest peer would ever derive — must get
 * back nothing from it: not the records, not their count, not a fingerprint
 * that differs from the empty one. */
void malicious_bounds_body(bool shared_base) {
    SCOPED_TRACE(shared_base ? "view over the shared unscoped base"
                             : "view over its own filtered base");
    sync_engine *owner = make(0xD1);
    sync_engine *v = make(0xD2);
    sync_engine *dense = make(0xD4); /* holds exactly the visible subset */
    sync_engine *peer = make(0xD3);
    uint8_t ppk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);

    /* Four namespaces, denied and readable INTERLEAVED, so the visible set is
     * two disjoint ranges with a denied gap between them:
     *
     *   base:  [ aaa (denied) ][ mmm (visible) ][ sss (denied) ][ zzz (visible) ]
     *   view:                  <--- range 0 --->                <--- range 1 --->
     *
     * That shape is what makes the bounds below adversarial rather than
     * decorative: a bound can land before every range, inside a range, inside
     * the DENIED GAP between two ranges, exactly at the end of the visible set,
     * or past everything — the five places a visible->base off-by-one hides. */
    const std::string kSentinel = "SENTINEL-DENIED-PAYLOAD";
    for (int i = 0; i < 4; i++) {
        std::string n = std::to_string(i);
        put(owner, "aaa", "d" + n, "f", kSentinel + "-aaa-" + n);
        put(owner, "mmm", "o" + n, "f", "visible-mmm-" + n);
        put(owner, "sss", "d" + n, "f", kSentinel + "-sss-" + n);
        put(owner, "zzz", "o" + n, "f", "visible-zzz-" + n);
    }

    sync_capability *ra = own_ns(owner, v, "aaa");
    sync_capability *rm = own_ns(owner, v, "mmm");
    sync_capability *rs = own_ns(owner, v, "sss");
    sync_capability *rz = own_ns(owner, v, "zzz");
    /* Finite expiry => the peer's scope is deadline-bearing => the view path. */
    sync_capability *dm = grant_read(owner, v, rm, ppk, kFarFuture);
    sync_capability *dz = grant_read(owner, v, rz, ppk, kFarFuture);
    apply_from(v, owner);
    /* Same signed records, visible namespaces only: the reference for what an
     * engine that simply DOES NOT HAVE the denied data answers. Element hashes
     * cover the author signature, so this only works because both engines are
     * seeded from owner's exported records (§3.5 fix 5). */
    apply_from(dense, owner, "mmm");
    apply_from(dense, owner, "zzz");

    if (shared_base) warm_base(v);
    ASSERT_EQ(v->recon_cache != nullptr, shared_base)
        << "test bug: the intended view representation is not the one under test";

    sync_session *probe0 = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(probe0, nullptr);
    ASSERT_EQ(v->scoped_view_cache.size(), 1u); /* the peer is on the view path */
    sync_session_end(probe0);

    using recon_wire::Bound;
    struct Probe { const char *what; std::string msg; };
    std::vector<Probe> probes;
    auto fp_probe = [&](const char *what, const Bound &lo, const Bound &hi) {
        probes.push_back({what, recon_wire::message({recon_wire::mismatching_fp(lo, hi)})});
    };
    auto leaf_probe = [&](const char *what, const Bound &lo, const Bound &hi) {
        probes.push_back({what, recon_wire::message({recon_wire::empty_leaf(lo, hi)})});
    };

    fp_probe("whole range FP", Bound::neg(), Bound::pos());
    fp_probe("FP starting inside the first denied namespace",
             Bound::ns_start("aaa"), Bound::ns_start("zzz"));
    fp_probe("FP spanning the denied GAP between two visible ranges",
             Bound::ns_start("mmm"), Bound::ns_start("zzz"));
    fp_probe("FP entirely inside the denied gap",
             Bound::ns_start("sss"), Bound::ns_start("zzz"));
    fp_probe("exact denied element bounds",
             Bound::at("aaa", "d0", true, ""), Bound::at("aaa", "d3", false, "f"));
    fp_probe("bounds landing exactly at v == visible",
             Bound::at("zzz", "o9", true, ""), Bound::pos());
    fp_probe("bounds entirely past every element",
             Bound::ns_start("zzzz"), Bound::pos());
    leaf_probe("empty LEAF over the whole range", Bound::neg(), Bound::pos());
    leaf_probe("empty LEAF over the denied namespace only",
               Bound::ns_start("aaa"), Bound::ns_start("mmm"));
    leaf_probe("empty LEAF over the denied gap",
               Bound::ns_start("sss"), Bound::ns_start("zzz"));
    leaf_probe("empty LEAF with inverted bounds", Bound::pos(), Bound::neg());
    leaf_probe("empty LEAF landing exactly at v == visible",
               Bound::at("zzz", "o9", true, ""), Bound::pos());

    for (const auto &pr : probes) {
        SCOPED_TRACE(pr.what);
        sync_session *s = sync_session_begin_scoped(v, 0, ppk);
        sync_session *ds = sync_session_begin(dense, 0);
        ASSERT_NE(s, nullptr);
        ASSERT_NE(ds, nullptr);
        std::vector<std::string> out = feed(s, pr.msg);
        std::vector<std::string> dout = feed(ds, pr.msg);
        /* (a) no denied BYTES. Raw scan, so a denied record leaks whether or
         *     not it survives as a decodable record. */
        for (const auto &m : out)
            EXPECT_FALSE(contains(m, kSentinel))
                << "denied bytes reached a restricted peer";
        /* (b) no denied COUNT and no denied FINGERPRINT: the answer must be
         *     byte-identical to the one an engine that never held the denied
         *     data gives to the very same crafted message. This is the half
         *     that catches a leak the sentinel scan cannot see — a fingerprint
         *     or a bucket boundary computed over hidden elements carries their
         *     content and their number without carrying their bytes.
         *     (Descriptors only: the [caps]/[revocations] blocks are delegation
         *     gossip and are outside the invariant — see descriptor_offset.) */
        ASSERT_EQ(out.size(), dout.size()) << "reply message count diverges";
        for (size_t i = 0; i < out.size(); i++)
            EXPECT_EQ(descriptors_of(out[i]), descriptors_of(dout[i]))
                << "reply descriptors diverge from a dense engine holding only "
                   "the visible subset, at message " << i;
        sync_session_end(s);
        sync_session_end(ds);
    }

    /* Not vacuous: the same vehicle does elicit the *visible* records, from
     * BOTH visible ranges (so "no leak" is not just "no reply"). */
    {
        sync_session *s = sync_session_begin_scoped(v, 0, ppk);
        ASSERT_NE(s, nullptr);
        std::vector<std::string> out =
            feed(s, recon_wire::message({recon_wire::empty_leaf(
                        Bound::neg(), Bound::pos())}));
        bool saw_mmm = false, saw_zzz = false;
        for (const auto &m : out) {
            saw_mmm |= contains(m, "visible-mmm-0");
            saw_zzz |= contains(m, "visible-zzz-3");
        }
        EXPECT_TRUE(saw_mmm && saw_zzz)
            << "the probe elicited nothing at all: the leak assertions above "
               "would pass on any implementation";
        sync_session_end(s);
    }

    /* End to end, through the real protocol: the peer converges on the visible
     * namespaces only. */
    sync_engine *p2 = make(0xD3);
    sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
    sync_session *sp = sync_session_begin(p2, 0);
    ASSERT_TRUE(drive(sv, sp));
    sync_session_end(sv);
    sync_session_end(sp);
    for (int i = 0; i < 4; i++) {
        std::string n = std::to_string(i);
        EXPECT_TRUE(cluster::exists(p2, "mmm", "o" + n));
        EXPECT_TRUE(cluster::exists(p2, "zzz", "o" + n));
        EXPECT_FALSE(cluster::exists(p2, "aaa", "d" + n));
        EXPECT_FALSE(cluster::exists(p2, "sss", "d" + n));
    }

    for (sync_capability *c : {ra, rm, rs, rz, dm, dz}) sync_capability_free(c);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(dense);
    sync_engine_destroy(peer);
    sync_engine_destroy(p2);
}

TEST(ScopedView, MaliciousBoundsCannotLeakDeniedBytes) {
    /* The shared-base run is the one that matters most: there the denied
     * records are physically present in the very snapshot the session indexes,
     * and only the range arithmetic keeps them out of the reply. */
    malicious_bounds_body(/*shared_base=*/false);
    malicious_bounds_body(/*shared_base=*/true);
}

/* ---- T5 the reply bound is sized from the visible count ----------------- */
/* sync_session_step caps reply descriptors at (elements + 1) * kBuckets + 64.
 * For a scoped session that element count must be the VISIBLE one: sizing it
 * off the base would hand a restricted peer an amplification budget scaled by
 * data it cannot read (and make reply volume a side channel on the hidden
 * count). The peer holds a finite-expiry read capability so it genuinely takes
 * the view path (§3.5 fix 8), and the bound is derived, not hand-picked. */
TEST(ScopedView, ReplyCapUsesVisibleCount) {
    sync_engine *owner = make(0xE1);
    sync_engine *v = make(0xE2);
    sync_engine *peer = make(0xE3);
    uint8_t ppk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);

    put(owner, "vis", "e0", "f", "v0");                 /* 2 visible elements */
    for (int i = 0; i < 99; i++)                        /* 198 hidden ones */
        put(owner, "hid", "e" + std::to_string(i), "f", "h" + std::to_string(i));

    sync_capability *rv = own_ns(owner, v, "vis");
    sync_capability *rh = own_ns(owner, v, "hid");
    sync_capability *dv = grant_read(owner, v, rv, ppk, kFarFuture);
    apply_from(v, owner);
    /* The shared unscoped base is what makes visible != base here: over a
     * private filtered base the two counts coincide and the assertion below
     * could not tell them apart. */
    warm_base(v);
    ASSERT_NE(v->recon_cache, nullptr);

    const size_t kVisible = 2, kBase = 200;
    const size_t derived = (kVisible + 1) * ke::kBuckets + 64 + ke::kBuckets;
    const size_t base_cap = (kBase + 1) * ke::kBuckets + 64;
    /* Companion assertion (§3.5 fix 8): the flood must be big enough that a
     * base-sized cap would have processed all of it, so the two bounds are
     * genuinely distinguishable by this test. */
    const size_t kFlood = 200;
    ASSERT_GT(kFlood, derived);
    ASSERT_GT(base_cap, kFlood);

    std::vector<recon_wire::Desc> flood;
    for (size_t i = 0; i < kFlood; i++)
        flood.push_back(recon_wire::mismatching_fp(recon_wire::Bound::neg(),
                                                   recon_wire::Bound::pos()));
    std::string msg = recon_wire::message(flood);

    sync_session *s = sync_session_begin_scoped(v, 0, ppk);
    ASSERT_NE(s, nullptr);
    ASSERT_EQ(v->scoped_view_cache.size(), 1u)
        << "the peer is not on the view path: the test would be vacuous";
    std::vector<std::string> out = feed(s, msg);
    size_t descs = 0;
    for (const auto &m : out) descs += descriptor_count(m);
    sync_session_end(s);

    EXPECT_LE(descs, derived)
        << "reply amplification was bounded by the base element count ("
        << kBase << "), not the visible one (" << kVisible << ")";
    /* And the cap is what stopped it, not some unrelated early exit: a flood of
     * kFlood whole-range mismatches yields one LEAF each (2 visible elements <=
     * kLeafThreshold), so an uncapped responder would emit kFlood descriptors
     * and a correctly capped one emits ~(kVisible+1)*kBuckets+64. Anything at or
     * below (kVisible+1)*kBuckets means the flood was dropped for some other
     * reason and the LE above proves nothing. */
    EXPECT_GT(descs, (kVisible + 1) * ke::kBuckets)
        << "the flood was cut short by something other than the reply cap: the "
           "upper-bound assertion above would hold vacuously";

    sync_capability_free(rv);
    sync_capability_free(rh);
    sync_capability_free(dv);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(peer);
}

/* ---- T6 the empty view -------------------------------------------------- */
/* A deadline-bearing peer that may read nothing at all: zero ranges, zero
 * visible elements. The whole-space fingerprint must be the empty-set one (byte
 * parity with a bare engine), and the session must be perfectly ordinary. */
TEST(ScopedView, EmptyVisibleSet) {
    sync_engine *owner = make(0xF1);
    sync_engine *v = make(0xF2);
    sync_engine *peer = make(0xF3);  /* denied everywhere */
    sync_engine *other = make(0xF4); /* holds the expiring capability */
    sync_engine *bare = make(0xF5);  /* empty, unscoped: the parity reference */
    uint8_t ppk[SYNC_PUBKEY_LEN], opk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);
    identity(other, opk);

    sync_capability *root = own_ns(owner, v, "s");
    /* The deadline comes from a capability held by someone else: `peer` is
     * denied, and that denial is time-dependent namespace-wide, so it lands on
     * the view path with nothing visible. */
    sync_capability *dother = grant_read(owner, v, root, opk, kFarFuture);
    put(v, "s", "e1", "f", "x");
    put(v, "s", "e2", "f", "y");
    /* Range the empty visible set over a base that is FULL: zero ranges over a
     * non-empty snapshot is the shape where an off-by-one would show. */
    warm_base(v);
    ASSERT_NE(v->recon_cache, nullptr);

    sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(sv, nullptr);
    ASSERT_EQ(v->scoped_view_cache.size(), 1u)
        << "a time-dependent denial must still take the deadline-cached path";
    sync_session *sb = sync_session_begin(bare, 1);
    ASSERT_NE(sb, nullptr);
    std::vector<std::string> vm = feed(sv, "");
    std::vector<std::string> bm = feed(sb, "");
    ASSERT_EQ(vm.size(), 1u);
    ASSERT_EQ(bm.size(), 1u);
    EXPECT_EQ(descriptors_of(vm[0]), descriptors_of(bm[0]))
        << "an empty visible set does not produce the empty-set fingerprint";
    sync_session_end(sv);
    sync_session_end(sb);

    /* And nothing crosses the wire. */
    sync_engine *p2 = make(0xF3);
    sync_session *a = sync_session_begin_scoped(v, 1, ppk);
    sync_session *b = sync_session_begin(p2, 0);
    ASSERT_TRUE(drive(a, b));
    sync_session_end(a);
    sync_session_end(b);
    EXPECT_FALSE(cluster::exists(p2, "s", "e1"));
    EXPECT_FALSE(cluster::exists(p2, "s", "e2"));

    sync_capability_free(root);
    sync_capability_free(dother);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(peer);
    sync_engine_destroy(other);
    sync_engine_destroy(bare);
    sync_engine_destroy(p2);
}

/* ---- T6b a denial that lapses with the clock ---------------------------- */
/* The blocker amendment 1 exists for. `owned()` ignores expiry, so a namespace
 * whose only root capability has a finite expiry is DENIED to everyone with no
 * delegation while the root is usable, and OPEN (no usable root == unowned ==
 * world-readable) the moment it lapses. No grant, no revoke and no write occur
 * across that flip, so neither generation counter moves: a cache that took its
 * deadline only from readable time-bound namespaces would serve the stale
 * denial forever. The expiring root is built directly against CapStore because
 * the public ABI mints only permanent roots — and, deliberately, that insertion
 * bumps no counter either. */
TEST(ScopedView, DenialDeadlineSurvivesRootExpiry) {
    sync_engine *owner = make(0x81);
    sync_engine *v = make(0x82);
    sync_engine *peer = make(0x83); /* holds nothing at all */
    uint8_t ppk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);

    put(v, "s", "e1", "f", "x"); /* local writes bypass write enforcement */

    const uint64_t kExp = ke::now_ms() + 300;
    {
        ke::Capability xr;
        xr.issuer = owner->identity.sign_pk;
        xr.subject = owner->identity.sign_pk; /* issuer == subject == root */
        xr.ns = "s";
        xr.access = ke::kAccessRead | ke::kAccessWrite;
        xr.expiry = kExp;
        std::string sb;
        ke::cap_signing_bytes(xr, sb);
        ke::sign(owner->identity.sign_sk.data(), sb.data(), sb.size(),
                 xr.sig.data());
        ASSERT_TRUE(ke::cap_sig_valid(xr));
        if (!v->caps) v->caps = new ke::CapStore();
        v->caps->add(xr);
    }

    sync_session *s1 = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(s1, nullptr);
    EXPECT_EQ(v->scoped_view_cache.size(), 1u)
        << "a denial that lapses with the clock must carry a deadline";
    EXPECT_TRUE(v->scoped_cache.empty())
        << "the denial was filed as permanent: it will never be revisited";
    sync_session_end(s1);
    const ke::GenPair g0 = v->gens();

    {   /* while the root is usable, the peer is denied */
        sync_engine *p1 = make(0x83);
        sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
        sync_session *sp = sync_session_begin(p1, 0);
        ASSERT_TRUE(drive(sv, sp));
        sync_session_end(sv);
        sync_session_end(sp);
        EXPECT_FALSE(cluster::exists(p1, "s", "e1"));
        sync_engine_destroy(p1);
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(400)); /* root lapses */

    sync_engine *p2 = make(0x83);
    sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
    sync_session *sp = sync_session_begin(p2, 0);
    ASSERT_TRUE(drive(sv, sp));
    sync_session_end(sv);
    sync_session_end(sp);
    EXPECT_EQ(v->gens(), g0)
        << "test bug: a state change crept in — the flip proves nothing";
    EXPECT_TRUE(cluster::exists(p2, "s", "e1"))
        << "the namespace stayed denied after its only root expired: the cache "
           "deadline ignored a time-dependent denial";

    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(peer);
    sync_engine_destroy(p2);
}

/* ---- T7 many ranges, including coalesced ones --------------------------- */
/* Readable and denied namespaces interleaved, with two ADJACENT readable ones
 * that must coalesce into a single range: the boundary shapes where an off-by-
 * one in the visible->base mapping would either hide a readable element or leak
 * a denied one. Under Debug (and every sanitizer leg) the build_view <->
 * build_filtered cross-check runs on each of these shapes. */
void multi_range_body(bool shared_base, const char *shape) {
    /* "pre-warmed" only requests the shared base; a peer that may read
     * everything gets it either way (build_view's share_base gate is
     * `base_is_current(e) || fully_open`), which the all-readable shape below
     * exercises deliberately. */
    SCOPED_TRACE(std::string(shared_base ? "shared base pre-warmed"
                                         : "shared base cold") +
                 ", shape " + shape);
    sync_engine *owner = make(0x71);
    sync_engine *v = make(0x72);
    sync_engine *peer = make(0x73);
    uint8_t ppk[SYNC_PUBKEY_LEN];
    identity(peer, ppk);

    /* `shape` is one character per namespace, 'r'eadable or 'd'enied, in the
     * order the namespaces sort. Adjacent readable namespaces coalesce into one
     * range, so the shape fixes the exact boundary geometry of the view. */
    const size_t kNs = std::strlen(shape);
    ASSERT_EQ(kNs, 6u) << "shapes are written over exactly six namespaces";
    bool readable[6] = {false, false, false, false, false, false};
    for (size_t i = 0; i < kNs; i++) readable[i] = (shape[i] == 'r');
    for (int i = 0; i < 6; i++) {
        std::string ns = "n" + std::to_string(i);
        for (int j = 0; j < 3; j++)
            put(owner, ns, "e" + std::to_string(j), "f",
                ns + "-val" + std::to_string(j));
    }
    std::vector<sync_capability *> caps;
    for (int i = 0; i < 6; i++) {
        std::string ns = "n" + std::to_string(i);
        sync_capability *root = own_ns(owner, v, ns.c_str());
        caps.push_back(root);
        if (readable[i])
            caps.push_back(grant_read(owner, v, root, ppk, kFarFuture));
    }
    apply_from(v, owner);

    if (shared_base) warm_base(v);
    ASSERT_EQ(v->recon_cache != nullptr, shared_base)
        << "test bug: the intended view representation is not the one under test";
    const void *base_before = (const void *)v->recon_cache.get();

    sync_session *probe = sync_session_begin_scoped(v, 1, ppk);
    ASSERT_NE(probe, nullptr);
    ASSERT_EQ(v->scoped_view_cache.size(), 1u);
    sync_session_end(probe);
    if (shared_base) {
        EXPECT_EQ((const void *)v->recon_cache.get(), base_before)
            << "the view rebuilt the shared base instead of ranging over it";
    }

    sync_engine *p2 = make(0x73);
    sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
    sync_session *sp = sync_session_begin(p2, 0);
    ASSERT_NE(sv, nullptr);
    ASSERT_NE(sp, nullptr);
    ASSERT_TRUE(drive(sv, sp)) << "scoped session did not converge";
    sync_session_end(sv);
    sync_session_end(sp);

    for (int i = 0; i < 6; i++) {
        std::string ns = "n" + std::to_string(i);
        for (int j = 0; j < 3; j++) {
            std::string ent = "e" + std::to_string(j);
            EXPECT_EQ(cluster::exists(p2, ns, ent), readable[i])
                << "namespace " << ns << " entity " << ent
                << (readable[i] ? " was withheld" : " leaked");
        }
    }

    for (auto *c : caps) sync_capability_free(c);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(peer);
    sync_engine_destroy(p2);
}

TEST(ScopedView, MultiRangeCoalescingConvergence) {
    /* Every boundary geometry a view can have, so the Debug/sanitizer
     * build_view <-> build_filtered cross-check runs on each of them:
     *   rrdrdr  interior denied runs, a coalesced leading pair (the original)
     *   drrddr  a LEADING denied namespace: range 0 does not start at base 0
     *   rrrrrd  a TRAILING denied namespace: the last range ends before the base
     *   drdrdr  strict alternation: the maximum number of ranges
     *   rrrrrr  everything readable: one range spanning the whole base
     *   drrrrd  denied at both ends, one coalesced range in the middle
     *   ddrddd  a single one-namespace range surrounded by denied ones */
    for (const char *shape : {"rrdrdr", "drrddr", "rrrrrd", "drdrdr", "rrrrrr",
                              "drrrrd", "ddrddd"}) {
        multi_range_body(/*shared_base=*/false, shape);
        /* The shared-base run is the one where the ranges are actually
         * multiple: over a private filtered base the visible set is always one
         * full-span range, whatever the shape. */
        multi_range_body(/*shared_base=*/true, shape);
    }
}

/* ---- T8 the adversarial vehicle's divergence guard has teeth ------------ */
/* Every leak assertion above is only as good as recon_wire's round-trip guard:
 * if `decoder_accepts` said yes to anything, a builder that had drifted from
 * reconcile.cpp's wire format would keep "passing" while exercising nothing.
 * So pin that the guard rejects each way a builder drifts. Only the truncation
 * case survives on length checks alone; the other three hold because
 * decode_message requires CANONICAL framing (`p == end`). An appended field, an
 * under-reported block count, and (in this message's shape) an inserted byte
 * all end with the parse stopping short of the buffer, and a decoder that
 * ignores trailing bytes is blind to exactly the drift a mirrored builder
 * accumulates. */
TEST(ScopedView, WireVehicleGuardIsDiscriminating) {
    const std::string good = recon_wire::message(
        {recon_wire::mismatching_fp(recon_wire::Bound::neg(),
                                    recon_wire::Bound::pos())});
    /* [caps=0][revs=0][ndescs=1][mode][lo][hi][32-byte fp] */
    ASSERT_GE(good.size(), 8u);
    ASSERT_EQ(good[0], '\x00');
    ASSERT_EQ(good[1], '\x00');
    ASSERT_EQ(good[2], '\x01');

    EXPECT_TRUE(recon_wire::decoder_accepts(good))
        << "the builder emits a message the shipping decoder rejects";
    EXPECT_FALSE(recon_wire::decoder_accepts(good.substr(0, good.size() - 4)))
        << "a truncated message was accepted";
    EXPECT_FALSE(recon_wire::decoder_accepts(std::string(good).insert(4, 1, '\x00')))
        << "a message with an extra byte inside a bound was accepted";
    EXPECT_FALSE(recon_wire::decoder_accepts(good + std::string(16, '\xff')))
        << "a message with 16 appended bytes was accepted: the guard cannot see "
           "a wire-format change that APPENDS a field";
    std::string under = good;
    under[2] = '\x00'; /* claim zero descriptors, leaving the descriptor bytes */
    EXPECT_FALSE(recon_wire::decoder_accepts(under))
        << "a message under-reporting its descriptor count was accepted: the "
           "guard cannot see a builder that stops emitting a block";
}

} // namespace
