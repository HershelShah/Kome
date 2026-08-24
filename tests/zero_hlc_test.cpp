/* zero_hlc_test.cpp — regression tests for the zero-HLC phantom-existence bug
 * and for the digest/RBSR agreement that fixing it depends on.
 *
 * THE BUG (pre-fix behaviour, reproduced on master @ f0e819a):
 *   ke::Entity::asserted() (src/engine.hpp) DERIVES "does this entity carry a
 *   presence assertion?" from presence_hlc != {0,0} rather than storing a bit.
 *   apply_change's EXISTENCE branch compared (hlc, author) against a synthesised
 *   {0,0} + kZeroAuthor tuple for an absent cell, so an incoming record stamped
 *   {0,0} TIED on HLC and WON the memcmp tie-break for any real public key. It
 *   then committed present_v / ex_author / ex_sig onto a cell asserted() still
 *   reported as unasserted, and four subsystems disagreed about one cell:
 *     sync_engine_exists -> 1        (reads present_v)
 *     sync_engine_digest -> moved    (hashed every entity, asserted or not)
 *     build_snapshot     -> nothing  (emits only asserted() cells)
 *     reopen             -> dropped  (apply_entry re-derives asserted())
 *
 * THE FIX has two halves, and both are pinned here:
 *   A. Both apply paths reject a {0,0} EXISTENCE record with SYNC_ERR_INVALID.
 *      {0,0} is a reserved "no assertion" sentinel; Hlc::tick cannot emit it.
 *   C. sync_engine_digest hashes an entity's presence block only when
 *      asserted(). Necessary independently of A: an element-less entity key is
 *      un-reconcilable by construction (RBSR equalises the ELEMENT set, not the
 *      key set), and the compute-then-commit contract in engine.hpp DELIBERATELY
 *      permits an empty unasserted shell on a bad_alloc — so the digest itself
 *      has to be shell-immune. gc_tombstones keeps shells and compaction
 *      re-emits them, so without C a poisoned replica never recovers.
 *
 * Every case below FAILS on master. The exact pre-fix failures are named on
 * each test. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "engine.hpp" /* ke::Entity — the white-box shell-immunity case */
#include "storage.h"  /* Storage::put_meta_u64 — the clock-restore case */
#include "tempdir.hpp"

namespace {

using cluster::B;
using cluster::Digest;
using synctest::TempDir;

/* The initiator's first session message: one fingerprint descriptor over the
 * whole key space, whose value is the sum of every snapshot element hash
 * (src/reconcile.cpp). Byte-identical before and after == reconciliation's view
 * of this engine did not change. */
std::vector<uint8_t> first_message(sync_engine *e) {
    sync_session *s = sync_session_begin(e, 1);
    uint8_t *o = nullptr;
    size_t ol = 0;
    int done = 0;
    sync_session_step(s, nullptr, 0, &o, &ol, &done);
    std::vector<uint8_t> v(o, o + ol);
    if (o) sync_free(o);
    sync_session_end(s);
    return v;
}

size_t export_count(sync_engine *e) {
    sync_change *r = nullptr;
    size_t n = 0;
    sync_engine_export(e, &r, &n);
    sync_changes_free(r, n);
    return n;
}

size_t scan_count(sync_engine *e, const std::string &ns) {
    sync_scan_entry *ents = nullptr;
    size_t n = 0;
    sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0, &ents, &n);
    sync_scan_free(ents, n);
    return n;
}

/* Sign an EXISTENCE record at a chosen HLC with a real keypair, and apply it. */
int apply_existence_at(sync_engine *e, const std::string &ns,
                       const std::string &ent, bool present, uint64_t phys,
                       uint32_t logi, uint32_t signer_seed) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_EXISTENCE;
    c.ns = B(ns);
    c.ns_len = ns.size();
    c.entity = B(ent);
    c.entity_len = ent.size();
    c.causal_length = present ? 1 : 0;
    c.hlc.physical = phys;
    c.hlc.logical = logi;
    auto s = cluster::seed_from(signer_seed);
    EXPECT_EQ(sync_change_sign(&c, s.data()), SYNC_OK);
    return sync_engine_apply(e, &c);
}

/* The shared body: a {0,0} existence record must be refused, and must leave
 * every observable exactly as it found it. */
void expect_zero_hlc_refused(sync_engine *e, const char *label) {
    SCOPED_TRACE(label);
    const std::string ns = "ns", ghost = "ghost";

    const Digest d0 = cluster::digest(e);
    const std::vector<uint8_t> m0 = first_message(e);
    const size_t x0 = export_count(e);

    /* PRE-FIX: this returned SYNC_OK. */
    EXPECT_EQ(apply_existence_at(e, ns, ghost, /*present=*/true, 0, 0, 0xA5),
              SYNC_ERR_INVALID)
        << "a {0,0} EXISTENCE record must be refused, not accepted";

    int ex = -1;
    ASSERT_EQ(sync_engine_exists(e, B(ns), ns.size(), B(ghost), ghost.size(),
                                 &ex),
              SYNC_OK);

    /* PRE-FIX: exists == 1, digest moved, scan listed it — while the reconcile
     * message and the export stayed empty. That four-way split IS the bug. */
    EXPECT_EQ(ex, 0) << "the phantom must not read as present";
    EXPECT_EQ(cluster::digest(e), d0) << "a refused record must not move the digest";
    EXPECT_EQ(first_message(e), m0) << "a refused record must not move the snapshot";
    EXPECT_EQ(export_count(e), x0) << "a refused record must not be exported";
    EXPECT_EQ(scan_count(e, ns), 0u) << "a refused record must not be scannable";

    /* The guard is narrow: the smallest REAL timestamps are still accepted, so
     * this is not an over-broad rejection of low-clock peers. */
    EXPECT_EQ(apply_existence_at(e, ns, "lo_phys", true, 1, 0, 0xA5), SYNC_OK)
        << "hlc {1,0} is a legitimate assertion";
    EXPECT_EQ(apply_existence_at(e, ns, "lo_logi", true, 0, 1, 0xA5), SYNC_OK)
        << "hlc {0,1} is a legitimate assertion (Hlc::tick's zero-clock output)";
    EXPECT_TRUE(cluster::exists(e, ns, "lo_phys"));
    EXPECT_TRUE(cluster::exists(e, ns, "lo_logi"));

    /* A tombstone at {0,0} is refused for the same reason (present bit is not
     * what makes the record malformed). */
    EXPECT_EQ(apply_existence_at(e, ns, "ghost2", /*present=*/false, 0, 0, 0xA5),
              SYNC_ERR_INVALID);
}

} // namespace

/* ---- 0. The clock can never MINT the sentinel --------------------------- *
 * The whole fix rests on "no honest writer can emit {0,0}", which rests on
 * Hlc::tick never returning it. `logical` is uint32_t and both increment sites
 * were a bare +1, so {p, UINT32_MAX} wrapped to {p, 0} -- and at p == 0 (a host
 * whose now_ms() is stuck at the epoch: no RTC) that is exactly the sentinel.
 * PRE-FIX both lines below returned {0,0}. */
TEST(ZeroHlcExistence, ClockNeverMintsTheSentinel) {
    ke::Hlc t;
    t.physical = 0;
    t.logical = 0xFFFFFFFFu;
    const ke::Hlc before = t;
    t.tick(0);
    EXPECT_FALSE(t.physical == 0 && t.logical == 0)
        << "tick wrapped onto the reserved {0,0} sentinel";
    EXPECT_GT(ke::hlc_cmp(t, before), 0) << "tick must be strictly monotonic";

    ke::Hlc r;
    r.physical = 0;
    r.logical = 0xFFFFFFFEu;
    ke::Hlc remote;
    remote.physical = 0;
    remote.logical = 0xFFFFFFFFu;
    r.receive(remote, 0);
    EXPECT_FALSE(r.physical == 0 && r.logical == 0)
        << "receive wrapped onto the reserved {0,0} sentinel";
    EXPECT_GT(ke::hlc_cmp(r, remote), 0)
        << "receive must dominate the remote timestamp";

    /* The ordinary paths are untouched. */
    ke::Hlc n;
    n.physical = 5;
    n.logical = 3;
    n.tick(9);
    EXPECT_EQ(n.physical, 9u);
    EXPECT_EQ(n.logical, 0u);
    n.tick(9);
    EXPECT_EQ(n.physical, 9u);
    EXPECT_EQ(n.logical, 1u);

    /* receive's fourth branch sets logical = 0 DELIBERATELY (the wall clock
     * advanced past both sides). Deciding the carry from "logical == 0" after
     * the fact fires here and pushes physical one past `now` on every ordinary
     * apply, breaking receive's own bound physical <= max(local, remote, now). */
    ke::Hlc w;
    w.physical = 1000;
    w.logical = 7;
    ke::Hlc past;
    past.physical = 900;
    past.logical = 3;
    w.receive(past, 2000);
    EXPECT_EQ(w.physical, 2000u) << "receive pushed physical past now";
    EXPECT_EQ(w.logical, 0u);

    /* The carry itself must not overflow. `physical` is remote-influenced
     * (receive adopts a peer's physical with no clamp on future timestamps), so
     * an unguarded physical += 1 at UINT64_MAX wraps to 0 with logical already
     * 0 -- landing on the sentinel from the other direction. Saturate instead. */
    ke::Hlc top;
    top.physical = UINT64_MAX;
    top.logical = 0xFFFFFFFFu;
    top.tick(0);
    EXPECT_FALSE(top.physical == 0 && top.logical == 0)
        << "the carry overflowed physical straight onto the sentinel";
}

/* A peer-reachable version of the same hazard: one signed record at a far-future
 * HLC drives the local clock to the top of its range, and the next LOCAL write
 * must still produce a usable assertion rather than the sentinel. */
TEST(ZeroHlcExistence, FarFutureRecordCannotPoisonTheNextLocalWrite) {
    sync_engine *e = cluster::make(0x71);
    ASSERT_NE(e, nullptr);

    ASSERT_EQ(apply_existence_at(e, "ns", "poison", true, UINT64_MAX,
                                 0xFFFFFFFEu, 0xA5),
              SYNC_OK)
        << "a far-future HLC is accepted verbatim today; that is the premise";

    cluster::put(e, "ns", "mydoc", "title", "hello");

    EXPECT_TRUE(cluster::exists(e, "ns", "mydoc"))
        << "the local write after a far-future record must still land";
    EXPECT_EQ(cluster::get(e, "ns", "mydoc", "title"), "hello");

    const ke::Entity &en = e->ns["ns"]["mydoc"];
    EXPECT_TRUE(en.asserted())
        << "the local assertion was stamped with the reserved sentinel";
    EXPECT_TRUE(en.present());
    sync_engine_destroy(e);
}

/* ---- 0b. The persisted clock must never be restored BACKWARDS ----------- *
 * `logical` is written to the meta frame as 8 bytes (put_meta_u64) but held as
 * uint32_t, so the restore narrows. A truncating cast can hand back a clock
 * strictly smaller than the one persisted, and a clock that moves backwards
 * lets the next local write tie or lose LWW against a record already on disk --
 * dropping that write silently, which is the same failure mode the {0,0}
 * reservation exists to prevent. A log this code writes can never store more
 * than UINT32_MAX, so the hazard only reaches a corrupt or hand-edited file --
 * which is exactly what this test writes.
 *
 * PRE-FIX the cast truncated: 0x1_0000_0007 came back as 7. */
TEST(ZeroHlcExistence, OversizedPersistedLogicalClampsInsteadOfTruncating) {
    TempDir dir;
    ASSERT_FALSE(dir.path.empty());
    const std::string path = dir.file("clock.db");
    auto seed = cluster::seed_from(0x81);

    {
        sync_engine *e = sync_engine_open(path.c_str(), seed.data());
        ASSERT_NE(e, nullptr);
        cluster::put(e, "ns", "ent", "f", "v"); /* make the log non-trivial */
        ASSERT_NE(e->store, nullptr);
        /* Wider than uint32 by exactly one, plus a small remainder: a truncating
         * restore yields 7, a clamping one yields UINT32_MAX. */
        ASSERT_TRUE(e->store->put_meta_u64("hlc_logical", 0x100000007ull));
        ASSERT_EQ(sync_engine_flush(e), SYNC_OK);
        sync_engine_destroy(e);
    }

    sync_engine *r = sync_engine_open(path.c_str(), seed.data());
    ASSERT_NE(r, nullptr);
    EXPECT_EQ(r->clock.logical, 0xFFFFFFFFu)
        << "an out-of-range persisted logical must clamp, not wrap around to a "
           "smaller clock";

    /* And the clock still makes progress from the clamp: tick carries into
     * physical rather than wrapping onto the sentinel. */
    const ke::Hlc before = r->clock;
    const ke::Hlc after = r->clock.tick(0);
    EXPECT_GT(ke::hlc_cmp(after, before), 0) << "clamped clock cannot advance";
    EXPECT_FALSE(after.physical == 0 && after.logical == 0);

    sync_engine_destroy(r);
}

/* ---- 0c. A pre-epoch wall clock must not wrap into the top of the range --*
 * std::chrono::milliseconds::rep is SIGNED, so a host whose clock reads before
 * 1970 hands now_ms() a negative count -- and a bare (uint64_t) cast is a
 * modular wrap, not a clamp. Every consumer treats now_ms() as a BOUNDED
 * wall-clock ms (tick's monotonicity gate, gc_tombstones' cutoff, capability
 * expiry, ReconView deadlines), and tick's gate is one-way, so one local write
 * on such a host pins the engine-global clock ~584 million years ahead for the
 * life of the process and of the database.
 *
 * PRE-FIX: ms_since_epoch did not exist and now_ms() returned
 * 18446741864720751616 for 1900-01-01 and UINT64_MAX for one ms before the
 * epoch. */
TEST(ZeroHlcExistence, PreEpochClockClampsToTheEpoch) {
    EXPECT_EQ(ke::ms_since_epoch(-1), 0u)
        << "one millisecond before the epoch wrapped to UINT64_MAX";
    EXPECT_EQ(ke::ms_since_epoch(-2208988800000ll), 0u) << "1900-01-01 wrapped";
    EXPECT_EQ(ke::ms_since_epoch(INT64_MIN), 0u);

    /* The ordinary domain is untouched. */
    EXPECT_EQ(ke::ms_since_epoch(0), 0u);
    EXPECT_EQ(ke::ms_since_epoch(1), 1u);
    EXPECT_EQ(ke::ms_since_epoch(1755000000000ll), 1755000000000ull);

    /* Clamping to 0 is safe against the {0,0} reservation: at now == 0 tick
     * takes the else branch into bump_logical, which yields logical >= 1. */
    ke::Hlc t;
    t.physical = 0;
    t.logical = 0;
    t.tick(ke::ms_since_epoch(-1));
    EXPECT_FALSE(t.physical == 0 && t.logical == 0)
        << "a clamped clock must still not mint the reserved sentinel";
}

/* ---- 0d. One far-future record must not pin the engine-global clock ------ *
 * bump_logical's saturating branch is a FIXED POINT: at {UINT64_MAX,
 * UINT32_MAX} tick() returns a value EQUAL to the pre-tick one, because no
 * larger HLC exists. receive() adopted a peer's physical with no ceiling, so
 * ONE signed record at the top of the range put the engine there -- and the
 * local write paths commit tick()'s value with no LWW gate, on the documented
 * assumption that it "wins", while apply_change gates every remote record on
 * `order <= 0`. The result is not lost progress but silent, permanent
 * DIVERGENCE, engine-wide: the write lands locally and dies at every peer.
 *
 * PRE-FIX both halves failed: `a` adopted UINT64_MAX, and the second write to
 * "doc" (and the delete) tied its own earlier record and was dropped by `b`. */
TEST(ZeroHlcExistence, FarFutureRecordCannotPinTheEngineClock) {
    /* Unit half: receive refuses to adopt above the ceiling, and tick stays
     * strictly monotonic afterwards. */
    ke::Hlc c;
    c.physical = 1000;
    c.logical = 0;
    ke::Hlc top;
    top.physical = UINT64_MAX;
    top.logical = 0xFFFFFFFFu;
    c.receive(top, 1000);
    EXPECT_LE(c.physical, ke::kMaxAdoptablePhysical)
        << "receive adopted a physical past the ceiling and pinned the clock";
    const ke::Hlc before = c;
    const ke::Hlc after = c.tick(0);
    EXPECT_GT(ke::hlc_cmp(after, before), 0)
        << "tick is no longer strictly monotonic: bump_logical's fixed point";

    /* End-to-end half: a poisoned engine must still converge with a peer. */
    sync_engine *a = cluster::make(0x91);
    sync_engine *b = cluster::make(0x92);
    ASSERT_NE(a, nullptr);
    ASSERT_NE(b, nullptr);

    ASSERT_EQ(apply_existence_at(a, "ns", "poison", true, UINT64_MAX,
                                 0xFFFFFFFFu, 0xA5),
              SYNC_OK)
        << "a top-of-range HLC is still accepted verbatim; that is the premise";
    EXPECT_LE(a->clock.physical, ke::kMaxAdoptablePhysical)
        << "one applied record pinned the engine-global clock";

    /* Values chosen so the later write is lexicographically SMALLER: at the
     * fixed point register_cmp ties on (hlc, author) and falls through to the
     * value, so "b" then "a" is the ordering that actually exposes the bug. */
    cluster::put(a, "ns", "doc", "f", "b");
    cluster::sync2(a, b);
    ASSERT_EQ(cluster::get(b, "ns", "doc", "f"), "b") << "the pump must work";

    cluster::put(a, "ns", "doc", "f", "a");
    cluster::sync2(a, b);
    EXPECT_EQ(cluster::get(a, "ns", "doc", "f"), "a");
    EXPECT_EQ(cluster::get(b, "ns", "doc", "f"), "a")
        << "the second local write landed locally but was dropped by the peer";

    cluster::del(a, "ns", "doc");
    cluster::sync2(a, b);
    EXPECT_FALSE(cluster::exists(a, "ns", "doc"));
    EXPECT_FALSE(cluster::exists(b, "ns", "doc"))
        << "the tombstone tied its own presence assertion and never replicated";
    EXPECT_EQ(cluster::digest(a), cluster::digest(b))
        << "replicas diverged permanently after one far-future record";

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- 0e. A persisted physical past the ceiling must clamp on restore ----- *
 * The clock is persisted verbatim, so a database written by a binary without
 * the adoption ceiling -- or a corrupt meta frame -- would restore an engine
 * straight onto the fixed point above. Clamping on restore is what lets such a
 * database heal on upgrade instead of carrying the pin forever. Same shape as
 * the hlc_logical clamp two tests up, applied to the sibling field.
 *
 * PRE-FIX: r->clock.physical came back as UINT64_MAX and tick() was a no-op. */
TEST(ZeroHlcExistence, PoisonedPersistedPhysicalClampsOnRestore) {
    TempDir dir;
    ASSERT_FALSE(dir.path.empty());
    const std::string path = dir.file("pinned.db");
    auto seed = cluster::seed_from(0x82);

    {
        sync_engine *e = sync_engine_open(path.c_str(), seed.data());
        ASSERT_NE(e, nullptr);
        cluster::put(e, "ns", "ent", "f", "v"); /* make the log non-trivial */
        ASSERT_NE(e->store, nullptr);
        ASSERT_TRUE(e->store->put_meta_u64("hlc_physical", UINT64_MAX));
        ASSERT_TRUE(e->store->put_meta_u64("hlc_logical", 0xFFFFFFFFull));
        ASSERT_EQ(sync_engine_flush(e), SYNC_OK);
        sync_engine_destroy(e);
    }

    sync_engine *r = sync_engine_open(path.c_str(), seed.data());
    ASSERT_NE(r, nullptr);
    EXPECT_LE(r->clock.physical, ke::kMaxAdoptablePhysical)
        << "a persisted physical past the ceiling restored the fixed point";

    const ke::Hlc before = r->clock;
    const ke::Hlc after = r->clock.tick(0);
    EXPECT_GT(ke::hlc_cmp(after, before), 0)
        << "the restored clock cannot advance: tick is a no-op at the fixed point";

    sync_engine_destroy(r);
}

/* ---- 1. In-memory engine: no storage, no compaction, no batching --------- */
TEST(ZeroHlcExistence, MemoryEngineRefusesZeroHlc) {
    sync_engine *e = cluster::make(0x33);
    ASSERT_NE(e, nullptr);
    expect_zero_hlc_refused(e, "memory");
    sync_engine_destroy(e);
}

/* ---- 2. Durable engine: nothing committed, and the digest survives reopen -*/
TEST(ZeroHlcExistence, DurableEngineRefusesAndSurvivesReopen) {
    TempDir dir;
    ASSERT_FALSE(dir.path.empty());
    const std::string path = dir.file("phantom.db");
    auto seed = cluster::seed_from(0x11);

    sync_engine *e = sync_engine_open(path.c_str(), seed.data());
    ASSERT_NE(e, nullptr);
    expect_zero_hlc_refused(e, "durable");

    const Digest before = cluster::digest(e);
    ASSERT_EQ(sync_engine_flush(e), SYNC_OK);
    sync_engine_destroy(e);

    /* PRE-FIX: the phantom vanished here AND left a shell behind, so the digest
     * took a THIRD value — neither the pre-apply nor the post-apply one. */
    sync_engine *r = sync_engine_open(path.c_str(), seed.data());
    ASSERT_NE(r, nullptr);
    int ex = -1;
    ASSERT_EQ(sync_engine_exists(r, B(std::string("ns")), 2,
                                 B(std::string("ghost")), 5, &ex),
              SYNC_OK);
    EXPECT_EQ(ex, 0);
    EXPECT_EQ(cluster::digest(r), before) << "digest must be preserved across reopen";
    sync_engine_destroy(r);
}

/* ---- 3. The oracle agrees with reconciliation ---------------------------- *
 * Two replicas driven to convergence must report equal digests. PRE-FIX the
 * phantom made this fail: the pump ran to completion, the phantom never crossed
 * (build_snapshot advertised no element for it), and the digests stayed apart
 * with no route to repair. */
TEST(ZeroHlcExistence, ReconciledReplicasAgreeOnDigest) {
    sync_engine *a = cluster::make(0x51);
    sync_engine *b = cluster::make(0x52);
    ASSERT_NE(a, nullptr);
    ASSERT_NE(b, nullptr);

    cluster::put(a, "ns", "real", "f", "v");
    EXPECT_EQ(apply_existence_at(a, "ns", "ghost", true, 0, 0, 0xA5),
              SYNC_ERR_INVALID);

    cluster::sync2(a, b);

    EXPECT_TRUE(cluster::exists(b, "ns", "real")) << "the pump must actually work";
    EXPECT_FALSE(cluster::exists(b, "ns", "ghost"));
    EXPECT_EQ(cluster::digest(a), cluster::digest(b))
        << "reconciliation reported convergence but the digests disagree";

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- 4. The invariant, not the symptom: the digest is shell-immune ------- *
 * An entity key that carries NO reconciliation element must contribute nothing
 * to the digest. This is the half of the fix that does not depend on the
 * zero-HLC record at all: engine.hpp's compute-then-commit contract explicitly
 * permits "an empty, unasserted entity shell ... which emits no element" on a
 * bad_alloc, and RBSR can only ever equalise the ELEMENT set — so a shell that
 * moved the digest would be permanently un-reconcilable.
 *
 * PRE-FIX this failed on the first EXPECT: sync_engine_digest hashed a presence
 * block ('E', ns, entity, present=0, hlc {0,0}, 32 zero bytes) for every entity
 * in the map regardless of asserted(). */
TEST(ZeroHlcExistence, DigestIgnoresElementlessEntityKeys) {
    sync_engine *plain = cluster::make(0x61);
    sync_engine *shelled = cluster::make(0x61); /* same identity seed */
    ASSERT_NE(plain, nullptr);
    ASSERT_NE(shelled, nullptr);

    /* Build identical state with EXPLICIT timestamps. cluster::put stamps from
     * the engine's own wall clock, so two engines whose puts straddle a
     * millisecond boundary would diverge here for a reason that has nothing to
     * do with what this test is about (observed under ASan and the
     * amalgamation build, which are slow enough to cross one). */
    for (sync_engine *e : {plain, shelled}) {
        ASSERT_EQ(apply_existence_at(e, "ns", "real", true, 1000, 0, 0x61),
                  SYNC_OK);
        cluster::apply_register(e, "ns", "real", "f", "v", 1001, 0, 0x61);
    }
    ASSERT_EQ(cluster::digest(plain), cluster::digest(shelled))
        << "the two engines must start byte-identical";

    /* Exactly the state engine.hpp's bad_alloc path is documented to leave. */
    (void)shelled->ns["ns"]["orphan"];
    ASSERT_TRUE(shelled->ns["ns"].count("orphan"))
        << "the shell must actually be in the map for this test to mean anything";
    ASSERT_FALSE(shelled->ns["ns"]["orphan"].asserted());

    EXPECT_EQ(cluster::digest(shelled), cluster::digest(plain))
        << "an element-less entity key must not move the digest";
    EXPECT_EQ(first_message(shelled), first_message(plain))
        << "control: it contributes no reconciliation element either";
    EXPECT_EQ(export_count(shelled), export_count(plain));

    /* A shell that DOES carry a register still contributes that register: the
     * gate drops the absent assertion, never real state. */
    cluster::apply_register(shelled, "ns", "orphan", "g", "w", 4242, 0, 0x62);
    ASSERT_TRUE(shelled->ns["ns"]["orphan"].fields.count("g"));
    ASSERT_FALSE(shelled->ns["ns"]["orphan"].asserted())
        << "a register must not fabricate a presence assertion";
    EXPECT_NE(cluster::digest(shelled), cluster::digest(plain))
        << "a register under an unasserted entity is real state and must hash";
    EXPECT_NE(first_message(shelled), first_message(plain))
        << "...and must be advertised to reconciliation";

    sync_engine_destroy(plain);
    sync_engine_destroy(shelled);
}
