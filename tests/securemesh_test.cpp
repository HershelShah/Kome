/* securemesh_test.cpp — in-process exercise of SecurePeerSession, the secure
 * per-peer state machine (Noise XX + transcript-bound identity proof +
 * capability-scoped reconcile) driven as a multiplexed gossip mesh. No real
 * sockets, so this runs under CI and WASM. It proves the two things the daemon
 * depends on and that meshnode cannot give: multi-hop convergence on the secure
 * path, and the security properties (authentication required before any data
 * flows; read-scoping enforced). */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <cstring>
#include <deque>
#include <memory>
#include <string>
#include <vector>

#include "capability.h" /* CapStore::rev_count — revocation-propagation probe */
#include "cluster.hpp"
#include "engine.hpp"
#include "transport/connection.h"

using namespace ke;
using cluster::B;

namespace {

/* One end of a secure link: its session, an inbound datagram queue, and a
 * pointer to the counterpart end on the peer node. Datagrams a session emits are
 * appended to its counterpart's inbox. */
struct Endp {
    SecurePeerSession       sps;
    std::deque<std::string> inbox;
    Endp                   *peer = nullptr;
    Endp(sync_engine *e, bool initiator, uint32_t interval)
        : sps(e, initiator, interval) {}
};

/* A mesh of in-memory engines connected by undirected edges. Each edge gets two
 * Endp ends (one per node). Pumps poll/deliver rounds on a virtual clock. */
struct Mesh {
    std::vector<sync_engine *>         eng;
    std::vector<std::unique_ptr<Endp>> ends;
    uint32_t                           interval;
    uint64_t                           now = 1000;

    explicit Mesh(uint32_t interval_) : interval(interval_) {}
    ~Mesh() {
        ends.clear(); /* sessions hold sync_session*; free them before engines */
        for (auto *e : eng) sync_engine_destroy(e);
    }

    sync_engine *add_engine(uint32_t seed) {
        eng.push_back(cluster::make(seed));
        return eng.back();
    }

    /* Connect engines i and j. Initiator chosen by identity-key compare, exactly
     * as netmesh does (strict order => exactly one initiator per edge). */
    void connect(int i, int j) {
        uint8_t pi[32], pj[32];
        sync_engine_identity(eng[i], pi);
        sync_engine_identity(eng[j], pj);
        bool i_init = std::memcmp(pi, pj, 32) < 0;
        auto a = std::make_unique<Endp>(eng[i], i_init, interval);
        auto b = std::make_unique<Endp>(eng[j], !i_init, interval);
        a->peer = b.get();
        b->peer = a.get();
        ends.push_back(std::move(a));
        ends.push_back(std::move(b));
    }

    void enqueue(Endp *e, std::vector<std::string> &out) {
        for (auto &dg : out) e->peer->inbox.push_back(std::move(dg));
        out.clear();
    }

    void start() {
        std::vector<std::string> out;
        for (auto &e : ends) { e->sps.start(now, out); enqueue(e.get(), out); }
    }

    /* One round: poll every end (retransmits + gossip kicks), then deliver each
     * end's queued inbound datagrams. */
    void round() {
        now += 60;
        std::vector<std::string> out;
        for (auto &e : ends) { e->sps.poll(now, out); enqueue(e.get(), out); }
        for (auto &e : ends) {
            std::deque<std::string> local;
            local.swap(e->inbox);
            for (auto &dg : local) {
                e->sps.on_datagram(dg, now, out);
                enqueue(e.get(), out);
            }
        }
    }

    void run_rounds(int n) {
        for (int r = 0; r < n; r++) round();
    }
};

/* Drive until all engines converge to one digest with `expect_records` register
 * records each, or `max_rounds` elapse. */
bool run_until_converged(Mesh &m, int expect_records, int max_rounds = 600) {
    m.start();
    for (int r = 0; r < max_rounds; r++) {
        m.round();
        if (!cluster::all_converged(m.eng)) continue;
        bool ok = true;
        for (auto *e : m.eng)
            if (cluster::record_count(e) != expect_records) { ok = false; break; }
        if (ok) return true;
    }
    return false;
}

} // namespace

/* ---- Convergence: multi-hop over the secure path ----------------------- */
TEST(SecureMesh, RingConverges) {
    Mesh m(/*interval=*/200);
    const int N = 8;
    for (int i = 0; i < N; i++) {
        sync_engine *e = m.add_engine(100 + i);
        std::string ent = "n" + std::to_string(i);
        cluster::put(e, "mesh", ent, "v", ent); /* one local record each */
    }
    for (int i = 0; i < N; i++) m.connect(i, (i + 1) % N); /* ring */
    EXPECT_TRUE(run_until_converged(m, N))
        << "ring did not converge on the secure path";
}

TEST(SecureMesh, FullMeshConverges) {
    Mesh m(/*interval=*/200);
    const int N = 5;
    for (int i = 0; i < N; i++) {
        sync_engine *e = m.add_engine(200 + i);
        std::string ent = "n" + std::to_string(i);
        cluster::put(e, "mesh", ent, "v", ent);
    }
    for (int i = 0; i < N; i++)
        for (int j = i + 1; j < N; j++) m.connect(i, j);
    EXPECT_TRUE(run_until_converged(m, N));
}

/* ---- Security: read-scoping enforced on the secure path ----------------- */
/* A owns namespace "secret" and has an "open" record. An authenticated peer with
 * no read delegation must receive "open" but NOT "secret" — the capability
 * scoping meshnode's plain session skips. Mirrors connection_test's
 * ReadScopingEnforcedOverTransport, in-process. */
TEST(SecureMesh, ReadScopingEnforced) {
    Mesh m(/*interval=*/0); /* single reconcile cycle is enough */
    sync_engine *a = m.add_engine(1);
    sync_engine *b = m.add_engine(2);

    sync_capability *root =
        sync_capability_root(a, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_EQ(sync_engine_grant(a, root), SYNC_OK); /* A owns "secret" */
    sync_capability_free(root);
    cluster::put(a, "secret", "s1", "f", "v");
    cluster::put(a, "open", "p1", "f", "v");

    m.connect(0, 1);
    m.start();
    m.run_rounds(60); /* let the one cycle settle */

    EXPECT_TRUE(cluster::exists(b, "open", "p1"))
        << "open namespace should have synced";
    EXPECT_FALSE(cluster::exists(b, "secret", "s1"))
        << "read-scoping bypassed: peer received a restricted namespace";
}

/* ---- A grant must take effect on a live gossip link --------------------- */
/* The scoped snapshot is cached per peer (reconcile.cpp ensure_scoped_cache). A
 * capability grant bumps the engine's scope_gen (capability.cpp), clearing that
 * cache so a newly-readable namespace is included on the next cycle. Without the
 * bump, A would keep serving B its stale cached scope and the grant would never
 * propagate over an established link. */
TEST(SecureMesh, GrantMidSyncInvalidatesScopeCache) {
    Mesh m(/*interval=*/200);
    sync_engine *a = m.add_engine(31);
    sync_engine *b = m.add_engine(32);

    sync_capability *root =
        sync_capability_root(a, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_EQ(sync_engine_grant(a, root), SYNC_OK); /* A owns "secret" */
    cluster::put(a, "secret", "s1", "f", "v");
    cluster::put(a, "open", "p1", "f", "v");

    m.connect(0, 1);
    m.start();
    m.run_rounds(120); /* converge the readable slice; A caches B's scope */

    ASSERT_TRUE(cluster::exists(b, "open", "p1")) << "open record should sync";
    ASSERT_FALSE(cluster::exists(b, "secret", "s1"))
        << "read-scoping bypassed before grant";

    /* A grants B a permanent read delegation for "secret". */
    uint8_t bpk[32];
    sync_engine_identity(b, bpk);
    sync_capability *readB =
        sync_capability_delegate(a, root, bpk, SYNC_ACCESS_READ, 0);
    ASSERT_NE(readB, nullptr);
    ASSERT_EQ(sync_engine_grant(a, readB), SYNC_OK);

    /* The grant must reach B over the live link — the scope_gen bump dropped the
     * cached scope, so the next cycle re-snapshots with "secret" included. */
    bool got = false;
    for (int r = 0; r < 400; r++) {
        m.round();
        if (cluster::exists(b, "secret", "s1")) { got = true; break; }
    }
    EXPECT_TRUE(got) << "granted namespace did not propagate after mid-sync grant";

    sync_capability_free(root);
    sync_capability_free(readB);
}

/* ---- A revoke must cut off a live gossip link (responder side) ----------- */
/* Respecified (review blocker): the capability-changing engine sits on the
 * RESPONDER side of the edge — m.connect() picks the initiator by identity-key
 * compare (the smaller key initiates), so the owner below is chosen at runtime
 * as the engine with the larger key. GrantMidSyncInvalidatesScopeCache above
 * grants on the *initiator*, so this test covers the responder direction.
 *
 * TWO independent transport routes can refresh a responder's stale scope, so
 * end-to-end propagation alone cannot pin either one:
 *   (1) on_datagram's cycle restart: a responder whose previous cycle drained
 *       (sess_done_) re-begins — and thus re-scopes — its session on the next
 *       inbound datagram, with no gen comparison at all; and
 *   (2) poll()'s cycle-boundary refresh: the two-counter
 *       (content_gen || scope_gen) comparison, which fires with no inbound
 *       traffic whatsoever, needing only an idle link.
 * On full mesh rounds the initiator kicks a fresh fingerprint every interval,
 * so route (1) alone reproduces every propagation observable below. Route (2)
 * is therefore pinned directly, twice: after the revoke (scope-only change —
 * the zero-write phase is guarded) and again after content-only writes, a
 * single poll() of the owner's end — no datagram delivered to any end — must
 * re-begin the owner's scoped session. Observable: the engine's
 * scoped_cache_gens restamp; ensure_scoped_cache runs only from a session
 * begin, and the owner's end holds the only session on that engine, so
 * nothing but poll()'s refresh can produce it. One probe per counter, so
 * deleting either term of the compare — or the whole refresh branch — fails
 * this test even though route (1) would still deliver the data end-to-end.
 *
 * The propagation half remains the whole-chain check: the revoke is followed
 * by ZERO content writes, so only a scope-driven re-scope can separate the
 * owner's state from the settled session; the re-begun cycle excludes
 * "secret", the owner's next reply mismatches the peer's fingerprint, and —
 * being a fresh session's first message — it carries the revocation to the
 * peer. Data cut-off is then pinned with post-assertion writes: new open data
 * still syncs (the link is alive), new secret data does not. Already-delivered
 * data stays: read cut-off is eventually consistent, never mid-session
 * (SECURITY.md). GenSplit.RevokeDropsCachedScope is the engine-level
 * security-direction gate; this test covers the transport chain. */
TEST(SecureMesh, RevokeMidSyncCutsOff) {
    Mesh m(/*interval=*/200);
    sync_engine *e0 = m.add_engine(41);
    sync_engine *e1 = m.add_engine(42);
    uint8_t p0[32], p1[32];
    sync_engine_identity(e0, p0);
    sync_engine_identity(e1, p1);
    /* The owner (capability-changing engine) must be the responder: connect()
     * makes the smaller identity key the initiator, so pick the larger. */
    bool e0_owner = std::memcmp(p0, p1, 32) > 0;
    sync_engine *a = e0_owner ? e0 : e1; /* owner — responder on the edge */
    sync_engine *b = e0_owner ? e1 : e0; /* peer — initiator on the edge */
    uint8_t bpk[32];
    sync_engine_identity(b, bpk);

    sync_capability *root =
        sync_capability_root(a, "secret", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_EQ(sync_engine_grant(a, root), SYNC_OK); /* A owns "secret" */
    sync_capability *readB =
        sync_capability_delegate(a, root, bpk, SYNC_ACCESS_READ, 0);
    ASSERT_NE(readB, nullptr);
    ASSERT_EQ(sync_engine_grant(a, readB), SYNC_OK); /* B may read it */
    cluster::put(a, "secret", "s1", "f", "v");
    cluster::put(a, "open", "p1", "f", "v");

    m.connect(0, 1);
    ASSERT_TRUE(run_until_converged(m, 2)) << "grant-era convergence failed";
    ASSERT_TRUE(cluster::exists(b, "secret", "s1"))
        << "granted namespace did not sync while the delegation was live";
    ASSERT_NE(b->caps, nullptr) << "B never ingested A's delegation";
    ASSERT_EQ(b->caps->rev_count(), 0u);

    /* Settle to a cycle boundary: poll()'s refresh fires only when the owner's
     * reliability link is fully drained, and converged digests do not imply
     * that. Kicks land every ~4 rounds, so idle windows recur between cycles. */
    Endp *own = m.ends[e0_owner ? 0 : 1].get(); /* the owner's (responder) end */
    for (int r = 0; r < 100 && !own->sps.idle(); r++) m.round();
    ASSERT_TRUE(own->sps.idle()) << "owner link never drained after convergence";

    /* Revoke; from here to the propagation assertions: zero content writes. */
    const uint64_t ca = a->content_gen;
    const uint64_t sa = a->scope_gen;
    ASSERT_EQ(sync_engine_revoke(a, "secret", bpk), SYNC_OK);
    EXPECT_EQ(a->scope_gen, sa + 1);
    EXPECT_EQ(a->content_gen, ca);

    /* Probe 1 — the scope_gen term of poll()'s cycle-boundary compare. The
     * revoke left the owner's session stamps stale (content frozen, scope
     * advanced). One poll of the owner's idle end, delivering no datagram to
     * anyone, must re-begin its cycle: begin_cycle_ -> sync_session_begin_scoped
     * -> ensure_scoped_cache restamps scoped_cache_gens to gens(). */
    ASSERT_NE(a->scoped_cache_gens, a->gens());
    {
        std::vector<std::string> probe;
        own->sps.poll(m.now, probe);
        m.enqueue(own, probe); /* idle link: expected empty; keep flow normal */
    }
    EXPECT_EQ(a->scoped_cache_gens, a->gens())
        << "responder poll() did not re-begin its cycle on a scope-only change "
           "(the scope_gen term of connection.cpp's two-counter refresh)";

    /* The responder's refreshed (re-scoped) cycle must carry the revocation to
     * B — nothing else changed, so only the scope-driven refresh can. */
    bool rev_reached_b = false;
    for (int r = 0; r < 200 && !rev_reached_b; r++) {
        m.round();
        rev_reached_b = b->caps && b->caps->rev_count() > 0;
    }
    EXPECT_TRUE(rev_reached_b)
        << "revocation did not propagate: the responder never refreshed its "
           "cycle on a scope-only change";
    EXPECT_EQ(a->content_gen, ca)
        << "test bug: a content write crept in — propagation proves nothing";
    EXPECT_TRUE(cluster::exists(b, "secret", "s1"))
        << "already-delivered data must not be clawed back";

    /* Probe 2 — the content_gen term of the same compare, same shape: settle
     * to idle, bump content only (scope frozen), single owner-side poll. */
    for (int r = 0; r < 100 && !own->sps.idle(); r++) m.round();
    ASSERT_TRUE(own->sps.idle()) << "owner link never drained after propagation";

    /* Cut-off, pinned with fresh writes (after the zero-write phase): the open
     * namespace still syncs, the revoked one must not. */
    const uint64_t sa2 = a->scope_gen;
    cluster::put(a, "open", "p2", "f", "v2");
    cluster::put(a, "secret", "s2", "f", "v2");
    EXPECT_EQ(a->scope_gen, sa2) << "test bug: cut-off writes must be content-only";
    ASSERT_NE(a->scoped_cache_gens, a->gens());
    {
        std::vector<std::string> probe;
        own->sps.poll(m.now, probe);
        m.enqueue(own, probe);
    }
    EXPECT_EQ(a->scoped_cache_gens, a->gens())
        << "responder poll() did not re-begin its cycle on a content-only "
           "change (the content_gen term of connection.cpp's two-counter refresh)";
    bool open_arrived = false;
    for (int r = 0; r < 400 && !open_arrived; r++) {
        m.round();
        open_arrived = cluster::exists(b, "open", "p2");
    }
    EXPECT_TRUE(open_arrived) << "open namespace stopped syncing after revoke";
    m.run_rounds(200); /* generous extra window for a leak to surface */
    EXPECT_FALSE(cluster::exists(b, "secret", "s2"))
        << "revoked read scope kept syncing on the live link";

    sync_capability_free(root);
    sync_capability_free(readB);
}

/* ---- Security: no data flows without a completed secure handshake -------- */
/* If a peer never completes the authenticated handshake (here: the initiator's
 * post-handshake traffic — its identity proof and reconcile data — is dropped),
 * the responder never authenticates, never starts a scoped session, and learns
 * nothing. Guards the settle/scope gate: sess_ stays null until peer_ok. */
TEST(SecureMesh, NoSyncWithoutAuthentication) {
    sync_engine *a = cluster::make(1);
    sync_engine *b = cluster::make(2);
    cluster::put(a, "ns", "a1", "f", "x");

    uint8_t pa[32], pb[32];
    sync_engine_identity(a, pa);
    sync_engine_identity(b, pb);
    bool a_init = std::memcmp(pa, pb, 32) < 0;

    SecurePeerSession sa(a, a_init, 0);
    SecurePeerSession sb(b, !a_init, 0);
    SecurePeerSession &si = a_init ? sa : sb; /* initiator */
    SecurePeerSession &sr = a_init ? sb : sa; /* responder */

    uint64_t now = 1000;
    std::vector<std::string> to_r, to_i, tmp; /* datagrams bound for responder / initiator */
    si.start(now, to_r);

    auto move_into = [](std::vector<std::string> &dst, std::vector<std::string> &src) {
        for (auto &o : src) dst.push_back(std::move(o));
        src.clear();
    };

    for (int r = 0; r < 80; r++) {
        now += 60;
        /* Drop everything the initiator emits once its handshake is complete —
         * its identity proof and all reconcile traffic. The responder thus never
         * authenticates. */
        if (si.handshake_done()) to_r.clear();
        for (auto &dg : to_r) sr.on_datagram(dg, now, tmp); /* tmp accumulates */
        to_r.clear();
        move_into(to_i, tmp);
        for (auto &dg : to_i) si.on_datagram(dg, now, tmp);
        to_i.clear();
        move_into(to_r, tmp);
        si.poll(now, tmp); move_into(to_r, tmp);
        sr.poll(now, tmp); move_into(to_i, tmp);
    }

    EXPECT_FALSE(sr.authenticated())
        << "responder authenticated without receiving a valid identity proof";
    EXPECT_FALSE(cluster::exists(b, "ns", "a1"))
        << "responder learned data without completing authentication";

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- reset(): a restarted peer re-handshakes and re-converges ----------- */
TEST(SecureMesh, ResetReconverges) {
    Mesh m(/*interval=*/200);
    sync_engine *a = m.add_engine(11);
    sync_engine *b = m.add_engine(22);
    cluster::put(a, "ns", "a1", "f", "x");
    cluster::put(b, "ns", "b1", "f", "y");
    m.connect(0, 1);
    ASSERT_TRUE(run_until_converged(m, 2)) << "initial convergence failed";

    /* Both ends "restart": fresh Noise + reliability state, re-handshake. */
    std::vector<std::string> out;
    for (auto &e : m.ends) { e->sps.reset(m.now, out); m.enqueue(e.get(), out); }
    cluster::put(a, "ns", "a2", "f", "z"); /* new data written after the restart */

    bool ok = false;
    for (int r = 0; r < 600; r++) {
        m.round();
        if (cluster::all_converged(m.eng) && cluster::record_count(a) == 3 &&
            cluster::record_count(b) == 3) { ok = true; break; }
    }
    EXPECT_TRUE(ok) << "did not re-converge after reset()";
    EXPECT_TRUE(cluster::exists(b, "ns", "a2"))
        << "post-restart write did not propagate";
}
