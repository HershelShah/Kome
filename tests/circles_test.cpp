/* circles_test.cpp — end-to-end "Circles" (P2P, group-first, privacy-native
 * social) usage on the engine, driven entirely through the public API the
 * product would use. Groups are namespaces, posts are entities, post fields are
 * LWW registers, membership/roles are capabilities, and joins are invites. Sync
 * runs over real read-scoped reconcile sessions (the same path SecurePeerSession
 * drives per gossip cycle), so CRDT merge, capability enforcement, and
 * read-scoping are all exercised together as a user-visible whole rather than in
 * isolation. Complements the unit suites by checking product-level invariants. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "tempdir.hpp"

using namespace cluster;
using synctest::TempDir;
using Pk = std::array<uint8_t, SYNC_PUBKEY_LEN>;

namespace {

Pk idof(sync_engine *e) {
    Pk p{};
    sync_engine_identity(e, p.data());
    return p;
}

/* Read-scoped bidirectional sync: each side scopes its snapshot to the other's
 * identity, exactly as the secure mesh does each gossip cycle. (cluster::sync2
 * is unscoped; the read-scoping scenarios below need the scoped session.) */
bool sync_scoped(sync_engine *a, sync_engine *b) {
    Pk pa = idof(a), pb = idof(b);
    sync_session *sa = sync_session_begin_scoped(a, 1, pb.data());
    sync_session *sb = sync_session_begin_scoped(b, 0, pa.data());
    if (!sa || !sb) { sync_session_end(sa); sync_session_end(sb); return false; }

    uint8_t *out = nullptr; size_t ol = 0; int done = 0;
    sync_session_step(sa, nullptr, 0, &out, &ol, &done);
    std::vector<uint8_t> msg(out, out + ol); if (out) sync_free(out);
    sync_session *turn = sb, *other = sa;
    int empties = (ol == 0) ? 1 : 0;
    for (int i = 0; i < 4000; i++) {
        out = nullptr; ol = 0; done = 0;
        sync_session_step(turn, msg.data(), msg.size(), &out, &ol, &done);
        std::vector<uint8_t> next(out, out + ol); if (out) sync_free(out);
        empties = (ol == 0) ? empties + 1 : 0;
        if (empties >= 2) break;
        msg.swap(next); std::swap(turn, other);
    }
    sync_session_end(sa); sync_session_end(sb);
    return true;
}

/* Owner self-grants a root over ns (returns it; caller frees). */
sync_capability *own(sync_engine *owner, const char *ns) {
    sync_capability *r =
        sync_capability_root(owner, ns, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    EXPECT_NE(r, nullptr);
    EXPECT_EQ(sync_engine_grant(owner, r), SYNC_OK);
    return r;
}

/* Owner delegates `access` (until expiry; 0 = never) over root's ns to subject,
 * installing the delegation into engine `at`. */
void invite(sync_engine *owner, sync_capability *root, const Pk &subject,
            int access, uint64_t expiry, sync_engine *at) {
    sync_capability *d =
        sync_capability_delegate(owner, root, subject.data(), access, expiry);
    ASSERT_NE(d, nullptr);
    EXPECT_EQ(sync_engine_grant(at, d), SYNC_OK);
    sync_capability_free(d);
}

} // namespace

/* S1 — a circle with the owner, a read/write member, and a read-only member all
 * converge on the readable content. */
TEST(Circles, OwnerWriterReaderConverge) {
    sync_engine *alice = make(1), *bob = make(2), *carol = make(3);
    const char *C = "circle:friends";
    sync_capability *root = own(alice, C);
    invite(alice, root, idof(bob), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0, alice);
    invite(alice, root, idof(carol), SYNC_ACCESS_READ, 0, alice);

    put(alice, C, "p1", "body", "hello circle");
    sync_scoped(alice, bob);
    sync_scoped(alice, carol);
    EXPECT_TRUE(exists(bob, C, "p1"));
    EXPECT_TRUE(exists(carol, C, "p1"));

    put(bob, C, "p2", "body", "bob says hi");
    sync_scoped(alice, bob);   /* owner ingests Bob's authorized post */
    sync_scoped(alice, carol); /* fan out to Carol */
    EXPECT_TRUE(exists(alice, C, "p2"));
    EXPECT_TRUE(exists(carol, C, "p2"));
    EXPECT_EQ(get(carol, C, "p2", "body"), "bob says hi");

    sync_capability_free(root);
    sync_engine_destroy(alice); sync_engine_destroy(bob); sync_engine_destroy(carol);
}

/* S2 — characterization of where write-enforcement lives. A read-only member's
 * post is rejected by the OWNER (which holds the root), but a fellow member that
 * holds only a delegation does not own the namespace, so it treats it as open
 * and accepts (and would re-gossip) the post. This is a real design property of
 * a capability CRDT — enforcement happens at root-holders — not a bug. If the
 * product later changes this (e.g. by sharing the root with trusted members),
 * update this test. */
TEST(Circles, WriteEnforcementLivesAtRootHolders) {
    sync_engine *alice = make(1), *bob = make(2), *carol = make(3);
    const char *C = "circle:friends";
    sync_capability *root = own(alice, C);
    invite(alice, root, idof(bob), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0, alice);
    invite(alice, root, idof(carol), SYNC_ACCESS_READ, 0, alice);

    /* Carol is read-only but writes locally anyway — local writes are never
     * capability-checked (it is your own replica). */
    put(carol, C, "x1", "body", "should not be allowed to post");

    sync_scoped(alice, carol);
    EXPECT_FALSE(exists(alice, C, "x1"))
        << "owner must reject a read-only member's unauthorized post";

    sync_scoped(bob, carol);
    EXPECT_TRUE(exists(bob, C, "x1"))
        << "documented property: a non-owner member does not enforce writes";

    sync_capability_free(root);
    sync_engine_destroy(alice); sync_engine_destroy(bob); sync_engine_destroy(carol);
}

/* S3 — offline partition then reconnect: disjoint posts authored on each side
 * all merge (CRDT). */
TEST(Circles, OfflinePartitionMerges) {
    sync_engine *alice = make(1), *bob = make(2);
    const char *C = "circle:open"; /* open namespace, no caps required */
    for (int i = 0; i < 3; i++) put(alice, C, "a" + std::to_string(i), "body", "A");
    for (int i = 0; i < 4; i++) put(bob, C, "b" + std::to_string(i), "body", "B");
    sync_scoped(alice, bob);
    for (int i = 0; i < 3; i++) EXPECT_TRUE(exists(bob, C, "a" + std::to_string(i)));
    for (int i = 0; i < 4; i++) EXPECT_TRUE(exists(alice, C, "b" + std::to_string(i)));
    EXPECT_EQ(digest(alice), digest(bob));
    sync_engine_destroy(alice); sync_engine_destroy(bob);
}

/* S4 — concurrent edits of the same field resolve to one deterministic value. */
TEST(Circles, ConcurrentSameFieldEditLWW) {
    sync_engine *alice = make(1), *bob = make(2);
    const char *C = "circle:open";
    put(alice, C, "topic", "title", "original");
    sync_scoped(alice, bob);
    put(alice, C, "topic", "title", "alice edit");
    put(bob, C, "topic", "title", "bob edit");
    sync_scoped(alice, bob);
    EXPECT_EQ(get(alice, C, "topic", "title"), get(bob, C, "topic", "title"));
    EXPECT_EQ(digest(alice), digest(bob));
    sync_engine_destroy(alice); sync_engine_destroy(bob);
}

/* S5 — a deletion (tombstone) propagates; a concurrent edit-vs-delete converges
 * to one deterministic outcome on both sides. */
TEST(Circles, DeleteAndEditVsDeleteConverge) {
    sync_engine *alice = make(1), *bob = make(2);
    const char *C = "circle:open";
    put(alice, C, "p", "body", "deletable");
    sync_scoped(alice, bob);
    EXPECT_TRUE(exists(bob, C, "p"));
    del(alice, C, "p");
    sync_scoped(alice, bob);
    EXPECT_FALSE(exists(bob, C, "p"));
    EXPECT_EQ(digest(alice), digest(bob));

    put(alice, C, "q", "body", "v0");
    sync_scoped(alice, bob);
    del(alice, C, "q");                 /* delete on one side */
    put(bob, C, "q", "body", "v1-edit");/* concurrent edit on the other */
    sync_scoped(alice, bob);
    EXPECT_EQ(digest(alice), digest(bob))
        << "edit-vs-delete must converge to one outcome";
    EXPECT_EQ(exists(alice, C, "q"), exists(bob, C, "q"));
    sync_engine_destroy(alice); sync_engine_destroy(bob);
}

/* S6 — read-scoping: a member of one circle never receives another circle's
 * posts, and their existence never leaks through reconciliation. */
TEST(Circles, ReadScopingNoCrossCircleLeak) {
    sync_engine *alice = make(1), *bob = make(2);
    sync_capability *work = own(alice, "circle:work");
    sync_capability *family = own(alice, "circle:family");
    invite(alice, work, idof(bob), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0, alice);
    /* Bob is NOT in family. */
    put(alice, "circle:work", "w1", "body", "work post");
    put(alice, "circle:family", "f1", "body", "family secret");
    sync_scoped(alice, bob);
    EXPECT_TRUE(exists(bob, "circle:work", "w1"));
    EXPECT_FALSE(exists(bob, "circle:family", "f1"));
    sync_scoped(bob, alice); /* Bob re-shares everything he holds back */
    EXPECT_FALSE(exists(bob, "circle:family", "f1"))
        << "family existence must never reach a non-member";
    sync_capability_free(work); sync_capability_free(family);
    sync_engine_destroy(alice); sync_engine_destroy(bob);
}

/* S7 — promote a member from read-only to read/write by granting a second,
 * broader delegation; afterwards the owner accepts their posts. (Also guards the
 * order-dependent authorization fix — pre-fix this stayed UNAUTHORIZED.) */
TEST(Circles, MembershipUpgradeEnablesPosting) {
    sync_engine *alice = make(1), *carol = make(3);
    const char *C = "circle:friends";
    sync_capability *root = own(alice, C);
    invite(alice, root, idof(carol), SYNC_ACCESS_READ, 0, alice); /* read-only */
    put(carol, C, "c1", "body", "before upgrade");
    sync_scoped(alice, carol);
    EXPECT_FALSE(exists(alice, C, "c1")) << "pre-upgrade write must be rejected";

    invite(alice, root, idof(carol), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0, alice);
    put(carol, C, "c2", "body", "after upgrade");
    sync_scoped(alice, carol);
    EXPECT_TRUE(exists(alice, C, "c2")) << "post-upgrade write must be accepted";
    sync_capability_free(root);
    sync_engine_destroy(alice); sync_engine_destroy(carol);
}

/* S8 — time-limited access: an expired read cap receives nothing new; a still-
 * valid one grants read. */
TEST(Circles, TimeLimitedAccessExpiry) {
    sync_engine *alice = make(1), *dave = make(4), *erin = make(5);
    const char *C = "circle:event";
    sync_capability *root = own(alice, C);
    invite(alice, root, idof(dave), SYNC_ACCESS_READ, 1 /* expired */, alice);
    invite(alice, root, idof(erin), SYNC_ACCESS_READ, 4000000000000ull, alice);
    put(alice, C, "e1", "body", "event update");

    sync_scoped(alice, dave);
    EXPECT_FALSE(exists(dave, C, "e1")) << "expired-cap member gets nothing new";
    sync_scoped(alice, erin);
    EXPECT_TRUE(exists(erin, C, "e1")) << "valid-cap member can read";
    sync_capability_free(root);
    sync_engine_destroy(alice); sync_engine_destroy(dave); sync_engine_destroy(erin);
}

/* S9 — adversarial: a forged-author record and a validly-signed but
 * uncapability'd write are both rejected by the owner. */
TEST(Circles, ForgedAndUnauthorizedRejected) {
    sync_engine *alice = make(1);
    sync_capability *root = own(alice, "circle:friends");
    Pk bob_pk = [] { sync_engine *b = make(2); Pk p = idof(b); sync_engine_destroy(b); return p; }();

    const std::string ns = "circle:friends", f = "body", val = "fake";
    /* Forged: claims Bob's authorship but signed by Eve. */
    {
        const std::string ent = "forge";
        sync_change c; std::memset(&c, 0, sizeof c);
        c.kind = SYNC_CHANGE_REGISTER;
        c.ns = B(ns); c.ns_len = ns.size();
        c.entity = B(ent); c.entity_len = ent.size();
        c.field = B(f); c.field_len = f.size();
        c.value = B(val); c.value_len = val.size();
        c.hlc.physical = 1; c.hlc.logical = 0;
        EXPECT_SYNC_OK(sync_change_sign(&c, seed_from(99).data())); /* Eve signs */
        std::memcpy(c.author, bob_pk.data(), SYNC_PUBKEY_LEN);      /* claims Bob */
        EXPECT_EQ(sync_engine_apply(alice, &c), SYNC_ERR_BADSIG);
    }
    /* Correctly self-signed by Eve, but Eve holds no capability. */
    {
        const std::string ent = "eve";
        sync_change c; std::memset(&c, 0, sizeof c);
        c.kind = SYNC_CHANGE_REGISTER;
        c.ns = B(ns); c.ns_len = ns.size();
        c.entity = B(ent); c.entity_len = ent.size();
        c.field = B(f); c.field_len = f.size();
        c.value = B(val); c.value_len = val.size();
        c.hlc.physical = 2; c.hlc.logical = 0;
        EXPECT_SYNC_OK(sync_change_sign(&c, seed_from(99).data()));
        EXPECT_EQ(sync_engine_apply(alice, &c), SYNC_ERR_UNAUTHORIZED);
    }
    sync_capability_free(root);
    sync_engine_destroy(alice);
}

/* S10 — durability: an encrypted-at-rest circle survives close/reopen, and the
 * wrong key cannot open it. */
TEST(Circles, EncryptedDurabilitySurvivesReopen) {
    TempDir dir;
    std::string path = dir.file("circle.db");
    uint8_t key[32]; std::memset(key, 0x5A, sizeof key);
    auto seed = seed_from(7);

    sync_engine *e = sync_engine_open_encrypted(path.c_str(), seed.data(), key);
    ASSERT_NE(e, nullptr);
    put(e, "circle:open", "p1", "body", "durable post");
    EXPECT_SYNC_OK(sync_engine_flush(e));
    sync_engine_destroy(e);

    sync_engine *re = sync_engine_open_encrypted(path.c_str(), seed.data(), key);
    ASSERT_NE(re, nullptr);
    EXPECT_TRUE(exists(re, "circle:open", "p1"));
    sync_engine_destroy(re);

    uint8_t wrong[32]; std::memset(wrong, 0x00, sizeof wrong);
    sync_engine *bad = sync_engine_open_encrypted(path.c_str(), seed.data(), wrong);
    EXPECT_EQ(bad, nullptr) << "wrong key must not open the log";
    if (bad) sync_engine_destroy(bad);
}

/* S11 — scale: in an 8-member ring mesh, one member's post reaches everyone and
 * all members converge to one state. */
TEST(Circles, RingMeshBroadcastConverges) {
    const int N = 8;
    std::vector<sync_engine *> m(N);
    for (int i = 0; i < N; i++) m[i] = make((uint32_t)(40 + i));
    const char *C = "circle:open";
    put(m[0], C, "broadcast", "body", "reaches all?");
    bool all = false;
    for (int r = 0; r < N && !all; r++) {
        for (int i = 0; i < N; i++) sync_scoped(m[i], m[(i + 1) % N]);
        all = true;
        for (int i = 0; i < N; i++) all = all && exists(m[i], C, "broadcast");
    }
    EXPECT_TRUE(all) << "broadcast did not reach all members";
    EXPECT_TRUE(all_converged(m)) << "members did not converge";
    for (auto *e : m) sync_engine_destroy(e);
}

/* S12 — one user's two devices share an identity (same seed -> same keypair) and
 * sync as a single author: each device's writes to the user's own circle are
 * accepted by the other, and a concurrent same-cell edit converges. */
TEST(Circles, MultiDeviceSameIdentity) {
    sync_engine *phone = make(80), *laptop = make(80); /* same seed */
    Pk pp = idof(phone), pl = idof(laptop);
    ASSERT_EQ(std::memcmp(pp.data(), pl.data(), SYNC_PUBKEY_LEN), 0)
        << "same seed must yield the same identity";

    const char *C = "circle:me";
    sync_capability *root = own(phone, C); /* the user owns it (root on phone) */
    put(phone, C, "p1", "body", "from phone");
    put(laptop, C, "p2", "body", "from laptop"); /* laptop has no root: local write */
    sync_scoped(phone, laptop);
    EXPECT_TRUE(exists(phone, C, "p2"))
        << "owner must accept its other device's write (shared identity)";
    EXPECT_TRUE(exists(laptop, C, "p1"));

    put(phone, C, "p1", "body", "phone edit");
    put(laptop, C, "p1", "body", "laptop edit");
    sync_scoped(phone, laptop);
    EXPECT_EQ(get(phone, C, "p1", "body"), get(laptop, C, "p1", "body"));
    EXPECT_EQ(digest(phone), digest(laptop));
    sync_capability_free(root);
    sync_engine_destroy(phone); sync_engine_destroy(laptop);
}

/* S13 — bulk + large content round-trips intact: many records (forcing multiple
 * reconcile messages), a many-field entity, and a large single value. NOTE: a
 * single field value above ~60 KB cannot traverse a UDP datagram (64 KB minus
 * Noise + reliability framing) and currently wedges that link — verified in
 * connection_test (LargeValueWithinDatagramSyncs). In-process and over TCP/WS it
 * is fine; over UDP, large media must be chunked app-side. */
TEST(Circles, BulkAndLargeContentRoundTrips) {
    sync_engine *a = make(70), *b = make(71);
    const char *C = "circle:open";
    std::string body(400, 'x');
    for (int i = 0; i < 500; i++) put(a, C, "p" + std::to_string(i), "body", body); /* ~200 KB */
    for (int f = 0; f < 300; f++)
        put(a, C, "profile", "f" + std::to_string(f), "v" + std::to_string(f));
    std::string big(40 * 1024, 'Z'); /* under the 48 KB single-record bound */
    put(a, C, "media", "blob", big);

    sync_scoped(a, b);
    EXPECT_TRUE(exists(b, C, "p499"));
    EXPECT_EQ(get(b, C, "profile", "f299"), "v299");
    EXPECT_EQ(get(b, C, "media", "blob"), big) << "large value did not round-trip intact";
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* S14 — peers with badly skewed wall clocks still converge: the higher-HLC write
 * wins deterministically on both sides (HLC merge). */
TEST(Circles, ClockSkewConverges) {
    sync_engine *a = make(60), *b = make(61);
    const char *C = "circle:open";
    put(a, C, "cell", "v", "init"); /* assert existence with a real timestamp */
    sync_scoped(a, b);
    /* Inject skewed writes: a's clock is far behind, b's far ahead. */
    cluster::apply_register(a, C, "cell", "v", "early", 1'700'000'000'000ull, 0, 60);
    cluster::apply_register(b, C, "cell", "v", "late", 1'900'000'000'000ull, 0, 61);
    sync_scoped(a, b);
    EXPECT_EQ(get(a, C, "cell", "v"), "late") << "higher-HLC write must win on a";
    EXPECT_EQ(get(b, C, "cell", "v"), "late") << "higher-HLC write must win on b";
    EXPECT_EQ(digest(a), digest(b)) << "skewed clocks failed to converge";
    sync_engine_destroy(a); sync_engine_destroy(b);
}
