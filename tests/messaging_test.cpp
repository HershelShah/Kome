/* messaging_test.cpp — messaging-app usage on the engine: DMs and group chats as
 * namespaces, messages as entities, edits/reactions/read-receipts as LWW
 * registers, all driven over real read-scoped reconcile sessions. Covers the
 * properties a chat app depends on (ordering, no lost messages, offline delivery,
 * edit/unsend, reactions, DM privacy, multi-device, backlog sync) and pins two
 * modeling rules as characterization tests: message ids must be globally unique,
 * and read receipts are LWW-by-write-time (the app must keep them monotonic). */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "engine.hpp" /* ke::now_ms for controlled-HLC receipt writes */

using namespace cluster;
using Pk = std::array<uint8_t, SYNC_PUBKEY_LEN>;

namespace {

Pk idof(sync_engine *e) { Pk p{}; sync_engine_identity(e, p.data()); return p; }

/* Read-scoped bidirectional sync between two participants (the secure-mesh path). */
bool sync_scoped(sync_engine *a, sync_engine *b) {
    Pk pa = idof(a), pb = idof(b);
    sync_session *sa = sync_session_begin_scoped(a, 1, pb.data());
    sync_session *sb = sync_session_begin_scoped(b, 0, pa.data());
    if (!sa || !sb) { sync_session_end(sa); sync_session_end(sb); return false; }
    uint8_t *o = nullptr; size_t ol = 0; int d = 0;
    sync_session_step(sa, nullptr, 0, &o, &ol, &d);
    std::vector<uint8_t> m(o, o + ol); if (o) sync_free(o);
    sync_session *turn = sb, *other = sa;
    int empties = (ol == 0) ? 1 : 0;
    for (int i = 0; i < 8000; i++) {
        o = nullptr; ol = 0; d = 0;
        sync_session_step(turn, m.data(), m.size(), &o, &ol, &d);
        std::vector<uint8_t> nx(o, o + ol); if (o) sync_free(o);
        empties = (ol == 0) ? empties + 1 : 0;
        if (empties >= 2) break;
        m.swap(nx); std::swap(turn, other);
    }
    sync_session_end(sa); sync_session_end(sb);
    return true;
}

sync_capability *own(sync_engine *o, const char *ns) {
    sync_capability *r = sync_capability_root(o, ns, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    EXPECT_NE(r, nullptr);
    EXPECT_EQ(sync_engine_grant(o, r), SYNC_OK);
    return r;
}
void invite(sync_engine *o, sync_capability *root, const Pk &s, int acc, sync_engine *at) {
    sync_capability *d = sync_capability_delegate(o, root, s.data(), acc, 0);
    ASSERT_NE(d, nullptr);
    EXPECT_EQ(sync_engine_grant(at, d), SYNC_OK);
    sync_capability_free(d);
}

/* A realistic collision-free message id: time-sortable prefix + author tag. */
std::string mid(uint64_t t, const char *who, int seq) {
    char b[64];
    std::snprintf(b, sizeof b, "%013llu-%s-%03d", (unsigned long long)t, who, seq);
    return b;
}

/* Present message ids in `ns`, sorted (= chronological when ids are time-sortable). */
std::vector<std::string> order_of(sync_engine *e, const std::string &ns) {
    std::vector<std::string> out;
    sync_change *r = nullptr; size_t n = 0;
    EXPECT_SYNC_OK(sync_engine_export(e, &r, &n));
    for (size_t i = 0; i < n; i++) {
        if (r[i].kind != SYNC_CHANGE_EXISTENCE || r[i].causal_length != 1) continue;
        std::string rns((const char *)r[i].ns, r[i].ns_len);
        if (rns == ns) out.emplace_back((const char *)r[i].entity, r[i].entity_len);
    }
    sync_changes_free(r, n);
    std::sort(out.begin(), out.end());
    return out;
}

} // namespace

/* ---- ordering / delivery ------------------------------------------------ */

TEST(Messaging, DmConvergesWithConsistentOrder) {
    sync_engine *a = make(1), *b = make(2);
    const char *C = "dm:a:b";
    put(a, C, mid(100, "a", 0), "body", "hi");
    put(b, C, mid(101, "b", 0), "body", "hey");
    put(a, C, mid(102, "a", 1), "body", "how are you");
    sync_scoped(a, b);
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(order_of(a, C), order_of(b, C)) << "both sides must agree on order";
    EXPECT_EQ(order_of(a, C).size(), 3u) << "no message lost";
    sync_engine_destroy(a); sync_engine_destroy(b);
}

TEST(Messaging, OfflineBatchDeliversInOrder) {
    sync_engine *a = make(1), *b = make(2);
    const char *C = "dm:a:b";
    for (int i = 0; i < 5; i++) put(a, C, mid(200 + i, "a", i), "body", "m" + std::to_string(i));
    sync_scoped(a, b);
    auto ob = order_of(b, C);
    EXPECT_EQ(ob.size(), 5u);
    EXPECT_TRUE(std::is_sorted(ob.begin(), ob.end())) << "delivered out of order";
    sync_engine_destroy(a); sync_engine_destroy(b);
}

TEST(Messaging, ConcurrentSendsShareOneOrder) {
    sync_engine *a = make(1), *b = make(2);
    const char *C = "grp:x";
    put(a, C, mid(300, "a", 0), "body", "A0");
    put(b, C, mid(300, "b", 0), "body", "B0"); /* same timestamp, different author */
    put(a, C, mid(301, "a", 1), "body", "A1");
    sync_scoped(a, b);
    EXPECT_EQ(digest(a), digest(b));
    EXPECT_EQ(order_of(a, C), order_of(b, C));
    EXPECT_EQ(order_of(a, C).size(), 3u) << "same-timestamp messages must not collide";
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* Modeling rule: message ids must be globally unique. Naive per-sender sequence
 * numbers collide across senders -> one message silently overwrites the other.
 * Author-qualified (or random/ULID) ids never collide. */
TEST(Messaging, UniqueIdsPreventMessageLoss) {
    sync_engine *a = make(1), *b = make(2);
    /* Naive: both call their first message "msg-1". */
    put(a, "grp:naive", "msg-1", "body", "A's message");
    put(b, "grp:naive", "msg-1", "body", "B's message");
    sync_scoped(a, b);
    EXPECT_EQ(order_of(a, "grp:naive").size(), 1u)
        << "colliding ids collapse to one entity (a message is lost) — ids must be unique";
    /* Correct: author-qualified ids preserve both. */
    put(a, "grp:uniq", mid(400, "a", 1), "body", "A's message");
    put(b, "grp:uniq", mid(400, "b", 1), "body", "B's message");
    sync_scoped(a, b);
    EXPECT_EQ(order_of(a, "grp:uniq").size(), 2u) << "unique ids must preserve both messages";
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ---- edit / unsend ------------------------------------------------------ */

TEST(Messaging, EditMessageLastWriteWins) {
    sync_engine *a = make(1), *b = make(2);
    const char *C = "dm:a:b"; std::string id = mid(500, "a", 0);
    put(a, C, id, "body", "helo");
    sync_scoped(a, b);
    put(a, C, id, "body", "hello (edited)");
    sync_scoped(a, b);
    EXPECT_EQ(get(b, C, id, "body"), "hello (edited)");
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}

TEST(Messaging, UnsendRemovesMessage) {
    sync_engine *a = make(1), *b = make(2);
    const char *C = "dm:a:b"; std::string id = mid(600, "a", 0);
    put(a, C, id, "body", "wrong chat");
    sync_scoped(a, b);
    EXPECT_TRUE(exists(b, C, id));
    del(a, C, id);
    sync_scoped(a, b);
    EXPECT_FALSE(exists(b, C, id)) << "unsend (tombstone) must remove it for the recipient";
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ---- reactions ---------------------------------------------------------- */

TEST(Messaging, ReactionsDoNotConflict) {
    sync_engine *a = make(1), *b = make(2), *c = make(3);
    const char *C = "grp:z"; std::string m = mid(700, "a", 0);
    put(a, C, m, "body", "big news");
    sync_scoped(a, b); sync_scoped(a, c);
    put(b, C, m + ":react:b", "emoji", "thumbsup"); /* per-user reaction entity */
    put(c, C, m + ":react:c", "emoji", "heart");
    put(a, C, m + ":react:a", "emoji", "fire");
    sync_scoped(a, b); sync_scoped(a, c); sync_scoped(b, c); sync_scoped(a, b);
    int reacts = 0;
    for (const char *who : {"a", "b", "c"}) reacts += exists(a, C, m + ":react:" + who);
    EXPECT_EQ(reacts, 3) << "every user's reaction must survive";
    put(b, C, m + ":react:b", "emoji", "laugh"); /* B changes only its own */
    sync_scoped(a, b);
    EXPECT_EQ(get(a, C, m + ":react:b", "emoji"), "laugh");
    sync_engine_destroy(a); sync_engine_destroy(b); sync_engine_destroy(c);
}

/* ---- read receipts ------------------------------------------------------ */

/* Modeling rule: a "last-read = X" register is LWW by WRITE time, not message
 * order, so a stale read event applied with a newer HLC moves the pointer
 * backward. The app must advance receipts monotonically (max), not blind-set.
 * This pins the engine behavior so the rule stays visible. */
TEST(Messaging, ReadReceiptIsLwwByWriteTime) {
    sync_engine *a = make(1), *b = make(2);
    const char *C = "dm:a:b";
    put(b, C, "receipt", "b", mid(805, "a", 5)); /* B read up to msg 5 (real HLC) */
    sync_scoped(a, b);
    EXPECT_EQ(get(a, C, "receipt", "b"), mid(805, "a", 5));
    /* A delayed read event for an EARLIER message, written with a higher HLC. */
    apply_register(b, C, "receipt", "b", mid(802, "a", 2),
                   ke::now_ms() + 60'000, 0, /*seed*/ 2);
    sync_scoped(a, b);
    EXPECT_EQ(get(a, C, "receipt", "b"), mid(802, "a", 2))
        << "LWW tracks write time: a naive receipt can regress — app must keep it monotonic";
    sync_engine_destroy(a); sync_engine_destroy(b);
}

/* ---- group chat --------------------------------------------------------- */

TEST(Messaging, GroupChatConvergesInOrder) {
    const int N = 5;
    std::vector<sync_engine *> g(N);
    for (int i = 0; i < N; i++) g[i] = make(10 + (uint32_t)i);
    const char *C = "grp:big";
    const char *tag[] = {"a", "b", "c", "d", "e"};
    for (int i = 0; i < N; i++)
        for (int k = 0; k < 4; k++)
            put(g[i], C, mid(900 + i * 10 + k, tag[i], k), "body", "hi");
    for (int round = 0; round < N; round++)
        for (int i = 0; i < N; i++) sync_scoped(g[i], g[(i + 1) % N]);
    auto o0 = order_of(g[0], C);
    EXPECT_EQ(o0.size(), (size_t)(N * 4)) << "messages lost in the group";
    for (int i = 1; i < N; i++) {
        EXPECT_TRUE(all_converged({g[0], g[i]}));
        EXPECT_EQ(order_of(g[i], C), o0) << "member " << i << " disagrees on order";
    }
    for (auto *e : g) sync_engine_destroy(e);
}

/* ---- privacy / multi-device / backlog ----------------------------------- */

TEST(Messaging, DmPrivacyReadScoped) {
    sync_engine *a = make(1), *b = make(2), *c = make(3);
    const char *C = "dm:secret";
    sync_capability *root = own(a, C);
    invite(a, root, idof(b), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, a);
    put(a, C, mid(1000, "a", 0), "body", "just between us");
    sync_scoped(a, b); sync_scoped(a, c);
    EXPECT_TRUE(exists(b, C, mid(1000, "a", 0))) << "invited peer reads the DM";
    EXPECT_FALSE(exists(c, C, mid(1000, "a", 0))) << "outsider must not read the DM";
    sync_capability_free(root);
    sync_engine_destroy(a); sync_engine_destroy(b); sync_engine_destroy(c);
}

TEST(Messaging, MultiDeviceSameUser) {
    sync_engine *phone = make(7), *laptop = make(7); /* same seed = same user */
    const char *C = "dm:a:b";
    put(phone, C, mid(1100, "a", 0), "body", "from phone");
    sync_scoped(phone, laptop);
    EXPECT_TRUE(exists(laptop, C, mid(1100, "a", 0)));
    put(laptop, C, mid(1101, "a", 1), "body", "from laptop");
    sync_scoped(phone, laptop);
    EXPECT_TRUE(exists(phone, C, mid(1101, "a", 1)));
    EXPECT_EQ(digest(phone), digest(laptop));
    sync_engine_destroy(phone); sync_engine_destroy(laptop);
}

TEST(Messaging, BacklogSyncsToJoiner) {
    sync_engine *a = make(1), *b = make(2);
    const char *C = "grp:busy";
    for (int i = 0; i < 500; i++) put(a, C, mid(2000 + i, "a", i), "body", "m");
    sync_scoped(a, b); /* b cold-joins and pulls the backlog */
    auto ob = order_of(b, C);
    EXPECT_EQ(ob.size(), 500u) << "backlog message lost";
    EXPECT_TRUE(std::is_sorted(ob.begin(), ob.end()));
    EXPECT_EQ(digest(a), digest(b));
    sync_engine_destroy(a); sync_engine_destroy(b);
}
