/* resilience_test.cpp — real-life resilience scenarios.
 *
 * Beyond the unit-level building blocks (crash recovery, store-and-forward,
 * reconnection, LWW conflicts), these simulate cohesive operational situations:
 *   - a network partition that diverges (with a conflicting edit) then heals
 *   - a node that drops offline, misses + makes edits, then rejoins and catches up
 *   - a durable node that crashes, restarts, and rejoins without data loss
 *   - sustained random churn (nodes up/down + writes) converging with no loss
 * All in-process and deterministic (fixed seeds). */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <dirent.h>
#include <unistd.h>

#include <array>
#include <cstdio>
#include <cstring>
#include <random>
#include <set>
#include <string>
#include <vector>

namespace {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

std::array<uint8_t, SYNC_SEED_LEN> seed_from(uint32_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (size_t i = 0; i < s.size(); i++) s[i] = (uint8_t)(v >> ((i % 4) * 8));
    return s;
}

Digest digest(sync_engine *e) {
    Digest d{};
    EXPECT_EQ(sync_engine_digest(e, d.data()), SYNC_OK);
    return d;
}

void put(sync_engine *e, const std::string &ns, const std::string &ent,
         const std::string &field, const std::string &val) {
    ASSERT_EQ(sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(), B(field),
                              field.size(), B(val), val.size()),
              SYNC_OK);
}

int exists(sync_engine *e, const std::string &ns, const std::string &ent) {
    int p = 0;
    sync_engine_exists(e, B(ns), ns.size(), B(ent), ent.size(), &p);
    return p;
}

std::string get(sync_engine *e, const std::string &ns, const std::string &ent,
                const std::string &field) {
    uint8_t *v = nullptr;
    size_t n = 0;
    if (sync_engine_get(e, B(ns), ns.size(), B(ent), ent.size(), B(field),
                        field.size(), &v, &n) != SYNC_OK)
        return "<none>";
    std::string r((char *)v, n);
    sync_free(v);
    return r;
}

/* Count register records (distinct cells) an engine holds. */
int record_count(sync_engine *e) {
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_EQ(sync_engine_export(e, &recs, &n), SYNC_OK);
    int c = 0;
    for (size_t i = 0; i < n; i++)
        if (recs[i].kind == SYNC_CHANGE_REGISTER) c++;
    sync_changes_free(recs, n);
    return c;
}

/* Fully reconcile two engines via the in-process session pump. */
void sync2(sync_engine *a, sync_engine *b) {
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    uint8_t *out = nullptr;
    size_t ol = 0;
    int done = 0;
    sync_session_step(sa, nullptr, 0, &out, &ol, &done);
    std::vector<uint8_t> msg(out, out + ol);
    if (out) sync_free(out);
    sync_session *turn = sb, *other = sa;
    int empties = (ol == 0) ? 1 : 0;
    for (int i = 0; i < 100000; i++) {
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
}

/* Gossip a set of engines to full convergence over a ring. */
void gossip_to_converge(std::vector<sync_engine *> &g, int max_rounds = 50) {
    auto all_eq = [&]() {
        if (g.size() < 2) return true;
        Digest d0 = digest(g[0]);
        for (size_t i = 1; i < g.size(); i++)
            if (digest(g[i]) != d0) return false;
        return true;
    };
    for (int r = 0; r < max_rounds && !all_eq(); r++)
        for (size_t i = 0; i + 1 < g.size(); i++) sync2(g[i], g[i + 1]);
}

bool all_converged(std::vector<sync_engine *> &g) {
    if (g.size() < 2) return true;
    Digest d0 = digest(g[0]);
    for (size_t i = 1; i < g.size(); i++)
        if (digest(g[i]) != d0) return false;
    return true;
}

struct TempDir {
    std::string path;
    TempDir() {
        char t[] = "/tmp/sync_resil_XXXXXX";
        path = mkdtemp(t);
    }
    ~TempDir() {
        DIR *d = opendir(path.c_str());
        if (d) {
            struct dirent *e;
            while ((e = readdir(d))) {
                std::string n = e->d_name;
                if (n != "." && n != "..") std::remove((path + "/" + n).c_str());
            }
            closedir(d);
        }
        rmdir(path.c_str());
    }
    std::string file(const std::string &n) const { return path + "/" + n; }
};

} // namespace

/* ---- Network partition diverges (with a conflict) then heals ----------- */
TEST(Resilience, PartitionHealWithConflict) {
    const int n = 6;
    std::vector<sync_engine *> all;
    for (int i = 0; i < n; i++) all.push_back(sync_engine_create(seed_from(i + 1).data()));

    /* Everyone starts agreeing on one cell. */
    put(all[0], "doc", "title", "v", "original");
    gossip_to_converge(all);
    ASSERT_TRUE(all_converged(all));

    /* Partition into {0,1,2} and {3,4,5}; each side edits independently,
     * including a CONFLICTING write to doc/title. */
    std::vector<sync_engine *> left = {all[0], all[1], all[2]};
    std::vector<sync_engine *> right = {all[3], all[4], all[5]};

    put(left[0], "doc", "title", "v", "edited-by-left");
    put(left[1], "doc", "l1", "v", "left-only-1");
    put(right[0], "doc", "title", "v", "edited-by-right"); /* conflict */
    put(right[2], "doc", "r1", "v", "right-only-1");

    gossip_to_converge(left);
    gossip_to_converge(right);
    /* The two partitions disagree while split. */
    EXPECT_NE(digest(left[0]), digest(right[0]));

    /* Heal: a single cross-partition link, then settle. */
    sync2(left[0], right[0]);
    gossip_to_converge(all);

    EXPECT_TRUE(all_converged(all)) << "partition failed to heal";
    /* The conflicting cell resolved to one deterministic LWW winner everywhere. */
    std::string winner = get(all[0], "doc", "title", "v");
    for (int i = 0; i < n; i++)
        EXPECT_EQ(get(all[i], "doc", "title", "v"), winner);
    EXPECT_TRUE(winner == "edited-by-left" || winner == "edited-by-right");
    /* Non-conflicting edits from both sides survived everywhere. */
    for (int i = 0; i < n; i++) {
        EXPECT_EQ(exists(all[i], "doc", "l1"), 1);
        EXPECT_EQ(exists(all[i], "doc", "r1"), 1);
    }
    for (auto *e : all) sync_engine_destroy(e);
}

/* ---- A node drops offline, then rejoins and catches up ----------------- */
TEST(Resilience, OfflineNodeRejoinsAndCatchesUp) {
    const int n = 5;
    std::vector<sync_engine *> all;
    for (int i = 0; i < n; i++) all.push_back(sync_engine_create(seed_from(10 + i).data()));
    put(all[0], "ns", "base", "v", "base");
    gossip_to_converge(all);

    /* Node 4 goes offline. */
    std::vector<sync_engine *> online(all.begin(), all.begin() + 4);
    sync_engine *offline = all[4];

    /* While it's down: the others keep working, and it makes its own edits. */
    for (int t = 0; t < 5; t++) {
        put(online[t % 4], "ns", "online" + std::to_string(t), "v", "x");
        gossip_to_converge(online);
        put(offline, "ns", "offline" + std::to_string(t), "v", "y");
    }

    /* It rejoins. */
    gossip_to_converge(all);
    EXPECT_TRUE(all_converged(all)) << "rejoined node did not converge";

    /* It caught up on everything it missed... */
    for (int t = 0; t < 5; t++)
        EXPECT_EQ(exists(offline, "ns", "online" + std::to_string(t)), 1);
    /* ...and its offline edits reached everyone. */
    for (int t = 0; t < 5; t++)
        EXPECT_EQ(exists(all[0], "ns", "offline" + std::to_string(t)), 1);

    for (auto *e : all) sync_engine_destroy(e);
}

/* ---- A durable node crashes, restarts, and rejoins without data loss ---- */
TEST(Resilience, CrashRestartRejoin) {
    TempDir dir;
    auto sa = seed_from(21), sb = seed_from(22), sc = seed_from(23);
    std::string pa = dir.file("a.db"), pb = dir.file("b.db"), pc = dir.file("c.db");

    sync_engine *a = sync_engine_open(pa.c_str(), sa.data());
    sync_engine *b = sync_engine_open(pb.c_str(), sb.data());
    sync_engine *c = sync_engine_open(pc.c_str(), sc.data());

    put(a, "ns", "a-pre", "v", "pre-crash");
    { std::vector<sync_engine *> g = {a, b, c}; gossip_to_converge(g); }

    /* Node A crashes (process gone; data persisted on disk). */
    sync_engine_destroy(a);

    /* While A is down, B and C keep writing. */
    put(b, "ns", "b-new", "v", "1");
    put(c, "ns", "c-new", "v", "2");
    sync2(b, c);

    /* A restarts from its file — pre-crash data must still be there. */
    a = sync_engine_open(pa.c_str(), sa.data());
    ASSERT_NE(a, nullptr);
    EXPECT_EQ(exists(a, "ns", "a-pre"), 1) << "lost data across crash/restart";

    /* A rejoins and catches up. */
    { std::vector<sync_engine *> g = {a, b, c}; gossip_to_converge(g); }
    std::vector<sync_engine *> g = {a, b, c};
    EXPECT_TRUE(all_converged(g));
    EXPECT_EQ(exists(a, "ns", "b-new"), 1);
    EXPECT_EQ(exists(a, "ns", "c-new"), 1);
    EXPECT_EQ(exists(b, "ns", "a-pre"), 1);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
    sync_engine_destroy(c);
}

/* ---- Sustained random churn converges with no data loss ---------------- */
TEST(Resilience, RandomChurnNoDataLoss) {
    const int n = 8;
    std::mt19937 rng(2024);
    std::vector<sync_engine *> all;
    for (int i = 0; i < n; i++) all.push_back(sync_engine_create(seed_from(30 + i).data()));

    int writes = 0;
    for (int round = 0; round < 40; round++) {
        /* Each node is independently online this round (>=2 online). */
        std::vector<int> online;
        for (int i = 0; i < n; i++)
            if (rng() % 10 < 7) online.push_back(i);
        if (online.size() < 2) { online = {0, 1}; }

        /* Online nodes write unique records (no key ever reused -> no loss to
         * detect via count). */
        for (int idx : online)
            if (rng() % 2) {
                std::string key = "w" + std::to_string(writes++);
                put(all[idx], "ns", key, "v", "data");
            }

        /* A few random reconciles among the online set (partial connectivity). */
        for (int k = 0; k < (int)online.size(); k++) {
            int i = online[rng() % online.size()];
            int j = online[rng() % online.size()];
            if (i != j) sync2(all[i], all[j]);
        }
    }

    /* Churn stops; everyone comes online and gossips to quiescence. */
    gossip_to_converge(all, 100);
    EXPECT_TRUE(all_converged(all)) << "did not converge after churn";

    /* No data loss: every node holds every record ever written. */
    for (int i = 0; i < n; i++)
        EXPECT_EQ(record_count(all[i]), writes)
            << "node " << i << " missing records after churn (" << writes
            << " written)";

    for (auto *e : all) sync_engine_destroy(e);
}
