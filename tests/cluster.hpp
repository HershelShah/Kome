/* cluster.hpp — shared in-process helpers for multi-node scenario tests:
 * engines, full-reconcile sync, gossip-to-converge, and a controlled-HLC
 * signed-record injector (for clock-skew / stale-write scenarios). */
#ifndef SYNC_TEST_CLUSTER_HPP
#define SYNC_TEST_CLUSTER_HPP

#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <string>
#include <vector>

/* Assert/expect a SYNC_* call returned SYNC_OK, printing the code + its
 * sync_strerror on failure. Clearer than EXPECT_EQ(expr, SYNC_OK) at the 60+
 * status-check call sites across the suite. */
#define EXPECT_SYNC_OK(expr)                                                    \
    EXPECT_EQ((expr), SYNC_OK) << "expected SYNC_OK"
#define ASSERT_SYNC_OK(expr)                                                    \
    ASSERT_EQ((expr), SYNC_OK) << "expected SYNC_OK"

namespace cluster {

using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
inline const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

inline std::array<uint8_t, SYNC_SEED_LEN> seed_from(uint32_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (size_t i = 0; i < s.size(); i++) s[i] = (uint8_t)(v >> ((i % 4) * 8));
    return s;
}

inline sync_engine *make(uint32_t seed) {
    return sync_engine_create(seed_from(seed).data());
}

inline void put(sync_engine *e, const std::string &ns, const std::string &ent,
                const std::string &field, const std::string &val) {
    EXPECT_SYNC_OK(sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(),
                                   B(field), field.size(), B(val), val.size()));
}

inline void del(sync_engine *e, const std::string &ns, const std::string &ent) {
    EXPECT_SYNC_OK(sync_engine_delete(e, B(ns), ns.size(), B(ent), ent.size()));
}

inline std::string get(sync_engine *e, const std::string &ns,
                       const std::string &ent, const std::string &field) {
    uint8_t *v = nullptr;
    size_t n = 0;
    int rc = sync_engine_get(e, B(ns), ns.size(), B(ent), ent.size(), B(field),
                             field.size(), &v, &n);
    if (rc != SYNC_OK) return "<none>";
    std::string r((char *)v, n);
    sync_free(v);
    return r;
}

inline bool exists(sync_engine *e, const std::string &ns,
                   const std::string &ent) {
    int p = 0;
    sync_engine_exists(e, B(ns), ns.size(), B(ent), ent.size(), &p);
    return p != 0;
}

inline Digest digest(sync_engine *e) {
    Digest d{};
    EXPECT_SYNC_OK(sync_engine_digest(e, d.data()));
    return d;
}

inline int record_count(sync_engine *e) {
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_SYNC_OK(sync_engine_export(e, &recs, &n));
    int c = 0;
    for (size_t i = 0; i < n; i++)
        if (recs[i].kind == SYNC_CHANGE_REGISTER) c++;
    sync_changes_free(recs, n);
    return c;
}

/* Apply a register record with a chosen HLC, signed by `seed`'s identity.
 * Used to simulate clock skew / stale writes deterministically. */
inline void apply_register(sync_engine *e, const std::string &ns,
                           const std::string &ent, const std::string &field,
                           const std::string &val, uint64_t physical,
                           uint32_t logical, uint32_t seed) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_REGISTER;
    c.ns = B(ns); c.ns_len = ns.size();
    c.entity = B(ent); c.entity_len = ent.size();
    c.field = B(field); c.field_len = field.size();
    c.value = B(val); c.value_len = val.size();
    c.hlc.physical = physical;
    c.hlc.logical = logical;
    auto s = seed_from(seed);
    EXPECT_SYNC_OK(sync_change_sign(&c, s.data()));
    EXPECT_SYNC_OK(sync_engine_apply(e, &c));
}

/* Fully reconcile two engines (bidirectional, in-process session pump). */
inline void sync2(sync_engine *a, sync_engine *b) {
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

/* Export every record from `from` and apply it into `into`. */
inline void replicate(sync_engine *from, sync_engine *into) {
    sync_change *r = nullptr;
    size_t n = 0;
    EXPECT_SYNC_OK(sync_engine_export(from, &r, &n));
    for (size_t i = 0; i < n; i++)
        EXPECT_SYNC_OK(sync_engine_apply(into, &r[i]));
    sync_changes_free(r, n);
}

inline bool all_converged(const std::vector<sync_engine *> &g) {
    if (g.size() < 2) return true;
    Digest d0 = digest(g[0]);
    for (size_t i = 1; i < g.size(); i++)
        if (digest(g[i]) != d0) return false;
    return true;
}

/* Gossip a ring of engines to convergence. */
inline void gossip(std::vector<sync_engine *> &g, int max_rounds = 60) {
    for (int r = 0; r < max_rounds && !all_converged(g); r++)
        for (size_t i = 0; i + 1 < g.size(); i++) sync2(g[i], g[i + 1]);
}

inline void destroy(std::vector<sync_engine *> &g) {
    for (auto *e : g) sync_engine_destroy(e);
    g.clear();
}

} // namespace cluster

#endif /* SYNC_TEST_CLUSTER_HPP */
