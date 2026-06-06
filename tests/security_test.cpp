/* security_test.cpp — M4 acceptance tests.
 *
 * This file covers identity, capabilities, write authorization, read scoping,
 * and cross-namespace misuse (T4.4-T4.8). The Noise channel tests (T4.1, T4.3)
 * are added alongside noise.{h,cpp}; primitive KATs (T4.2) live in
 * crypto_test.cpp. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <string>
#include <vector>

#include "monocypher.h" /* crypto_blake2b for the T4.4 identity check */

namespace {

const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

std::array<uint8_t, SYNC_SEED_LEN> seed_from(uint8_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (auto &b : s) b = v;
    return s;
}

void set(sync_engine *e, const std::string &ns, const std::string &ent,
         const std::string &field, const std::string &val) {
    ASSERT_EQ(sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(), B(field),
                              field.size(), B(val), val.size()),
              SYNC_OK);
}

/* Apply every record exported from src into target; return the first non-OK
 * code, or SYNC_OK if all applied. */
int apply_all(sync_engine *target, sync_engine *src) {
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_EQ(sync_engine_export(src, &recs, &n), SYNC_OK);
    int rc = SYNC_OK;
    for (size_t i = 0; i < n; i++) {
        int r = sync_engine_apply(target, &recs[i]);
        if (r != SYNC_OK) { rc = r; break; }
    }
    sync_changes_free(recs, n);
    return rc;
}

/* Pump two already-begun sessions to quiescence. */
bool drive(sync_session *sa, sync_session *sb) {
    uint8_t *out = nullptr;
    size_t outlen = 0;
    int done = 0;
    EXPECT_EQ(sync_session_step(sa, nullptr, 0, &out, &outlen, &done), SYNC_OK);
    std::vector<uint8_t> msg(out, out + outlen);
    if (out) sync_free(out);

    sync_session *turn = sb, *other = sa;
    int empties = (outlen == 0) ? 1 : 0;
    for (int i = 0; i < 2000; i++) {
        out = nullptr; outlen = 0; done = 0;
        EXPECT_EQ(sync_session_step(turn, msg.data(), msg.size(), &out, &outlen,
                                    &done),
                  SYNC_OK);
        std::vector<uint8_t> next(out, out + outlen);
        if (out) sync_free(out);
        empties = (outlen == 0) ? empties + 1 : 0;
        if (empties >= 2) return true;
        msg.swap(next);
        std::swap(turn, other);
    }
    return false;
}

int exists(sync_engine *e, const std::string &ns, const std::string &ent) {
    int p = 0;
    sync_engine_exists(e, B(ns), ns.size(), B(ent), ent.size(), &p);
    return p;
}

} // namespace

/* ---- T4.4 Identity stability ------------------------------------------- */
TEST(Security, IdentityStability) {
    auto seed = seed_from(0x21);
    sync_engine *e = sync_engine_create(seed.data());
    ASSERT_NE(e, nullptr);

    uint8_t pk[SYNC_PUBKEY_LEN], sid[SYNC_SITE_ID_LEN];
    ASSERT_EQ(sync_engine_identity(e, pk), SYNC_OK);
    ASSERT_EQ(sync_engine_site_id(e, sid), SYNC_OK);

    uint8_t expect[32];
    crypto_blake2b(expect, 32, pk, 32);
    EXPECT_EQ(0, std::memcmp(sid, expect, 32)) << "site_id != BLAKE2b-256(pk)";

    /* Same seed -> same identity. */
    sync_engine *e2 = sync_engine_create(seed.data());
    uint8_t pk2[SYNC_PUBKEY_LEN];
    sync_engine_identity(e2, pk2);
    EXPECT_EQ(0, std::memcmp(pk, pk2, SYNC_PUBKEY_LEN));

    sync_engine_destroy(e);
    sync_engine_destroy(e2);
}

/* ---- T4.5 Capability verification -------------------------------------- */
TEST(Security, CapabilityVerification) {
    auto so = seed_from(0x01), sb = seed_from(0x02);
    sync_engine *owner = sync_engine_create(so.data());
    sync_engine *b = sync_engine_create(sb.data());
    uint8_t bpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(b, bpk);

    /* Valid chain: root(rw) -> delegate write to B. */
    sync_capability *root = sync_capability_root(owner, "nsA",
                                                 SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    sync_capability *deleg =
        sync_capability_delegate(owner, root, bpk, SYNC_ACCESS_WRITE, 0);
    ASSERT_NE(deleg, nullptr);

    /* Granting both into a verifier succeeds (self-signatures verify). */
    sync_engine *v = sync_engine_create(seed_from(0x09).data());
    EXPECT_EQ(sync_engine_grant(v, root), SYNC_OK);
    EXPECT_EQ(sync_engine_grant(v, deleg), SYNC_OK);

    /* Forged signature: corrupt an encoded capability -> grant rejects it. */
    int len = sync_capability_encode(deleg, nullptr, 0);
    std::vector<uint8_t> enc(len);
    ASSERT_EQ(sync_capability_encode(deleg, enc.data(), enc.size()), len);
    enc[len - 1] ^= 0x01; /* flip a signature byte */
    sync_capability *forged = sync_capability_decode(enc.data(), enc.size());
    ASSERT_NE(forged, nullptr);
    EXPECT_EQ(sync_engine_grant(v, forged), SYNC_ERR_BADSIG);
    sync_capability_free(forged);

    /* Over-broad: cannot delegate WRITE from a READ-only parent. */
    sync_capability *ro = sync_capability_root(owner, "nsRO", SYNC_ACCESS_READ);
    ASSERT_NE(ro, nullptr);
    sync_capability *broad =
        sync_capability_delegate(owner, ro, bpk, SYNC_ACCESS_WRITE, 0);
    EXPECT_EQ(broad, nullptr) << "over-broad delegation was not rejected";

    sync_capability_free(root);
    sync_capability_free(deleg);
    sync_capability_free(ro);
    sync_engine_destroy(owner);
    sync_engine_destroy(b);
    sync_engine_destroy(v);
}

/* ---- T4.6 Write authorization (incl. expiry) --------------------------- */
TEST(Security, WriteAuthorization) {
    auto so = seed_from(0x01), sb = seed_from(0x02), sc = seed_from(0x03);
    sync_engine *owner = sync_engine_create(so.data());
    sync_engine *writer = sync_engine_create(sb.data());
    sync_engine *stranger = sync_engine_create(sc.data());
    uint8_t bpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(writer, bpk);

    /* Verifier V owns nsA and grants writer a write capability. */
    sync_engine *v = sync_engine_create(seed_from(0x09).data());
    sync_capability *root = sync_capability_root(owner, "nsA",
                                                 SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_capability *deleg =
        sync_capability_delegate(owner, root, bpk, SYNC_ACCESS_WRITE, 0);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(v, deleg), SYNC_OK);

    /* Authorized writer's records are accepted. */
    set(writer, "nsA", "x", "f", "hello");
    EXPECT_EQ(apply_all(v, writer), SYNC_OK);

    /* Stranger (no capability) is rejected. */
    set(stranger, "nsA", "y", "f", "nope");
    EXPECT_EQ(apply_all(v, stranger), SYNC_ERR_UNAUTHORIZED);

    /* Open namespace (V does not own nsOpen): anyone may write. */
    set(stranger, "nsOpen", "z", "f", "ok");
    {
        /* apply only the nsOpen records */
        sync_change *recs = nullptr; size_t n = 0;
        sync_engine_export(stranger, &recs, &n);
        for (size_t i = 0; i < n; i++) {
            std::string ns((const char *)recs[i].ns, recs[i].ns_len);
            if (ns == "nsOpen") {
                EXPECT_EQ(sync_engine_apply(v, &recs[i]), SYNC_OK);
            }
        }
        sync_changes_free(recs, n);
    }

    /* Expired delegation is rejected. */
    auto sd = seed_from(0x04);
    sync_engine *late = sync_engine_create(sd.data());
    uint8_t dpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(late, dpk);
    sync_capability *expired =
        sync_capability_delegate(owner, root, dpk, SYNC_ACCESS_WRITE, 1 /* ms */);
    ASSERT_NE(expired, nullptr);
    /* Granting is fine (signature is valid); authorization fails (expired). */
    EXPECT_EQ(sync_engine_grant(v, expired), SYNC_OK);
    set(late, "nsA", "w", "f", "stale");
    EXPECT_EQ(apply_all(v, late), SYNC_ERR_UNAUTHORIZED);

    sync_capability_free(root);
    sync_capability_free(deleg);
    sync_capability_free(expired);
    sync_engine_destroy(owner);
    sync_engine_destroy(writer);
    sync_engine_destroy(stranger);
    sync_engine_destroy(late);
    sync_engine_destroy(v);
}

/* ---- T4.7 Read scoping ------------------------------------------------- */
TEST(Security, ReadScoping) {
    auto so = seed_from(0x01);
    sync_engine *owner = sync_engine_create(so.data());

    /* V owns nsA and nsB and holds data in both. */
    sync_engine *v = sync_engine_create(seed_from(0x09).data());
    for (const char *ns : {"nsA", "nsB"}) {
        sync_capability *r = sync_capability_root(owner, ns,
                                                  SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        /* Owner must be authorized to write into V to seed data; grant owner a
         * self root in V, then let owner write through V's enforcement. */
        ASSERT_EQ(sync_engine_grant(v, r), SYNC_OK);
        sync_capability_free(r);
    }
    /* Seed data authored by V's owner: simplest is to author in `owner` and
     * apply, but owner must be authorized. owner is the root issuer, so it is
     * authorized for both namespaces. */
    set(owner, "nsA", "a1", "f", "A-data");
    set(owner, "nsB", "b1", "f", "B-data");
    ASSERT_EQ(apply_all(v, owner), SYNC_OK);

    /* Peer P may read nsA only. */
    auto sp = seed_from(0x05);
    sync_engine *p = sync_engine_create(sp.data());
    uint8_t ppk[SYNC_PUBKEY_LEN];
    sync_engine_identity(p, ppk);
    sync_capability *rootA =
        sync_capability_root(owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_capability *readA =
        sync_capability_delegate(owner, rootA, ppk, SYNC_ACCESS_READ, 0);
    ASSERT_EQ(sync_engine_grant(v, readA), SYNC_OK);

    /* Reconcile: V scoped to P, P open. */
    sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
    sync_session *spz = sync_session_begin(p, 0);
    ASSERT_NE(sv, nullptr);
    ASSERT_NE(spz, nullptr);
    EXPECT_TRUE(drive(sv, spz));
    sync_session_end(sv);
    sync_session_end(spz);

    /* P received nsA but never saw nsB (no existence leak). */
    EXPECT_EQ(exists(p, "nsA", "a1"), 1);
    EXPECT_EQ(exists(p, "nsB", "b1"), 0);
    uint8_t *val = nullptr; size_t vl = 0;
    EXPECT_EQ(sync_engine_get(p, B(std::string("nsB")), 3, B(std::string("b1")),
                              2, B(std::string("f")), 1, &val, &vl),
              SYNC_ERR_NOTFOUND);

    sync_capability_free(rootA);
    sync_capability_free(readA);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(p);
}

/* ---- T4.8 Cross-namespace misuse --------------------------------------- */
TEST(Security, CrossNamespaceMisuse) {
    auto so = seed_from(0x01), sb = seed_from(0x02);
    sync_engine *owner = sync_engine_create(so.data());
    sync_engine *writer = sync_engine_create(sb.data());
    uint8_t bpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(writer, bpk);

    sync_engine *v = sync_engine_create(seed_from(0x09).data());
    /* V owns nsA and nsB; writer gets write on nsA only. */
    sync_capability *rootA = sync_capability_root(owner, "nsA",
                                                  SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_capability *rootB = sync_capability_root(owner, "nsB",
                                                  SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_capability *delegA =
        sync_capability_delegate(owner, rootA, bpk, SYNC_ACCESS_WRITE, 0);
    ASSERT_EQ(sync_engine_grant(v, rootA), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(v, rootB), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(v, delegA), SYNC_OK);

    /* Write to nsA: allowed. Write to nsB: rejected (cap is for nsA). */
    set(writer, "nsA", "x", "f", "ok");
    set(writer, "nsB", "y", "f", "denied");
    sync_change *recs = nullptr; size_t n = 0;
    sync_engine_export(writer, &recs, &n);
    for (size_t i = 0; i < n; i++) {
        std::string ns((const char *)recs[i].ns, recs[i].ns_len);
        int rc = sync_engine_apply(v, &recs[i]);
        if (ns == "nsA") EXPECT_EQ(rc, SYNC_OK);
        else EXPECT_EQ(rc, SYNC_ERR_UNAUTHORIZED);
    }
    sync_changes_free(recs, n);

    sync_capability_free(rootA);
    sync_capability_free(rootB);
    sync_capability_free(delegA);
    sync_engine_destroy(owner);
    sync_engine_destroy(writer);
    sync_engine_destroy(v);
}
