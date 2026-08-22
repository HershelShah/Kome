/* security_test.cpp — M4 acceptance tests.
 *
 * This file covers identity, capabilities, write authorization, read scoping,
 * and cross-namespace misuse (T4.4-T4.8). The Noise channel tests (T4.1, T4.3)
 * are added alongside noise.{h,cpp}; primitive KATs (T4.2) live in
 * crypto_test.cpp. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <chrono>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

#include "monocypher.h" /* crypto_blake2b for the T4.4 identity check */

#include "cluster.hpp"
#include "engine.hpp" /* access to the engine's identity KeyPair */
#include "capability.h"
#include "noise.h"

namespace {

using cluster::B;

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

/* Run the Noise XX handshake between two channels to completion. */
bool handshake(ke::NoiseChannel &ci, ke::NoiseChannel &cr) {
    std::string msg, out;
    bool d = false;
    if (!ci.step("", out, d)) return false; /* msg1 */
    msg = out;
    if (!cr.step(msg, out, d)) return false; /* msg2 */
    msg = out;
    if (!ci.step(msg, out, d)) return false; /* msg3, initiator done */
    msg = out;
    if (!cr.step(msg, out, d)) return false; /* responder done */
    return ci.done() && cr.done();
}

} // namespace

/* ---- T4.1 Handshake + sync over the encrypted channel ------------------ */
TEST(Security, HandshakeAndSync) {
    auto sa = seed_from(0x31), sb = seed_from(0x32);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());

    set(a, "n", "x", "f", "from-a");
    set(b, "n", "y", "f", "from-b");

    ke::NoiseChannel ci(true, a->identity);
    ke::NoiseChannel cr(false, b->identity);
    ASSERT_TRUE(handshake(ci, cr));

    /* Each side learned the other's static key. */
    EXPECT_EQ(0, std::memcmp(ci.remote_static(), b->identity.dh_pk.data(), 32));
    EXPECT_EQ(0, std::memcmp(cr.remote_static(), a->identity.dh_pk.data(), 32));

    /* Run the reconciliation session inside the channel. */
    sync_session *ssa = sync_session_begin(a, 1);
    sync_session *ssb = sync_session_begin(b, 0);

    uint8_t *out = nullptr; size_t outlen = 0; int done = 0;
    ASSERT_EQ(sync_session_step(ssa, nullptr, 0, &out, &outlen, &done), SYNC_OK);
    std::string plain((char *)out, outlen);
    if (out) sync_free(out);

    bool a_to_b = true; /* direction of the in-flight message */
    int empties = (plain.empty()) ? 1 : 0;
    std::string wire;
    /* encrypt initiator's first message */
    ASSERT_TRUE(ci.encrypt(plain, wire));

    for (int i = 0; i < 2000; i++) {
        /* deliver `wire` to the receiver, decrypting with its channel */
        ke::NoiseChannel &rx = a_to_b ? cr : ci;
        ke::NoiseChannel &tx = a_to_b ? ci : cr;
        (void)tx;
        std::string in_plain;
        ASSERT_TRUE(rx.decrypt(wire, in_plain));

        sync_session *target = a_to_b ? ssb : ssa;
        out = nullptr; outlen = 0; done = 0;
        ASSERT_EQ(sync_session_step(target, (const uint8_t *)in_plain.data(),
                                    in_plain.size(), &out, &outlen, &done),
                  SYNC_OK);
        std::string reply((char *)out, outlen);
        if (out) sync_free(out);
        empties = reply.empty() ? empties + 1 : 0;
        if (empties >= 2) break;
        /* encrypt reply with the receiver's channel for the trip back */
        ke::NoiseChannel &rtx = a_to_b ? cr : ci;
        ASSERT_TRUE(rtx.encrypt(reply, wire));
        a_to_b = !a_to_b;
    }

    sync_session_end(ssa);
    sync_session_end(ssb);

    uint8_t da[SYNC_DIGEST_LEN], db[SYNC_DIGEST_LEN];
    sync_engine_digest(a, da);
    sync_engine_digest(b, db);
    EXPECT_EQ(0, std::memcmp(da, db, SYNC_DIGEST_LEN));
    EXPECT_EQ(exists(a, "n", "y"), 1);
    EXPECT_EQ(exists(b, "n", "x"), 1);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- T4.3 Tamper detection --------------------------------------------- */
TEST(Security, TamperDetection) {
    auto sa = seed_from(0x41), sb = seed_from(0x42);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    ke::NoiseChannel ci(true, a->identity);
    ke::NoiseChannel cr(false, b->identity);
    ASSERT_TRUE(handshake(ci, cr));

    std::string ct;
    ASSERT_TRUE(ci.encrypt("hello world", ct));
    std::string pt;
    ASSERT_TRUE(cr.decrypt(ct, pt));
    EXPECT_EQ(pt, "hello world");

    /* Flip any ciphertext byte -> authentication fails (need a fresh channel
     * at the same nonce). */
    ke::NoiseChannel ci2(true, a->identity);
    ke::NoiseChannel cr2(false, b->identity);
    ASSERT_TRUE(handshake(ci2, cr2));
    std::string ct2;
    ASSERT_TRUE(ci2.encrypt("hello world", ct2));
    ct2[3] ^= 0x01;
    std::string pt2;
    EXPECT_FALSE(cr2.decrypt(ct2, pt2)) << "tampered ciphertext was accepted";

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* S4: a forged/corrupt frame is rejected WITHOUT advancing the receive counter,
 * so one injected frame can't permanently wedge the channel. */
TEST(Security, ForgedFrameDoesNotDesync) {
    auto sa = seed_from(0x4A), sb = seed_from(0x4B);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    ke::NoiseChannel ci(true, a->identity);
    ke::NoiseChannel cr(false, b->identity);
    ASSERT_TRUE(handshake(ci, cr));

    std::string ct1;
    ASSERT_TRUE(ci.encrypt("first", ct1));
    std::string forged = ct1;
    forged[5] ^= 0x01;
    std::string junk, pt1;
    EXPECT_FALSE(cr.decrypt(forged, junk));     /* rejected... */
    EXPECT_TRUE(cr.decrypt(ct1, pt1));          /* ...next legit frame still ok */
    EXPECT_EQ(pt1, "first");

    std::string ct2, pt2; /* stream continues in order */
    ASSERT_TRUE(ci.encrypt("second", ct2));
    EXPECT_TRUE(cr.decrypt(ct2, pt2));
    EXPECT_EQ(pt2, "second");

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* Begin a session pair and drive them to convergence. */
static void reconcile(sync_engine *a, sync_engine *b) {
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    drive(sa, sb);
    sync_session_end(sa);
    sync_session_end(sb);
}

/* ---- Capability exchange during sync (security follow-up) --------------- */
TEST(Security, CapabilityExchangeDuringSync) {
    sync_engine *owner = sync_engine_create(seed_from(0x80).data());
    sync_engine *writer = sync_engine_create(seed_from(0x81).data());
    sync_engine *stranger = sync_engine_create(seed_from(0x82).data());
    sync_engine *v = sync_engine_create(seed_from(0x83).data());

    uint8_t wpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(writer, wpk);

    /* V owns nsA. The writer holds a delegated write cap (but V has NOT been
     * told about it out-of-band). */
    sync_capability *root =
        sync_capability_root(owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_capability *deleg =
        sync_capability_delegate(owner, root, wpk, SYNC_ACCESS_WRITE, 0);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);    /* V trusts the root */
    ASSERT_EQ(sync_engine_grant(writer, deleg), SYNC_OK); /* writer carries it */

    /* Authorized writer's records flow: the delegation rides along the sync, so
     * V can authorize them without a prior grant. */
    set(writer, "nsA", "w1", "f", "hello");
    set(writer, "nsA", "w2", "f", "world");
    reconcile(writer, v);
    EXPECT_EQ(exists(v, "nsA", "w1"), 1) << "cap was not exchanged during sync";
    EXPECT_EQ(exists(v, "nsA", "w2"), 1);

    /* A stranger with no capability is still rejected (records dropped). */
    set(stranger, "nsA", "s1", "f", "nope");
    reconcile(stranger, v);
    EXPECT_EQ(exists(v, "nsA", "s1"), 0) << "unauthorized records leaked in";

    sync_capability_free(root);
    sync_capability_free(deleg);
    sync_engine_destroy(owner);
    sync_engine_destroy(writer);
    sync_engine_destroy(stranger);
    sync_engine_destroy(v);
}

/* ---- Channel-to-identity binding (security follow-up) ------------------ */
TEST(Security, ChannelIdentityBinding) {
    auto sa = seed_from(0x71), sb = seed_from(0x72);
    sync_engine *a = sync_engine_create(sa.data());
    sync_engine *b = sync_engine_create(sb.data());
    ke::NoiseChannel ci(true, a->identity);
    ke::NoiseChannel cr(false, b->identity);
    ASSERT_TRUE(handshake(ci, cr));

    /* Each side proves it holds its EdDSA signing key over this channel. */
    std::string pa, pb;
    ASSERT_TRUE(ci.make_identity_proof(pa));
    ASSERT_TRUE(cr.make_identity_proof(pb));

    uint8_t got_a[SYNC_PUBKEY_LEN], got_b[SYNC_PUBKEY_LEN];
    ASSERT_TRUE(cr.verify_identity_proof(pa, got_a)); /* B learns A */
    ASSERT_TRUE(ci.verify_identity_proof(pb, got_b)); /* A learns B */

    uint8_t ida[SYNC_PUBKEY_LEN], idb[SYNC_PUBKEY_LEN];
    sync_engine_identity(a, ida);
    sync_engine_identity(b, idb);
    /* The bound identity equals the peer's real signing identity — so a
     * read-scoped session can trust this pubkey instead of a claimed one. */
    EXPECT_EQ(0, std::memcmp(got_a, ida, SYNC_PUBKEY_LEN));
    EXPECT_EQ(0, std::memcmp(got_b, idb, SYNC_PUBKEY_LEN));

    /* A tampered proof is rejected. */
    std::string bad = pa;
    bad[40] ^= 0x01;
    uint8_t tmp[SYNC_PUBKEY_LEN];
    EXPECT_FALSE(cr.verify_identity_proof(bad, tmp));

    /* A proof from one handshake does not verify on another (no replay). */
    ke::NoiseChannel ci2(true, a->identity);
    ke::NoiseChannel cr2(false, b->identity);
    ASSERT_TRUE(handshake(ci2, cr2));
    EXPECT_FALSE(cr2.verify_identity_proof(pa, tmp));

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- Logging hook (off by default; no secrets) ------------------------- */
namespace {
struct LogCapture { std::vector<std::string> msgs; };
void log_sink(void *ctx, int /*level*/, const char *msg) {
    static_cast<LogCapture *>(ctx)->msgs.push_back(msg);
}
}

TEST(Security, LoggerHook) {
    auto so = seed_from(0x01);
    sync_engine *owner = sync_engine_create(so.data());
    sync_engine *v = sync_engine_create(seed_from(0x09).data());

    /* Off by default: nothing logged even on a rejected apply. */
    sync_capability *root = sync_capability_root(v, "nsA", SYNC_ACCESS_READ); /* v owns */
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    sync_capability_free(root);
    set(owner, "nsA", "x", "secretfield", "TOPSECRETVALUE");

    LogCapture cap;
    /* Install the logger and trigger a rejection (owner has no write cap). */
    ASSERT_EQ(sync_engine_set_logger(v, log_sink, &cap), SYNC_OK);
    EXPECT_EQ(apply_all(v, owner), SYNC_ERR_UNAUTHORIZED);
    ASSERT_FALSE(cap.msgs.empty()) << "logger captured nothing";

    /* No log line leaks the value, field, or namespace content. */
    for (const auto &m : cap.msgs) {
        EXPECT_EQ(m.find("TOPSECRETVALUE"), std::string::npos);
        EXPECT_EQ(m.find("secretfield"), std::string::npos);
    }

    /* Clearing the logger silences it. */
    sync_engine_set_logger(v, nullptr, nullptr);
    cap.msgs.clear();
    apply_all(v, owner);
    EXPECT_TRUE(cap.msgs.empty());

    sync_engine_destroy(owner);
    sync_engine_destroy(v);
}

/* ---- Invite encode/decode (discovery) ---------------------------------- */
TEST(Security, InviteRoundTrip) {
    sync_engine *owner = sync_engine_create(seed_from(0x01).data());
    sync_engine *peer = sync_engine_create(seed_from(0x02).data());
    uint8_t ppk[SYNC_PUBKEY_LEN];
    sync_engine_identity(peer, ppk);

    /* Owner mints a capability for the peer and bundles it into an invite. */
    sync_capability *root = sync_capability_root(owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_capability *deleg = sync_capability_delegate(owner, root, ppk, SYNC_ACCESS_WRITE, 0);
    const char *addr = "relay.example:9000";

    size_t need = sync_invite_encode(ppk, addr, deleg, nullptr, 0);
    ASSERT_GT(need, 0u);
    std::vector<uint8_t> buf(need);
    ASSERT_EQ(sync_invite_encode(ppk, addr, deleg, buf.data(), buf.size()), need);

    uint8_t got_pk[SYNC_PUBKEY_LEN];
    char got_addr[128];
    sync_capability *got_cap = nullptr;
    ASSERT_EQ(sync_invite_decode(buf.data(), buf.size(), got_pk, got_addr,
                                 sizeof got_addr, &got_cap),
              SYNC_OK);
    EXPECT_EQ(0, std::memcmp(got_pk, ppk, SYNC_PUBKEY_LEN));
    EXPECT_STREQ(got_addr, addr);
    ASSERT_NE(got_cap, nullptr);

    /* The carried capability is usable: granting it authorizes the peer. */
    sync_engine *v = sync_engine_create(seed_from(0x09).data());
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(v, got_cap), SYNC_OK);
    set(peer, "nsA", "p", "f", "ok");
    EXPECT_EQ(apply_all(v, peer), SYNC_OK);

    /* Invite without a capability also round-trips. */
    size_t n2 = sync_invite_encode(ppk, addr, nullptr, nullptr, 0);
    std::vector<uint8_t> b2(n2);
    sync_invite_encode(ppk, addr, nullptr, b2.data(), b2.size());
    sync_capability *c2 = (sync_capability *)0x1;
    ASSERT_EQ(sync_invite_decode(b2.data(), b2.size(), got_pk, got_addr,
                                 sizeof got_addr, &c2),
              SYNC_OK);
    EXPECT_EQ(c2, nullptr);

    sync_capability_free(root);
    sync_capability_free(deleg);
    sync_capability_free(got_cap);
    sync_engine_destroy(owner);
    sync_engine_destroy(peer);
    sync_engine_destroy(v);
}

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

/* An unauthorized far-future record must not advance the engine's HLC clock.
 *
 * The HLC physical adopts the max remote timestamp on receive, so a far-future
 * value would pin the engine clock (and, because the clock is engine-global,
 * degrade the wall-clock quality of conflict resolution across *all*
 * namespaces). The verify-on-win path gates this: clock.receive runs only after
 * signature + capability checks pass, so a record that is rejected for lack of
 * authorization reaches neither state nor the clock. This locks that ordering
 * in — a rejected far-future write leaves the engine's own subsequent writes
 * stamped at real wall-clock time, not the attacker's far future. */
TEST(Security, UnauthorizedFutureWriteDoesNotPoisonClock) {
    const uint64_t kFarFuture = 4000000000000ull; /* ms, ~year 2096 */

    /* v enforces "nsA": it holds a root owned by `owner` (the proven-enforcing
     * pattern from WriteAuthorization). v is NOT a delegate, so v writes only to
     * the open namespace "open" — which is what we use to observe v's clock. */
    sync_engine *owner = sync_engine_create(seed_from(0x21).data());
    sync_engine *v = sync_engine_create(seed_from(0x23).data());
    sync_capability *root =
        sync_capability_root(owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);

    /* A stranger (no capability) forges a far-future register in enforced nsA.
     * (Named locals: cluster::B borrows its argument, so the bytes must outlive
     * every use of `ff` — a temporary would dangle.) */
    const std::string ns = "nsA", ent = "x", field = "f", poison = "poison";
    sync_change ff;
    std::memset(&ff, 0, sizeof ff);
    ff.kind = SYNC_CHANGE_REGISTER;
    ff.ns = B(ns); ff.ns_len = ns.size();
    ff.entity = B(ent); ff.entity_len = ent.size();
    ff.field = B(field); ff.field_len = field.size();
    ff.value = B(poison); ff.value_len = poison.size();
    ff.hlc.physical = kFarFuture;
    ff.hlc.logical = 0;
    ASSERT_EQ(sync_change_sign(&ff, seed_from(0x22).data()), SYNC_OK);

    /* It wins LWW (huge physical) so it is not dropped as dominated, but it is
     * unauthorized, so apply must reject it before touching state or the clock. */
    EXPECT_EQ(sync_engine_apply(v, &ff), SYNC_ERR_UNAUTHORIZED);

    /* v now writes an open namespace. If the rejected record had poisoned the
     * clock, this write's physical would be pinned at kFarFuture; it must
     * instead carry a real (near-now) timestamp. */
    set(v, "open", "y", "f", "honest");

    sync_change *recs = nullptr;
    size_t n = 0;
    ASSERT_EQ(sync_engine_export(v, &recs, &n), SYNC_OK);
    bool saw_register = false;
    for (size_t i = 0; i < n; i++) {
        if (recs[i].kind == SYNC_CHANGE_REGISTER) {
            saw_register = true;
            EXPECT_LT(recs[i].hlc.physical, kFarFuture)
                << "engine clock was poisoned by a rejected far-future record";
        }
    }
    EXPECT_TRUE(saw_register);
    sync_changes_free(recs, n);

    sync_capability_free(root);
    sync_engine_destroy(owner);
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

/* The read-scope cache (reconcile.cpp ensure_scoped_cache) may cache a peer's
 * scoped snapshot only when its scope cannot change with time alone.
 * cap_authorize_read reports that via `time_bound`: open/unowned namespaces and
 * permanent-cap grants are stable (cacheable); a finite-expiry read cap makes
 * inclusion time-bound (not cacheable), so capability expiry stays exact even
 * with caching. This locks the predicate the cache relies on. */
TEST(Security, ReadScopeTimeBoundFlag) {
    sync_engine *owner = sync_engine_create(seed_from(0x31).data());
    sync_engine *v = sync_engine_create(seed_from(0x32).data());
    sync_engine *p = sync_engine_create(seed_from(0x33).data());
    uint8_t ppk[SYNC_PUBKEY_LEN];
    sync_engine_identity(p, ppk);

    /* Open (unowned) namespace: no caps consulted → stable, cacheable. */
    bool tb = true;
    EXPECT_TRUE(ke::cap_authorize_read(v, ppk, "open", &tb));
    EXPECT_FALSE(tb) << "open namespace must not be time-bound";

    /* v owns "ns"; grant P a *permanent* (expiry==0) read delegation → stable. */
    sync_capability *root =
        sync_capability_root(owner, "ns", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    sync_capability *perm =
        sync_capability_delegate(owner, root, ppk, SYNC_ACCESS_READ, 0);
    ASSERT_EQ(sync_engine_grant(v, perm), SYNC_OK);
    tb = true;
    EXPECT_TRUE(ke::cap_authorize_read(v, ppk, "ns", &tb));
    EXPECT_FALSE(tb) << "permanent read cap must not be time-bound";

    /* Peer Q holds a *finite-expiry* (still-usable) read cap → time-bound. */
    sync_engine *q = sync_engine_create(seed_from(0x34).data());
    uint8_t qpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(q, qpk);
    const uint64_t kFarFuture = 4000000000000ull; /* ~2096, still usable */
    sync_capability *temp =
        sync_capability_delegate(owner, root, qpk, SYNC_ACCESS_READ, kFarFuture);
    ASSERT_EQ(sync_engine_grant(v, temp), SYNC_OK);
    tb = false;
    EXPECT_TRUE(ke::cap_authorize_read(v, qpk, "ns", &tb));
    EXPECT_TRUE(tb) << "finite-expiry read cap must be flagged time-bound";

    /* Peer R holds only an *expired* cap → filtered out, R excluded. Exclusion is
     * stable (access only decreases as caps expire), so it is not time-bound. */
    sync_engine *r = sync_engine_create(seed_from(0x35).data());
    uint8_t rpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(r, rpk);
    sync_capability *expd =
        sync_capability_delegate(owner, root, rpk, SYNC_ACCESS_READ, 1 /* ms */);
    ASSERT_EQ(sync_engine_grant(v, expd), SYNC_OK);
    tb = true;
    EXPECT_FALSE(ke::cap_authorize_read(v, rpk, "ns", &tb));
    EXPECT_FALSE(tb) << "an excluded (expired-cap) peer is stable, not time-bound";

    sync_capability_free(root);
    sync_capability_free(perm);
    sync_capability_free(temp);
    sync_capability_free(expd);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(p);
    sync_engine_destroy(q);
    sync_engine_destroy(r);
}

/* Promoting a member's role — granting a second, broader delegation to a subject
 * who already holds a narrower one — must take effect regardless of grant order.
 * Regression for the first-match chain walk that honored only whichever single
 * delegation it reached first, so a READ-then-READ|WRITE upgrade was denied. */
TEST(Security, RoleUpgradeBroadensAccess) {
    for (int rw_first = 0; rw_first <= 1; rw_first++) {
        sync_engine *owner = sync_engine_create(seed_from(0x41).data());
        sync_engine *v = sync_engine_create(seed_from(0x49).data()); /* enforcer */
        sync_engine *carol = sync_engine_create(seed_from(0x43).data());
        uint8_t cpk[SYNC_PUBKEY_LEN];
        sync_engine_identity(carol, cpk);

        sync_capability *root = sync_capability_root(
            owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
        sync_capability *rd =
            sync_capability_delegate(owner, root, cpk, SYNC_ACCESS_READ, 0);
        sync_capability *rw = sync_capability_delegate(
            owner, root, cpk, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);
        if (rw_first) {
            ASSERT_EQ(sync_engine_grant(v, rw), SYNC_OK);
            ASSERT_EQ(sync_engine_grant(v, rd), SYNC_OK);
        } else {
            ASSERT_EQ(sync_engine_grant(v, rd), SYNC_OK);
            ASSERT_EQ(sync_engine_grant(v, rw), SYNC_OK);
        }

        /* Carol writes; the enforcing replica must accept it (she holds R|W). */
        set(carol, "nsA", "c1", "f", "hi");
        EXPECT_EQ(apply_all(v, carol), SYNC_OK)
            << "role upgrade denied with rw_first=" << rw_first;

        sync_capability_free(root);
        sync_capability_free(rd);
        sync_capability_free(rw);
        sync_engine_destroy(owner);
        sync_engine_destroy(v);
        sync_engine_destroy(carol);
    }
}

/* Two independent delegation chains to the same subject union their access:
 * holding READ via one chain and WRITE via another means holding both. The old
 * walk reached the subject via a single chain and used only that chain's access
 * for every query, so one of the two rights was always denied. */
TEST(Security, DiamondDelegationUnionsAccess) {
    sync_engine *owner = sync_engine_create(seed_from(0x51).data());
    sync_engine *x = sync_engine_create(seed_from(0x52).data());
    sync_engine *y = sync_engine_create(seed_from(0x53).data());
    sync_engine *carol = sync_engine_create(seed_from(0x54).data());
    sync_engine *v = sync_engine_create(seed_from(0x59).data()); /* enforcer */
    uint8_t xpk[SYNC_PUBKEY_LEN], ypk[SYNC_PUBKEY_LEN], cpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(x, xpk);
    sync_engine_identity(y, ypk);
    sync_engine_identity(carol, cpk);

    sync_capability *root = sync_capability_root(
        owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    /* owner -> X (R|W), owner -> Y (R|W). */
    sync_capability *ox = sync_capability_delegate(
        owner, root, xpk, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);
    sync_capability *oy = sync_capability_delegate(
        owner, root, ypk, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);
    /* X -> Carol (READ only); Y -> Carol (WRITE only). */
    sync_capability *xc = sync_capability_delegate(x, ox, cpk, SYNC_ACCESS_READ, 0);
    sync_capability *yc = sync_capability_delegate(y, oy, cpk, SYNC_ACCESS_WRITE, 0);
    for (sync_capability *c : {root, ox, oy, xc, yc})
        ASSERT_EQ(sync_engine_grant(v, c), SYNC_OK);

    /* WRITE via the Y chain. */
    set(carol, "nsA", "c1", "f", "hi");
    EXPECT_EQ(apply_all(v, carol), SYNC_OK) << "WRITE via the Y chain not honored";
    /* READ via the X chain. */
    EXPECT_TRUE(ke::cap_authorize_read(v, cpk, "nsA"))
        << "READ via the X chain not honored";

    for (sync_capability *c : {root, ox, oy, xc, yc}) sync_capability_free(c);
    sync_engine_destroy(owner);
    sync_engine_destroy(x);
    sync_engine_destroy(y);
    sync_engine_destroy(carol);
    sync_engine_destroy(v);
}

/* An expired delegation in the middle of a chain revokes everything downstream:
 * owner -> A (permanent) -> B (expired) leaves A authorized but cuts off B, since
 * the expired link is filtered before the chain is walked. */
TEST(Security, ExpiredMidChainDelegationRevokes) {
    sync_engine *owner = sync_engine_create(seed_from(0x61).data());
    sync_engine *a = sync_engine_create(seed_from(0x62).data());
    sync_engine *bd = sync_engine_create(seed_from(0x63).data());
    sync_engine *v = sync_engine_create(seed_from(0x69).data()); /* enforcer */
    uint8_t apk[SYNC_PUBKEY_LEN], bpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(a, apk);
    sync_engine_identity(bd, bpk);

    sync_capability *root = sync_capability_root(
        owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_capability *oa = sync_capability_delegate(
        owner, root, apk, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);     /* permanent */
    sync_capability *ab = sync_capability_delegate(
        a, oa, bpk, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 1 /* expired */);
    for (sync_capability *c : {root, oa, ab})
        ASSERT_EQ(sync_engine_grant(v, c), SYNC_OK);

    set(a, "nsA", "x", "f", "ok");
    EXPECT_EQ(apply_all(v, a), SYNC_OK) << "A holds a permanent cap";
    set(bd, "nsA", "y", "f", "stale");
    EXPECT_EQ(apply_all(v, bd), SYNC_ERR_UNAUTHORIZED)
        << "an expired mid-chain link must revoke the downstream subject";

    for (sync_capability *c : {root, oa, ab}) sync_capability_free(c);
    sync_engine_destroy(owner); sync_engine_destroy(a);
    sync_engine_destroy(bd); sync_engine_destroy(v);
}

/* Capability expiry takes effect as wall-clock time passes: a delegation valid
 * now becomes unusable once its expiry deadline is reached, with no event other
 * than the clock advancing. (Real-time test with a short sleep; the deadline and
 * sleep are chosen with a wide margin so it is not timing-fragile.) */
TEST(Security, ExpiryTransitionRevokesOverTime) {
    sync_engine *owner = sync_engine_create(seed_from(0x71).data());
    sync_engine *v = sync_engine_create(seed_from(0x79).data()); /* enforcer */
    sync_engine *peer = sync_engine_create(seed_from(0x72).data());
    uint8_t ppk[SYNC_PUBKEY_LEN];
    sync_engine_identity(peer, ppk);

    sync_capability *root = sync_capability_root(
        owner, "ns", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    sync_capability *d = sync_capability_delegate(
        owner, root, ppk, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, ke::now_ms() + 250);
    ASSERT_EQ(sync_engine_grant(v, d), SYNC_OK);

    set(peer, "ns", "before", "f", "v1");
    EXPECT_EQ(apply_all(v, peer), SYNC_OK) << "authorized before expiry";

    std::this_thread::sleep_for(std::chrono::milliseconds(400)); /* cross the deadline */

    set(peer, "ns", "after", "f", "v2");
    EXPECT_EQ(apply_all(v, peer), SYNC_ERR_UNAUTHORIZED) << "revoked once expired";

    sync_capability_free(root);
    sync_capability_free(d);
    sync_engine_destroy(owner);
    sync_engine_destroy(v);
    sync_engine_destroy(peer);
}

/* Capability attenuation: a delegation confers at most what its issuer can
 * currently prove, not what the delegation nominally claims. When a holder's
 * broader cap expires, delegations it issued narrow to the holder's remaining
 * (permanent) access rather than being voided entirely. */
TEST(Security, AttenuatedDelegationConfersProvableSubset) {
    sync_engine *owner = sync_engine_create(seed_from(0x81).data());
    sync_engine *holder = sync_engine_create(seed_from(0x82).data());
    sync_engine *x = sync_engine_create(seed_from(0x83).data());
    sync_engine *v = sync_engine_create(seed_from(0x89).data()); /* enforcer */
    uint8_t hpk[SYNC_PUBKEY_LEN], xpk[SYNC_PUBKEY_LEN];
    sync_engine_identity(holder, hpk);
    sync_engine_identity(x, xpk);

    sync_capability *root = sync_capability_root(
        owner, "nsA", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_EQ(sync_engine_grant(v, root), SYNC_OK);
    /* Holder gets an EXPIRED R|W and a PERMANENT READ from the owner. */
    sync_capability *exp_rw = sync_capability_delegate(
        owner, root, hpk, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 1 /* expired */);
    sync_capability *perm_r = sync_capability_delegate(
        owner, root, hpk, SYNC_ACCESS_READ, 0 /* permanent */);
    ASSERT_EQ(sync_engine_grant(v, exp_rw), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(v, perm_r), SYNC_OK);
    /* Holder delegates R|W to X from its (now-expired) R|W cap. */
    sync_capability *to_x =
        sync_capability_delegate(holder, exp_rw, xpk, SYNC_ACCESS_READ | SYNC_ACCESS_WRITE, 0);
    ASSERT_NE(to_x, nullptr);
    ASSERT_EQ(sync_engine_grant(v, to_x), SYNC_OK);

    /* Holder can now only prove READ (its R|W expired), so X is attenuated to
     * READ: readable, NOT writable, and crucially NOT denied entirely. */
    EXPECT_TRUE(ke::cap_authorize_read(v, xpk, "nsA"))
        << "attenuated delegation must still confer the issuer's provable READ";
    set(x, "nsA", "rec", "f", "v");
    EXPECT_EQ(apply_all(v, x), SYNC_ERR_UNAUTHORIZED)
        << "X must not gain WRITE the issuer cannot currently prove";

    sync_capability_free(root);
    sync_capability_free(exp_rw);
    sync_capability_free(perm_r);
    sync_capability_free(to_x);
    sync_engine_destroy(owner);
    sync_engine_destroy(holder);
    sync_engine_destroy(x);
    sync_engine_destroy(v);
}

/* A scope whose readable set depends on a finite-expiry cap must never be cached,
 * even when an EARLIER-sorted namespace is denied. Regression for a pre-scan that
 * stopped at the first denied namespace and so missed a later expiring one,
 * caching the scope and serving it after the cap expired. */
TEST(Security, ExpiringScopeNotCachedPastExpiry) {
    sync_engine *owner = sync_engine_create(seed_from(0x91).data());
    sync_engine *v = sync_engine_create(seed_from(0x99).data()); /* enforcer/sender */
    sync_engine *p = sync_engine_create(seed_from(0x92).data());
    uint8_t ppk[SYNC_PUBKEY_LEN];
    sync_engine_identity(p, ppk);

    /* v owns "a" (P will be denied) and "z" (P gets a soon-expiring READ). "a" < "z"
     * so a pre-scan that breaks on the denied "a" would never see z's expiry. */
    sync_capability *ra = sync_capability_root(owner, "a", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_capability *rz = sync_capability_root(owner, "z", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_EQ(sync_engine_grant(v, ra), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(v, rz), SYNC_OK);
    sync_capability *dz = sync_capability_delegate(owner, rz, ppk, SYNC_ACCESS_READ,
                                                   ke::now_ms() + 400 /* expires soon */);
    ASSERT_EQ(sync_engine_grant(v, dz), SYNC_OK);
    set(owner, "a", "arec", "f", "x");
    set(owner, "z", "zrec", "f", "secret");
    ASSERT_EQ(apply_all(v, owner), SYNC_OK);

    /* While the cap is valid, P syncs and receives z (and not a). This populates
     * v's per-peer scoped cache for P. */
    {
        sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
        sync_session *sp = sync_session_begin(p, 0);
        EXPECT_TRUE(drive(sv, sp));
        sync_session_end(sv); sync_session_end(sp);
    }
    EXPECT_EQ(exists(p, "z", "zrec"), 1) << "P should read z while the cap is valid";
    EXPECT_EQ(exists(p, "a", "arec"), 0) << "P is denied a";

    std::this_thread::sleep_for(std::chrono::milliseconds(550)); /* cross expiry */

    /* A fresh peer with P's identity syncs after expiry. With no write to bump
     * content_gen (and no capability change to bump scope_gen), a wrongly-cached
     * scope would still serve z. */
    sync_engine *p2 = sync_engine_create(seed_from(0x92).data()); /* same identity as p */
    {
        sync_session *sv = sync_session_begin_scoped(v, 1, ppk);
        sync_session *sp = sync_session_begin(p2, 0);
        EXPECT_TRUE(drive(sv, sp));
        sync_session_end(sv); sync_session_end(sp);
    }
    EXPECT_EQ(exists(p2, "z", "zrec"), 0)
        << "z served after its read cap expired (scope was cached despite being time-bound)";

    sync_capability_free(ra); sync_capability_free(rz); sync_capability_free(dz);
    sync_engine_destroy(owner); sync_engine_destroy(v);
    sync_engine_destroy(p); sync_engine_destroy(p2);
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
