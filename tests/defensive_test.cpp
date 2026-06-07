/* defensive_test.cpp — exercise the library's defensive paths: NULL and
 * invalid arguments, malformed/truncated input, and bad versions. Verifies the
 * public ABI rejects misuse gracefully (no crash, correct error code) rather
 * than only the happy path. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <string>
#include <vector>

namespace {
std::array<uint8_t, SYNC_SEED_LEN> seed(uint8_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (auto &b : s) b = v;
    return s;
}
const uint8_t *U(const char *s) { return (const uint8_t *)s; }
} // namespace

/* ---- Lifecycle / NULL handles ------------------------------------------ */
TEST(Defensive, LifecycleNullArgs) {
    EXPECT_EQ(sync_engine_create(nullptr), nullptr);
    EXPECT_EQ(sync_engine_open(nullptr, seed(1).data()), nullptr);
    EXPECT_EQ(sync_engine_open("/tmp/x", nullptr), nullptr);

    /* Safe no-ops on NULL. */
    sync_engine_destroy(nullptr);
    sync_session_end(nullptr);
    sync_capability_free(nullptr);
    sync_change_free_decoded(nullptr);
    sync_changes_free(nullptr, 0);
    sync_free(nullptr);

    EXPECT_EQ(sync_engine_flush(nullptr), SYNC_ERR_INVALID);
    uint8_t out[SYNC_PUBKEY_LEN];
    EXPECT_EQ(sync_engine_identity(nullptr, out), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_site_id(nullptr, out), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_set_logger(nullptr, nullptr, nullptr), SYNC_ERR_INVALID);
}

/* ---- CRUD invalid args ------------------------------------------------- */
TEST(Defensive, CrudInvalidArgs) {
    sync_engine *e = sync_engine_create(seed(2).data());
    ASSERT_NE(e, nullptr);

    /* NULL engine. */
    EXPECT_EQ(sync_engine_set(nullptr, U("n"), 1, U("x"), 1, U("f"), 1, U("v"), 1),
              SYNC_ERR_INVALID);
    /* NULL pointer with non-zero length. */
    EXPECT_EQ(sync_engine_set(e, nullptr, 1, U("x"), 1, U("f"), 1, U("v"), 1),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_set(e, U("n"), 1, nullptr, 1, U("f"), 1, U("v"), 1),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_set(e, U("n"), 1, U("x"), 1, nullptr, 1, U("v"), 1),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_set(e, U("n"), 1, U("x"), 1, U("f"), 1, nullptr, 1),
              SYNC_ERR_INVALID);

    EXPECT_EQ(sync_engine_delete(nullptr, U("n"), 1, U("x"), 1), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_delete(e, nullptr, 1, U("x"), 1), SYNC_ERR_INVALID);

    uint8_t *val = nullptr;
    size_t vl = 0;
    EXPECT_EQ(sync_engine_get(nullptr, U("n"), 1, U("x"), 1, U("f"), 1, &val, &vl),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_get(e, U("n"), 1, U("x"), 1, U("f"), 1, nullptr, &vl),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_get(e, U("n"), 1, U("x"), 1, U("f"), 1, &val, nullptr),
              SYNC_ERR_INVALID);
    /* Not found is a clean error, not a crash. */
    EXPECT_EQ(sync_engine_get(e, U("nope"), 4, U("x"), 1, U("f"), 1, &val, &vl),
              SYNC_ERR_NOTFOUND);

    int present = 0;
    EXPECT_EQ(sync_engine_exists(nullptr, U("n"), 1, U("x"), 1, &present),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_exists(e, U("n"), 1, U("x"), 1, nullptr),
              SYNC_ERR_INVALID);

    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_EQ(sync_engine_export(nullptr, &recs, &n), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_export(e, nullptr, &n), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_export(e, &recs, nullptr), SYNC_ERR_INVALID);

    uint8_t dig[SYNC_DIGEST_LEN];
    EXPECT_EQ(sync_engine_digest(nullptr, dig), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_digest(e, nullptr), SYNC_ERR_INVALID);

    sync_engine_destroy(e);
}

/* ---- apply invalid args ------------------------------------------------ */
TEST(Defensive, ApplyInvalid) {
    sync_engine *e = sync_engine_create(seed(3).data());
    EXPECT_EQ(sync_engine_apply(nullptr, nullptr), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_apply(e, nullptr), SYNC_ERR_INVALID);

    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = 99; /* unknown kind */
    c.ns = U("n"); c.ns_len = 1;
    c.entity = U("x"); c.entity_len = 1;
    EXPECT_EQ(sync_engine_apply(e, &c), SYNC_ERR_INVALID);

    /* NULL ns with non-zero length. */
    c.kind = SYNC_CHANGE_EXISTENCE;
    c.ns = nullptr; c.ns_len = 3;
    EXPECT_EQ(sync_engine_apply(e, &c), SYNC_ERR_INVALID);

    /* Register with NULL field but non-zero field_len. */
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_REGISTER;
    c.ns = U("n"); c.ns_len = 1;
    c.entity = U("x"); c.entity_len = 1;
    c.field = nullptr; c.field_len = 2;
    EXPECT_EQ(sync_engine_apply(e, &c), SYNC_ERR_INVALID);

    /* Validly signed record with a tampered signature -> rejected. */
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_REGISTER;
    c.ns = U("n"); c.ns_len = 1;
    c.entity = U("x"); c.entity_len = 1;
    c.field = U("f"); c.field_len = 1;
    c.value = U("v"); c.value_len = 1;
    ASSERT_EQ(sync_change_sign(&c, seed(9).data()), SYNC_OK);
    c.signature[0] ^= 0x01; /* corrupt */
    EXPECT_EQ(sync_engine_apply(e, &c), SYNC_ERR_BADSIG);

    sync_engine_destroy(e);
}

/* verify-on-win contract (docs/PERF.md, optimization ch.2): apply checks a
 * record's signature only if it would change state. A forged record that would
 * LOSE LWW is dropped silently (no error, no state change — it reaches no
 * state); one that would WIN is verified and rejected. No forged data is ever
 * accepted either way. */
TEST(Defensive, VerifyOnlyWhenRecordWouldChangeState) {
    sync_engine *e = sync_engine_create(seed(7).data());
    auto b = [](const std::string &s) { return (const uint8_t *)s.data(); };
    const std::string n = "n", x = "x", f = "f";

    /* Make (n,x) present so get() returns its register. */
    {
        sync_change c;
        std::memset(&c, 0, sizeof c);
        c.kind = SYNC_CHANGE_EXISTENCE;
        c.ns = b(n); c.ns_len = 1; c.entity = b(x); c.entity_len = 1;
        c.causal_length = 1;
        ASSERT_EQ(sync_change_sign(&c, seed(7).data()), SYNC_OK);
        ASSERT_EQ(sync_engine_apply(e, &c), SYNC_OK);
    }

    auto reg = [&](uint64_t phys, const std::string &val) {
        sync_change c;
        std::memset(&c, 0, sizeof c);
        c.kind = SYNC_CHANGE_REGISTER;
        c.ns = b(n); c.ns_len = 1; c.entity = b(x); c.entity_len = 1;
        c.field = b(f); c.field_len = 1;
        c.value = b(val); c.value_len = val.size();
        c.hlc.physical = phys;
        sync_change_sign(&c, seed(7).data());
        return c;
    };
    auto value = [&]() -> std::string {
        uint8_t *v = nullptr; size_t vl = 0;
        int rc = sync_engine_get(e, b(n), 1, b(x), 1, b(f), 1, &v, &vl);
        std::string s = rc == SYNC_OK ? std::string((char *)v, vl) : "<none>";
        if (v) sync_free(v);
        return s;
    };

    /* A legitimately signed value at a high HLC. */
    const std::string good = "good", evil_lo = "evil-lo", evil_hi = "evil-hi";
    sync_change ok = reg(1000000, good);
    ASSERT_EQ(sync_engine_apply(e, &ok), SYNC_OK);
    EXPECT_EQ(value(), "good");

    /* Forged + would-lose (lower HLC): skipped without verifying -> SYNC_OK. */
    sync_change lose = reg(5, evil_lo);
    lose.signature[0] ^= 0x01;
    EXPECT_EQ(sync_engine_apply(e, &lose), SYNC_OK);
    EXPECT_EQ(value(), "good") << "a dominated record must not change state";

    /* Forged + would-win (higher HLC): verified and rejected. */
    sync_change win = reg(2000000, evil_hi);
    win.signature[0] ^= 0x01;
    EXPECT_EQ(sync_engine_apply(e, &win), SYNC_ERR_BADSIG);
    EXPECT_EQ(value(), "good") << "a forged winning record must be rejected";

    sync_engine_destroy(e);
}

/* ---- codec invalid / malformed ----------------------------------------- */
TEST(Defensive, CodecInvalid) {
    EXPECT_EQ(sync_change_encode(nullptr, nullptr, 0), 0u);

    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = 42; /* bad kind */
    EXPECT_EQ(sync_change_encode(&c, nullptr, 0), 0u);

    sync_change out;
    size_t consumed = 0;
    EXPECT_EQ(sync_change_decode(nullptr, 10, &out, &consumed), SYNC_ERR_INVALID);
    std::vector<uint8_t> buf = {0x00};
    EXPECT_EQ(sync_change_decode(buf.data(), buf.size(), nullptr, &consumed),
              SYNC_ERR_INVALID);

    /* Empty / truncated / wrong-version / bad-kind inputs decode cleanly to
     * an error (no crash). */
    EXPECT_NE(sync_change_decode((const uint8_t *)"", 0, &out, &consumed), SYNC_OK);
    std::vector<uint8_t> badver = {0x99, 0x00};
    EXPECT_NE(sync_change_decode(badver.data(), badver.size(), &out, &consumed),
              SYNC_OK);
    std::vector<uint8_t> badkind = {0x02, 0x7f, 0x01, 'n'};
    EXPECT_NE(sync_change_decode(badkind.data(), badkind.size(), &out, &consumed),
              SYNC_OK);
    std::vector<uint8_t> trunc = {0x02, 0x00, 0x05, 'a'}; /* ns_len 5, 1 byte */
    EXPECT_NE(sync_change_decode(trunc.data(), trunc.size(), &out, &consumed),
              SYNC_OK);

    /* sign with NULL args. */
    EXPECT_EQ(sync_change_sign(nullptr, seed(1).data()), SYNC_ERR_INVALID);
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_REGISTER;
    EXPECT_EQ(sync_change_sign(&c, nullptr), SYNC_ERR_INVALID);
    c.kind = 7; /* bad kind */
    EXPECT_EQ(sync_change_sign(&c, seed(1).data()), SYNC_ERR_INVALID);
}

/* ---- session invalid args ---------------------------------------------- */
TEST(Defensive, SessionInvalid) {
    EXPECT_EQ(sync_session_begin(nullptr, 1), nullptr);
    EXPECT_EQ(sync_session_begin_scoped(nullptr, 1, seed(1).data()), nullptr);

    sync_engine *e = sync_engine_create(seed(4).data());
    EXPECT_EQ(sync_session_begin_scoped(e, 1, nullptr), nullptr);

    sync_session *s = sync_session_begin(e, 1);
    ASSERT_NE(s, nullptr);
    uint8_t *out = nullptr;
    size_t ol = 0;
    int done = 0;
    EXPECT_EQ(sync_session_step(nullptr, nullptr, 0, &out, &ol, &done),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_session_step(s, nullptr, 0, nullptr, &ol, &done),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_session_step(s, nullptr, 0, &out, nullptr, &done),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_session_step(s, nullptr, 0, &out, &ol, nullptr),
              SYNC_ERR_INVALID);
    sync_session_end(s);

    /* Malformed incoming message -> clean error (responder processes input;
     * an initiator ignores input on its first step by design). */
    sync_session *r = sync_session_begin(e, 0);
    ASSERT_NE(r, nullptr);
    std::vector<uint8_t> junk = {0xff, 0xff, 0xff};
    EXPECT_EQ(sync_session_step(r, junk.data(), junk.size(), &out, &ol, &done),
              SYNC_ERR_INVALID);
    sync_session_end(r);
    sync_engine_destroy(e);
}

/* ---- capability invalid args ------------------------------------------- */
TEST(Defensive, CapabilityInvalid) {
    sync_engine *owner = sync_engine_create(seed(5).data());
    EXPECT_EQ(sync_capability_root(nullptr, "ns", SYNC_ACCESS_READ), nullptr);
    EXPECT_EQ(sync_capability_root(owner, nullptr, SYNC_ACCESS_READ), nullptr);
    EXPECT_EQ(sync_capability_root(owner, "ns", 0), nullptr);          /* empty access */
    EXPECT_EQ(sync_capability_root(owner, "ns", 0xff), nullptr);       /* bad bits */

    sync_capability *root = sync_capability_root(owner, "ns", SYNC_ACCESS_READ);
    ASSERT_NE(root, nullptr);
    uint8_t sub[SYNC_PUBKEY_LEN];
    std::memset(sub, 7, sizeof sub);
    EXPECT_EQ(sync_capability_delegate(nullptr, root, sub, SYNC_ACCESS_READ, 0), nullptr);
    EXPECT_EQ(sync_capability_delegate(owner, nullptr, sub, SYNC_ACCESS_READ, 0), nullptr);
    EXPECT_EQ(sync_capability_delegate(owner, root, nullptr, SYNC_ACCESS_READ, 0), nullptr);
    EXPECT_EQ(sync_capability_delegate(owner, root, sub, 0, 0), nullptr);
    /* over-broad (WRITE from READ-only parent). */
    EXPECT_EQ(sync_capability_delegate(owner, root, sub, SYNC_ACCESS_WRITE, 0), nullptr);

    EXPECT_EQ(sync_capability_encode(nullptr, nullptr, 0), 0);
    EXPECT_EQ(sync_capability_decode(nullptr, 10), nullptr);
    std::vector<uint8_t> junk = {0x00};
    EXPECT_EQ(sync_capability_decode(junk.data(), junk.size()), nullptr);

    EXPECT_EQ(sync_engine_grant(nullptr, root), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_grant(owner, nullptr), SYNC_ERR_INVALID);

    sync_capability_free(root);
    sync_engine_destroy(owner);
}

/* ---- invite invalid args ----------------------------------------------- */
TEST(Defensive, InviteInvalid) {
    uint8_t pk[SYNC_PUBKEY_LEN];
    std::memset(pk, 1, sizeof pk);
    EXPECT_EQ(sync_invite_encode(nullptr, "addr", nullptr, nullptr, 0), 0u);
    EXPECT_EQ(sync_invite_encode(pk, nullptr, nullptr, nullptr, 0), 0u);

    /* A valid encoding, then decode-side errors. */
    size_t need = sync_invite_encode(pk, "addr", nullptr, nullptr, 0);
    ASSERT_GT(need, 0u);
    std::vector<uint8_t> buf(need);
    sync_invite_encode(pk, "addr", nullptr, buf.data(), buf.size());

    uint8_t gpk[SYNC_PUBKEY_LEN];
    char addr[64];
    EXPECT_EQ(sync_invite_decode(nullptr, need, gpk, addr, sizeof addr, nullptr),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_invite_decode(buf.data(), need, nullptr, addr, sizeof addr, nullptr),
              SYNC_ERR_INVALID);
    EXPECT_EQ(sync_invite_decode(buf.data(), need, gpk, nullptr, sizeof addr, nullptr),
              SYNC_ERR_INVALID);
    /* Address buffer too small. */
    EXPECT_EQ(sync_invite_decode(buf.data(), need, gpk, addr, 1, nullptr),
              SYNC_ERR_INVALID);
    /* Truncated / malformed. */
    EXPECT_EQ(sync_invite_decode(buf.data(), 1, gpk, addr, sizeof addr, nullptr),
              SYNC_ERR_INVALID);
    std::vector<uint8_t> badver = {0x99};
    EXPECT_EQ(sync_invite_decode(badver.data(), 1, gpk, addr, sizeof addr, nullptr),
              SYNC_ERR_INVALID);
}
