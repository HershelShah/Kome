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

#ifndef __EMSCRIPTEN__
#include <sys/wait.h> /* RevokeInsideBatchSurvivesCrash (fork, native-only) */
#include <unistd.h>
#endif

#include "cluster.hpp"    /* put/get/exists + seed_from (batch-contract tests) */
#include "log_frames.hpp" /* fsync counter (revoke-inside-batch durability)   */
#include "tempdir.hpp"    /* durable-engine scaffolding, WASM-capable (§3.3)  */

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
        c.hlc.physical = 1; /* a real assertion: {0,0} is the "no assertion"
                             * sentinel and apply refuses it */
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

    /* F3: a reconcile message can't be amplified into GiBs of vector entries.
     * (a) An over-large message (> 8 MiB byte cap) is rejected before parsing. */
    sync_session *r2 = sync_session_begin(e, 0);
    ASSERT_NE(r2, nullptr);
    std::vector<uint8_t> huge(9u * 1024 * 1024, 0x00);
    EXPECT_EQ(sync_session_step(r2, huge.data(), huge.size(), &out, &ol, &done),
              SYNC_ERR_INVALID);
    sync_session_end(r2);

    /* (b) A message that *declares* more elements than the per-message budget
     * (1<<20) is rejected before allocating them. Hand-encode a cap-count varint
     * of 1,050,000 (> 1,048,576) followed by enough filler that the cheap
     * "count > remaining bytes" guard doesn't fire first — so it is the element
     * budget that rejects it. Must not OOM/crash (ASan-clean). */
    sync_session *r3 = sync_session_begin(e, 0);
    ASSERT_NE(r3, nullptr);
    std::vector<uint8_t> amp;
    amp.push_back(0x90); amp.push_back(0x8B); amp.push_back(0x40); /* varint 1050000 */
    amp.resize(amp.size() + 1050000, 0x00);
    EXPECT_EQ(sync_session_step(r3, amp.data(), amp.size(), &out, &ol, &done),
              SYNC_ERR_INVALID);
    sync_session_end(r3);
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

/* ---- Write batching (§3.3): ABI misuse + lifecycle contracts ------------- *
 * WASM-capable (no fork): durable engines come from synctest::TempDir, per
 * the resilience_test.cpp pattern. */

namespace {

/* Apply one signed register record authored by `seed_v`'s identity (the same
 * derivation cluster::apply_register uses), returning the raw status so the
 * unauthorized path is observable. Fresh entities + a fixed HLC keep the
 * record un-dominated, so apply reaches the signature/authorization gate. */
int apply_signed(sync_engine *e, const std::string &ns, const std::string &ent,
                 uint32_t seed_v, uint64_t physical) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_REGISTER;
    c.ns = (const uint8_t *)ns.data();
    c.ns_len = ns.size();
    c.entity = (const uint8_t *)ent.data();
    c.entity_len = ent.size();
    c.field = U("f");
    c.field_len = 1;
    c.value = U("v");
    c.value_len = 1;
    c.hlc.physical = physical;
    c.hlc.logical = 0;
    auto s = cluster::seed_from(seed_v);
    int rc = sync_change_sign(&c, s.data());
    if (rc != SYNC_OK) return rc;
    return sync_engine_apply(e, &c);
}

/* Signing public key of the identity derived from seed_v. */
void pk_of(uint32_t seed_v, uint8_t out[SYNC_PUBKEY_LEN]) {
    sync_engine *t = sync_engine_create(cluster::seed_from(seed_v).data());
    ASSERT_NE(t, nullptr);
    ASSERT_EQ(sync_engine_identity(t, out), SYNC_OK);
    sync_engine_destroy(t);
}

struct WarnCounter {
    int warns = 0;
};
void count_warns(void *ctx, int level, const char *) {
    if (level == SYNC_LOG_WARN) static_cast<WarnCounter *>(ctx)->warns++;
}

} // namespace

TEST(Defensive, BatchAbiMisuse) {
    /* NULL engine. */
    EXPECT_EQ(sync_engine_batch_begin(nullptr), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_batch_commit(nullptr), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_batch_abort(nullptr), SYNC_ERR_INVALID);

    /* In-memory engine: no log to batch — all three are clean no-ops, even
     * "unbalanced" ones (there is no depth to unbalance), and writes between
     * them behave exactly as without a batch. */
    sync_engine *m = sync_engine_create(seed(0x51).data());
    ASSERT_NE(m, nullptr);
    EXPECT_EQ(sync_engine_batch_commit(m), SYNC_OK); /* no begin: still OK */
    EXPECT_EQ(sync_engine_batch_abort(m), SYNC_OK);
    EXPECT_EQ(sync_engine_batch_begin(m), SYNC_OK);
    cluster::put(m, "ns", "k", "f", "v");
    EXPECT_EQ(sync_engine_batch_commit(m), SYNC_OK);
    EXPECT_EQ(cluster::get(m, "ns", "k", "f"), "v");
    /* In-memory compact refuses for its own reason: no log to rewrite. */
    EXPECT_EQ(sync_engine_compact(m), SYNC_ERR_INVALID);
    sync_engine_destroy(m);

    /* Durable engine: an unbalanced close is caught... */
    synctest::TempDir dir;
    std::string db = dir.file("abi_misuse.db");
    auto sd = cluster::seed_from(0xC6);
    sync_engine *e = sync_engine_open(db.c_str(), sd.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(sync_engine_batch_commit(e), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_batch_abort(e), SYNC_ERR_INVALID);

    /* ...compact refuses at EVERY open depth — the batch holds the log
     * transaction for its whole lifetime, so the erase-then-tombstone-then-
     * compact physical-erasure pairing must run OUTSIDE a batch, BY DESIGN
     * (documented at sync_engine_compact and the batch ABI section)... */
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
    cluster::put(e, "ns", "k", "f", "v");
    EXPECT_EQ(sync_engine_compact(e), SYNC_ERR_INTERNAL);
    ASSERT_EQ(sync_engine_batch_commit(e), SYNC_OK); /* inner */
    EXPECT_EQ(sync_engine_compact(e), SYNC_ERR_INTERNAL);
    ASSERT_EQ(sync_engine_batch_commit(e), SYNC_OK); /* outermost */
    /* ...and works again the moment the batch is closed. */
    EXPECT_EQ(sync_engine_compact(e), SYNC_OK);
    /* Depth is back to zero: one more close of either kind is misuse again. */
    EXPECT_EQ(sync_engine_batch_commit(e), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_batch_abort(e), SYNC_ERR_INVALID);
    sync_engine_destroy(e);
}

/* sync_engine_destroy with a batch still open is a defined, non-silent path:
 * the staged mutations are COMMITTED (outermost level) before the store
 * closes — and when that commit cannot happen (poisoned batch), a
 * SYNC_LOG_WARN is emitted rather than dropping the tail silently. */
TEST(Defensive, DestroyWithOpenBatchCommits) {
    synctest::TempDir dir;
    std::string db = dir.file("destroy_batch.db");
    auto sd = cluster::seed_from(0xC4);
    WarnCounter wc;
    {
        sync_engine *e = sync_engine_open(db.c_str(), sd.data());
        ASSERT_NE(e, nullptr);
        ASSERT_EQ(sync_engine_set_logger(e, count_warns, &wc), SYNC_OK);
        ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
        ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK); /* nested, left open */
        cluster::put(e, "ns", "forgot", "f", "v");
        sync_engine_destroy(e); /* embedder forgot both commits */
    }
    EXPECT_EQ(wc.warns, 0) << "healthy destroy-time commit warned";
    {
        sync_engine *e = sync_engine_open(db.c_str(), sd.data());
        ASSERT_NE(e, nullptr);
        EXPECT_EQ(cluster::get(e, "ns", "forgot", "f"), "v")
            << "mutations staged in a batch left open at destroy were dropped";

        /* A POISONED batch left open at destroy: its tail is discarded by
         * contract, so destroy must warn — never a silent drop. */
        ASSERT_EQ(sync_engine_set_logger(e, count_warns, &wc), SYNC_OK);
        ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
        cluster::put(e, "ns", "doomed", "f", "v");
        ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
        ASSERT_EQ(sync_engine_batch_abort(e), SYNC_OK); /* poison the batch */
        sync_engine_destroy(e);
    }
    EXPECT_GE(wc.warns, 1)
        << "poisoned batch dropped at destroy with no diagnostic";

    sync_engine *e = sync_engine_open(db.c_str(), sd.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(cluster::get(e, "ns", "forgot", "f"), "v");
    EXPECT_EQ(cluster::exists(e, "ns", "doomed"), false)
        << "poisoned batch's staged tail was committed anyway";
    sync_engine_destroy(e);
}

/* sync_engine_flush is the "make everything durable now" call: with a batch
 * open (any depth) it commits every level rather than silently violating its
 * safety-net contract. */
TEST(Defensive, FlushCommitsOpenBatch) {
    synctest::TempDir dir;
    std::string db = dir.file("flush_batch.db");
    auto sd = cluster::seed_from(0xC5);
    sync_engine *e = sync_engine_open(db.c_str(), sd.data());
    ASSERT_NE(e, nullptr);
    /* No batch open: flush stays the documented no-op safety net. */
    EXPECT_EQ(sync_engine_flush(e), SYNC_OK);

    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
    cluster::put(e, "ns", "bg", "f", "v");
    synctest::fsync_reset();
    EXPECT_EQ(sync_engine_flush(e), SYNC_OK); /* commits ALL levels */
    EXPECT_EQ(synctest::fsync_count(), 1u)
        << "flush did not write+fsync the staged batch tail";
    /* Fully closed: a further close is unbalanced, and compaction (refused
     * mid-batch) works again immediately — flush is how an embedder ends a
     * batch before backgrounding without tracking its own depth. */
    EXPECT_EQ(sync_engine_batch_commit(e), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_compact(e), SYNC_OK);

    /* Durability came from flush's commit alone: the batch was already closed
     * at destroy time, so destroy's own safety net had nothing to commit. */
    sync_engine_destroy(e);
    e = sync_engine_open(db.c_str(), sd.data());
    ASSERT_NE(e, nullptr);
    EXPECT_EQ(cluster::get(e, "ns", "bg", "f"), "v");
    sync_engine_destroy(e);
}

/* Capability writes are EXCLUDED from batch staging (spec §3.3 point 5):
 * grant/revoke write their own immediately-fsync'd frame even inside an open
 * batch, so a later batch_abort can discard staged data mutations but can
 * never discard a "remove this stolen device" cut-off the caller was told
 * succeeded. */
TEST(Defensive, RevokeInsideBatchSurvivesAbort) {
    synctest::TempDir dir;
    std::string db = dir.file("revoke_batch.db");
    auto own = cluster::seed_from(0xC0);
    uint8_t dev_pk[SYNC_PUBKEY_LEN], dev2_pk[SYNC_PUBKEY_LEN];
    pk_of(0xC1, dev_pk);
    pk_of(0xC2, dev2_pk);

    sync_engine *e = sync_engine_open(db.c_str(), own.data());
    ASSERT_NE(e, nullptr);

    /* Setup (write-through, outside any batch): owner claims "ns" (enforced
     * mode) and delegates WRITE to dev; dev's signed records then land. */
    sync_capability *root =
        sync_capability_root(e, "ns", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_EQ(sync_engine_grant(e, root), SYNC_OK);
    sync_capability *dcap =
        sync_capability_delegate(e, root, dev_pk, SYNC_ACCESS_WRITE, 0);
    ASSERT_NE(dcap, nullptr);
    ASSERT_EQ(sync_engine_grant(e, dcap), SYNC_OK);
    ASSERT_EQ(apply_signed(e, "ns", "d1", 0xC1, 1000), SYNC_OK)
        << "authorization not live before the revocation — test would be "
           "vacuous";

    /* Open a batch, stage a plain data mutation, then grant + revoke INSIDE
     * the open batch. */
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
    cluster::put(e, "misc", "staged", "f", "v");
    synctest::fsync_reset();
    sync_capability *d2cap =
        sync_capability_delegate(e, root, dev2_pk, SYNC_ACCESS_WRITE, 0);
    ASSERT_NE(d2cap, nullptr);
    ASSERT_EQ(sync_engine_grant(e, d2cap), SYNC_OK);
    ASSERT_EQ(sync_engine_revoke(e, "ns", dev_pk), SYNC_OK);
    /* Each capability write bypassed the batch: one immediately-fsync'd
     * frame apiece, while the data mutation above stays staged (0 fsyncs). */
    EXPECT_EQ(synctest::fsync_count(), 2u)
        << "grant/revoke did not keep synchronous fsync durability inside "
           "the open batch";
    int rv = 0;
    ASSERT_EQ(sync_engine_is_revoked(e, "ns", dev_pk, &rv), SYNC_OK);
    EXPECT_EQ(rv, 1);

    /* Abort the batch: the staged data mutation dies with it. */
    ASSERT_EQ(sync_engine_batch_abort(e), SYNC_OK);
    sync_engine_destroy(e);

    e = sync_engine_open(db.c_str(), own.data());
    ASSERT_NE(e, nullptr);
    /* The abort really discarded the batch tail (non-vacuity anchor). This
     * holds because destroy followed the abort with no intervening
     * compaction (the log stays under the auto-compact floor): a compaction
     * before destroy would have re-persisted the aborted-but-in-RAM key —
     * the documented durability-boundary contract, pinned by
     * Storage.AbortedTailReturnsAtCompaction. */
    EXPECT_EQ(cluster::exists(e, "misc", "staged"), false)
        << "aborted batch tail reached disk — abort had nothing to discard";
    /* ...but the revocation survived: SYNC_OK from revoke meant durable NOW. */
    rv = 0;
    ASSERT_EQ(sync_engine_is_revoked(e, "ns", dev_pk, &rv), SYNC_OK);
    EXPECT_EQ(rv, 1) << "revocation was discarded by a later batch_abort";
    EXPECT_EQ(apply_signed(e, "ns", "d2", 0xC1, 2000), SYNC_ERR_UNAUTHORIZED)
        << "revoked device can still write after reopen";
    /* ...and the in-batch grant survived the abort just the same. */
    EXPECT_EQ(apply_signed(e, "ns", "d3", 0xC2, 3000), SYNC_OK)
        << "in-batch grant was discarded by the abort";

    sync_capability_free(root);
    sync_capability_free(dcap);
    sync_capability_free(d2cap);
    sync_engine_destroy(e);
}

#ifndef __EMSCRIPTEN__
/* CRASH variant of the exclusion above: the process dies (_exit, no unwind)
 * with the batch still OPEN — no abort, no commit, none of the destroy-time
 * safety nets. The abort variant alone cannot pin the security property,
 * because destroy commits an open batch: only process death proves the
 * revocation was already durable on its OWN fsync'd frame at the moment
 * sync_engine_revoke returned SYNC_OK, while the data mutations staged
 * around it (never flushed, never committed) are gone. Fork-based, so
 * native-only, like storage_test's crash tests. */
TEST(Defensive, RevokeInsideBatchSurvivesCrash) {
    synctest::TempDir dir;
    std::string db = dir.file("revoke_crash.db");
    auto own = cluster::seed_from(0xC7);
    uint8_t dev_pk[SYNC_PUBKEY_LEN];
    pk_of(0xC8, dev_pk);

    { /* Durable setup, write-through, clean close: owner claims "ns"
       * (enforced mode) and delegates WRITE to dev. */
        sync_engine *e = sync_engine_open(db.c_str(), own.data());
        ASSERT_NE(e, nullptr);
        sync_capability *root =
            sync_capability_root(e, "ns", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        ASSERT_NE(root, nullptr);
        ASSERT_EQ(sync_engine_grant(e, root), SYNC_OK);
        sync_capability *dcap =
            sync_capability_delegate(e, root, dev_pk, SYNC_ACCESS_WRITE, 0);
        ASSERT_NE(dcap, nullptr);
        ASSERT_EQ(sync_engine_grant(e, dcap), SYNC_OK);
        ASSERT_EQ(apply_signed(e, "ns", "d1", 0xC8, 1000), SYNC_OK)
            << "authorization not live before the revocation — test would "
               "be vacuous";
        sync_capability_free(root);
        sync_capability_free(dcap);
        sync_engine_destroy(e);
    }

    /* Child: open, batch_begin, stage a mutation, revoke, stage another,
     * then die mid-batch. No gtest in the child; exit code reports. */
    pid_t pid = fork();
    ASSERT_GE(pid, 0);
    if (pid == 0) {
        sync_engine *c = sync_engine_open(db.c_str(), own.data());
        if (!c) _exit(2);
        if (sync_engine_batch_begin(c) != SYNC_OK) _exit(3);
        if (sync_engine_set(c, U("misc"), 4, U("s1"), 2, U("f"), 1, U("v"), 1)
            != SYNC_OK)
            _exit(4);
        if (sync_engine_revoke(c, "ns", dev_pk) != SYNC_OK) _exit(5);
        if (sync_engine_set(c, U("misc"), 4, U("s2"), 2, U("f"), 1, U("v"), 1)
            != SYNC_OK)
            _exit(6);
        _exit(0); /* crash: the batch is never closed */
    }
    int status = 0;
    ASSERT_EQ(waitpid(pid, &status, 0), pid);
    ASSERT_TRUE(WIFEXITED(status));
    ASSERT_EQ(WEXITSTATUS(status), 0)
        << "child failed (2=open 3=batch_begin 4=set-before 5=revoke "
           "6=set-after)";

    sync_engine *e = sync_engine_open(db.c_str(), own.data());
    ASSERT_NE(e, nullptr);
    int rv = 0;
    ASSERT_EQ(sync_engine_is_revoked(e, "ns", dev_pk, &rv), SYNC_OK);
    EXPECT_EQ(rv, 1) << "revocation lost to a mid-batch crash: SYNC_OK from "
                        "sync_engine_revoke did not mean durable NOW";
    EXPECT_EQ(apply_signed(e, "ns", "d2", 0xC8, 2000), SYNC_ERR_UNAUTHORIZED)
        << "revoked device can still write after the crash";
    /* The staged tail around the revocation never reached disk. */
    EXPECT_EQ(cluster::exists(e, "misc", "s1"), false)
        << "uncommitted staged mutation survived the crash";
    EXPECT_EQ(cluster::exists(e, "misc", "s2"), false)
        << "uncommitted staged mutation survived the crash";
    sync_engine_destroy(e);
}
#endif /* !__EMSCRIPTEN__ */
