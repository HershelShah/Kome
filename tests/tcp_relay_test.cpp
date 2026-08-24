/* tcp_relay_test.cpp — blind TCP relay (issue #49): in-process gtest suite.
 *
 * Pure logic, no sockets: MailboxLog (retained-log semantics, TTL, caps,
 * fetch-driven LRU eviction), RateLimits (token buckets), the standalone
 * per-op signature verifier (forge / cross-nonce replay / ctr replay), the
 * client-frame parser (fuzz-shaped malformed input), and a source-level
 * check that the server-side code never calls a decrypt/DH/sign primitive
 * (the structural half of the blindness invariant — see tcp_relay.h).
 * Real-socket coverage (the wire protocol end to end, offline convergence,
 * blindness over the actual connection) lives in tcp_relay_service_test.cpp. */
#include "transport/tcp_relay.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstring>
#include <fstream>
#include <random>
#include <regex>
#include <sstream>
#include <string>

#include "crypto.h"

using namespace ke;

namespace {

std::array<uint8_t, 32> idx_key(uint32_t i) {
    std::array<uint8_t, 32> k{};
    std::memcpy(k.data(), &i, sizeof i);
    return k;
}

} // namespace

/* ============================== MailboxLog =============================== */

TEST(TcpRelayLog, GlobalSeqMonotonicAcrossMailboxes) {
    MailboxLog log(168, 1000);
    uint8_t pkA[32], pkB[32];
    std::memset(pkA, 0xAA, 32);
    std::memset(pkB, 0xBB, 32);
    uint64_t seqA1 = 0, seqB1 = 0, seqA2 = 0;
    ASSERT_TRUE(log.store(pkA, "a1", 0, &seqA1));
    ASSERT_TRUE(log.store(pkB, "b1", 0, &seqB1));
    ASSERT_TRUE(log.store(pkA, "a2", 0, &seqA2));
    EXPECT_EQ(seqA1, 1000u);
    EXPECT_LT(seqA1, seqB1);
    EXPECT_LT(seqB1, seqA2);
}

/* A restarted/recreated mailbox space must never reuse seqs a client already
 * saw — a per-mailbox counter restarting at 1 would strand every saved
 * cursor. The seed-parametrized constructor lets this be asserted
 * deterministically instead of racing the real wall clock. */
TEST(TcpRelayLog, SeqSpaceNeverReusedAcrossRestart) {
    uint8_t pk[32];
    std::memset(pk, 1, 32);
    MailboxLog before(168, 1000);
    uint64_t s_before = 0;
    ASSERT_TRUE(before.store(pk, "x", 0, &s_before));

    MailboxLog after(168, 5000); /* a later wall-clock seed, as a restart gets */
    uint64_t s_after = 0;
    ASSERT_TRUE(after.store(pk, "y", 0, &s_after));
    EXPECT_GT(s_after, s_before);
}

TEST(TcpRelayLog, FetchIsNonDestructiveWithCursor) {
    MailboxLog log(168, 1);
    uint8_t pk[32];
    std::memset(pk, 7, 32);
    uint64_t s1 = 0, s2 = 0, s3 = 0;
    ASSERT_TRUE(log.store(pk, "one", 0, &s1));
    ASSERT_TRUE(log.store(pk, "two", 0, &s2));
    ASSERT_TRUE(log.store(pk, "three", 0, &s3));

    std::vector<std::pair<uint64_t, std::string>> out;
    uint64_t evicted = 123;
    log.fetch(pk, 0, 0, out, &evicted);
    ASSERT_EQ(out.size(), 3u);
    EXPECT_EQ(evicted, 0u);
    EXPECT_EQ(out[0].second, "one");
    EXPECT_EQ(out[2].second, "three");

    /* Re-fetching the same cursor yields the same records (non-destructive:
     * a shared mailbox must let every member read the same broadcast). */
    std::vector<std::pair<uint64_t, std::string>> out2;
    log.fetch(pk, 0, 0, out2, &evicted);
    EXPECT_EQ(out2.size(), 3u);

    std::vector<std::pair<uint64_t, std::string>> out3;
    log.fetch(pk, s2, 0, out3, &evicted);
    ASSERT_EQ(out3.size(), 1u);
    EXPECT_EQ(out3[0].second, "three");

    std::vector<std::pair<uint64_t, std::string>> out4;
    log.fetch(pk, s3, 0, out4, &evicted);
    EXPECT_TRUE(out4.empty());
}

TEST(TcpRelayLog, UnknownMailboxFetchIsEmptyWithZeroEvictedUpTo) {
    MailboxLog log;
    uint8_t pk[32];
    std::memset(pk, 9, 32);
    std::vector<std::pair<uint64_t, std::string>> out;
    uint64_t evicted = 42;
    log.fetch(pk, 0, 0, out, &evicted);
    EXPECT_TRUE(out.empty());
    EXPECT_EQ(evicted, 0u);
}

TEST(TcpRelayLog, TtlExpiryLazyOnAccessTracksEvictedUpTo) {
    MailboxLog log(1 /* hour */, 1);
    uint8_t pk[32];
    std::memset(pk, 3, 32);
    uint64_t s1 = 0, s2 = 0;
    ASSERT_TRUE(log.store(pk, "old", 1000, &s1));
    ASSERT_TRUE(log.store(pk, "new", 1000 + 3600000 - 1, &s2));

    uint64_t now = 1000 + 3600000 + 1; /* just past "old"'s 1h retention */
    std::vector<std::pair<uint64_t, std::string>> out;
    uint64_t evicted = 0;
    log.fetch(pk, 0, now, out, &evicted);
    ASSERT_EQ(out.size(), 1u);
    EXPECT_EQ(out[0].second, "new");
    EXPECT_EQ(evicted, s1); /* client whose cursor is below this knows it missed data */
}

TEST(TcpRelayLog, PerMailboxFifoCapDropsOldest) {
    MailboxLog log(168, 1);
    uint8_t pk[32];
    std::memset(pk, 5, 32);
    uint64_t s = 0;
    for (int i = 0; i < 300; i++)
        ASSERT_TRUE(log.store(pk, "b" + std::to_string(i), 0, &s));

    std::vector<std::pair<uint64_t, std::string>> out;
    uint64_t evicted = 0;
    log.fetch(pk, 0, 0, out, &evicted);
    EXPECT_LE(out.size(), 256u) << "per-mailbox blob count not bounded";
    EXPECT_GT(evicted, 0u);
    ASSERT_FALSE(out.empty());
    EXPECT_EQ(out.front().second, "b44"); /* 300 - 256 = 44 dropped */
    EXPECT_EQ(out.back().second, "b299");
}

TEST(TcpRelayLog, PerMailboxByteCapBounded) {
    MailboxLog log(168, 1);
    uint8_t pk[32];
    std::memset(pk, 6, 32);
    std::string blob(60000, 'x');
    uint64_t s = 0;
    for (int i = 0; i < 20; i++) ASSERT_TRUE(log.store(pk, blob, 0, &s));
    /* Only mailbox in this log, so total_bytes() is exactly its bytes. */
    EXPECT_LE(log.total_bytes(), 1u << 20) << "per-mailbox byte cap not bounded";
    EXPECT_GT(log.total_bytes(), 0u);
}

/* F6-equivalent for the retained log: once the mailbox-count table is full, a
 * new mailbox is admitted by evicting the LRU one (fetch-driven), not
 * refused — a spray of junk mailbox keys can't lock out new circles. */
TEST(TcpRelayLog, GlobalMailboxCountCapEvictsLru) {
    MailboxLog log(168, 1);
    const uint32_t kMax = 4096;
    uint64_t s = 0;
    for (uint32_t i = 0; i < kMax; i++) {
        auto k = idx_key(i);
        ASSERT_TRUE(log.store(k.data(), "blob", 0, &s));
    }
    ASSERT_EQ(log.mailboxes(), (size_t)kMax);

    /* Touch mailbox 1 via FETCH so it is recently used. */
    auto k1 = idx_key(1);
    std::vector<std::pair<uint64_t, std::string>> out;
    uint64_t evicted = 0;
    log.fetch(k1.data(), 0, 0, out, &evicted);

    auto knew = idx_key(0xABCDEF);
    ASSERT_TRUE(log.store(knew.data(), "hello", 0, &s));
    EXPECT_EQ(log.mailboxes(), (size_t)kMax) << "table not bounded";
    EXPECT_TRUE(log.exists(knew.data())) << "new mailbox refused";

    EXPECT_TRUE(log.exists(k1.data())) << "recently-fetched mailbox evicted";
    auto k0 = idx_key(0);
    EXPECT_FALSE(log.exists(k0.data())) << "LRU mailbox not evicted";
}

/* POST must never refresh a mailbox's LRU position (only FETCH and creation
 * do) — a write-only junk spray shouldn't be able to keep its own mailboxes
 * alive over readerful ones. */
TEST(TcpRelayLog, FetchDrivenLruNotTouchedByPost) {
    MailboxLog log(168, 1);
    uint8_t pkA[32];
    std::memset(pkA, 1, 32);
    uint64_t s = 0;
    ASSERT_TRUE(log.store(pkA, "1", 0, &s));
    for (int i = 0; i < 10; i++) ASSERT_TRUE(log.store(pkA, "x", 0, &s));

    const uint32_t kMax = 4096;
    for (uint32_t i = 1; i < kMax; i++) {
        auto k = idx_key(i);
        ASSERT_TRUE(log.store(k.data(), "blob", 0, &s));
    }
    ASSERT_EQ(log.mailboxes(), (size_t)kMax);

    uint8_t pkNew[32];
    std::memset(pkNew, 0xEE, 32);
    ASSERT_TRUE(log.store(pkNew, "new", 0, &s));
    EXPECT_FALSE(log.exists(pkA)) << "post-only mailbox survived eviction";
}

TEST(TcpRelayLog, GlobalByteCapEvictsLruMailboxesUntilFits) {
    MailboxLog log(168, 1);
    log.set_total_bytes_cap_for_test(3000);
    std::string blob(1000, 'x');
    uint8_t pkA[32], pkB[32], pkC[32], pkD[32];
    std::memset(pkA, 0xA, 32);
    std::memset(pkB, 0xB, 32);
    std::memset(pkC, 0xC, 32);
    std::memset(pkD, 0xD, 32);
    uint64_t s = 0;
    ASSERT_TRUE(log.store(pkA, blob, 0, &s));
    ASSERT_TRUE(log.store(pkB, blob, 1, &s));
    ASSERT_TRUE(log.store(pkC, blob, 2, &s));
    ASSERT_EQ(log.mailboxes(), 3u);

    ASSERT_TRUE(log.store(pkD, blob, 3, &s)); /* forces an eviction to fit */
    EXPECT_FALSE(log.exists(pkA)) << "global-LRU mailbox not evicted";
    EXPECT_TRUE(log.exists(pkB));
    EXPECT_TRUE(log.exists(pkC));
    EXPECT_TRUE(log.exists(pkD));
    EXPECT_LE(log.total_bytes(), 3000u);
}

/* The mailbox currently being posted to is never its own eviction victim —
 * if evicting every other mailbox still can't make room, the store fails
 * (ERR 5 at the wire layer) rather than losing the write it's servicing. */
TEST(TcpRelayLog, GlobalByteCapNeverEvictsSelfPostCapacityFails) {
    MailboxLog log(168, 1);
    log.set_total_bytes_cap_for_test(1500);
    std::string blob(1000, 'x');
    uint8_t pk[32];
    std::memset(pk, 1, 32);
    uint64_t s1 = 0, s2 = 0;
    ASSERT_TRUE(log.store(pk, blob, 0, &s1));
    EXPECT_FALSE(log.store(pk, blob, 1, &s2)) << "capacity drop should fail cleanly";
    EXPECT_TRUE(log.exists(pk));

    std::vector<std::pair<uint64_t, std::string>> out;
    uint64_t evicted = 0;
    log.fetch(pk, 0, 0, out, &evicted);
    ASSERT_EQ(out.size(), 1u) << "the first record must survive the failed second store";
}

TEST(TcpRelayLog, FetchBudgetPaginates) {
    MailboxLog log(168, 1);
    uint8_t pk[32];
    std::memset(pk, 2, 32);
    std::string blob(60000, 'z');
    uint64_t s = 0;
    for (int i = 0; i < 10; i++) ASSERT_TRUE(log.store(pk, blob, 0, &s));

    std::vector<std::pair<uint64_t, std::string>> out1;
    uint64_t evicted = 0;
    log.fetch(pk, 0, 0, out1, &evicted);
    EXPECT_GT(out1.size(), 0u);
    EXPECT_LT(out1.size(), 10u) << "one FETCH returned everything (budget not exercised)";

    std::vector<std::pair<uint64_t, std::string>> out2;
    log.fetch(pk, out1.back().first, 0, out2, &evicted);
    EXPECT_GT(out2.size(), 0u) << "the paginate loop made no progress";
}

TEST(TcpRelayLog, PushRegisterBoundedEvictOldestAndDedup) {
    MailboxLog log(168, 1);
    uint8_t pk[32];
    std::memset(pk, 4, 32);
    ASSERT_TRUE(log.register_push(pk, 1, "h0", 0));
    ASSERT_TRUE(log.register_push(pk, 1, "h1", 0));
    ASSERT_TRUE(log.register_push(pk, 1, "h0", 0)); /* dup: no-op */
    ASSERT_TRUE(log.register_push(pk, 1, "h2", 0));
    ASSERT_TRUE(log.register_push(pk, 1, "h3", 0));
    ASSERT_TRUE(log.register_push(pk, 1, "h4", 0)); /* 5th: evicts h0 */

    std::vector<TcpRelayWakeTarget> wakes;
    uint64_t s = 0;
    ASSERT_TRUE(log.store(pk, "post", 100000, &s, &wakes));
    std::vector<std::string> handles;
    for (auto &w : wakes) handles.push_back(w.handle);
    EXPECT_EQ(handles.size(), 4u);
    EXPECT_EQ(std::find(handles.begin(), handles.end(), "h0"), handles.end());
    EXPECT_NE(std::find(handles.begin(), handles.end(), "h4"), handles.end());
}

TEST(TcpRelayLog, PushHandleTooLongRejected) {
    MailboxLog log;
    uint8_t pk[32];
    std::memset(pk, 8, 32);
    std::string big(257, 'x');
    EXPECT_FALSE(log.register_push(pk, 1, big, 0));
}

TEST(TcpRelayLog, PushDebounceSuppressesRapidWakes) {
    MailboxLog log(168, 1);
    uint8_t pk[32];
    std::memset(pk, 9, 32);
    ASSERT_TRUE(log.register_push(pk, 2, "h", 0));

    std::vector<TcpRelayWakeTarget> w1;
    uint64_t s = 0;
    ASSERT_TRUE(log.store(pk, "p1", 1000, &s, &w1));
    EXPECT_EQ(w1.size(), 1u);

    std::vector<TcpRelayWakeTarget> w2;
    ASSERT_TRUE(log.store(pk, "p2", 1000 + 5000, &s, &w2)); /* 5s later: suppressed */
    EXPECT_EQ(w2.size(), 0u);

    std::vector<TcpRelayWakeTarget> w3;
    ASSERT_TRUE(log.store(pk, "p3", 1000 + 31000, &s, &w3)); /* 31s later: fires again */
    EXPECT_EQ(w3.size(), 1u);
}

/* ============================== RateLimits ================================ */

TEST(TcpRelayRateLimits, OpsBucketRateAndBurst) {
    RateLimits rl;
    std::string ip = "1.2.3.4";
    for (int i = 0; i < 60; i++) EXPECT_TRUE(rl.charge_op(ip, 0)) << i;
    EXPECT_FALSE(rl.charge_op(ip, 0)) << "burst not enforced";
    for (int i = 0; i < 20; i++) EXPECT_TRUE(rl.charge_op(ip, 1000)) << i;
    EXPECT_FALSE(rl.charge_op(ip, 1000)) << "1s refill exceeded the 20/s rate";
}

TEST(TcpRelayRateLimits, PostBytesBucket) {
    RateLimits rl;
    std::string ip = "2.2.2.2";
    EXPECT_TRUE(rl.charge_post_bytes(ip, 1024 * 1024, 0));
    EXPECT_FALSE(rl.charge_post_bytes(ip, 1, 0));
}

TEST(TcpRelayRateLimits, NewMailboxBucket) {
    RateLimits rl;
    std::string ip = "3.3.3.3";
    for (int i = 0; i < 8; i++) EXPECT_TRUE(rl.charge_new_mailbox(ip, 0)) << i;
    EXPECT_FALSE(rl.charge_new_mailbox(ip, 0));
}

TEST(TcpRelayRateLimits, ConcurrentConnectionCapPerIp) {
    RateLimits rl;
    std::string ip = "4.4.4.4";
    for (int i = 0; i < RateLimits::kMaxConnsPerIp; i++) EXPECT_TRUE(rl.admit_connection(ip));
    EXPECT_FALSE(rl.admit_connection(ip));
    rl.release_connection(ip);
    EXPECT_TRUE(rl.admit_connection(ip));
}

/* Budgets are per-IP, not per-connection: reconnecting must not reset them,
 * or burst-churn (disconnect/reconnect) would be a free rate-limit bypass. */
TEST(TcpRelayRateLimits, BudgetsPersistAcrossReconnectSameIp) {
    RateLimits rl;
    std::string ip = "5.5.5.5";
    for (int i = 0; i < 60; i++) rl.charge_op(ip, 0);
    ASSERT_FALSE(rl.charge_op(ip, 0));

    ASSERT_TRUE(rl.admit_connection(ip));
    rl.release_connection(ip); /* simulated disconnect + reconnect */
    ASSERT_TRUE(rl.admit_connection(ip));

    EXPECT_FALSE(rl.charge_op(ip, 0)) << "reconnect reset the ops budget";
}

/* ============================ per-op signature ============================= */

namespace {
struct MailboxIdentity {
    KeyPair mb;
    uint8_t server_pk[32];
    uint8_t nonce[16];
};
MailboxIdentity make_identity(uint8_t seed_byte, uint8_t server_byte, uint8_t nonce_byte) {
    MailboxIdentity id;
    uint8_t seed[32];
    std::memset(seed, seed_byte, 32);
    id.mb = keypair_from_seed(seed);
    std::memset(id.server_pk, server_byte, 32);
    std::memset(id.nonce, nonce_byte, 16);
    return id;
}
} // namespace

TEST(TcpRelayAuth, ValidSignatureVerifiesAndAdvancesCtr) {
    auto id = make_identity(0x11, 0x22, 0x33);
    std::string payload = "hello";
    std::string msg = tcp_relay_op_transcript(id.server_pk, id.nonce, kTcpRelayOpPost,
                                              id.mb.sign_pk.data(), 1, payload);
    uint8_t sig[64];
    sign(id.mb.sign_sk.data(), msg.data(), msg.size(), sig);

    bool init = false;
    uint64_t last = 0;
    EXPECT_TRUE(tcp_relay_verify_op(id.server_pk, id.nonce, kTcpRelayOpPost,
                                    id.mb.sign_pk.data(), 1, payload, sig, &init, &last));
    EXPECT_TRUE(init);
    EXPECT_EQ(last, 1u);
}

TEST(TcpRelayAuth, ForgedSignatureRejectedAndStateNotAdvanced) {
    auto id = make_identity(0x44, 0x22, 0x33);
    auto attacker = make_identity(0x99, 0x22, 0x33); /* different secret key */
    std::string payload = "hello";
    std::string msg = tcp_relay_op_transcript(id.server_pk, id.nonce, kTcpRelayOpPost,
                                              id.mb.sign_pk.data(), 1, payload);
    uint8_t sig[64];
    sign(attacker.mb.sign_sk.data(), msg.data(), msg.size(), sig); /* wrong key */

    bool init = false;
    uint64_t last = 0;
    EXPECT_FALSE(tcp_relay_verify_op(id.server_pk, id.nonce, kTcpRelayOpPost,
                                     id.mb.sign_pk.data(), 1, payload, sig, &init, &last));
    EXPECT_FALSE(init) << "a forged frame must not poison ctr state";
}

/* A signature minted for one relay (server_pk) or connection (nonce) is
 * worthless replayed against another — the transcript binds both. */
TEST(TcpRelayAuth, CrossNonceReplayRejected) {
    auto id = make_identity(0x55, 0x22, 0x33);
    std::string payload = "hello";
    std::string msg = tcp_relay_op_transcript(id.server_pk, id.nonce, kTcpRelayOpFetch,
                                              id.mb.sign_pk.data(), 1, payload);
    uint8_t sig[64];
    sign(id.mb.sign_sk.data(), msg.data(), msg.size(), sig);

    uint8_t other_nonce[16];
    std::memset(other_nonce, 0x77, 16);
    bool init = false;
    uint64_t last = 0;
    EXPECT_FALSE(tcp_relay_verify_op(id.server_pk, other_nonce, kTcpRelayOpFetch,
                                     id.mb.sign_pk.data(), 1, payload, sig, &init, &last));
}

TEST(TcpRelayAuth, CrossServerPkReplayRejected) {
    auto id = make_identity(0x66, 0x22, 0x33);
    std::string payload = "hello";
    std::string msg = tcp_relay_op_transcript(id.server_pk, id.nonce, kTcpRelayOpFetch,
                                              id.mb.sign_pk.data(), 1, payload);
    uint8_t sig[64];
    sign(id.mb.sign_sk.data(), msg.data(), msg.size(), sig);

    uint8_t other_server_pk[32];
    std::memset(other_server_pk, 0x88, 32);
    bool init = false;
    uint64_t last = 0;
    EXPECT_FALSE(tcp_relay_verify_op(other_server_pk, id.nonce, kTcpRelayOpFetch,
                                     id.mb.sign_pk.data(), 1, payload, sig, &init, &last));
}

TEST(TcpRelayAuth, CtrReplayAndNonIncreasingRejected) {
    auto id = make_identity(0x1A, 0x22, 0x33);
    bool init = false;
    uint64_t last = 0;
    auto verify_ctr = [&](uint64_t ctr) {
        std::string payload = "p";
        std::string msg = tcp_relay_op_transcript(id.server_pk, id.nonce, kTcpRelayOpPost,
                                                  id.mb.sign_pk.data(), ctr, payload);
        uint8_t sig[64];
        sign(id.mb.sign_sk.data(), msg.data(), msg.size(), sig);
        return tcp_relay_verify_op(id.server_pk, id.nonce, kTcpRelayOpPost, id.mb.sign_pk.data(),
                                   ctr, payload, sig, &init, &last);
    };
    EXPECT_TRUE(verify_ctr(5));
    EXPECT_FALSE(verify_ctr(5)) << "exact replay accepted";
    EXPECT_FALSE(verify_ctr(3)) << "lower ctr accepted";
    EXPECT_TRUE(verify_ctr(6));
    EXPECT_EQ(last, 6u);
}

/* ============================== frame parsing ============================== */

TEST(TcpRelayFraming, ParseRejectsTooShort) {
    for (size_t n : {(size_t)0, (size_t)1, (size_t)50, (size_t)104}) {
        std::string frame(n, 'x');
        TcpRelayParsedOp po;
        EXPECT_FALSE(tcp_relay_parse_client_frame(frame, po)) << n;
    }
}

TEST(TcpRelayFraming, ParseAcceptsMinimalFrameWithEmptyPayload) {
    std::string frame(105, 'x');
    TcpRelayParsedOp po;
    ASSERT_TRUE(tcp_relay_parse_client_frame(frame, po));
    EXPECT_TRUE(po.payload.empty());
}

TEST(TcpRelayFraming, BuildParseRoundTrip) {
    uint8_t mbpk[32];
    std::memset(mbpk, 5, 32);
    uint8_t sig[64];
    std::memset(sig, 6, 64);
    std::string payload = "abc";
    std::string frame = tcp_relay_build_op_frame((uint8_t)kTcpRelayOpPost, mbpk, 42, payload, sig);

    TcpRelayParsedOp po;
    ASSERT_TRUE(tcp_relay_parse_client_frame(frame, po));
    EXPECT_EQ(po.op, (uint8_t)kTcpRelayOpPost);
    EXPECT_EQ(0, std::memcmp(po.mailbox_pk, mbpk, 32));
    EXPECT_EQ(po.ctr, 42u);
    EXPECT_EQ(po.payload, payload);
    EXPECT_EQ(0, std::memcmp(po.sig, sig, 64));
}

TEST(TcpRelayFraming, ParseNeverCrashesOnRandomBytes) {
    std::mt19937 rng(12345);
    for (int i = 0; i < 5000; i++) {
        size_t n = rng() % 400;
        std::string frame;
        frame.reserve(n);
        for (size_t j = 0; j < n; j++) frame.push_back((char)(rng() & 0xff));
        TcpRelayParsedOp po;
        tcp_relay_parse_client_frame(frame, po); /* must not crash; return value unchecked */
    }
}

/* ============================== blindness (static) ========================= */

namespace {
std::string read_whole_file(const std::string &path) {
    std::ifstream f(path, std::ios::binary);
    std::ostringstream ss;
    ss << f.rdbuf();
    return ss.str();
}
/* True if `text` contains a call-shaped occurrence of `name` (word-bounded,
 * followed by '('), so it doesn't false-positive on identifiers like
 * "assign(" or on English prose. */
bool has_call(const std::string &text, const std::string &name) {
    std::regex re("\\b" + name + "\\s*\\(");
    return std::regex_search(text, re);
}
} // namespace

/* Structural half of the blindness invariant (the plan's adversarial-
 * verification checklist): the server-side implementation never calls a
 * decrypt, DH, or signing primitive — it only verifies. The client helpers
 * (which legitimately sign, per decision 2) live in the same file below a
 * clearly marked "client helpers" section; this test scopes the check to
 * everything above that marker, plus the whole daemon (which never needs a
 * client helper at all). */
TEST(TcpRelayBlindness, ServerSideNeverDecryptsOrSigns) {
    std::string this_file = __FILE__;
    std::string suffix = "/tests/tcp_relay_test.cpp";
    size_t pos = this_file.rfind(suffix);
    ASSERT_NE(pos, std::string::npos) << "unexpected test file path: " << this_file;
    std::string root = this_file.substr(0, pos);

    std::string src = read_whole_file(root + "/src/transport/tcp_relay.cpp");
    ASSERT_FALSE(src.empty());
    std::string marker = "client helpers";
    size_t marker_pos = src.find(marker);
    ASSERT_NE(marker_pos, std::string::npos) << "client-helpers section marker moved/renamed";
    std::string server_side = src.substr(0, marker_pos);

    EXPECT_FALSE(has_call(server_side, "sign")) << "server-side code must never sign";
    EXPECT_FALSE(server_side.find("x25519") != std::string::npos)
        << "server-side code must never touch X25519 (no session key material)";
    EXPECT_FALSE(server_side.find("aead_decrypt") != std::string::npos)
        << "server-side code must never decrypt";
    EXPECT_TRUE(has_call(src, "verify")) << "the server should still verify client ops";

    std::string daemon = read_whole_file(root + "/services/tcp_relay/tcp_relay_main.cpp");
    ASSERT_FALSE(daemon.empty());
    EXPECT_FALSE(has_call(daemon, "sign")) << "the daemon must never sign";
    EXPECT_FALSE(daemon.find("x25519") != std::string::npos);
    EXPECT_FALSE(daemon.find("aead_decrypt") != std::string::npos);
}

/* The relay stamps its connection deadlines from the WALL clock, not a steady
 * one, so `now` can legitimately be LESS than a stamp taken moments earlier —
 * an ordinary NTP step backwards is enough, with no attacker and no broken RTC.
 * A bare `now - start` underflows to a value near UINT64_MAX, which every
 * deadline test in poll_once reads as "elapsed time exceeded the bound"
 * (kIdleTimeoutMs, kFrameProgressMs, kTxStallMs): one backward step reaps every
 * live connection on the relay at once.
 *
 * PRE-FIX: ke::elapsed_ms did not exist and all three tests were bare
 * subtractions. */
TEST(TcpRelay, ElapsedTimeSaturatesAcrossABackwardClockStep) {
    /* Forward time behaves exactly as the subtraction did. */
    EXPECT_EQ(ke::elapsed_ms(10, 5), 5u);
    EXPECT_EQ(ke::elapsed_ms(5, 5), 0u);
    EXPECT_EQ(ke::elapsed_ms(UINT64_MAX, 0), UINT64_MAX);

    /* A backward step reads as "no time has passed", never as "overdue". */
    EXPECT_EQ(ke::elapsed_ms(5, 10), 0u)
        << "a backward clock step underflowed into an astronomical elapsed time";
    EXPECT_EQ(ke::elapsed_ms(0, 1), 0u);
    EXPECT_EQ(ke::elapsed_ms(0, UINT64_MAX), 0u);

    /* The property the reap loop actually depends on: after any backward step,
     * no deadline can read as exceeded. */
    const uint64_t stamps[] = {1ull, 1000ull, 1755000000000ull, UINT64_MAX};
    const uint64_t nows[] = {0ull, 1ull, 999ull};
    for (uint64_t stamp : stamps) {
        for (uint64_t now : nows) {
            if (now >= stamp) continue;
            EXPECT_LE(ke::elapsed_ms(now, stamp), 0u)
                << "now=" << now << " stamp=" << stamp;
        }
    }
}
