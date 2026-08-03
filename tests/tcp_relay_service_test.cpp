/* tcp_relay_service_test.cpp — blind TCP relay (issue #49): real-socket
 * suite. The server runs on a background thread (service_test.cpp's
 * pattern); clients drive it over real loopback TCP via the client helpers
 * and hand-built frames. Covers the wire protocol end to end: HELLO/POST/
 * FETCH/PUSH_REG, disjoint client lifetimes (store-and-forward), forged/
 * replayed/unauthorized rejection, caps and their ERR codes, and the
 * offline-convergence e2e (sync_engine export -> encode -> seal -> relay ->
 * decode -> apply), the TCP counterpart of tests/relay_test.cpp:234-263. */
#include "transport/tcp_relay.h"

#include <gtest/gtest.h>

#include <unistd.h>

#include <array>
#include <atomic>
#include <cstring>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#include "crypto.h"
#include "sync_engine.h"
#include "transport/tcp.h"

using namespace ke;

namespace {
KeyPair mkid(uint8_t b) {
    uint8_t seed[32];
    std::memset(seed, b, 32);
    return keypair_from_seed(seed);
}
} // namespace

class TcpRelayService : public ::testing::Test {
protected:
    struct CountingNotifier : PushNotifier {
        std::mutex m;
        std::vector<std::pair<uint8_t, std::string>> wakes;
        void wake(uint8_t provider, const std::string &handle) override {
            std::lock_guard<std::mutex> lk(m);
            wakes.push_back({provider, handle});
        }
    };

    void SetUp() override {
        server_id_ = mkid(0xEE);
        server_.reset(new TcpRelayServer(server_id_.sign_pk.data(), &notifier_));
        ASSERT_TRUE(server_->listen("127.0.0.1", 0));
        ep_ = server_->local();
        stop_.store(false);
        th_ = std::thread([this] {
            while (!stop_.load()) server_->step(20);
        });
    }
    void TearDown() override {
        stop_.store(true);
        th_.join();
    }

    KeyPair                      server_id_;
    CountingNotifier              notifier_;
    std::unique_ptr<TcpRelayServer> server_;
    Endpoint                      ep_;
    std::atomic<bool>             stop_{false};
    std::thread                   th_;
};

/* ---- basic wire protocol -------------------------------------------------- */

TEST_F(TcpRelayService, HelloPostFetchRoundTrip) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    EXPECT_EQ(0, std::memcmp(spk, server_id_.sign_pk.data(), 32));

    KeyPair mb = mkid(0x01);
    uint64_t seq = 0;
    uint8_t err = 0;
    ASSERT_TRUE(tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 1,
                                      "ciphertext-blob", &seq, &err, 1000));
    EXPECT_GT(seq, 0u);

    std::vector<std::pair<uint64_t, std::string>> recs;
    uint64_t evicted = 0;
    ASSERT_TRUE(tcp_relay_client_fetch(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 2, 0,
                                       recs, &evicted, &err, 1000));
    ASSERT_EQ(recs.size(), 1u);
    EXPECT_EQ(recs[0].first, seq);
    EXPECT_EQ(recs[0].second, "ciphertext-blob");
    EXPECT_EQ(evicted, 0u);
}

TEST_F(TcpRelayService, DisjointClientLifetimesStoreAndForward) {
    KeyPair mb = mkid(0x02);
    uint64_t posted_seq = 0;
    uint8_t err = 0;
    {
        TcpStream sa;
        ASSERT_TRUE(sa.connect_to(ep_));
        uint8_t spk[32], nonce[16];
        ASSERT_TRUE(tcp_relay_client_hello(sa, spk, nonce, 1000));
        ASSERT_TRUE(tcp_relay_client_post(sa, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 1,
                                          "blob-A", &posted_seq, &err, 1000));
        sa.close(); /* A disconnects entirely */
    }
    {
        TcpStream sb; /* B connects later, unrelated connection */
        ASSERT_TRUE(sb.connect_to(ep_));
        uint8_t spk[32], nonce[16];
        ASSERT_TRUE(tcp_relay_client_hello(sb, spk, nonce, 1000));
        std::vector<std::pair<uint64_t, std::string>> recs;
        uint64_t evicted = 0;
        ASSERT_TRUE(tcp_relay_client_fetch(sb, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 1,
                                           0, recs, &evicted, &err, 1000));
        ASSERT_EQ(recs.size(), 1u);
        EXPECT_EQ(recs[0].first, posted_seq);
        EXPECT_EQ(recs[0].second, "blob-A");
    }
}

TEST_F(TcpRelayService, PushRegistrationAndWakeOnPost) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    KeyPair mb = mkid(0x80);
    uint8_t err = 0;
    ASSERT_TRUE(tcp_relay_client_register_push(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(),
                                               1, 9, "handle-1", &err, 1000));
    uint64_t seq = 0;
    ASSERT_TRUE(tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 2,
                                      "post-body", &seq, &err, 1000));

    bool saw = false;
    for (int i = 0; i < 100 && !saw; i++) {
        {
            std::lock_guard<std::mutex> lk(notifier_.m);
            saw = !notifier_.wakes.empty();
        }
        if (!saw) usleep(5 * 1000);
    }
    ASSERT_TRUE(saw) << "push wake never fired";
    std::lock_guard<std::mutex> lk(notifier_.m);
    ASSERT_EQ(notifier_.wakes.size(), 1u);
    EXPECT_EQ(notifier_.wakes[0].first, 9);
    EXPECT_EQ(notifier_.wakes[0].second, "handle-1");
}

/* ---- auth: forge / replay / unauthorized ---------------------------------- */

TEST_F(TcpRelayService, ForgedSignatureRejected) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    KeyPair mb = mkid(0x03), attacker = mkid(0x04);
    std::string payload = "blob";
    std::string msg =
        tcp_relay_op_transcript(spk, nonce, (uint8_t)kTcpRelayOpPost, mb.sign_pk.data(), 1, payload);
    uint8_t sig[64];
    sign(attacker.sign_sk.data(), msg.data(), msg.size(), sig); /* wrong secret key */
    std::string frame =
        tcp_relay_build_op_frame((uint8_t)kTcpRelayOpPost, mb.sign_pk.data(), 1, payload, sig);
    ASSERT_TRUE(s.send_frame(frame));
    std::string reply;
    ASSERT_TRUE(s.recv_frame(reply, 1000));
    ASSERT_EQ(reply.size(), 2u);
    EXPECT_EQ(reply[0], kTcpRelayOpErr);
    EXPECT_EQ((uint8_t)reply[1], kTcpRelayErrAuth);
}

TEST_F(TcpRelayService, CtrReplayRejectedOverWire) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    KeyPair mb = mkid(0x05);
    uint64_t seq = 0;
    uint8_t err = 0;
    ASSERT_TRUE(tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 5, "one",
                                      &seq, &err, 1000));
    ASSERT_FALSE(tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 5, "two",
                                       &seq, &err, 1000))
        << "exact ctr replay accepted";
    EXPECT_EQ(err, kTcpRelayErrAuth);
    ASSERT_FALSE(tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 3,
                                       "three", &seq, &err, 1000))
        << "lower ctr accepted";
    EXPECT_EQ(err, kTcpRelayErrAuth);
}

TEST_F(TcpRelayService, ThreeAuthFailuresDisconnects) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    KeyPair mb = mkid(0x06), attacker = mkid(0x07);

    for (int i = 0; i < 4; i++) {
        std::string payload = "x";
        std::string msg = tcp_relay_op_transcript(spk, nonce, (uint8_t)kTcpRelayOpPost,
                                                  mb.sign_pk.data(), i + 1, payload);
        uint8_t sig[64];
        sign(attacker.sign_sk.data(), msg.data(), msg.size(), sig);
        std::string frame = tcp_relay_build_op_frame((uint8_t)kTcpRelayOpPost, mb.sign_pk.data(),
                                                      i + 1, payload, sig);
        ASSERT_TRUE(s.send_frame(frame));
        std::string reply;
        ASSERT_TRUE(s.recv_frame(reply, 1000)) << "iteration " << i;
        ASSERT_EQ(reply.size(), 2u);
        EXPECT_EQ((uint8_t)reply[1], kTcpRelayErrAuth);
    }
    /* kMaxAuthFailures (3) tolerated; the 4th above pushed the count to 4 and
     * the connection must now be dropped. */
    std::string trailing;
    EXPECT_FALSE(s.recv_frame(trailing, 1000))
        << "connection not dropped after repeated auth failures";
}

/* ---- caps and their ERR codes ---------------------------------------------- */

TEST_F(TcpRelayService, TooManyDistinctMailboxesRejected) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    /* FETCH (not POST) to register 16 distinct mailboxes on this connection
     * without also charging the independent per-IP new-mailbox-creation
     * budget (burst 8) — that limit is real but is not what this test is
     * isolating; the distinct-mailbox-per-connection cap (16) is. */
    for (int i = 0; i < 16; i++) {
        KeyPair mb = mkid((uint8_t)(0x40 + i));
        std::vector<std::pair<uint64_t, std::string>> recs;
        uint64_t evicted = 0;
        uint8_t err = 0;
        ASSERT_TRUE(tcp_relay_client_fetch(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 1,
                                           0, recs, &evicted, &err, 1000))
            << i;
    }
    KeyPair mb17 = mkid(0x51);
    std::vector<std::pair<uint64_t, std::string>> recs;
    uint64_t evicted = 0;
    uint8_t err = 0;
    EXPECT_FALSE(tcp_relay_client_fetch(s, spk, nonce, mb17.sign_sk.data(), mb17.sign_pk.data(), 1,
                                        0, recs, &evicted, &err, 1000));
    EXPECT_EQ(err, kTcpRelayErrTooManyMailboxes);
}

TEST_F(TcpRelayService, BlobTooLargeRejected) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    KeyPair mb = mkid(0x60);
    std::string big((1u << 16) + 1, 'x'); /* one over the 64 KiB per-blob cap */
    uint64_t seq = 0;
    uint8_t err = 0;
    EXPECT_FALSE(tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 1, big,
                                       &seq, &err, 1000));
    EXPECT_EQ(err, kTcpRelayErrTooLarge);
}

TEST_F(TcpRelayService, EmptyBlobRejectedAsMalformed) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    KeyPair mb = mkid(0x61);
    uint64_t seq = 0;
    uint8_t err = 0;
    EXPECT_FALSE(tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 1, "",
                                       &seq, &err, 1000));
    EXPECT_EQ(err, kTcpRelayErrMalformed);
}

TEST_F(TcpRelayService, OversizedFramePrefixDropsConnection) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    std::string huge(70000, 'a'); /* > the 68 KiB client-frame cap, at the prefix */
    ASSERT_TRUE(s.send_frame(huge));
    std::string reply;
    EXPECT_FALSE(s.recv_frame(reply, 1000)) << "server did not drop an oversized frame";
}

TEST_F(TcpRelayService, MalformedFrameGetsErr1) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    std::string garbage(50, 'z'); /* too short to hold op+mailbox_pk+ctr+sig */
    ASSERT_TRUE(s.send_frame(garbage));
    std::string reply;
    ASSERT_TRUE(s.recv_frame(reply, 1000));
    ASSERT_EQ(reply.size(), 2u);
    EXPECT_EQ(reply[0], kTcpRelayOpErr);
    EXPECT_EQ((uint8_t)reply[1], kTcpRelayErrMalformed);
}

/* A flood of tiny malformed frames must not buy unthrottled work from the
 * single-threaded loop: past kMaxProtocolErrors bad frames the server drops the
 * connection instead of answering ERR forever (adversarial-review finding). */
TEST_F(TcpRelayService, MalformedFrameFloodReapsConnection) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));

    /* Send well past the protocol-error budget; each 4-byte frame is a
     * complete, zero-length, unparseable frame (the cheapest bad frame). */
    std::string empty_frame; /* send_frame writes the 4-byte length prefix (0) */
    int replies = 0;
    bool closed = false;
    for (int i = 0; i < 200; i++) {
        if (!s.send_frame(empty_frame)) { closed = true; break; }
        std::string reply;
        if (s.recv_frame(reply, 200)) {
            replies++;
            EXPECT_EQ((uint8_t)reply[1], kTcpRelayErrMalformed);
        } else {
            closed = true; /* connection dropped: no ERR, no timeout data */
            break;
        }
    }
    EXPECT_TRUE(closed) << "server answered a malformed-frame flood indefinitely";
    EXPECT_LE(replies, TcpRelayServer::kMaxProtocolErrors + 1)
        << "server issued more ERR replies than the protocol-error budget allows";
}

TEST_F(TcpRelayService, RateLimitedOpsReturnsErr3) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    KeyPair mb = mkid(0x70);
    uint64_t seq = 0;
    uint8_t err = 0;
    bool saw_rate_limited = false;
    for (int i = 0; i < 200 && !saw_rate_limited; i++) {
        bool ok = tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), i + 1,
                                        "x", &seq, &err, 1000);
        if (!ok && err == kTcpRelayErrRateLimited) saw_rate_limited = true;
    }
    EXPECT_TRUE(saw_rate_limited) << "the 20/s-burst-60 ops budget was never exhausted";
}

/* ---- blindness: verbatim passthrough --------------------------------------- */

TEST_F(TcpRelayService, StoredBytesAreByteIdenticalPassthrough) {
    TcpStream s;
    ASSERT_TRUE(s.connect_to(ep_));
    uint8_t spk[32], nonce[16];
    ASSERT_TRUE(tcp_relay_client_hello(s, spk, nonce, 1000));
    KeyPair mb = mkid(0x90);

    /* Stands in for a real ciphertext blob: the relay must never interpret,
     * transform, or truncate it — whatever bytes are posted come back
     * verbatim, proving there is no processing step that could touch
     * plaintext even if a caller mistakenly posted some. */
    std::string blob;
    for (int i = 0; i < 4096; i++) blob.push_back((char)(i & 0xff));

    uint64_t seq = 0;
    uint8_t err = 0;
    ASSERT_TRUE(tcp_relay_client_post(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 1, blob,
                                      &seq, &err, 1000));
    std::vector<std::pair<uint64_t, std::string>> recs;
    uint64_t evicted = 0;
    ASSERT_TRUE(tcp_relay_client_fetch(s, spk, nonce, mb.sign_sk.data(), mb.sign_pk.data(), 2, 0,
                                       recs, &evicted, &err, 1000));
    ASSERT_EQ(recs.size(), 1u);
    EXPECT_EQ(recs[0].second, blob);
}

/* ---- offline convergence e2e (TCP counterpart of relay_test.cpp:234-263) -- */

namespace {
/* Seal one already-encoded record as nonce24(random) || ct || mac16 under a
 * shared symmetric key (as if agreed inside the circle's E2EE state — the
 * relay never sees it). Fresh random nonce per record. */
std::string seal(const uint8_t key[32], const std::vector<uint8_t> &plain) {
    uint8_t rn[24];
    EXPECT_TRUE(random_bytes(rn, 24));
    std::vector<uint8_t> ct(plain.size());
    uint8_t mac[16];
    aead_encrypt(key, rn, nullptr, 0, plain.data(), plain.size(), ct.data(), mac);
    std::string blob;
    blob.append((const char *)rn, 24);
    blob.append((const char *)ct.data(), ct.size());
    blob.append((const char *)mac, 16);
    return blob;
}
bool open_envelope(const uint8_t key[32], const std::string &blob, std::vector<uint8_t> &out) {
    if (blob.size() < 24 + 16) return false;
    const uint8_t *rn = (const uint8_t *)blob.data();
    size_t ct_len = blob.size() - 24 - 16;
    const uint8_t *ct = (const uint8_t *)blob.data() + 24;
    const uint8_t *mac = ct + ct_len;
    out.resize(ct_len);
    return aead_decrypt(key, rn, nullptr, 0, ct, ct_len, mac, out.data());
}
/* Export every record of `from`, seal each, POST it to `mailbox` over `s`. */
void export_seal_post(sync_engine *from, TcpStream &s, const uint8_t spk[32],
                      const uint8_t nonce[16], const KeyPair &mailbox,
                      const uint8_t envelope_key[32], uint64_t &ctr) {
    sync_change *recs = nullptr;
    size_t n = 0;
    ASSERT_EQ(sync_engine_export(from, &recs, &n), SYNC_OK);
    ASSERT_GT(n, 0u);
    for (size_t i = 0; i < n; i++) {
        size_t len = sync_change_encode(&recs[i], nullptr, 0);
        std::vector<uint8_t> enc(len);
        sync_change_encode(&recs[i], enc.data(), enc.size());
        std::string blob = seal(envelope_key, enc);

        uint64_t seq = 0;
        uint8_t err = 0;
        ASSERT_TRUE(tcp_relay_client_post(s, spk, nonce, mailbox.sign_sk.data(),
                                          mailbox.sign_pk.data(), ctr++, blob, &seq, &err, 1000))
            << "record " << i;
    }
    sync_changes_free(recs, n);
}
/* FETCH every record posted to `mailbox`, open + decode + apply each into `into`. */
void fetch_open_apply(sync_engine *into, TcpStream &s, const uint8_t spk[32],
                      const uint8_t nonce[16], const KeyPair &mailbox,
                      const uint8_t envelope_key[32], uint64_t ctr,
                      const std::string &plaintext_marker) {
    std::vector<std::pair<uint64_t, std::string>> blobs;
    uint64_t evicted = 0;
    uint8_t err = 0;
    ASSERT_TRUE(tcp_relay_client_fetch(s, spk, nonce, mailbox.sign_sk.data(), mailbox.sign_pk.data(),
                                       ctr, 0, blobs, &evicted, &err, 1000));
    ASSERT_GT(blobs.size(), 0u);
    for (auto &kv : blobs) {
        const std::string &blob = kv.second;
        if (!plaintext_marker.empty()) {
            EXPECT_EQ(blob.find(plaintext_marker), std::string::npos)
                << "relay-visible bytes contain a plaintext marker";
        }
        std::vector<uint8_t> plain;
        ASSERT_TRUE(open_envelope(envelope_key, blob, plain));
        sync_change out;
        size_t consumed = 0;
        ASSERT_EQ(sync_change_decode(plain.data(), plain.size(), &out, &consumed), SYNC_OK);
        EXPECT_EQ(sync_engine_apply(into, &out), SYNC_OK);
        sync_change_free_decoded(&out);
    }
}
} // namespace

TEST_F(TcpRelayService, OfflineConvergenceViaSealedEnvelopesBothDirections) {
    using Digest = std::array<uint8_t, SYNC_DIGEST_LEN>;
    uint8_t seedA[32], seedB[32];
    std::memset(seedA, 0xA1, 32);
    std::memset(seedB, 0xB1, 32);
    sync_engine *a = sync_engine_create(seedA);
    sync_engine *b = sync_engine_create(seedB);
    ASSERT_TRUE(a);
    ASSERT_TRUE(b);

    const std::string marker = "PLAINTEXT-MARKER-";
    for (int i = 0; i < 10; i++) {
        std::string ent = "e" + std::to_string(i);
        std::string val = marker + std::to_string(i);
        ASSERT_EQ(sync_engine_set(a, (const uint8_t *)"ns", 2, (const uint8_t *)ent.data(),
                                  ent.size(), (const uint8_t *)"f", 1, (const uint8_t *)val.data(),
                                  val.size()),
                  SYNC_OK);
    }

    KeyPair mailboxAB = mkid(0xC1);
    uint8_t envelope_key[32];
    std::memset(envelope_key, 0xC2, 32); /* shared out-of-band; the relay never sees it */

    /* A is online just long enough to post, then disconnects entirely. */
    {
        TcpStream sa;
        ASSERT_TRUE(sa.connect_to(ep_));
        uint8_t spk[32], nonce[16];
        ASSERT_TRUE(tcp_relay_client_hello(sa, spk, nonce, 1000));
        uint64_t ctr = 1;
        export_seal_post(a, sa, spk, nonce, mailboxAB, envelope_key, ctr);
    } /* sa destructed: connection closed */

    /* B comes online later (disjoint lifetime) and drains the mailbox. */
    {
        TcpStream sb;
        ASSERT_TRUE(sb.connect_to(ep_));
        uint8_t spk[32], nonce[16];
        ASSERT_TRUE(tcp_relay_client_hello(sb, spk, nonce, 1000));
        fetch_open_apply(b, sb, spk, nonce, mailboxAB, envelope_key, 1, marker);
    }

    Digest da{}, db{};
    ASSERT_EQ(sync_engine_digest(a, da.data()), SYNC_OK);
    ASSERT_EQ(sync_engine_digest(b, db.data()), SYNC_OK);
    EXPECT_EQ(da, db);

    /* Reverse direction: B writes new local data and posts it to a second
     * mailbox; A (freshly connecting) fetches and converges too. */
    for (int i = 0; i < 5; i++) {
        std::string ent = "e" + std::to_string(i);
        std::string val = marker + "reverse-" + std::to_string(i);
        ASSERT_EQ(sync_engine_set(b, (const uint8_t *)"ns2", 3, (const uint8_t *)ent.data(),
                                  ent.size(), (const uint8_t *)"f", 1, (const uint8_t *)val.data(),
                                  val.size()),
                  SYNC_OK);
    }
    KeyPair mailboxBA = mkid(0xC3);
    {
        TcpStream sb2;
        ASSERT_TRUE(sb2.connect_to(ep_));
        uint8_t spk[32], nonce[16];
        ASSERT_TRUE(tcp_relay_client_hello(sb2, spk, nonce, 1000));
        uint64_t ctr = 1;
        export_seal_post(b, sb2, spk, nonce, mailboxBA, envelope_key, ctr);
    }
    {
        TcpStream sa2;
        ASSERT_TRUE(sa2.connect_to(ep_));
        uint8_t spk[32], nonce[16];
        ASSERT_TRUE(tcp_relay_client_hello(sa2, spk, nonce, 1000));
        fetch_open_apply(a, sa2, spk, nonce, mailboxBA, envelope_key, 1, marker);
    }

    Digest da2{}, db2{};
    ASSERT_EQ(sync_engine_digest(a, da2.data()), SYNC_OK);
    ASSERT_EQ(sync_engine_digest(b, db2.data()), SYNC_OK);
    EXPECT_EQ(da2, db2);

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}
