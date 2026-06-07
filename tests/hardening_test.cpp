/* hardening_test.cpp — M6 acceptance (runnable in-container).
 *
 *   T6.2 — parsers survive arbitrary/mutated input with no crash or OOB
 *          (same entry points as the libFuzzer targets; real fuzzing needs a
 *          clang with the fuzzer runtime, built via -DSYNC_FUZZ=ON).
 *   T6.4 — repeated kill-mid-write always reopens to a consistent state.
 *   T6.5 — unknown wire/codec versions are rejected cleanly.
 *   T6.7 — every alloc/free pair is exercised (leak-checked under ASan).
 */
#include "sync_engine.h"

#include "cluster.hpp"
#include "tempdir.hpp"

#include <gtest/gtest.h>

#include <dirent.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

#include <array>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <string>
#include <vector>

namespace {

using cluster::B;
using synctest::TempDir;

std::array<uint8_t, SYNC_SEED_LEN> seed_from(uint8_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (auto &b : s) b = v;
    return s;
}

} // namespace

/* ---- T6.2 Parsers survive arbitrary + mutated input -------------------- */
TEST(Hardening, DecodersNoCrashOnArbitraryInput) {
    std::mt19937 rng(0xF0F0);

    /* Build a valid record and a valid capability to mutate near the boundary. */
    auto seed = seed_from(0x01);
    sync_engine *e = sync_engine_create(seed.data());
    sync_engine_set(e, B(std::string("ns")), 2, B(std::string("ent")), 3,
                    B(std::string("f")), 1, B(std::string("val")), 3);
    sync_change *recs = nullptr;
    size_t n = 0;
    sync_engine_export(e, &recs, &n);
    std::vector<uint8_t> valid_rec;
    if (n) {
        size_t len = sync_change_encode(&recs[0], nullptr, 0);
        valid_rec.resize(len);
        sync_change_encode(&recs[0], valid_rec.data(), len);
    }
    sync_changes_free(recs, n);

    sync_capability *root = sync_capability_root(e, "ns", SYNC_ACCESS_WRITE);
    std::vector<uint8_t> valid_cap;
    if (root) {
        int len = sync_capability_encode(root, nullptr, 0);
        valid_cap.resize(len);
        sync_capability_encode(root, valid_cap.data(), valid_cap.size());
        sync_capability_free(root);
    }

    auto try_change = [](const uint8_t *d, size_t s) {
        sync_change c;
        size_t used = 0;
        if (sync_change_decode(d, s, &c, &used) == SYNC_OK)
            sync_change_free_decoded(&c);
    };
    auto try_cap = [](const uint8_t *d, size_t s) {
        sync_capability *c = sync_capability_decode(d, s);
        if (c) sync_capability_free(c);
    };
    auto try_session = [&](const uint8_t *d, size_t s) {
        sync_session *sess = sync_session_begin(e, 0);
        uint8_t *out = nullptr;
        size_t ol = 0;
        int done = 0;
        sync_session_step(sess, d, s, &out, &ol, &done);
        if (out) sync_free(out);
        sync_session_end(sess);
    };

    for (int i = 0; i < 30000; i++) {
        /* purely random buffer */
        size_t len = rng() % 200;
        std::vector<uint8_t> buf(len);
        for (auto &b : buf) b = (uint8_t)rng();
        try_change(buf.data(), buf.size());
        try_cap(buf.data(), buf.size());
        try_session(buf.data(), buf.size());

        /* mutated-valid record */
        if (!valid_rec.empty()) {
            std::vector<uint8_t> m = valid_rec;
            for (int k = 0; k < 1 + (int)(rng() % 4); k++)
                m[rng() % m.size()] ^= (uint8_t)(1u << (rng() % 8));
            if (rng() % 3 == 0 && m.size() > 1) m.resize(rng() % m.size());
            try_change(m.data(), m.size());
        }
        /* mutated-valid capability */
        if (!valid_cap.empty()) {
            std::vector<uint8_t> m = valid_cap;
            m[rng() % m.size()] ^= (uint8_t)(1u << (rng() % 8));
            try_cap(m.data(), m.size());
        }
    }
    sync_engine_destroy(e);
    SUCCEED();
}

/* ---- T6.5 Version negotiation ------------------------------------------ */
TEST(Hardening, RejectsUnknownVersions) {
    auto seed = seed_from(0x02);
    sync_engine *e = sync_engine_create(seed.data());
    sync_engine_set(e, B(std::string("n")), 1, B(std::string("x")), 1,
                    B(std::string("f")), 1, B(std::string("v")), 1);
    sync_change *recs = nullptr;
    size_t n = 0;
    sync_engine_export(e, &recs, &n);
    ASSERT_GT(n, 0u);
    size_t len = sync_change_encode(&recs[0], nullptr, 0);
    std::vector<uint8_t> rec(len);
    sync_change_encode(&recs[0], rec.data(), len);
    sync_changes_free(recs, n);

    /* A valid record decodes. */
    {
        sync_change c; size_t used = 0;
        ASSERT_EQ(sync_change_decode(rec.data(), rec.size(), &c, &used), SYNC_OK);
        sync_change_free_decoded(&c);
    }
    /* Unknown future codec version (byte 0) is rejected, not crashed. */
    {
        std::vector<uint8_t> bad = rec;
        bad[0] = 99;
        sync_change c; size_t used = 0;
        EXPECT_EQ(sync_change_decode(bad.data(), bad.size(), &c, &used),
                  SYNC_ERR_INVALID);
    }
    /* Old codec version 1 is also rejected. */
    {
        std::vector<uint8_t> bad = rec;
        bad[0] = 1;
        sync_change c; size_t used = 0;
        EXPECT_EQ(sync_change_decode(bad.data(), bad.size(), &c, &used),
                  SYNC_ERR_INVALID);
    }
    sync_engine_destroy(e);
}

/* ---- T6.4 Repeated crash recovery -------------------------------------- */
TEST(Hardening, RepeatedCrashRecovery) {
    TempDir dir;
    std::string db = dir.file("rc.db");
    auto seed = seed_from(0x03);

    /* Seed a committed anchor. */
    {
        sync_engine *e = sync_engine_open(db.c_str(), seed.data());
        ASSERT_NE(e, nullptr);
        sync_engine_set(e, B(std::string("n")), 1, B(std::string("anchor")), 6,
                        B(std::string("f")), 1, B(std::string("v")), 1);
        sync_engine_destroy(e);
    }

    for (int round = 0; round < 5; round++) {
        pid_t pid = fork();
        ASSERT_GE(pid, 0);
        if (pid == 0) {
            sync_engine *c = sync_engine_open(db.c_str(), seed.data());
            if (!c) _exit(2);
            for (int i = 0;; i++) {
                std::string ent = "r" + std::to_string(round) + "_" + std::to_string(i);
                sync_engine_set(c, B(std::string("n")), 1, B(ent), ent.size(),
                                B(std::string("f")), 1, B(std::string("x")), 1);
            }
            _exit(0);
        }
        usleep(25 * 1000);
        kill(pid, SIGKILL);
        int st = 0;
        waitpid(pid, &st, 0);

        sync_engine *e = sync_engine_open(db.c_str(), seed.data());
        ASSERT_NE(e, nullptr) << "corrupt after crash round " << round;
        uint8_t dg[SYNC_DIGEST_LEN];
        ASSERT_EQ(sync_engine_digest(e, dg), SYNC_OK);

        /* Convergence still holds: export applies cleanly into a fresh peer. */
        sync_engine *peer = sync_engine_create(seed_from(0x04).data());
        sync_change *recs = nullptr; size_t n = 0;
        sync_engine_export(e, &recs, &n);
        for (size_t i = 0; i < n; i++)
            ASSERT_EQ(sync_engine_apply(peer, &recs[i]), SYNC_OK);
        sync_changes_free(recs, n);
        uint8_t de[SYNC_DIGEST_LEN], dp[SYNC_DIGEST_LEN];
        sync_engine_digest(e, de);
        sync_engine_digest(peer, dp);
        EXPECT_EQ(0, std::memcmp(de, dp, SYNC_DIGEST_LEN));

        int anchor = 0;
        sync_engine_exists(e, B(std::string("n")), 1, B(std::string("anchor")), 6,
                           &anchor);
        EXPECT_EQ(anchor, 1) << "anchor lost after crash round " << round;

        sync_engine_destroy(peer);
        sync_engine_destroy(e);
    }
}

/* ---- T6.7 Memory ownership (every alloc/free pair) --------------------- */
TEST(Hardening, MemoryOwnership) {
    for (int iter = 0; iter < 200; iter++) {
        auto seed = seed_from((uint8_t)(iter & 0xff));
        sync_engine *e = sync_engine_create(seed.data());
        sync_engine_set(e, B(std::string("ns")), 2, B(std::string("e")), 1,
                        B(std::string("f")), 1, B(std::string("val")), 3);

        /* export / sync_changes_free */
        sync_change *recs = nullptr; size_t n = 0;
        sync_engine_export(e, &recs, &n);

        /* encode / decode / free_decoded */
        if (n) {
            size_t len = sync_change_encode(&recs[0], nullptr, 0);
            std::vector<uint8_t> buf(len);
            sync_change_encode(&recs[0], buf.data(), len);
            sync_change dec; size_t used = 0;
            if (sync_change_decode(buf.data(), buf.size(), &dec, &used) == SYNC_OK)
                sync_change_free_decoded(&dec);
        }
        sync_changes_free(recs, n);

        /* get / sync_free */
        uint8_t *val = nullptr; size_t vl = 0;
        if (sync_engine_get(e, B(std::string("ns")), 2, B(std::string("e")), 1,
                            B(std::string("f")), 1, &val, &vl) == SYNC_OK)
            sync_free(val);

        /* capability root / delegate / encode / free */
        sync_capability *root = sync_capability_root(e, "ns",
                                                     SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        if (root) {
            uint8_t sub[SYNC_PUBKEY_LEN];
            std::memset(sub, 0xAB, sizeof sub);
            sync_capability *d =
                sync_capability_delegate(e, root, sub, SYNC_ACCESS_READ, 0);
            if (d) {
                int len = sync_capability_encode(d, nullptr, 0);
                std::vector<uint8_t> cb(len);
                sync_capability_encode(d, cb.data(), cb.size());
                sync_capability *d2 = sync_capability_decode(cb.data(), cb.size());
                if (d2) sync_capability_free(d2);
                sync_capability_free(d);
            }
            sync_engine_grant(e, root);
            sync_capability_free(root);
        }

        /* session begin / end */
        sync_session *s = sync_session_begin(e, 1);
        uint8_t *out = nullptr; size_t ol = 0; int done = 0;
        sync_session_step(s, nullptr, 0, &out, &ol, &done);
        if (out) sync_free(out);
        sync_session_end(s);

        sync_engine_destroy(e);
    }
    SUCCEED();
}
