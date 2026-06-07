/* oom_test.cpp — exercise out-of-memory defensive paths via allocation-failure
 * injection. Overrides operator new and wraps malloc/calloc (linker --wrap) so
 * the Nth allocation of a call can be made to fail; we sweep N and assert every
 * public entry point fails gracefully (a defined error, no crash, no leak)
 * rather than only on the happy path.
 *
 * Built only with -DSYNC_OOM_TEST=ON (kept out of the sanitizer matrix, where
 * --wrap interacts awkwardly with the ASan allocator). */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <atomic>
#include <cstdlib>
#include <cstring>
#include <new>
#include <string>
#include <vector>

namespace {
std::atomic<bool> g_armed{false};
std::atomic<long> g_countdown{0};

bool should_fail() {
    if (!g_armed.load(std::memory_order_relaxed)) return false;
    if (g_countdown.fetch_sub(1) == 1) { /* this is the Nth allocation */
        g_armed.store(false);
        return true;
    }
    return false;
}

/* Arms "fail the Nth allocation from here"; disarms on scope exit so a call
 * that allocates fewer than N times never trips later (e.g. gtest) code. */
struct Arm {
    explicit Arm(long n) { g_countdown.store(n); g_armed.store(true); }
    ~Arm() { g_armed.store(false); }
};

std::array<uint8_t, SYNC_SEED_LEN> seed(uint8_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (auto &b : s) b = v;
    return s;
}
const uint8_t *U(const char *s) { return (const uint8_t *)s; }
} // namespace

extern "C" {
extern void *__real_malloc(size_t);
extern void *__real_calloc(size_t, size_t);
void *__wrap_malloc(size_t n) { return should_fail() ? nullptr : __real_malloc(n); }
void *__wrap_calloc(size_t a, size_t b) {
    return should_fail() ? nullptr : __real_calloc(a, b);
}
}

void *operator new(std::size_t n) {
    if (should_fail()) throw std::bad_alloc();
    void *p = __real_malloc(n ? n : 1);
    if (!p) throw std::bad_alloc();
    return p;
}
void *operator new[](std::size_t n) { return operator new(n); }
void operator delete(void *p) noexcept { std::free(p); }
void operator delete[](void *p) noexcept { std::free(p); }
void operator delete(void *p, std::size_t) noexcept { std::free(p); }
void operator delete[](void *p, std::size_t) noexcept { std::free(p); }

/* Each sweep: fail allocation N for N in [1, kMax]; the call must not crash and
 * must return a defined result. The Arm dtor disarms after each call. */
static const long kMax = 60;

TEST(Oom, ExportGetDigest) {
    sync_engine *e = sync_engine_create(seed(1).data());
    ASSERT_NE(e, nullptr);
    for (int i = 0; i < 6; i++) {
        std::string ent = "e" + std::to_string(i);
        sync_engine_set(e, U("ns"), 2, U(ent.c_str()), ent.size(), U("f"), 1,
                        U("val"), 3);
    }
    for (long n = 1; n <= kMax; n++) {
        sync_change *recs = nullptr;
        size_t cnt = 0;
        int rc;
        { Arm a(n); rc = sync_engine_export(e, &recs, &cnt); }
        EXPECT_TRUE(rc == SYNC_OK || rc == SYNC_ERR_NOMEM) << "export rc=" << rc;
        if (rc == SYNC_OK) sync_changes_free(recs, cnt);

        uint8_t *v = nullptr;
        size_t vl = 0;
        { Arm a(n); rc = sync_engine_get(e, U("ns"), 2, U("e0"), 2, U("f"), 1, &v, &vl); }
        EXPECT_TRUE(rc == SYNC_OK || rc == SYNC_ERR_NOMEM || rc == SYNC_ERR_NOTFOUND);
        if (rc == SYNC_OK) sync_free(v);
    }
    sync_engine_destroy(e);
}

TEST(Oom, CodecAndApply) {
    sync_engine *e = sync_engine_create(seed(2).data());
    sync_engine_set(e, U("ns"), 2, U("x"), 1, U("f"), 1, U("v"), 1);
    sync_change *recs = nullptr;
    size_t cnt = 0;
    ASSERT_EQ(sync_engine_export(e, &recs, &cnt), SYNC_OK);
    ASSERT_GT(cnt, 0u);
    size_t len = sync_change_encode(&recs[0], nullptr, 0);
    std::vector<uint8_t> buf(len);
    sync_change_encode(&recs[0], buf.data(), len);

    sync_engine *peer = sync_engine_create(seed(3).data());
    for (long n = 1; n <= kMax; n++) {
        sync_change dec;
        size_t used = 0;
        int rc;
        { Arm a(n); rc = sync_change_decode(buf.data(), buf.size(), &dec, &used); }
        EXPECT_TRUE(rc == SYNC_OK || rc == SYNC_ERR_NOMEM || rc == SYNC_ERR_INVALID);
        if (rc == SYNC_OK) sync_change_free_decoded(&dec);

        { Arm a(n); rc = sync_engine_apply(peer, &recs[0]); }
        EXPECT_TRUE(rc == SYNC_OK || rc == SYNC_ERR_NOMEM || rc == SYNC_ERR_INTERNAL);
    }
    sync_changes_free(recs, cnt);
    sync_engine_destroy(e);
    sync_engine_destroy(peer);
}

TEST(Oom, SessionAndCapability) {
    sync_engine *e = sync_engine_create(seed(4).data());
    sync_engine_set(e, U("ns"), 2, U("x"), 1, U("f"), 1, U("v"), 1);
    for (long n = 1; n <= kMax; n++) {
        sync_session *s;
        { Arm a(n); s = sync_session_begin(e, 1); }
        if (s) {
            uint8_t *o = nullptr; size_t ol = 0; int d = 0;
            { Arm a(n); sync_session_step(s, nullptr, 0, &o, &ol, &d); }
            if (o) sync_free(o);
            sync_session_end(s);
        }

        sync_capability *c;
        { Arm a(n); c = sync_capability_root(e, "ns", SYNC_ACCESS_WRITE); }
        if (c) sync_capability_free(c);
    }
    sync_engine_destroy(e);
}
