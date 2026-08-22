/* compact_stream_test.cpp — Phase 4 (§3.4) peak-single-allocation probe for
 * streamed compaction.
 *
 * Overrides the global operator new family to record the LARGEST SINGLE
 * allocation made while armed, arms it around sync_engine_compact on a
 * 50,000-entity durable engine (plaintext and encrypted), and asserts the
 * peak stays under the CORRECTED §3.4 bound: kCompactBufSize + ~3x the
 * largest possible single frame — where "frame" may be the entire
 * capability/revocation blob set, NOT just one entity (§3.4 amendment 4).
 * The engine holds granted capabilities AND a revocation, so the cap/rev
 * frames actually stream through the writer under the probe.
 *
 * Follows tests/oom_test.cpp's pattern: the COMPLETE operator
 * new/new[]/delete/delete[]/sized-delete family is defined, because a bare
 * global operator new paired with a sanitizer runtime's operator delete is
 * the classic alloc-dealloc-mismatch configuration — which is why this test
 * is registered if(NOT SYNC_SANITIZER) in CMakeLists.txt (§3.4 amendment 8),
 * exactly like oom_test stays out of the sanitizer matrix. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <sys/stat.h>
#include <unistd.h>

#include <array>
#include <atomic>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <new>
#include <string>

#include "tempdir.hpp"

/* ---- peak-single-allocation probe -------------------------------------- */

namespace {
std::atomic<bool> g_armed{false};
std::atomic<size_t> g_peak{0}; /* largest single allocation while armed */

void record(std::size_t n) {
    if (!g_armed.load(std::memory_order_relaxed)) return;
    size_t prev = g_peak.load(std::memory_order_relaxed);
    while (n > prev && !g_peak.compare_exchange_weak(
                           prev, n, std::memory_order_relaxed)) {
    }
}
} // namespace

/* The full family, per tests/oom_test.cpp (no malloc/calloc --wrap needed
 * here — we only observe C++ allocations, we never fail them). */
void *operator new(std::size_t n) {
    record(n);
    void *p = std::malloc(n ? n : 1);
    if (!p) throw std::bad_alloc();
    return p;
}
void *operator new[](std::size_t n) { return operator new(n); }
void operator delete(void *p) noexcept { std::free(p); }
void operator delete[](void *p) noexcept { std::free(p); }
void operator delete(void *p, std::size_t) noexcept { std::free(p); }
void operator delete[](void *p, std::size_t) noexcept { std::free(p); }

namespace {

using synctest::TempDir;

/* ---- the corrected bound (§3.4 amendment 4), derived, not hand-tuned ----
 *
 * The streaming writer's resident transient is:
 *   - the FrameSink buffer: capacity pinned at kCompactBufSize for the whole
 *     run (storage.cpp, amendment 1) — its reserve() is the stream's only
 *     long-lived allocation; plus
 *   - the transients of ONE frame being built and sealed. A frame is
 *     AEAD-sealed as a unit and cannot be streamed away, so the bound is set
 *     by the largest possible single frame — which is NOT an entity frame
 *     (an entity plus its fields, ~KBs here) but the ENTIRE capability blob
 *     set serialized as one frame:
 *       kMaxIngestedCaps = 4096                        (capability.cpp)
 *       cap wire blob    = version(1) + issuer(32) + subject(32)
 *                          + varint+ns(~5) + access(1) + expiry(8) + sig(64)
 *                        ~= 143 B for a short namespace
 *       frame entry      = type(1) + varint(143)(2) + blob(143) = 146 B
 *       frame body      ~= 4096 * 146 + 4 (entry count)  ~= 598,020 B
 *     On the encrypted path seal_frame materializes `full` (count+body),
 *     `ct` (same size) and `framed` (len4 + nonce24 + ct + mac16) — three
 *     ~one-frame transients, ~1.8 MB total for the max cap set.
 *
 * Corrected peak bound (the number this test asserts the largest single
 * allocation under):
 *   kCompactBufSize + 3 * largest-frame
 *   = 262,144 + 3 * 598,064 = 2,056,336 B (~2.0 MiB)
 * — ~50x the originally-claimed ~33 KiB entity-only bound (§3.4 amendment
 * 4), and ~13x SMALLER than the ~27 MB (plaintext) / ~29 MB (encrypted)
 * image this engine compacts to: the pre-Phase-4 serialize_state built that
 * whole image in one std::string, so its largest single allocation was >=
 * the image size and this test FAILS on the old code (the discriminating
 * assertions below pin both directions). */
constexpr size_t kCompactBufSize = 256u * 1024;  /* storage.cpp   */
constexpr size_t kMaxIngestedCaps = 4096;        /* capability.cpp */
constexpr size_t kCapFrameEntryBytes = 1 + 2 + 143;
constexpr size_t kLargestFrameBytes =
    4 + 24 + (4 + kMaxIngestedCaps * kCapFrameEntryBytes) + 16;
constexpr size_t kPeakBound = kCompactBufSize + 3 * kLargestFrameBytes;
static_assert(kPeakBound == 2056336, "threshold arithmetic drifted");

constexpr int kEntities = 50000;
constexpr int kFields = 3;

const uint8_t *U(const char *s) { return (const uint8_t *)s; }

std::array<uint8_t, SYNC_SEED_LEN> seed_from(uint8_t v) {
    std::array<uint8_t, SYNC_SEED_LEN> s{};
    for (size_t i = 0; i < s.size(); i++) s[i] = (uint8_t)(v + i * 31);
    return s;
}

uint64_t file_bytes(const std::string &p) {
    struct stat st;
    return ::stat(p.c_str(), &st) == 0 ? (uint64_t)st.st_size : 0;
}

/* 50k entities x 3 short fields (the Phase 4 measurement shape from
 * docs/IMPROVEMENT_PLAN.md §4), written inside one Phase-3 batch so setup
 * costs ~a dozen sub-frame fsyncs instead of 150k frame fsyncs. The batch is
 * committed (and its maybe_compact has fired) BEFORE the probe arms; the
 * explicit sync_engine_compact under the probe rewrites the full image
 * unconditionally. */
void populate(sync_engine *e) {
    ASSERT_EQ(sync_engine_batch_begin(e), SYNC_OK);
    for (int i = 0; i < kEntities; i++) {
        std::string ent = "ent_" + std::to_string(i);
        for (int j = 0; j < kFields; j++) {
            std::string f = "f" + std::to_string(j);
            std::string v = "v" + std::to_string(i) + "_" + std::to_string(j);
            ASSERT_EQ(sync_engine_set(e, U("ns1"), 3, U(ent.data()),
                                      ent.size(), U(f.data()), f.size(),
                                      U(v.data()), v.size()),
                      SYNC_OK)
                << "set failed at entity " << i;
        }
    }
    ASSERT_EQ(sync_engine_batch_commit(e), SYNC_OK);
}

/* Capabilities + a revocation on a namespace unrelated to the entity writes
 * (the CompactionIsDeterministicByteForByte pattern): the durable engine
 * mints its own root — making it the owner, so it may revoke — plus one
 * delegation; then revokes an uninvolved third key. This guarantees the
 * compaction under the probe streams a cap frame AND a rev frame, so the
 * cap/rev leg of the writer runs under the allocation probe (§3.4 fix 4). */
void grant_caps_and_revocation(sync_engine *e, const uint8_t wpk[SYNC_PUBKEY_LEN],
                               const uint8_t tpk[SYNC_PUBKEY_LEN]) {
    sync_capability *root =
        sync_capability_root(e, "zeta", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    sync_capability *deleg =
        sync_capability_delegate(e, root, wpk, SYNC_ACCESS_WRITE, 0);
    ASSERT_NE(deleg, nullptr);
    ASSERT_EQ(sync_engine_grant(e, root), SYNC_OK);
    ASSERT_EQ(sync_engine_grant(e, deleg), SYNC_OK);
    sync_capability_free(root);
    sync_capability_free(deleg);
    ASSERT_EQ(sync_engine_revoke(e, "zeta", tpk), SYNC_OK);
}

void run_variant(bool encrypted) {
    TempDir dir;
    std::string db = dir.file(encrypted ? "peak_enc.db" : "peak_plain.db");
    auto site = seed_from(encrypted ? 0x51 : 0x50);

    /* In-memory identities for the delegation / revocation subjects. */
    sync_engine *writer = sync_engine_create(seed_from(0x52).data());
    sync_engine *third = sync_engine_create(seed_from(0x53).data());
    ASSERT_NE(writer, nullptr);
    ASSERT_NE(third, nullptr);
    uint8_t wpk[SYNC_PUBKEY_LEN], tpk[SYNC_PUBKEY_LEN];
    ASSERT_EQ(sync_engine_identity(writer, wpk), SYNC_OK);
    ASSERT_EQ(sync_engine_identity(third, tpk), SYNC_OK);
    sync_engine_destroy(writer);
    sync_engine_destroy(third);

    sync_engine *e = nullptr;
    if (encrypted) {
        std::array<uint8_t, 32> key{};
        for (size_t i = 0; i < key.size(); i++) key[i] = (uint8_t)(42 + i * 7);
        e = sync_engine_open_encrypted(db.c_str(), site.data(), key.data());
    } else {
        e = sync_engine_open(db.c_str(), site.data());
    }
    ASSERT_NE(e, nullptr);

    grant_caps_and_revocation(e, wpk, tpk);
    populate(e);
    ASSERT_EQ(sync_engine_flush(e), SYNC_OK);

    /* Arm ONLY around the compaction itself; nothing gtest-side allocates in
     * between (assertions run after disarm). sync_engine_compact catches
     * std::bad_alloc internally, so no exception can escape past disarm. */
    g_peak.store(0, std::memory_order_relaxed);
    g_armed.store(true, std::memory_order_relaxed);
    int rc = sync_engine_compact(e);
    g_armed.store(false, std::memory_order_relaxed);
    size_t peak = g_peak.load(std::memory_order_relaxed);

    ASSERT_EQ(rc, SYNC_OK);
    uint64_t image = file_bytes(db); /* == the streamed compacted image */

    /* Informational: the numbers the assertions below discriminate on. */
    std::printf("[          ] %s: peak single alloc %zu B, bound %zu B, "
                "compacted image %llu B\n",
                encrypted ? "encrypted" : "plaintext", peak, kPeakBound,
                (unsigned long long)image);

    /* The bound itself (fails on the old full-image serialize_state). */
    EXPECT_LT(peak, kPeakBound)
        << "largest single allocation during compaction ("
        << peak << " B) exceeds kCompactBufSize + 3x largest-frame ("
        << kPeakBound << " B)";

    /* Discriminating half: the image must dwarf the bound (so the bound
     * genuinely discriminates streaming from the old build-the-whole-image
     * path, whose one std::string allocation was >= `image`), and the
     * measured peak must sit far below the image. At 50k x 3 the image is
     * ~27 MB plaintext / ~29 MB encrypted vs the ~2.0 MiB bound. */
    ASSERT_GT(image, (uint64_t)kPeakBound * 8)
        << "test engine too small to discriminate streaming from the old "
           "full-image path";
    EXPECT_LT((uint64_t)peak, image / 8)
        << "peak allocation is not far below the old full-image transient";

    /* The compaction under the probe really carried the cap/rev state. */
    int revoked = 0;
    ASSERT_EQ(sync_engine_is_revoked(e, "zeta", tpk, &revoked), SYNC_OK);
    EXPECT_EQ(revoked, 1);

    sync_engine_destroy(e);
}

TEST(CompactStream, PeakAllocationBoundedPlaintext) { run_variant(false); }
TEST(CompactStream, PeakAllocationBoundedEncrypted) { run_variant(true); }

} // namespace
