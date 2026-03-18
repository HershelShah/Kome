#include <gtest/gtest.h>
#include "kome_conflict.hpp"
#include <cstring>

using namespace kome;

static KomeEntryMeta make_meta(uint64_t ts, uint8_t author_byte, uint64_t seq) {
    KomeEntryMeta m = {};
    m.timestamp_us = ts;
    std::memset(m.author, author_byte, 32);
    m.seq = seq;
    return m;
}

/* --- LWW: timestamp wins ------------------------------------------------ */

TEST(ConflictTest, HigherTimestampWins) {
    auto local  = make_meta(100, 0x11, 1);
    auto remote = make_meta(200, 0x11, 1);
    EXPECT_TRUE(lww_remote_wins(&local, &remote));
}

TEST(ConflictTest, LowerTimestampLoses) {
    auto local  = make_meta(200, 0x11, 1);
    auto remote = make_meta(100, 0x11, 1);
    EXPECT_FALSE(lww_remote_wins(&local, &remote));
}

/* --- LWW: author tiebreak ----------------------------------------------- */

TEST(ConflictTest, SameTimestampHigherAuthorWins) {
    auto local  = make_meta(100, 0x11, 1);
    auto remote = make_meta(100, 0xFF, 1);
    EXPECT_TRUE(lww_remote_wins(&local, &remote));
}

TEST(ConflictTest, SameTimestampLowerAuthorLoses) {
    auto local  = make_meta(100, 0xFF, 1);
    auto remote = make_meta(100, 0x11, 1);
    EXPECT_FALSE(lww_remote_wins(&local, &remote));
}

/* --- LWW: seq tiebreak -------------------------------------------------- */

TEST(ConflictTest, SameTimestampSameAuthorHigherSeqWins) {
    auto local  = make_meta(100, 0x11, 1);
    auto remote = make_meta(100, 0x11, 5);
    EXPECT_TRUE(lww_remote_wins(&local, &remote));
}

TEST(ConflictTest, SameTimestampSameAuthorLowerSeqLoses) {
    auto local  = make_meta(100, 0x11, 5);
    auto remote = make_meta(100, 0x11, 1);
    EXPECT_FALSE(lww_remote_wins(&local, &remote));
}

TEST(ConflictTest, IdenticalEntriesLocalWins) {
    auto local  = make_meta(100, 0x11, 1);
    auto remote = make_meta(100, 0x11, 1);
    /* Exact same → remote does NOT win → local keeps */
    EXPECT_FALSE(lww_remote_wins(&local, &remote));
}

/* --- resolve_conflict: default LWW -------------------------------------- */

TEST(ConflictTest, ResolveDefaultLWW) {
    auto local  = make_meta(100, 0x11, 1);
    auto remote = make_meta(200, 0x22, 1);
    uint8_t *merge_val = nullptr;
    size_t merge_len = 0;

    auto choice = resolve_conflict("ns", (const uint8_t*)"k", 1,
                                    &local, nullptr, &remote, nullptr,
                                    nullptr, nullptr,
                                    &merge_val, &merge_len);
    EXPECT_EQ(KOME_KEEP_REMOTE, choice);
    EXPECT_EQ(nullptr, merge_val);
}

/* --- resolve_conflict: callback override -------------------------------- */

static KomeConflictChoice always_keep_local(
    void *, const char *, const uint8_t *, size_t,
    const KomeEntryMeta *, const uint8_t *,
    const KomeEntryMeta *, const uint8_t *,
    uint8_t **, size_t *) {
    return KOME_KEEP_LOCAL;
}

TEST(ConflictTest, CallbackOverride) {
    auto local  = make_meta(100, 0x11, 1);
    auto remote = make_meta(200, 0x22, 1);
    uint8_t *merge_val = nullptr;
    size_t merge_len = 0;

    auto choice = resolve_conflict("ns", (const uint8_t*)"k", 1,
                                    &local, nullptr, &remote, nullptr,
                                    always_keep_local, nullptr,
                                    &merge_val, &merge_len);
    EXPECT_EQ(KOME_KEEP_LOCAL, choice);
}

/* --- resolve_conflict: merge callback ----------------------------------- */

static KomeConflictChoice merge_callback(
    void *, const char *, const uint8_t *, size_t,
    const KomeEntryMeta *, const uint8_t *,
    const KomeEntryMeta *, const uint8_t *,
    uint8_t **merge_out, size_t *merge_len_out) {
    const char *merged = "merged_data";
    size_t len = std::strlen(merged);
    *merge_out = (uint8_t*)std::malloc(len);
    std::memcpy(*merge_out, merged, len);
    *merge_len_out = len;
    return KOME_MERGE;
}

TEST(ConflictTest, MergeChoice) {
    auto local  = make_meta(100, 0x11, 1);
    auto remote = make_meta(200, 0x22, 1);
    uint8_t *merge_val = nullptr;
    size_t merge_len = 0;

    auto choice = resolve_conflict("ns", (const uint8_t*)"k", 1,
                                    &local, nullptr, &remote, nullptr,
                                    merge_callback, nullptr,
                                    &merge_val, &merge_len);
    EXPECT_EQ(KOME_MERGE, choice);
    EXPECT_NE(nullptr, merge_val);
    EXPECT_EQ(11u, merge_len);
    EXPECT_EQ(0, std::memcmp(merge_val, "merged_data", 11));
    std::free(merge_val);
}
