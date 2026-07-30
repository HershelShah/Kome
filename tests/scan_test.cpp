/* scan_test.cpp — sync_engine_scan acceptance tests.
 *
 * Verifies the namespace entity-scan read primitive: present-only,
 * byte-lexicographic order, exclusive resume-cursor pagination, empty/unknown
 * namespace and past-the-end termination, invalid-argument rejection,
 * embedded-NUL round-tripping, and agreement across durable reopen and
 * export/apply convergence. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstring>
#include <set>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "tempdir.hpp"

namespace {

using cluster::B;
using synctest::TempDir;

/* Run sync_engine_scan and unpack the result into a vector<string> for easy
 * comparison, freeing the array before returning. */
std::vector<std::string> scan(sync_engine *e, const std::string &ns,
                              const std::string &start_after, size_t limit,
                              sync_error *out_rc = nullptr) {
    sync_scan_entry *entries = nullptr;
    size_t count = 0;
    sync_error rc = sync_engine_scan(
        e, B(ns), ns.size(),
        start_after.empty() ? nullptr : B(start_after), start_after.size(),
        limit, &entries, &count);
    if (out_rc) *out_rc = rc;
    std::vector<std::string> out;
    if (rc == SYNC_OK) {
        for (size_t i = 0; i < count; i++)
            out.emplace_back((const char *)entries[i].entity, entries[i].entity_len);
    }
    sync_scan_free(entries, count);
    return out;
}

} // namespace

/* ---- Basic: two namespaces, present entities only, sorted --------------- */
TEST(Scan, BasicSortedPerNamespace) {
    sync_engine *e = cluster::make(1);
    cluster::put(e, "ns1", "charlie", "f", "1");
    cluster::put(e, "ns1", "alpha", "f", "1");
    cluster::put(e, "ns1", "bravo", "f", "1");
    cluster::put(e, "ns2", "zulu", "f", "1");

    std::vector<std::string> got = scan(e, "ns1", "", 0);
    std::vector<std::string> want = {"alpha", "bravo", "charlie"};
    EXPECT_EQ(got, want);

    std::vector<std::string> got2 = scan(e, "ns2", "", 0);
    std::vector<std::string> want2 = {"zulu"};
    EXPECT_EQ(got2, want2);

    sync_engine_destroy(e);
}

/* ---- Deleted excluded; re-added included again --------------------------- */
TEST(Scan, DeletedExcludedReaddedIncluded) {
    sync_engine *e = cluster::make(2);
    cluster::put(e, "ns", "a", "f", "1");
    cluster::put(e, "ns", "b", "f", "1");
    cluster::put(e, "ns", "c", "f", "1");

    EXPECT_EQ((scan(e, "ns", "", 0)), (std::vector<std::string>{"a", "b", "c"}));

    cluster::del(e, "ns", "b");
    EXPECT_EQ((scan(e, "ns", "", 0)), (std::vector<std::string>{"a", "c"}));

    cluster::put(e, "ns", "b", "f", "2");
    EXPECT_EQ((scan(e, "ns", "", 0)), (std::vector<std::string>{"a", "b", "c"}));

    sync_engine_destroy(e);
}

/* ---- Pagination: limit=2 walk visits every entity exactly once ----------- */
TEST(Scan, PaginationWalkMatchesUnpaginated) {
    sync_engine *e = cluster::make(3);
    std::vector<std::string> names;
    for (int i = 0; i < 11; i++) {
        std::string n = "e" + std::to_string(i);
        names.push_back(n);
        cluster::put(e, "ns", n, "f", "v");
    }
    std::vector<std::string> full = scan(e, "ns", "", 0);
    std::sort(names.begin(), names.end());
    EXPECT_EQ(full, names);

    std::vector<std::string> walked;
    std::string cursor;
    int guard = 0;
    for (;; guard++) {
        ASSERT_LT(guard, 100) << "pagination walk failed to terminate";
        std::vector<std::string> page = scan(e, "ns", cursor, 2);
        if (page.empty()) break;
        EXPECT_LE(page.size(), 2u);
        for (auto &n : page) walked.push_back(n);
        cursor = page.back();
    }
    EXPECT_EQ(walked, full);

    /* No duplicates, no skips. */
    std::set<std::string> uniq(walked.begin(), walked.end());
    EXPECT_EQ(uniq.size(), walked.size());

    /* Cursor past the end returns 0, cleanly. */
    sync_error rc = SYNC_ERR_INTERNAL;
    std::vector<std::string> past = scan(e, "ns", "zzzzz", 0, &rc);
    EXPECT_EQ(rc, SYNC_OK);
    EXPECT_TRUE(past.empty());

    sync_engine_destroy(e);
}

/* ---- Cursor is a valid bound even when it names no live entity ----------- */
TEST(Scan, CursorBetweenKeysAndOnTombstone) {
    sync_engine *e = cluster::make(10);
    cluster::put(e, "ns", "a", "f", "1");
    cluster::put(e, "ns", "c", "f", "1");
    cluster::put(e, "ns", "e", "f", "1");
    cluster::put(e, "ns", "d", "f", "1");
    cluster::del(e, "ns", "d"); /* "d" now names a tombstone, not a live key */

    /* Cursor strictly between two existing keys, naming nothing at all
     * (upper_bound semantics: land on the first key past it). */
    EXPECT_EQ((scan(e, "ns", "b", 0)), (std::vector<std::string>{"c", "e"}));

    /* Cursor naming a tombstoned entity: still a valid bound, excludes only
     * the tombstone's own key. */
    EXPECT_EQ((scan(e, "ns", "d", 0)), (std::vector<std::string>{"e"}));

    sync_engine_destroy(e);
}

/* ---- Namespace exists but every entity is tombstoned: empty, not error --- */
TEST(Scan, AllTombstonedNamespaceReturnsEmpty) {
    sync_engine *e = cluster::make(11);
    cluster::put(e, "ns", "a", "f", "1");
    cluster::put(e, "ns", "b", "f", "1");
    cluster::put(e, "ns", "c", "f", "1");
    cluster::del(e, "ns", "a");
    cluster::del(e, "ns", "b");
    cluster::del(e, "ns", "c");

    /* Pre-seed out params with garbage to confirm they are overwritten. */
    sync_scan_entry *entries = reinterpret_cast<sync_scan_entry *>(0x1);
    size_t count = 12345;
    std::string ns = "ns";
    sync_error rc = sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0,
                                     &entries, &count);
    EXPECT_EQ(rc, SYNC_OK);
    EXPECT_EQ(entries, nullptr);
    EXPECT_EQ(count, 0u);

    sync_engine_destroy(e);
}

/* ---- Unknown namespace / empty engine ------------------------------------ */
TEST(Scan, UnknownNamespaceAndEmptyEngine) {
    sync_engine *e = cluster::make(4);

    sync_error rc = SYNC_ERR_INTERNAL;
    std::vector<std::string> got = scan(e, "nope", "", 0, &rc);
    EXPECT_EQ(rc, SYNC_OK);
    EXPECT_TRUE(got.empty());

    cluster::put(e, "other", "x", "f", "v"); /* engine non-empty overall */
    std::vector<std::string> still = scan(e, "nope", "", 0, &rc);
    EXPECT_EQ(rc, SYNC_OK);
    EXPECT_TRUE(still.empty());

    sync_engine_destroy(e);
}

/* ---- Invalid arguments ---------------------------------------------------- */
TEST(Scan, InvalidArgs) {
    sync_engine *e = cluster::make(5);
    sync_scan_entry *entries = nullptr;
    size_t count = 0;
    std::string ns = "ns";

    /* NULL engine. */
    EXPECT_EQ(sync_engine_scan(nullptr, B(ns), ns.size(), nullptr, 0, 0,
                               &entries, &count),
             SYNC_ERR_INVALID);

    /* NULL out params. */
    EXPECT_EQ(sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0, nullptr,
                               &count),
             SYNC_ERR_INVALID);
    EXPECT_EQ(sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0, &entries,
                               nullptr),
             SYNC_ERR_INVALID);

    /* NULL ns with ns_len > 0. */
    EXPECT_EQ(sync_engine_scan(e, nullptr, 3, nullptr, 0, 0, &entries, &count),
             SYNC_ERR_INVALID);

    /* NULL start_after with start_after_len > 0. */
    EXPECT_EQ(sync_engine_scan(e, B(ns), ns.size(), nullptr, 3, 0, &entries,
                               &count),
             SYNC_ERR_INVALID);

    sync_engine_destroy(e);
}

/* ---- Embedded NUL bytes round-trip ----------------------------------------- */
TEST(Scan, EmbeddedNulRoundTrip) {
    sync_engine *e = cluster::make(6);
    std::string ns = std::string("na\0mespace", 10);
    std::string ent_a = std::string("ent\0A", 5);
    std::string ent_b = std::string("ent\0B", 5);
    ASSERT_LT(ent_a, ent_b); /* sanity: the embedded byte differentiates order */

    cluster::put(e, ns, ent_b, "f", "1");
    cluster::put(e, ns, ent_a, "f", "1");

    std::vector<std::string> got = scan(e, ns, "", 0);
    ASSERT_EQ(got.size(), 2u);
    EXPECT_EQ(got[0], ent_a);
    EXPECT_EQ(got[1], ent_b);

    /* Resume with an embedded-NUL cursor. */
    std::vector<std::string> rest = scan(e, ns, ent_a, 0);
    EXPECT_EQ(rest, (std::vector<std::string>{ent_b}));

    sync_engine_destroy(e);
}

/* ---- Entity named "" yields a non-NULL owned buffer, per the header's ---- */
/* documented malloc(1) special case (a plain dup_field() would return NULL   */
/* here, which is indistinguishable from "no cursor" and would hang a        */
/* pagination loop). Also pins the header's caveat: such an entity cannot be */
/* resumed past by cursor, since its 0-length name equals "no cursor". */
TEST(Scan, EmptyNamedEntityNonNullAndPageBoundaryCaveat) {
    sync_engine *e = cluster::make(12);
    cluster::put(e, "ns", "", "f", "1");
    cluster::put(e, "ns", "b", "f", "1");

    sync_scan_entry *entries = nullptr;
    size_t count = 0;
    std::string ns = "ns";
    ASSERT_EQ(sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0, &entries,
                               &count),
             SYNC_OK);
    ASSERT_EQ(count, 2u);
    ASSERT_EQ(entries[0].entity_len, 0u); /* "" sorts first */
    EXPECT_NE(entries[0].entity, nullptr); /* must be a real owned buffer */
    EXPECT_EQ(entries[1].entity_len, 1u);

    /* Caveat: passing the "" entity's own name (0-length) as start_after is
     * indistinguishable from "no cursor" and restarts from the beginning
     * rather than resuming past it. */
    sync_scan_entry *page2 = nullptr;
    size_t count2 = 0;
    ASSERT_EQ(sync_engine_scan(e, B(ns), ns.size(), entries[0].entity,
                               entries[0].entity_len, 0, &page2, &count2),
             SYNC_OK);
    ASSERT_EQ(count2, 2u);
    EXPECT_EQ(page2[0].entity_len, 0u);
    EXPECT_EQ(page2[1].entity_len, 1u);

    sync_scan_free(page2, count2);
    sync_scan_free(entries, count);
    sync_engine_destroy(e);
}

/* ---- Durable engine: scan after reopen matches pre-close scan ------------- */
TEST(Scan, DurableReopenMatches) {
    TempDir dir;
    std::string db = dir.file("state.db");
    auto seed = cluster::seed_from(7);

    sync_engine *e = sync_engine_open(db.c_str(), seed.data());
    ASSERT_NE(e, nullptr);
    cluster::put(e, "ns", "one", "f", "1");
    cluster::put(e, "ns", "two", "f", "1");
    cluster::put(e, "ns", "three", "f", "1");
    cluster::del(e, "ns", "two");

    std::vector<std::string> before = scan(e, "ns", "", 0);
    sync_engine_destroy(e);

    sync_engine *e2 = sync_engine_open(db.c_str(), seed.data());
    ASSERT_NE(e2, nullptr);
    std::vector<std::string> after = scan(e2, "ns", "", 0);
    EXPECT_EQ(before, after);
    EXPECT_EQ(after, (std::vector<std::string>{"one", "three"}));

    sync_engine_destroy(e2);
}

/* ---- Two engines converged via export/apply scan identically -------------- */
TEST(Scan, ConvergedEnginesMatch) {
    sync_engine *a = cluster::make(8);
    sync_engine *b = cluster::make(9);

    cluster::put(a, "ns", "alpha", "f", "1");
    cluster::put(a, "ns", "bravo", "f", "1");
    cluster::put(b, "ns", "charlie", "f", "1");
    cluster::put(b, "ns", "alpha", "f", "2"); /* concurrent edit, LWW resolves */

    cluster::replicate(a, b);
    cluster::replicate(b, a);

    std::vector<std::string> sa = scan(a, "ns", "", 0);
    std::vector<std::string> sb = scan(b, "ns", "", 0);
    EXPECT_EQ(sa, sb);
    EXPECT_EQ(sa, (std::vector<std::string>{"alpha", "bravo", "charlie"}));

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}
