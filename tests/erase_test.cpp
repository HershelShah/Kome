/* erase_test.cpp — privacy-erasure acceptance tests.
 *
 * Exercises sync_engine_erase_field and sync_blob_erase: empty-value
 * overwrites that replicate, the erase-before-tombstone ordering invariant
 * (erase on a tombstoned entity errors instead of resurrecting), blob
 * payload zeroing, and the documented limits (erase after a plain delete,
 * corrupt manifests). The physical half — superseded bytes leaving the
 * on-disk log via sync_engine_compact — is covered in storage_test.cpp. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "crypto.h" /* ke::blake2b — to name chunk entities directly */

namespace {

using cluster::B;

/* Deterministic pseudo-random fill (blob_test.cpp's generator). */
std::vector<uint8_t> make_data(size_t n, uint32_t seed) {
    std::vector<uint8_t> v(n);
    uint32_t x = seed ? seed : 1;
    for (size_t i = 0; i < n; i++) {
        x ^= x << 13; x ^= x >> 17; x ^= x << 5;
        v[i] = (uint8_t)x;
    }
    return v;
}

/* Mirrors blob.cpp's internal entity-key layout (documented in
 * include/sync_engine.h): tag, 0x00, 32-byte hash/id. */
std::string chunk_entity(const uint8_t hash[32]) {
    std::string s;
    s.push_back('c'); s.push_back('\0');
    s.append((const char *)hash, 32);
    return s;
}
std::string manifest_entity(const uint8_t id[32]) {
    std::string s;
    s.push_back('b'); s.push_back('\0');
    s.append((const char *)id, 32);
    return s;
}

/* The exported value of (entity, field), or "<absent>" if no such register is
 * in the export. Export includes registers hidden under tombstones, so this
 * observes exactly what a tombstone retains — the thing erasure must empty. */
std::string exported_value(sync_engine *e, const std::string &entity,
                           const std::string &field) {
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_SYNC_OK(sync_engine_export(e, &recs, &n));
    std::string out = "<absent>";
    for (size_t i = 0; i < n; i++) {
        const sync_change &c = recs[i];
        if (c.kind != SYNC_CHANGE_REGISTER) continue;
        if (std::string((const char *)c.entity, c.entity_len) != entity) continue;
        if (std::string((const char *)c.field, c.field_len) != field) continue;
        out.assign((const char *)c.value, c.value_len);
    }
    sync_changes_free(recs, n);
    return out;
}

/* Every 'c'-tagged chunk entity's "d" register in the export: count and
 * whether all of them are empty. Sees hidden (tombstoned) registers too. */
void exported_chunk_payloads(sync_engine *e, size_t *out_count,
                             bool *out_all_empty) {
    sync_change *recs = nullptr;
    size_t n = 0;
    EXPECT_SYNC_OK(sync_engine_export(e, &recs, &n));
    *out_count = 0;
    *out_all_empty = true;
    for (size_t i = 0; i < n; i++) {
        const sync_change &c = recs[i];
        if (c.kind != SYNC_CHANGE_REGISTER) continue;
        if (c.entity_len != 34 || c.entity[0] != 'c' || c.entity[1] != 0)
            continue;
        if (c.field_len != 1 || c.field[0] != 'd') continue;
        (*out_count)++;
        if (c.value_len != 0) *out_all_empty = false;
    }
    sync_changes_free(recs, n);
}

sync_error erase_field(sync_engine *e, const std::string &ns,
                       const std::string &ent, const std::string &field) {
    return sync_engine_erase_field(e, B(ns), ns.size(), B(ent), ent.size(),
                                   B(field), field.size());
}

} // namespace

/* ---- 1. Field erase: empty overwrite, not not-found ---------------------- */
TEST(EraseField, OverwritesInPlace) {
    sync_engine *e = cluster::make(0x51);
    cluster::put(e, "ns", "post", "text", "hello");
    cluster::put(e, "ns", "post", "an", "alice");

    ASSERT_EQ(erase_field(e, "ns", "post", "text"), SYNC_OK);

    /* The register survives with an empty value — readable, distinguishable
     * from not-found — and the entity is still present. */
    uint8_t *v = nullptr;
    size_t vlen = 99;
    ASSERT_SYNC_OK(sync_engine_get(e, B(std::string("ns")), 2,
                                   B(std::string("post")), 4,
                                   B(std::string("text")), 4, &v, &vlen));
    EXPECT_NE(v, nullptr);
    EXPECT_EQ(vlen, 0u);
    sync_free(v);
    EXPECT_TRUE(cluster::exists(e, "ns", "post"));
    EXPECT_EQ(cluster::get(e, "ns", "post", "an"), "alice"); /* untouched */

    sync_engine_destroy(e);
}

/* ---- 2. The safety win: no resurrection through a tombstone -------------- */
TEST(EraseField, RefusesTombstonedEntity) {
    sync_engine *e = cluster::make(0x52);
    cluster::put(e, "ns", "post", "text", "secret");
    cluster::del(e, "ns", "post");
    ASSERT_FALSE(cluster::exists(e, "ns", "post"));

    /* Erase-after-delete is the ordering bug this API exists to catch: it
     * must error out, write nothing, and leave the entity tombstoned. */
    EXPECT_EQ(erase_field(e, "ns", "post", "text"), SYNC_ERR_NOTFOUND);
    EXPECT_FALSE(cluster::exists(e, "ns", "post")) << "erase resurrected";
    /* The hidden register is untouched (erase wrote nothing) — emptying it
     * is the job of an erase issued BEFORE the delete. */
    EXPECT_EQ(exported_value(e, "post", "text"), "secret");

    sync_engine_destroy(e);
}

/* ---- 3. Never creates state ---------------------------------------------- */
TEST(EraseField, RefusesAbsentEntityOrField) {
    sync_engine *e = cluster::make(0x53);
    cluster::put(e, "ns", "post", "text", "hi");

    EXPECT_EQ(erase_field(e, "ns", "ghost", "text"), SYNC_ERR_NOTFOUND);
    EXPECT_FALSE(cluster::exists(e, "ns", "ghost"));
    EXPECT_EQ(erase_field(e, "other", "post", "text"), SYNC_ERR_NOTFOUND);

    EXPECT_EQ(erase_field(e, "ns", "post", "nofield"), SYNC_ERR_NOTFOUND);
    EXPECT_EQ(exported_value(e, "post", "nofield"), "<absent>")
        << "erase created a register";

    EXPECT_EQ(sync_engine_erase_field(nullptr, B(std::string("ns")), 2,
                                      B(std::string("post")), 4,
                                      B(std::string("text")), 4),
              SYNC_ERR_INVALID);

    sync_engine_destroy(e);
}

/* ---- 4. The erasure replicates and beats the original -------------------- */
TEST(EraseField, ReplicatesToPeerHoldingOldValue) {
    sync_engine *a = cluster::make(0x54);
    sync_engine *b = cluster::make(0x55);
    cluster::put(a, "ns", "post", "text", "secret");
    cluster::sync2(a, b);
    ASSERT_EQ(cluster::get(b, "ns", "post", "text"), "secret");

    ASSERT_EQ(erase_field(a, "ns", "post", "text"), SYNC_OK);
    cluster::sync2(a, b);

    /* B held the old value; A's fresh-HLC empty overwrite must win LWW. */
    uint8_t *v = nullptr;
    size_t vlen = 99;
    ASSERT_SYNC_OK(sync_engine_get(b, B(std::string("ns")), 2,
                                   B(std::string("post")), 4,
                                   B(std::string("text")), 4, &v, &vlen));
    EXPECT_EQ(vlen, 0u) << "peer still holds the erased value";
    sync_free(v);
    EXPECT_EQ(cluster::digest(a), cluster::digest(b));

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- 5. Blob erase: payload zeroed, then tombstoned ---------------------- */
TEST(BlobErase, ZeroesChunksAndTombstones) {
    sync_engine *e = cluster::make(0x56);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(SYNC_BLOB_CHUNK_MAX * 2 + 123, 42);
    uint8_t id[32];
    ASSERT_EQ(sync_blob_put(e, B(ns), ns.size(), data.data(), data.size(), id),
              SYNC_OK);

    ASSERT_EQ(sync_blob_erase(e, B(ns), ns.size(), id), SYNC_OK);

    /* Gone from every read surface... */
    uint8_t *out = nullptr;
    size_t out_len = 0;
    EXPECT_EQ(sync_blob_get(e, B(ns), ns.size(), id, &out, &out_len),
              SYNC_ERR_NOTFOUND);
    uint64_t size; int complete;
    EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete),
              SYNC_ERR_NOTFOUND);
    sync_scan_entry *entries = nullptr;
    size_t count = 0;
    ASSERT_SYNC_OK(sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0,
                                    &entries, &count));
    EXPECT_EQ(count, 0u);
    sync_scan_free(entries, count);

    /* ...and — the difference from sync_blob_delete — the payload registers
     * hidden under the tombstones are EMPTY, not the JPEG-sized originals. */
    size_t chunks = 0;
    bool all_empty = false;
    exported_chunk_payloads(e, &chunks, &all_empty);
    EXPECT_EQ(chunks, 3u) << "expected all chunk registers retained (hidden)";
    EXPECT_TRUE(all_empty) << "chunk payload survived the erase";

    /* A second erase finds nothing: the manifest is tombstoned. */
    EXPECT_EQ(sync_blob_erase(e, B(ns), ns.size(), id), SYNC_ERR_NOTFOUND);

    sync_engine_destroy(e);
}

/* ---- 6. Blob erasure replicates ------------------------------------------ */
TEST(BlobErase, ReplicatesToPeerHoldingBlob) {
    sync_engine *a = cluster::make(0x57);
    sync_engine *b = cluster::make(0x58);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(SYNC_BLOB_CHUNK_MAX + 999, 7);
    uint8_t id[32];
    ASSERT_EQ(sync_blob_put(a, B(ns), ns.size(), data.data(), data.size(), id),
              SYNC_OK);
    cluster::sync2(a, b);
    uint8_t *out = nullptr;
    size_t out_len = 0;
    ASSERT_SYNC_OK(sync_blob_get(b, B(ns), ns.size(), id, &out, &out_len));
    sync_free(out);

    ASSERT_EQ(sync_blob_erase(a, B(ns), ns.size(), id), SYNC_OK);
    cluster::sync2(a, b);

    /* B held the full payload; after one sync it holds empty registers under
     * tombstones, same as A. */
    out = nullptr; out_len = 0;
    EXPECT_EQ(sync_blob_get(b, B(ns), ns.size(), id, &out, &out_len),
              SYNC_ERR_NOTFOUND);
    size_t chunks = 0;
    bool all_empty = false;
    exported_chunk_payloads(b, &chunks, &all_empty);
    EXPECT_EQ(chunks, 2u);
    EXPECT_TRUE(all_empty) << "peer still holds erased payload bytes";
    EXPECT_EQ(cluster::digest(a), cluster::digest(b));

    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

/* ---- 7. Documented limit: erase cannot reach through a prior delete ------ */
TEST(BlobErase, AfterPlainDeleteCannotReachPayload) {
    sync_engine *e = cluster::make(0x59);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(5000, 3);
    uint8_t id[32];
    ASSERT_EQ(sync_blob_put(e, B(ns), ns.size(), data.data(), data.size(), id),
              SYNC_OK);
    ASSERT_EQ(sync_blob_delete(e, B(ns), ns.size(), id), SYNC_OK);

    /* The wrong order (delete first) leaves payload hidden under tombstones;
     * erase must NOT resurrect entities to get at it. Pinned as NOTFOUND +
     * payload intact — the header documents this, and tombstone GC is what
     * eventually drops it. */
    EXPECT_EQ(sync_blob_erase(e, B(ns), ns.size(), id), SYNC_ERR_NOTFOUND);
    size_t chunks = 0;
    bool all_empty = true;
    exported_chunk_payloads(e, &chunks, &all_empty);
    EXPECT_EQ(chunks, 1u);
    EXPECT_FALSE(all_empty) << "erase reached through a tombstone";
    uint8_t chash[32];
    ke::blake2b(data.data(), data.size(), chash, 32);
    int exists = 1;
    std::string ck = chunk_entity(chash);
    ASSERT_SYNC_OK(sync_engine_exists(e, B(ns), ns.size(),
                                      (const uint8_t *)ck.data(), ck.size(),
                                      &exists));
    EXPECT_EQ(exists, 0) << "erase resurrected a tombstoned chunk";

    sync_engine_destroy(e);
}

/* ---- 8. Corrupt manifest: tombstone what exists, report CORRUPT ---------- */
TEST(BlobErase, CorruptManifestTombstonedAndReported) {
    sync_engine *e = cluster::make(0x5A);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(100, 9);
    uint8_t id[32];
    ASSERT_EQ(sync_blob_put(e, B(ns), ns.size(), data.data(), data.size(), id),
              SYNC_OK);

    /* Overwrite the manifest with garbage a peer could have written. */
    std::string ment = manifest_entity(id);
    std::string garbage(5, '\x7f');
    ASSERT_SYNC_OK(sync_engine_set(e, B(ns), ns.size(),
                                   (const uint8_t *)ment.data(), ment.size(),
                                   B(std::string("m")), 1,
                                   (const uint8_t *)garbage.data(),
                                   garbage.size()));

    EXPECT_EQ(sync_blob_erase(e, B(ns), ns.size(), id), SYNC_ERR_CORRUPT);
    int exists = 1;
    ASSERT_SYNC_OK(sync_engine_exists(e, B(ns), ns.size(),
                                      (const uint8_t *)ment.data(), ment.size(),
                                      &exists));
    EXPECT_EQ(exists, 0) << "corrupt manifest entity was not tombstoned";

    sync_engine_destroy(e);
}

/* ---- 9. Edge cases -------------------------------------------------------- */
TEST(BlobErase, EmptyBlobAndInvalidArgs) {
    sync_engine *e = cluster::make(0x5B);
    const std::string ns = "photos.blobs";

    uint8_t id[32];
    ASSERT_EQ(sync_blob_put(e, B(ns), ns.size(), nullptr, 0, id), SYNC_OK);
    EXPECT_EQ(sync_blob_erase(e, B(ns), ns.size(), id), SYNC_OK);
    uint64_t size; int complete;
    EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete),
              SYNC_ERR_NOTFOUND);

    uint8_t unknown[32] = {0xFF};
    EXPECT_EQ(sync_blob_erase(e, B(ns), ns.size(), unknown), SYNC_ERR_NOTFOUND);
    EXPECT_EQ(sync_blob_erase(nullptr, B(ns), ns.size(), id), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_blob_erase(e, B(ns), ns.size(), nullptr), SYNC_ERR_INVALID);

    sync_engine_destroy(e);
}
