/* blob_test.cpp — Blob extension acceptance tests.
 *
 * Exercises sync_blob_put/get/stat/delete: round-trip across chunk-count
 * boundaries, empty blobs, idempotency, partial-replication semantics,
 * corruption detection, defensive parsing of hostile manifests, delete
 * cascade, and cross-engine convergence. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "byteorder.h"
#include "cluster.hpp"
#include "crypto.h" /* ke::blake2b — to compute/tamper chunk hashes directly */

namespace {

using cluster::B;

/* Deterministic pseudo-random fill so different sizes produce non-repeating
 * content (a naive all-zero buffer could hide chunk-boundary bugs). */
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

/* Mirrors blob.cpp's manifest header layout: version(1) + total_size(8) +
 * chunk_count(4). */
constexpr size_t kManifestHeaderLen = 13;

/* Read the raw manifest field bytes for `id` directly through the engine's
 * generic get, bypassing sync_blob_get's validation entirely -- used to
 * splice/tamper genuine manifests in the attack-surface tests below. */
sync_error read_raw_manifest(sync_engine *e, const std::string &ns,
                             const uint8_t id[32], std::string &out) {
    std::string ment = manifest_entity(id);
    uint8_t *raw = nullptr;
    size_t raw_len = 0;
    int rc = sync_engine_get(e, B(ns), ns.size(), (const uint8_t *)ment.data(),
                             ment.size(), B(std::string("m")), 1, &raw,
                             &raw_len);
    if (rc == SYNC_OK) {
        out.assign((const char *)raw, raw_len);
        sync_free(raw);
    }
    return (sync_error)rc;
}

/* Plant raw manifest bytes for `id`, bypassing sync_blob_put entirely -- lets
 * a test construct a manifest an honest client could never produce. */
void write_manifest_for(sync_engine *e, const std::string &ns,
                        const uint8_t id[32], const std::string &bytes) {
    std::string ment = manifest_entity(id);
    ASSERT_SYNC_OK(sync_engine_set(e, B(ns), ns.size(),
                                   (const uint8_t *)ment.data(), ment.size(),
                                   B(std::string("m")), 1,
                                   (const uint8_t *)bytes.data(), bytes.size()));
}

sync_error put(sync_engine *e, const std::string &ns,
              const std::vector<uint8_t> &data, uint8_t out_id[32]) {
    return sync_blob_put(e, B(ns), ns.size(),
                         data.empty() ? nullptr : data.data(), data.size(),
                         out_id);
}

sync_error get(sync_engine *e, const std::string &ns, const uint8_t id[32],
              std::vector<uint8_t> &out) {
    uint8_t *buf = nullptr;
    size_t len = 0;
    sync_error rc = sync_blob_get(e, B(ns), ns.size(), id, &buf, &len);
    out.clear();
    if (rc == SYNC_OK) {
        if (len) out.assign(buf, buf + len);
        EXPECT_NE(buf, nullptr) << "SYNC_OK must never hand back a NULL buffer";
    }
    sync_free(buf);
    return rc;
}

/* Whether a change record's entity is exactly `entity`. */
bool entity_is(const sync_change &c, const std::string &entity) {
    return c.entity_len == entity.size() &&
          std::memcmp(c.entity, entity.data(), entity.size()) == 0;
}

} // namespace

/* ---- 1. Round-trip across chunk-count boundaries ------------------------ */
TEST(Blob, RoundTripSizes) {
    sync_engine *e = cluster::make(1);
    ASSERT_NE(e, nullptr);
    const std::string ns = "photos.blobs";

    std::vector<size_t> sizes = {
        100,
        SYNC_BLOB_CHUNK_MAX,
        SYNC_BLOB_CHUNK_MAX + 1,
        100 * 1024, /* ~100 KiB => 4 chunks */
    };
    for (size_t sz : sizes) {
        std::vector<uint8_t> data = make_data(sz, (uint32_t)sz + 7);
        uint8_t id1[32], id2[32];
        ASSERT_EQ(put(e, ns, data, id1), SYNC_OK) << "size=" << sz;
        ASSERT_EQ(put(e, ns, data, id2), SYNC_OK) << "size=" << sz;
        EXPECT_EQ(0, std::memcmp(id1, id2, 32))
            << "same content must yield the same id, size=" << sz;

        std::vector<uint8_t> back;
        ASSERT_EQ(get(e, ns, id1, back), SYNC_OK) << "size=" << sz;
        EXPECT_EQ(data, back) << "size=" << sz;
    }
    sync_engine_destroy(e);
}

/* ---- 2. Empty blob ------------------------------------------------------- */
TEST(Blob, EmptyRoundTrip) {
    sync_engine *e = cluster::make(2);
    const std::string ns = "photos.blobs";

    uint8_t id[32];
    std::vector<uint8_t> empty;
    ASSERT_EQ(put(e, ns, empty, id), SYNC_OK);

    uint64_t size = 999;
    int complete = 0;
    ASSERT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete), SYNC_OK);
    EXPECT_EQ(size, 0u);
    EXPECT_EQ(complete, 1);

    std::vector<uint8_t> back;
    ASSERT_EQ(get(e, ns, id, back), SYNC_OK);
    EXPECT_TRUE(back.empty());

    /* data may be NULL only when len==0; NULL+0 must still be accepted. */
    uint8_t id_nulldata[32];
    EXPECT_EQ(sync_blob_put(e, B(ns), ns.size(), nullptr, 0, id_nulldata), SYNC_OK);
    EXPECT_EQ(0, std::memcmp(id, id_nulldata, 32));

    sync_engine_destroy(e);
}

/* ---- 3. Idempotent re-put; two different blobs coexist ------------------ */
TEST(Blob, IdempotentAndCoexist) {
    sync_engine *e = cluster::make(3);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> a = make_data(5000, 11);
    std::vector<uint8_t> b = make_data(5000, 22);
    ASSERT_NE(a, b);

    uint8_t id_a1[32], id_a2[32], id_b[32];
    ASSERT_EQ(put(e, ns, a, id_a1), SYNC_OK);
    ASSERT_EQ(put(e, ns, a, id_a2), SYNC_OK); /* re-put: harmless */
    ASSERT_EQ(put(e, ns, b, id_b), SYNC_OK);

    EXPECT_EQ(0, std::memcmp(id_a1, id_a2, 32));
    EXPECT_NE(0, std::memcmp(id_a1, id_b, 32));

    std::vector<uint8_t> back_a, back_b;
    ASSERT_EQ(get(e, ns, id_a1, back_a), SYNC_OK);
    ASSERT_EQ(get(e, ns, id_b, back_b), SYNC_OK);
    EXPECT_EQ(a, back_a);
    EXPECT_EQ(b, back_b);

    sync_engine_destroy(e);
}

/* ---- 4. Partial replication ---------------------------------------------- */
TEST(Blob, PartialReplicationIncompleteThenComplete) {
    sync_engine *a = cluster::make(4);
    sync_engine *bE = cluster::make(5);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(SYNC_BLOB_CHUNK_MAX * 3 + 123, 42);
    uint8_t id[32];
    ASSERT_EQ(put(a, ns, data, id), SYNC_OK);

    sync_change *recs = nullptr;
    size_t n = 0;
    ASSERT_SYNC_OK(sync_engine_export(a, &recs, &n));

    std::string mkey = manifest_entity(id);
    for (size_t i = 0; i < n; i++) {
        if (entity_is(recs[i], mkey)) {
            ASSERT_SYNC_OK(sync_engine_apply(bE, &recs[i]));
        }
    }

    uint64_t size = 0;
    int complete = 1;
    ASSERT_EQ(sync_blob_stat(bE, B(ns), ns.size(), id, &size, &complete), SYNC_OK);
    EXPECT_EQ(size, data.size());
    EXPECT_EQ(complete, 0);

    std::vector<uint8_t> back;
    EXPECT_EQ(get(bE, ns, id, back), SYNC_ERR_NOTFOUND);

    /* Apply the remaining (chunk) records. */
    for (size_t i = 0; i < n; i++) {
        if (!entity_is(recs[i], mkey)) {
            ASSERT_SYNC_OK(sync_engine_apply(bE, &recs[i]));
        }
    }
    sync_changes_free(recs, n);

    ASSERT_EQ(sync_blob_stat(bE, B(ns), ns.size(), id, &size, &complete), SYNC_OK);
    EXPECT_EQ(complete, 1);
    ASSERT_EQ(get(bE, ns, id, back), SYNC_OK);
    EXPECT_EQ(back, data);

    sync_engine_destroy(a);
    sync_engine_destroy(bE);
}

/* ---- 5. Corruption: tampered chunk payload ------------------------------- */
TEST(Blob, CorruptChunkDetected) {
    sync_engine *e = cluster::make(6);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(SYNC_BLOB_CHUNK_MAX + 500, 77);
    uint8_t id[32];
    ASSERT_EQ(put(e, ns, data, id), SYNC_OK);

    /* Recompute chunk 0's hash the same way blob.cpp does, then overwrite its
     * "d" field with wrong bytes of the same length (so manifest length/size
     * checks still pass; only the hash disagrees). */
    uint8_t chash[32];
    ke::blake2b(data.data(), SYNC_BLOB_CHUNK_MAX, chash, 32);
    std::string centity = chunk_entity(chash);
    std::vector<uint8_t> wrong(SYNC_BLOB_CHUNK_MAX, 0xAB);
    ASSERT_SYNC_OK(sync_engine_set(e, B(ns), ns.size(),
                                   (const uint8_t *)centity.data(), centity.size(),
                                   B(std::string("d")), 1, wrong.data(),
                                   wrong.size()));

    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);

    sync_engine_destroy(e);
}

/* ---- 5b. Corruption: chunk payload length disagrees with the manifest ----
 *
 * These pin the `clen == expect` half of blob.cpp's per-chunk check
 * independently of the hash comparison. Each plants a chunk whose stored
 * payload is *honestly* hashed (so the hash half of the check would pass on
 * its own) but whose manifest declares a size that disagrees with the
 * payload actually on disk -- exactly the shape that, if the length check is
 * dropped, drives a memcpy of `clen` bytes into a buffer sized for
 * `expect`. */
TEST(Blob, ChunkLongerThanDeclaredLengthDetected) {
    sync_engine *e = cluster::make(13);
    const std::string ns = "photos.blobs";

    /* A real, honestly-hashed 4000-byte chunk payload. */
    std::vector<uint8_t> payload = make_data(4000, 801);
    uint8_t chash[32];
    ke::blake2b(payload.data(), payload.size(), chash, 32);
    std::string centity = chunk_entity(chash);
    ASSERT_SYNC_OK(sync_engine_set(e, B(ns), ns.size(),
                                   (const uint8_t *)centity.data(),
                                   centity.size(), B(std::string("d")), 1,
                                   payload.data(), payload.size()));

    /* Manifest for an arbitrary id: references this chunk's genuinely
     * correct hash, but declares a total_size of only 500 bytes -- the
     * actual stored payload (4000 bytes) is longer than what the manifest
     * says a single-chunk blob of this size should contain. */
    uint8_t id[32];
    for (int i = 0; i < 32; i++) id[i] = (uint8_t)(0xC0 + i);
    std::string m;
    m.push_back((char)1);
    ke::put_u64le(m, 500);
    ke::put_u32le(m, 1);
    m.append((const char *)chash, 32);
    write_manifest_for(e, ns, id, m);

    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);

    sync_engine_destroy(e);
}

TEST(Blob, ChunkZeroLengthWhenNonzeroDeclaredDetected) {
    sync_engine *e = cluster::make(14);
    const std::string ns = "photos.blobs";

    /* A real, honestly-hashed EMPTY chunk payload. */
    uint8_t chash[32];
    ke::blake2b(nullptr, 0, chash, 32);
    std::string centity = chunk_entity(chash);
    ASSERT_SYNC_OK(sync_engine_set(e, B(ns), ns.size(),
                                   (const uint8_t *)centity.data(),
                                   centity.size(), B(std::string("d")), 1,
                                   nullptr, 0));

    /* Manifest claims a 500-byte single chunk but points at the empty
     * chunk's (genuinely correct) hash: stored payload (0 bytes) is shorter
     * than declared. */
    uint8_t id[32];
    for (int i = 0; i < 32; i++) id[i] = (uint8_t)(0xD0 + i);
    std::string m;
    m.push_back((char)1);
    ke::put_u64le(m, 500);
    ke::put_u32le(m, 1);
    m.append((const char *)chash, 32);
    write_manifest_for(e, ns, id, m);

    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);

    sync_engine_destroy(e);
}

/* ---- 6. Malformed manifests (attack surface) ----------------------------- */
class BlobMalformedManifest : public ::testing::Test {
protected:
    sync_engine *e = nullptr;
    std::string ns = "photos.blobs";
    uint8_t id[32];

    void SetUp() override {
        e = cluster::make(7);
        std::vector<uint8_t> data = make_data(10, 1);
        ASSERT_EQ(put(e, ns, data, id), SYNC_OK);
    }
    void TearDown() override { sync_engine_destroy(e); }

    void write_manifest(const std::string &bytes) {
        std::string ment = manifest_entity(id);
        ASSERT_SYNC_OK(sync_engine_set(
            e, B(ns), ns.size(), (const uint8_t *)ment.data(), ment.size(),
            B(std::string("m")), 1, (const uint8_t *)bytes.data(), bytes.size()));
    }
};

TEST_F(BlobMalformedManifest, Truncated) {
    /* Byte 0 must be a VALID version (0x01): if it isn't, parse_manifest
     * rejects on the version check (blob.cpp:65) before ever reaching the
     * header-length bounds check this test exists to pin, so a truncated
     * manifest whose first byte happens to be zero (an invalid version)
     * would exercise the wrong guard. With a valid version byte, control
     * reaches read_u64le/read_u32le past the end of a too-short buffer
     * unless the `mlen < kManifestHeaderLen` guard (blob.cpp:64) stops it
     * first -- exactly the heap over-read this guard exists to prevent. */
    for (size_t len : {(size_t)1, (size_t)12}) { /* both < 13-byte header */
        std::string m(len, '\0');
        m[0] = (char)1;
        write_manifest(m);
        std::vector<uint8_t> back;
        EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT) << "len=" << len;
        uint64_t size; int complete;
        EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete),
                 SYNC_ERR_CORRUPT) << "len=" << len;
    }
}

TEST_F(BlobMalformedManifest, TruncatedHashArray) {
    /* Header alone (13 bytes, >= kManifestHeaderLen so the header-length
     * guard at blob.cpp:64 does NOT fire) declaring chunk_count=1 but
     * carrying zero bytes of hash data: the hash array is entirely absent.
     * Only the `mlen != expected_len` guard (blob.cpp:73) stops
     * parse_manifest from handing back an out-of-bounds `hashes` pointer
     * that get/stat/delete would then read 32 bytes past the end of. */
    {
        std::string m;
        m.push_back((char)1);
        ke::put_u64le(m, 32768);
        ke::put_u32le(m, 1);
        ASSERT_EQ(m.size(), kManifestHeaderLen);
        write_manifest(m);
        std::vector<uint8_t> back;
        EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);
        uint64_t size; int complete;
        EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete),
                 SYNC_ERR_CORRUPT);
    }
    /* Scaled up: chunk_count=1000 with the hash array entirely absent (0
     * bytes) and with only 1 byte present -- a 32000-byte (resp.
     * 31999-byte) would-be over-read if the length-consistency guard were
     * gone, versus the 32-byte over-read above. */
    for (size_t hash_bytes : {(size_t)0, (size_t)1}) {
        constexpr uint32_t kCount = 1000;
        std::string m;
        m.push_back((char)1);
        ke::put_u64le(m, (uint64_t)kCount * SYNC_BLOB_CHUNK_MAX);
        ke::put_u32le(m, kCount);
        m.append(hash_bytes, '\0');
        write_manifest(m);
        std::vector<uint8_t> back;
        EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT)
            << "hash_bytes=" << hash_bytes;
        uint64_t size; int complete;
        EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete),
                 SYNC_ERR_CORRUPT) << "hash_bytes=" << hash_bytes;
    }
}

TEST_F(BlobMalformedManifest, WrongVersion) {
    std::string m;
    m.push_back((char)9); /* bogus version */
    ke::put_u64le(m, 10);
    ke::put_u32le(m, 1);
    m.append(32, '\0');
    write_manifest(m);
    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);
}

TEST_F(BlobMalformedManifest, ChunkCountTooLarge) {
    /* A manifest whose LENGTH IS CONSISTENT with an over-limit chunk_count
     * (kMaxChunks == 1000): chunk_count = 1001, exactly 1001*32 bytes of
     * hashes, and a total_size that satisfies the count/size consistency
     * check too. This is the case that actually reaches and exercises the
     * `chunk_count > kMaxChunks` guard (blob.cpp:69) -- a manifest merely
     * *claiming* a huge count while being byte-short (as in a naive test)
     * is instead rejected earlier by the length-consistency check
     * (blob.cpp:73), leaving the count guard itself unverified. */
    constexpr uint32_t kOverLimitCount = 1001;
    std::string m;
    m.push_back((char)1);
    ke::put_u64le(m, (uint64_t)kOverLimitCount * SYNC_BLOB_CHUNK_MAX);
    ke::put_u32le(m, kOverLimitCount);
    m.append((size_t)kOverLimitCount * 32, '\0'); /* content irrelevant */
    write_manifest(m);
    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);
    uint64_t size; int complete;
    EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete),
             SYNC_ERR_CORRUPT);
}

TEST_F(BlobMalformedManifest, SizeCountInconsistent) {
    /* chunk_count=1 implies total_size in (0, CHUNK_MAX]; claim a size that
     * would require 2 chunks. */
    std::string m;
    m.push_back((char)1);
    ke::put_u64le(m, (uint64_t)SYNC_BLOB_CHUNK_MAX + 1);
    ke::put_u32le(m, 1);
    uint8_t h[32] = {0};
    m.append((const char *)h, 32);
    write_manifest(m);
    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);
}

TEST_F(BlobMalformedManifest, ZeroChunksNonzeroSize) {
    /* Pins the `total_size != 0` guard for chunk_count==0 (blob.cpp:76).
     * Without it, get()'s SYNC_OK vs SYNC_ERR_CORRUPT outcome depends on an
     * uninitialized malloc(5) happening to mismatch `id` -- invisible to
     * ASan and not a real assertion of the guard's job. stat() and delete()
     * don't touch that uninitialized buffer at all, so they're the ones that
     * actually demonstrate a forged zero-chunk manifest being silently
     * accepted as complete (spec test #6: "get and stat return
     * SYNC_ERR_CORRUPT"). */
    std::string m;
    m.push_back((char)1);
    ke::put_u64le(m, 5); /* nonzero size but zero chunks */
    ke::put_u32le(m, 0);
    write_manifest(m);
    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);
    uint64_t size; int complete;
    EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete),
             SYNC_ERR_CORRUPT);
    EXPECT_EQ(sync_blob_delete(e, B(ns), ns.size(), id), SYNC_ERR_CORRUPT);
}

TEST_F(BlobMalformedManifest, ZeroChunksHugeSizeNoAllocation) {
    /* count=0 with an astronomically large total_size (2^40): the guard's
     * real job is refusing to let an unvalidated manifest field size an
     * allocation. Without it, sync_blob_get would malloc(2^40) at
     * blob.cpp:198 -- a huge-allocation abort under ASan and a real DoS
     * vector from a peer-supplied manifest in production. */
    std::string m;
    m.push_back((char)1);
    ke::put_u64le(m, (uint64_t)1 << 40);
    ke::put_u32le(m, 0);
    write_manifest(m);
    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);
    uint64_t size; int complete;
    EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, &size, &complete),
             SYNC_ERR_CORRUPT);
    EXPECT_EQ(sync_blob_delete(e, B(ns), ns.size(), id), SYNC_ERR_CORRUPT);
}

TEST_F(BlobMalformedManifest, DeleteRefusesOnCorrupt) {
    std::string m(5, '\0');
    write_manifest(m);
    EXPECT_EQ(sync_blob_delete(e, B(ns), ns.size(), id), SYNC_ERR_CORRUPT);
}

/* ---- 6b. Whole-blob hash guard: content-addressing is not just per-chunk -
 *
 * Every check below is one where each individual chunk referenced by the
 * manifest genuinely exists, has the right length, and hashes to exactly
 * what the manifest claims -- so ALL per-chunk verification passes. Only the
 * final assembled-buffer hash (blob.cpp:245, `id == BLAKE2b(whole blob)`)
 * can catch the forgery. These pin that guard, which is the spec's central
 * "never return unverified bytes" promise. */

TEST(Blob, ChunkSubstitutionAcrossBlobsDetected) {
    sync_engine *e = cluster::make(15);
    const std::string ns = "photos.blobs";

    /* Two distinct, same-length, multi-chunk blobs: their manifests have
     * identical chunk_count/total_size, but every chunk hash differs. */
    size_t sz = SYNC_BLOB_CHUNK_MAX * 2 + 100; /* 3 chunks */
    std::vector<uint8_t> da = make_data(sz, 501);
    std::vector<uint8_t> db = make_data(sz, 502);
    ASSERT_NE(da, db);
    uint8_t id_a[32], id_b[32];
    ASSERT_EQ(put(e, ns, da, id_a), SYNC_OK);
    ASSERT_EQ(put(e, ns, db, id_b), SYNC_OK);

    std::string manifest_a, manifest_b;
    ASSERT_EQ(read_raw_manifest(e, ns, id_a, manifest_a), SYNC_OK);
    ASSERT_EQ(read_raw_manifest(e, ns, id_b, manifest_b), SYNC_OK);
    ASSERT_EQ(manifest_a.size(), manifest_b.size());

    /* Splice: A's manifest, but chunk slot 1 replaced with B's chunk 1
     * hash. Chunk index 1 is not the last chunk in either blob, so it's a
     * full SYNC_BLOB_CHUNK_MAX chunk in both -- lengths still line up, only
     * the referenced content differs. Every per-chunk check therefore
     * passes: B's chunk 1 genuinely exists with exactly that hash and
     * length. */
    std::string spliced = manifest_a;
    size_t off = kManifestHeaderLen + 1 * SYNC_BLOB_ID_LEN;
    spliced.replace(off, SYNC_BLOB_ID_LEN, manifest_b, off, SYNC_BLOB_ID_LEN);
    ASSERT_NE(spliced, manifest_a);

    write_manifest_for(e, ns, id_a, spliced);

    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id_a, back), SYNC_ERR_CORRUPT);

    sync_engine_destroy(e);
}

TEST(Blob, ChunkReorderingDetected) {
    sync_engine *e = cluster::make(16);
    const std::string ns = "photos.blobs";

    /* 3 chunks; the first two are both full-length, so swapping their
     * manifest slots keeps every per-chunk length check consistent while
     * changing the assembled content (and therefore the whole-blob hash). */
    size_t sz = SYNC_BLOB_CHUNK_MAX * 2 + 100;
    std::vector<uint8_t> data = make_data(sz, 601);
    uint8_t id[32];
    ASSERT_EQ(put(e, ns, data, id), SYNC_OK);

    std::string manifest;
    ASSERT_EQ(read_raw_manifest(e, ns, id, manifest), SYNC_OK);

    std::string reordered = manifest;
    for (size_t i = 0; i < SYNC_BLOB_ID_LEN; i++)
        std::swap(reordered[kManifestHeaderLen + i],
                 reordered[kManifestHeaderLen + SYNC_BLOB_ID_LEN + i]);
    ASSERT_NE(reordered, manifest);

    write_manifest_for(e, ns, id, reordered);

    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);

    sync_engine_destroy(e);
}

TEST(Blob, ManifestUnderWrongIdDetected) {
    sync_engine *e = cluster::make(17);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(SYNC_BLOB_CHUNK_MAX + 500, 701);
    uint8_t id[32];
    ASSERT_EQ(put(e, ns, data, id), SYNC_OK);

    std::string manifest;
    ASSERT_EQ(read_raw_manifest(e, ns, id, manifest), SYNC_OK);

    /* Plant A's genuine, unmodified manifest under an unrelated id. Every
     * chunk it references genuinely exists with the right hash and length
     * (they're A's real chunks), so per-chunk verification is a no-op here;
     * only the outer whole-blob-hash-vs-id check can catch that this
     * content was never meant to live under `wrong_id`. */
    uint8_t wrong_id[32];
    for (int i = 0; i < 32; i++) wrong_id[i] = (uint8_t)(0xE0 + i);
    ASSERT_NE(0, std::memcmp(wrong_id, id, 32));

    write_manifest_for(e, ns, wrong_id, manifest);

    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, wrong_id, back), SYNC_ERR_CORRUPT);

    sync_engine_destroy(e);
}

/* ---- 7. Delete cascade ---------------------------------------------------- */
TEST(Blob, DeleteRemovesManifestAndChunks) {
    sync_engine *e = cluster::make(8);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(SYNC_BLOB_CHUNK_MAX * 2 + 10, 99);
    uint8_t id[32];
    ASSERT_EQ(put(e, ns, data, id), SYNC_OK);

    sync_scan_entry *entries = nullptr;
    size_t count = 0;
    ASSERT_SYNC_OK(sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0,
                                    &entries, &count));
    EXPECT_GT(count, 0u); /* manifest + >=1 chunk entities */
    sync_scan_free(entries, count);

    ASSERT_EQ(sync_blob_delete(e, B(ns), ns.size(), id), SYNC_OK);

    entries = nullptr; count = 0;
    ASSERT_SYNC_OK(sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0,
                                    &entries, &count));
    EXPECT_EQ(count, 0u);
    sync_scan_free(entries, count);

    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_NOTFOUND);

    /* Deleting again (nothing left) is a clean not-found, not a crash. */
    EXPECT_EQ(sync_blob_delete(e, B(ns), ns.size(), id), SYNC_ERR_NOTFOUND);

    sync_engine_destroy(e);
}

/* ---- Per-chunk hash verification (not subsumed by the whole-blob check) -- */
/* A manifest whose slot-0 hash is bogus, paired with the GENUINE chunk-0
 * payload stored under the bogus name, assembles to the original content —
 * the whole-blob hash still matches the blob id, so only the per-chunk
 * re-hash can catch the lie. Pins blob.cpp's per-chunk verification. */
TEST(Blob, ChunkHashMismatchDetectedEvenWhenWholeBlobMatches) {
    sync_engine *e = cluster::make(18);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(2 * SYNC_BLOB_CHUNK_MAX + 100, 91);
    uint8_t id[32];
    ASSERT_EQ(put(e, ns, data, id), SYNC_OK);

    std::string m;
    ASSERT_EQ(read_raw_manifest(e, ns, id, m), SYNC_OK);
    ASSERT_GE(m.size(), kManifestHeaderLen + 32);

    /* Store the genuine chunk-0 payload under a bogus chunk name... */
    uint8_t bogus[32];
    std::memset(bogus, 0x5A, sizeof bogus);
    std::string centity = chunk_entity(bogus);
    ASSERT_SYNC_OK(sync_engine_set(e, B(ns), ns.size(),
                                   (const uint8_t *)centity.data(),
                                   centity.size(), B(std::string("d")), 1,
                                   data.data(), SYNC_BLOB_CHUNK_MAX));

    /* ...and point the manifest's slot 0 at that name. */
    m.replace(kManifestHeaderLen, 32, (const char *)bogus, 32);
    write_manifest_for(e, ns, id, m);

    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, id, back), SYNC_ERR_CORRUPT);

    sync_engine_destroy(e);
}

/* ---- 8. Convergence ------------------------------------------------------- */
TEST(Blob, ConvergesAcrossFullExportApply) {
    sync_engine *a = cluster::make(9);
    sync_engine *bE = cluster::make(10);
    const std::string ns = "photos.blobs";

    std::vector<uint8_t> data = make_data(SYNC_BLOB_CHUNK_MAX * 5 + 777, 5);
    uint8_t id[32];
    ASSERT_EQ(put(a, ns, data, id), SYNC_OK);

    cluster::replicate(a, bE);

    std::vector<uint8_t> back;
    ASSERT_EQ(get(bE, ns, id, back), SYNC_OK);
    EXPECT_EQ(back, data);

    EXPECT_EQ(cluster::digest(a), cluster::digest(bE));

    sync_engine_destroy(a);
    sync_engine_destroy(bE);
}

/* ---- 9. Over-limit blob rejected, nothing written ------------------------ */
TEST(Blob, OverLimitRejectedNoWrites) {
    sync_engine *e = cluster::make(11);
    const std::string ns = "photos.blobs";

    size_t too_big = (size_t)SYNC_BLOB_CHUNK_MAX * 1001; /* > 1000 chunks */
    std::vector<uint8_t> data(too_big, 0x42);
    uint8_t id[32];
    EXPECT_EQ(put(e, ns, data, id), SYNC_ERR_INVALID);

    sync_scan_entry *entries = nullptr;
    size_t count = 0;
    ASSERT_SYNC_OK(sync_engine_scan(e, B(ns), ns.size(), nullptr, 0, 0,
                                    &entries, &count));
    EXPECT_EQ(count, 0u) << "over-limit put must not write anything";
    sync_scan_free(entries, count);

    sync_engine_destroy(e);
}

/* ---- Invalid-argument rejection ------------------------------------------ */
TEST(Blob, InvalidArgs) {
    sync_engine *e = cluster::make(12);
    const std::string ns = "photos.blobs";
    uint8_t id[32] = {0};

    EXPECT_EQ(sync_blob_put(nullptr, B(ns), ns.size(), B(std::string("x")), 1, id),
             SYNC_ERR_INVALID);
    EXPECT_EQ(sync_blob_put(e, B(ns), ns.size(), nullptr, 1, id), SYNC_ERR_INVALID)
        << "data NULL with nonzero len must be rejected";
    EXPECT_EQ(sync_blob_put(e, B(ns), ns.size(), B(std::string("x")), 1, nullptr),
             SYNC_ERR_INVALID);

    uint8_t *out = nullptr; size_t out_len = 0;
    EXPECT_EQ(sync_blob_get(nullptr, B(ns), ns.size(), id, &out, &out_len),
             SYNC_ERR_INVALID);
    EXPECT_EQ(sync_blob_get(e, B(ns), ns.size(), nullptr, &out, &out_len),
             SYNC_ERR_INVALID);
    EXPECT_EQ(sync_blob_get(e, B(ns), ns.size(), id, nullptr, &out_len),
             SYNC_ERR_INVALID);

    uint64_t size; int complete;
    EXPECT_EQ(sync_blob_stat(nullptr, B(ns), ns.size(), id, &size, &complete),
             SYNC_ERR_INVALID);
    EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), id, nullptr, &complete),
             SYNC_ERR_INVALID);

    EXPECT_EQ(sync_blob_delete(nullptr, B(ns), ns.size(), id), SYNC_ERR_INVALID);
    EXPECT_EQ(sync_blob_delete(e, B(ns), ns.size(), nullptr), SYNC_ERR_INVALID);

    /* Unknown id: clean not-found, not a crash. */
    uint8_t unknown[32] = {0xFF};
    std::vector<uint8_t> back;
    EXPECT_EQ(get(e, ns, unknown, back), SYNC_ERR_NOTFOUND);
    EXPECT_EQ(sync_blob_stat(e, B(ns), ns.size(), unknown, &size, &complete),
             SYNC_ERR_NOTFOUND);
    EXPECT_EQ(sync_blob_delete(e, B(ns), ns.size(), unknown), SYNC_ERR_NOTFOUND);

    sync_engine_destroy(e);
}
