/* blob.cpp — content-addressed large-value storage (Blob extension).
 *
 * A pure layer over the engine's public C ABI (sync_engine_set/get/delete/
 * exists) — it never touches engine.hpp state directly, only the same
 * primitives any external caller has. Internal hashing uses ke::blake2b
 * (src/crypto.h) since this file compiles into libsync_engine.
 *
 * Entity key layout inside the caller's namespace (see include/sync_engine.h
 * for the full picture):
 *   Chunk entity:    'c' 0x00 + 32-byte raw chunk hash;  field "d" = payload.
 *   Manifest entity: 'b' 0x00 + 32-byte raw blob id;     field "m" = manifest.
 *
 * Manifest field wire form: [u8 version=1][u64le total_size][u32le
 * chunk_count][chunk_count * 32-byte chunk hashes]. Manifests arrive from
 * peers, so sync_blob_get/stat/delete parse this defensively: every count
 * and length is bounds-checked before it is used to size a read or an
 * allocation. */
#include "sync_engine.h"

#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "byteorder.h"
#include "crypto.h"

using namespace ke;

namespace {

constexpr uint32_t kMaxChunks = 1000; /* => max blob ~31.25 MiB */
constexpr uint8_t kManifestVersion = 1;
constexpr size_t kManifestHeaderLen = 1 + 8 + 4; /* version + size + count */

/* 34-byte entity key: tag, 0x00, 32-byte hash/id. */
struct EntityKey {
    uint8_t bytes[2 + SYNC_BLOB_ID_LEN];
};

EntityKey make_key(char tag, const uint8_t id[SYNC_BLOB_ID_LEN]) {
    EntityKey k;
    k.bytes[0] = (uint8_t)tag;
    k.bytes[1] = 0x00;
    std::memcpy(k.bytes + 2, id, SYNC_BLOB_ID_LEN);
    return k;
}

const uint8_t kFieldData[1] = {'d'};
const uint8_t kFieldManifest[1] = {'m'};

/* Parsed, validated manifest. hashes points at chunk_count*32 bytes inside
 * the caller-owned manifest buffer (borrowed; do not outlive it). */
struct Manifest {
    uint64_t total_size = 0;
    uint32_t chunk_count = 0;
    const uint8_t *hashes = nullptr;
};

/* Defensively parse a manifest field value. Every field is bounds-checked
 * against the untrusted bytes before use; a malformed manifest never causes
 * an over-read or a huge allocation based on an unvalidated count. */
sync_error parse_manifest(const uint8_t *m, size_t mlen, Manifest &out) {
    if (mlen < kManifestHeaderLen) return SYNC_ERR_CORRUPT;
    if (m[0] != kManifestVersion) return SYNC_ERR_CORRUPT;

    uint64_t total_size = read_u64le(m + 1);
    uint32_t chunk_count = read_u32le(m + 9);
    if (chunk_count > kMaxChunks) return SYNC_ERR_CORRUPT;

    size_t expected_len =
        kManifestHeaderLen + (size_t)chunk_count * SYNC_BLOB_ID_LEN;
    if (mlen != expected_len) return SYNC_ERR_CORRUPT;

    if (chunk_count == 0) {
        if (total_size != 0) return SYNC_ERR_CORRUPT;
    } else {
        /* Every chunk but the last is exactly CHUNK_MAX bytes; the last is
         * 1..CHUNK_MAX bytes. Equivalent to
         * ceil(total_size / CHUNK_MAX) == chunk_count. */
        uint64_t full = (uint64_t)(chunk_count - 1) * SYNC_BLOB_CHUNK_MAX;
        if (total_size <= full || total_size > full + SYNC_BLOB_CHUNK_MAX)
            return SYNC_ERR_CORRUPT;
    }

    out.total_size = total_size;
    out.chunk_count = chunk_count;
    out.hashes = m + kManifestHeaderLen;
    return SYNC_OK;
}

/* BatchGuard — RAII over the engine-global write batch, driven through the
 * public sync_engine_batch_* ABI only (preserving this file's pure-layer
 * rule). Constructed immediately before a multi-record mutation sequence —
 * never before the read-only validation that precedes one, so an early
 * NOTFOUND/CORRUPT return cannot touch (or poison) a caller's batch.
 * commit() closes the guard on the success path; the destructor aborts on
 * any other exit, discarding the sequence's staged, un-flushed tail rather
 * than committing a half-written blob.
 *
 * ENGINE-GLOBAL SCOPE (spec §3.3 point 7): the batch belongs to the engine,
 * not to this guard. Nested inside an embedder's own open batch, commit()
 * merely closes one level — durability then arrives only at the embedder's
 * outermost commit (the header documents this at the three blob write
 * functions) — and an abort here POISONS the embedder's whole outer batch,
 * discarding the un-flushed tail of everything it staged. That is the
 * documented hard contract: never hold a batch open across calls into code
 * you do not control. For in-memory engines every sync_engine_batch_* call
 * is a clean no-op, so the guard is one too — it only ever changes behavior
 * on store-backed engines. */
class BatchGuard {
public:
    explicit BatchGuard(sync_engine *e)
        : e_(e), armed_(sync_engine_batch_begin(e) == SYNC_OK) {}
    BatchGuard(const BatchGuard &) = delete;
    BatchGuard &operator=(const BatchGuard &) = delete;
    ~BatchGuard() {
        if (armed_) sync_engine_batch_abort(e_);
    }
    /* Success path: commit this nesting level. SYNC_OK inside an enclosing
     * embedder batch means staged, not yet durable (see above). */
    sync_error commit() {
        if (!armed_) return SYNC_OK;
        armed_ = false;
        return (sync_error)sync_engine_batch_commit(e_);
    }

private:
    sync_engine *e_;
    bool armed_;
};

/* Expected payload length of chunk index i (0-based) under a validated
 * manifest. */
size_t chunk_len_at(const Manifest &mf, uint32_t i) {
    if (i + 1 < mf.chunk_count) return SYNC_BLOB_CHUNK_MAX;
    uint64_t full = (uint64_t)(mf.chunk_count - 1) * SYNC_BLOB_CHUNK_MAX;
    return (size_t)(mf.total_size - full);
}

/* Read and parse the manifest for `id`. SYNC_ERR_NOTFOUND if absent,
 * SYNC_ERR_CORRUPT if present but malformed. On SYNC_OK, *raw owns the
 * manifest field bytes (release with sync_free once done with mf.hashes). */
sync_error load_manifest(sync_engine *e, const uint8_t *ns, size_t ns_len,
                         const uint8_t id[SYNC_BLOB_ID_LEN], Manifest &mf,
                         uint8_t **raw, size_t *raw_len) {
    EntityKey mkey = make_key('b', id);
    int rc = sync_engine_get(e, ns, ns_len, mkey.bytes, sizeof mkey.bytes,
                             kFieldManifest, sizeof kFieldManifest, raw,
                             raw_len);
    if (rc != SYNC_OK) return (sync_error)rc;
    sync_error perr = parse_manifest(*raw, *raw_len, mf);
    if (perr != SYNC_OK) {
        sync_free(*raw);
        *raw = nullptr;
        *raw_len = 0;
        return perr;
    }
    return SYNC_OK;
}

} // namespace

extern "C" {

sync_error sync_blob_put(sync_engine *e, const uint8_t *ns, size_t ns_len,
                         const uint8_t *data, size_t len,
                         uint8_t out_id[SYNC_BLOB_ID_LEN]) {
    if (!e || !out_id || (!ns && ns_len) || (!data && len))
        return SYNC_ERR_INVALID;
    try {
        /* Bound len before any arithmetic on it, so a huge len can't overflow
         * the chunk-count computation below. */
        if ((uint64_t)len > (uint64_t)kMaxChunks * SYNC_BLOB_CHUNK_MAX)
            return SYNC_ERR_INVALID;
        uint32_t chunk_count =
            len == 0 ? 0
                     : (uint32_t)((len + SYNC_BLOB_CHUNK_MAX - 1) /
                                  SYNC_BLOB_CHUNK_MAX);

        uint8_t blob_id[SYNC_BLOB_ID_LEN];
        blake2b(data, len, blob_id, SYNC_BLOB_ID_LEN);

        std::string manifest;
        manifest.reserve(kManifestHeaderLen +
                         (size_t)chunk_count * SYNC_BLOB_ID_LEN);
        manifest.push_back((char)kManifestVersion);
        put_u64le(manifest, (uint64_t)len);
        put_u32le(manifest, chunk_count);

        /* One batch for the whole put: N chunk records + the manifest land
         * in O(1) bounded, clock-covered frames instead of one fsync per
         * record. The guard aborts (discarding the staged tail) on any early
         * return below. */
        BatchGuard batch(e);

        for (uint32_t i = 0; i < chunk_count; i++) {
            size_t off = (size_t)i * SYNC_BLOB_CHUNK_MAX;
            size_t clen = off + SYNC_BLOB_CHUNK_MAX <= len
                             ? (size_t)SYNC_BLOB_CHUNK_MAX
                             : len - off;
            uint8_t chash[SYNC_BLOB_ID_LEN];
            blake2b(data + off, clen, chash, SYNC_BLOB_ID_LEN);
            manifest.append((const char *)chash, SYNC_BLOB_ID_LEN);

            EntityKey ckey = make_key('c', chash);
            int rc = sync_engine_set(e, ns, ns_len, ckey.bytes,
                                     sizeof ckey.bytes, kFieldData,
                                     sizeof kFieldData, data + off, clen);
            if (rc != SYNC_OK) return (sync_error)rc;
        }

        EntityKey mkey = make_key('b', blob_id);
        int rc = sync_engine_set(e, ns, ns_len, mkey.bytes, sizeof mkey.bytes,
                                 kFieldManifest, sizeof kFieldManifest,
                                 (const uint8_t *)manifest.data(),
                                 manifest.size());
        if (rc != SYNC_OK) return (sync_error)rc;

        sync_error brc = batch.commit();
        if (brc != SYNC_OK) return brc;

        std::memcpy(out_id, blob_id, SYNC_BLOB_ID_LEN);
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

sync_error sync_blob_get(sync_engine *e, const uint8_t *ns, size_t ns_len,
                         const uint8_t id[SYNC_BLOB_ID_LEN],
                         uint8_t **out, size_t *out_len) {
    if (!e || !id || !out || !out_len || (!ns && ns_len))
        return SYNC_ERR_INVALID;
    *out = nullptr;
    *out_len = 0;
    try {
        Manifest mf;
        uint8_t *raw = nullptr;
        size_t raw_len = 0;
        sync_error err = load_manifest(e, ns, ns_len, id, mf, &raw, &raw_len);
        if (err != SYNC_OK) return err;

        /* Non-NULL even when empty, mirroring sync_engine_get's convention so
         * callers can distinguish a successful empty blob from not-found. */
        uint8_t *buf = static_cast<uint8_t *>(
            std::malloc(mf.total_size == 0 ? 1 : (size_t)mf.total_size));
        if (!buf) {
            sync_free(raw);
            return SYNC_ERR_NOMEM;
        }

        for (uint32_t i = 0; i < mf.chunk_count; i++) {
            const uint8_t *chash = mf.hashes + (size_t)i * SYNC_BLOB_ID_LEN;
            EntityKey ckey = make_key('c', chash);
            uint8_t *cval = nullptr;
            size_t clen = 0;
            int rc = sync_engine_get(e, ns, ns_len, ckey.bytes,
                                     sizeof ckey.bytes, kFieldData,
                                     sizeof kFieldData, &cval, &clen);
            if (rc == SYNC_ERR_NOTFOUND) {
                /* Manifest replicated, chunk hasn't (yet): eventual-
                 * consistency answer, distinguishable via sync_blob_stat. */
                std::free(buf);
                sync_free(raw);
                return SYNC_ERR_NOTFOUND;
            }
            if (rc != SYNC_OK) {
                std::free(buf);
                sync_free(raw);
                return (sync_error)rc;
            }

            size_t expect = chunk_len_at(mf, i);
            uint8_t got_hash[SYNC_BLOB_ID_LEN];
            blake2b(cval, clen, got_hash, SYNC_BLOB_ID_LEN);
            bool ok = clen == expect &&
                     std::memcmp(got_hash, chash, SYNC_BLOB_ID_LEN) == 0;
            if (ok) {
                std::memcpy(buf + (size_t)i * SYNC_BLOB_CHUNK_MAX, cval, clen);
            }
            sync_free(cval);
            if (!ok) {
                std::free(buf);
                sync_free(raw);
                return SYNC_ERR_CORRUPT;
            }
        }

        uint8_t got_id[SYNC_BLOB_ID_LEN];
        blake2b(buf, mf.total_size, got_id, SYNC_BLOB_ID_LEN);
        sync_free(raw);
        if (std::memcmp(got_id, id, SYNC_BLOB_ID_LEN) != 0) {
            std::free(buf);
            return SYNC_ERR_CORRUPT;
        }

        *out = buf;
        *out_len = (size_t)mf.total_size;
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

sync_error sync_blob_stat(sync_engine *e, const uint8_t *ns, size_t ns_len,
                          const uint8_t id[SYNC_BLOB_ID_LEN],
                          uint64_t *out_size, int *out_complete) {
    if (!e || !id || !out_size || !out_complete || (!ns && ns_len))
        return SYNC_ERR_INVALID;
    try {
        Manifest mf;
        uint8_t *raw = nullptr;
        size_t raw_len = 0;
        sync_error err = load_manifest(e, ns, ns_len, id, mf, &raw, &raw_len);
        if (err != SYNC_OK) return err;

        int complete = 1;
        for (uint32_t i = 0; i < mf.chunk_count; i++) {
            const uint8_t *chash = mf.hashes + (size_t)i * SYNC_BLOB_ID_LEN;
            EntityKey ckey = make_key('c', chash);
            int exists = 0;
            int rc = sync_engine_exists(e, ns, ns_len, ckey.bytes,
                                        sizeof ckey.bytes, &exists);
            if (rc != SYNC_OK) {
                sync_free(raw);
                return (sync_error)rc;
            }
            if (!exists) { complete = 0; break; }
        }

        *out_size = mf.total_size;
        *out_complete = complete;
        sync_free(raw);
        return SYNC_OK;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

sync_error sync_blob_delete(sync_engine *e, const uint8_t *ns, size_t ns_len,
                            const uint8_t id[SYNC_BLOB_ID_LEN]) {
    if (!e || !id || (!ns && ns_len)) return SYNC_ERR_INVALID;
    try {
        Manifest mf;
        uint8_t *raw = nullptr;
        size_t raw_len = 0;
        sync_error err = load_manifest(e, ns, ns_len, id, mf, &raw, &raw_len);
        if (err != SYNC_OK) return err; /* NOTFOUND or CORRUPT: nothing deleted */

        /* One batch for the N chunk tombstones + the manifest tombstone
         * (constructed only after validation, so the NOTFOUND/CORRUPT paths
         * above never touch a caller's batch); aborted on any early return. */
        BatchGuard batch(e);

        for (uint32_t i = 0; i < mf.chunk_count; i++) {
            const uint8_t *chash = mf.hashes + (size_t)i * SYNC_BLOB_ID_LEN;
            EntityKey ckey = make_key('c', chash);
            int rc = sync_engine_delete(e, ns, ns_len, ckey.bytes,
                                        sizeof ckey.bytes);
            if (rc != SYNC_OK) {
                sync_free(raw);
                return (sync_error)rc;
            }
        }
        sync_free(raw);

        EntityKey mkey = make_key('b', id);
        int rc = sync_engine_delete(e, ns, ns_len, mkey.bytes, sizeof mkey.bytes);
        if (rc != SYNC_OK) return (sync_error)rc;
        return batch.commit();
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

sync_error sync_blob_erase(sync_engine *e, const uint8_t *ns, size_t ns_len,
                           const uint8_t id[SYNC_BLOB_ID_LEN]) {
    if (!e || !id || (!ns && ns_len)) return SYNC_ERR_INVALID;
    try {
        Manifest mf;
        uint8_t *raw = nullptr;
        size_t raw_len = 0;
        sync_error err = load_manifest(e, ns, ns_len, id, mf, &raw, &raw_len);
        if (err == SYNC_ERR_CORRUPT) {
            /* The chunk list is unusable, so the payload cannot be zeroed —
             * but the manifest entity itself is present (its field was just
             * read). Tombstone what exists rather than leave a corrupt blob
             * visible; CORRUPT tells the caller chunk payloads may survive
             * until tombstone GC. */
            EntityKey mkey = make_key('b', id);
            int rc = sync_engine_delete(e, ns, ns_len, mkey.bytes,
                                        sizeof mkey.bytes);
            return rc == SYNC_OK ? SYNC_ERR_CORRUPT : (sync_error)rc;
        }
        if (err != SYNC_OK) return err; /* NOTFOUND: nothing left to reach */

        /* One batch for the zero-overwrites + tombstones (constructed after
         * the validation/CORRUPT paths above, so they never touch a caller's
         * batch; aborted on any early return). Staging preserves append
         * order AMONG STAGED RECORDS and sub-frames fsync in append order,
         * so the zero-before-tombstone durable-prefix property below
         * survives batching — load() stops at the first bad frame. (The one
         * writes that jump the staging queue are capability/revocation
         * frames, excluded from batching by §3.3 point 5; this sequence
         * emits only records, so the durable-prefix argument is unaffected —
         * and even an interleaved cap frame would be harmless, since load()
         * merges records only after the whole replay.) */
        BatchGuard batch(e);

        /* Zero every locally present chunk's payload BEFORE any tombstone
         * lands — a set on a tombstoned entity would resurrect it. Absent
         * chunks are skipped for the same reason (a set would create them);
         * peers holding them erase when these records replicate. */
        for (uint32_t i = 0; i < mf.chunk_count; i++) {
            const uint8_t *chash = mf.hashes + (size_t)i * SYNC_BLOB_ID_LEN;
            EntityKey ckey = make_key('c', chash);
            int exists = 0;
            int rc = sync_engine_exists(e, ns, ns_len, ckey.bytes,
                                        sizeof ckey.bytes, &exists);
            if (rc == SYNC_OK && exists)
                rc = sync_engine_set(e, ns, ns_len, ckey.bytes,
                                     sizeof ckey.bytes, kFieldData,
                                     sizeof kFieldData, nullptr, 0);
            if (rc != SYNC_OK) {
                sync_free(raw);
                return (sync_error)rc;
            }
        }

        /* Then tombstone chunks and manifest, exactly as sync_blob_delete. */
        for (uint32_t i = 0; i < mf.chunk_count; i++) {
            const uint8_t *chash = mf.hashes + (size_t)i * SYNC_BLOB_ID_LEN;
            EntityKey ckey = make_key('c', chash);
            int rc = sync_engine_delete(e, ns, ns_len, ckey.bytes,
                                        sizeof ckey.bytes);
            if (rc != SYNC_OK) {
                sync_free(raw);
                return (sync_error)rc;
            }
        }
        sync_free(raw);

        EntityKey mkey = make_key('b', id);
        int rc = sync_engine_delete(e, ns, ns_len, mkey.bytes, sizeof mkey.bytes);
        if (rc != SYNC_OK) return (sync_error)rc;
        return batch.commit();
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

} // extern "C"
