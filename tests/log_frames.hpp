/* log_frames.hpp — shared frame-boundary walker for the on-disk append-only
 * log, plus a thin read/reset helper over the storage layer's debug/test fsync
 * counter (ke::storage_fsync_count, src/storage.h). Used by the Phase-3 batch
 * tests; written generically so the Phase-4 structural compaction tests can
 * reuse it. Header-only, synctest namespace, tempdir.hpp conventions.
 *
 * On-disk layouts walked (authoritative source: src/storage.cpp):
 *   plaintext  "KOMELOG1"(8)                      then per frame:
 *              [body_len:u32le][body:body_len][sha8(body)]
 *   encrypted  "KOMEENC1"(8) keycheck_ct(16) keycheck_mac(16)   then per frame:
 *              [body_len:u32le][nonce:24][ciphertext:body_len][mac:16]
 *
 * The walk mirrors Storage::load()'s acceptance rules: it stops at a zero
 * length, at a frame that does not physically fit in the remaining bytes,
 * and — plaintext only — at the first checksum mismatch (encrypted frames
 * need the key to authenticate, so for them the walk is structural only:
 * length-driven, tag not verified). Bytes past the last accepted frame are
 * reported as `trailing`, exactly the torn tail load() would ignore. */
#ifndef SYNC_TEST_LOG_FRAMES_HPP
#define SYNC_TEST_LOG_FRAMES_HPP

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>

#include "sha256.h"  /* plaintext frames end in sha8(body) */
#include "storage.h" /* ke::storage_fsync_count() */

namespace synctest {

struct LogFrame {
    size_t offset;      /* file offset of the frame's 4-byte length prefix   */
    size_t size;        /* total on-disk frame size, framing included        */
    size_t body_offset; /* plaintext: offset of body; encrypted: ciphertext  */
    uint32_t body_len;  /* declared body length (plaintext bytes both ways)  */
};

struct LogWalk {
    bool ok = false;        /* header recognized (magic matched)             */
    bool encrypted = false; /* KOMEENC1 layout                               */
    size_t header_size = 0; /* 8 plaintext, 8+16+16 encrypted                */
    std::vector<LogFrame> frames;
    size_t end = 0;      /* offset just past the last accepted frame         */
    size_t trailing = 0; /* bytes past `end` (torn/garbage tail); 0 = clean  */
};

inline LogWalk walk_frames(const std::string &raw) {
    LogWalk w;
    if (raw.size() < 8) return w;
    if (raw.compare(0, 8, "KOMELOG1") == 0) {
        w.encrypted = false;
        w.header_size = 8;
    } else if (raw.compare(0, 8, "KOMEENC1") == 0) {
        w.encrypted = true;
        w.header_size = 8 + 16 + 16; /* magic + key-check ct + mac */
    } else {
        return w;
    }
    if (raw.size() < w.header_size) return w;
    w.ok = true;

    size_t off = w.header_size;
    const size_t pre = w.encrypted ? 24u : 0u;  /* nonce before the body   */
    const size_t post = w.encrypted ? 16u : 8u; /* mac16, or sha8 trailer  */
    for (;;) {
        if (off + 4 > raw.size()) break;
        const uint8_t *p = (const uint8_t *)raw.data() + off;
        uint32_t body_len = (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
                            ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
        if (body_len == 0) break; /* load() stops here too */
        size_t frame = 4 + pre + (size_t)body_len + post;
        if (off + frame > raw.size()) break; /* torn trailing frame */
        if (!w.encrypted) {
            /* Reject what load() would reject: a checksum-mismatched frame is
             * a torn/corrupt tail, not a frame. */
            uint8_t digest[32];
            sync_engine_detail::sha256(raw.data() + off + 4, body_len, digest);
            if (std::memcmp(digest, raw.data() + off + 4 + body_len, 8) != 0)
                break;
        }
        LogFrame f;
        f.offset = off;
        f.size = frame;
        f.body_offset = off + 4 + pre;
        f.body_len = body_len;
        w.frames.push_back(f);
        off += frame;
    }
    w.end = off;
    w.trailing = raw.size() - off;
    return w;
}

/* Whole file as bytes ("" if unreadable — walk_frames then reports !ok). */
inline std::string slurp_file(const std::string &path) {
    std::FILE *f = std::fopen(path.c_str(), "rb");
    if (!f) return std::string();
    std::string b;
    char tmp[4096];
    size_t n;
    while ((n = std::fread(tmp, 1, sizeof tmp, f)) > 0) b.append(tmp, n);
    std::fclose(f);
    return b;
}

inline LogWalk walk_log_file(const std::string &path) {
    return walk_frames(slurp_file(path));
}

/* Entry count of a frame's body ([entry_count:u32le][entry*]) — PLAINTEXT
 * logs only (an encrypted body is ciphertext at rest). */
inline uint32_t frame_entry_count(const std::string &raw, const LogFrame &f) {
    if (f.body_len < 4 || f.body_offset + 4 > raw.size()) return 0;
    const uint8_t *p = (const uint8_t *)raw.data() + f.body_offset;
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
           ((uint32_t)p[3] << 24);
}

/* Nonce of an ENCRYPTED frame (24 bytes right after the length prefix); ""
 * for a plaintext walk. */
inline std::string frame_nonce(const std::string &raw, const LogWalk &w,
                               const LogFrame &f) {
    if (!w.encrypted || f.offset + 4 + 24 > raw.size()) return std::string();
    return raw.substr(f.offset + 4, 24);
}

/* ---- fsync accounting (see the counter's contract in src/storage.h) ----- *
 * Counts write_frame's per-frame fsync and rewrite_log_streamed's two fsyncs (temp
 * file + best-effort directory), nothing else. Process-global (and atomic —
 * independent engines on independent threads share it): reset before the
 * operation under test. */
inline uint64_t fsync_count() {
    return ke::storage_fsync_count().load(std::memory_order_relaxed);
}
inline uint64_t fsync_reset() {
    return ke::storage_fsync_count().exchange(0, std::memory_order_relaxed);
}

} // namespace synctest

#endif /* SYNC_TEST_LOG_FRAMES_HPP */
