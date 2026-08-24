/* storage.cpp — append-only log persistence (replaces the SQLite layer).
 *
 * On-disk format
 * --------------
 *   file   = HEADER  frame*
 *   HEADER = "KOMELOG1"(8)                              (plaintext), or
 *            "KOMEENC1"(8) keycheck_ct(16) keycheck_mac(16)  (encrypted at rest)
 *   frame  = plaintext : body_len:u32le  body(body_len)  sha8(body)
 *            encrypted : body_len:u32le  nonce(24)  ciphertext(body_len)  mac(16)
 *   body   = entry_count:u32le  entry*
 *   entry  = type:u8  payload
 *     META(1)   : key:bytes  value:bytes
 *     ENTITY(2) : ns:bytes ent:bytes  present:u8  hlc_physical:u64le
 *                 hlc_logical:u32le  ex_author[32] ex_sig[64]
 *     FIELD(3)  : ns:bytes ent:bytes field:bytes value:bytes
 *                 hlc_physical:u64le hlc_logical:u32le  author[32] sig[64]
 *     CAP(4)    : blob:bytes
 *   bytes  = varint(len) raw
 *
 * When opened with a key (sync_engine_open_encrypted), every frame is sealed
 * with XChaCha20-Poly1305 — the AEAD tag both authenticates and detects torn
 * writes (replacing the SHA checksum). A header key-check rejects a wrong key
 * up front so it can't be mistaken for corruption and truncate the log.
 *
 * A frame is one mutation (or a standalone put_*), written and fsync'd as a
 * unit. A crash mid-append leaves at most a torn trailing frame; load() detects
 * it (short read or checksum mismatch), truncates the file to the last good
 * frame, and continues. Replay merges each record by the same LWW / existence
 * rule the engine uses, so it is order-independent and idempotent: a duplicated
 * or partially-written tail can never corrupt state. Signatures are re-verified
 * on load (an on-disk row is not trusted just because it is on disk).
 *
 * Growth is bounded by compaction (rewrite the log as one record per live cell);
 * see compact() — invoked from open() when the log is much larger than its live
 * state. */
#include "storage.h"

#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cassert> /* the Debug-only streamed-size exactness check (§3.4) */
#include <cstring>
#include <vector>
#ifndef __EMSCRIPTEN__
#include <thread> /* parallel signature re-verification on load (native only) */
#endif

#include "byteorder.h"
#include "capability.h"
#include "codec.h"
#include "crypto.h"
#include "sha256.h"

namespace ke {

namespace {

constexpr char kMagic[8] = {'K', 'O', 'M', 'E', 'L', 'O', 'G', '1'};    /* plaintext */
constexpr char kMagicEnc[8] = {'K', 'O', 'M', 'E', 'E', 'N', 'C', '1'}; /* sealed */

/* Fixed plaintext sealed into the encrypted header so a wrong key fails the open
 * cleanly (rather than being mistaken for a torn frame and truncating data). */
constexpr uint8_t kKeyCheck[16] = {'K', 'O', 'M', 'E', 'k', 'e', 'y', 'c',
                                   'h', 'e', 'c', 'k', '0', '0', '0', '1'};

enum EntryType : uint8_t {
    kMeta = 1, kEntity = 2, kField = 3, kCap = 4, kRev = 5
};

/* Persisted records are re-verified on load — a crafted/swapped file must not
 * inject forged records that bypass the signature gate the network path
 * enforces. The verification itself is inlined in verify_and_merge (below) so it
 * can run in parallel across all collected records.
 *
 * (hlc, author) order on presence assertions: same total order apply() uses. */
int existence_cmp(const Hlc &hlc_a, const PubKey &au_a, const Hlc &hlc_b,
                  const PubKey &au_b) {
    if (int c = hlc_cmp(hlc_a, hlc_b)) return c;
    return std::memcmp(au_a.data(), au_b.data(), SYNC_PUBKEY_LEN);
}

void put_bytes(std::string &out, const std::string &s) {
    put_varint(out, s.size());
    out.append(s);
}
void put_raw(std::string &out, const uint8_t *p, size_t n) {
    out.append(reinterpret_cast<const char *>(p), n);
}

bool get_blob(const uint8_t *&p, const uint8_t *end, std::string &out) {
    uint64_t len = 0;
    if (!get_varint(p, end, len)) return false;
    if ((uint64_t)(end - p) < len) return false;
    out.assign(reinterpret_cast<const char *>(p), (size_t)len);
    p += len;
    return true;
}
bool get_raw(const uint8_t *&p, const uint8_t *end, uint8_t *out, size_t n) {
    if ((size_t)(end - p) < n) return false;
    std::memcpy(out, p, n);
    p += n;
    return true;
}

/* Read exactly n bytes at the current offset; false on short read / error. */
bool read_exact(int fd, void *buf, size_t n) {
    uint8_t *p = (uint8_t *)buf;
    size_t got = 0;
    while (got < n) {
        ssize_t r = ::read(fd, p + got, n - got);
        if (r <= 0) return false;
        got += (size_t)r;
    }
    return true;
}

bool write_all(int fd, const void *buf, size_t n) {
    const uint8_t *p = (const uint8_t *)buf;
    size_t put = 0;
    while (put < n) {
        ssize_t w = ::write(fd, p + put, n - put);
        if (w <= 0) return false;
        put += (size_t)w;
    }
    return true;
}

/* ---- streaming compaction plumbing (§3.4) ------------------------------ */

/* FrameSink buffer size: the compaction stream's only long-lived allocation.
 * Its capacity is pinned here for the whole run (see FrameSink::append). */
constexpr size_t kCompactBufSize = 256u * 1024;

/* Exact encoded length of one varint, mirroring put_varint (codec.cpp): one
 * byte per 7 bits, minimal form. Named frame_varint_len / frame_field_len —
 * NOT `blen` — because the amalgamated (unity) build concatenates this TU
 * with noise.cpp, whose locals named `blen` (noise.cpp decrypt paths) would
 * collide; -Wshadow is absent from the flag set, so the collision would be a
 * silent latent trap rather than a build error (§3.4 amendment 6). */
size_t frame_varint_len(uint64_t v) {
    size_t n = 1;
    while (v >= 0x80) {
        v >>= 7;
        n++;
    }
    return n;
}
/* On-disk size of one length-prefixed byte string (put_bytes): varint + raw. */
size_t frame_field_len(size_t n) { return frame_varint_len(n) + n; }

/* Exact wire-blob sizes for capability / revocation entries. These MUST
 * mirror cap_encode / rev_encode (capability.cpp) byte for byte:
 *   cap = version(1) issuer(32) subject(32) varint(ns)+ns access(1)
 *         expiry(8) sig(64)
 *   rev = version(1) revoker(32) subject(32) varint(ns)+ns issued_ms(8)
 *         sig(64)
 * The Debug assert in rewrite_log_streamed cross-checks this arithmetic
 * against the real encoders' output on every Debug compaction. */
size_t cap_blob_size(const Capability &c) {
    return 1 + 2 * SYNC_PUBKEY_LEN + frame_field_len(c.ns.size()) + 1 + 8 +
           SYNC_SIG_LEN;
}
size_t rev_blob_size(const Revocation &r) {
    return 1 + 2 * SYNC_PUBKEY_LEN + frame_field_len(r.ns.size()) + 8 +
           SYNC_SIG_LEN;
}

/* RAII guard for the compaction temp file `<path>.tmp`, with EXPLICIT
 * ownership transitions so no path can double-close a descriptor (§3.4
 * amendment 3): close_fd() closes and sets fd = -1, so the destructor's close
 * branch is dead afterwards; disarm() (legal only once the fd is manually
 * closed) releases the unlink duty once the rename has consumed the path.
 * The destructor handles every early-return/throw: close a still-open fd,
 * unlink a still-armed path — never both acting on a live descriptor after a
 * manual close. Double-close matters here because this process spawns threads
 * (load()'s verification pool, transport/connection.cpp): a second ::close on
 * a reused descriptor number silently reaps another thread's fd, invisible to
 * ASan/TSan. */
struct TmpFile {
    std::string path;
    int fd = -1;
    bool armed = false; /* unlink path in the destructor (cleanup on failure) */
    ~TmpFile() {
        if (fd >= 0) ::close(fd);
        if (armed) ::unlink(path.c_str());
    }
    void close_fd() {
        if (fd >= 0) {
            ::close(fd);
            fd = -1;
        }
    }
    void disarm() {
        assert(fd == -1); /* close_fd() first; never abandon a live fd */
        armed = false;
    }
};

/* Buffered sequential writer for the streamed compaction. append() is
 * PRE-checked (§3.4 amendment 1): it returns immediately when !ok; it flushes
 * FIRST when the incoming bytes would push buf past kCompactBufSize; and it
 * writes anything >= kCompactBufSize straight through, bypassing the buffer —
 * so buf's capacity is pinned at exactly kCompactBufSize for the whole run
 * (a threshold checked only after copying would let one oversized frame grow
 * the buffer geometrically, and std::string never shrinks on clear()).
 * ok latches false on the first write error and every subsequent append/flush
 * is a no-op; the caller also checks ok in its entity-loop condition so a
 * mid-stream ENOSPC/EIO aborts the stream instead of continuing to build,
 * seal, and buffer every remaining frame (§3.4 amendment 2). */
struct FrameSink {
    int fd;
    std::string buf;
    uint64_t total = 0; /* bytes successfully accepted (buffered or written) */
    bool ok = true;
    explicit FrameSink(int f) : fd(f) { buf.reserve(kCompactBufSize); }
    void flush() {
        if (!ok || buf.empty()) return;
        if (!write_all(fd, buf.data(), buf.size())) ok = false;
        buf.clear(); /* keeps capacity — pinned at kCompactBufSize */
    }
    void append(const char *p, size_t n) {
        if (!ok) return;
        if (buf.size() + n > kCompactBufSize) flush();
        if (!ok) return;
        if (n >= kCompactBufSize) {
            if (!write_all(fd, p, n)) ok = false;
        } else {
            buf.append(p, n);
        }
        if (ok) total += n;
    }
    void append(const std::string &s) { append(s.data(), s.size()); }
};

/* ---- entry + frame builders (shared by append and compaction) ---------- */

std::string build_meta(const std::string &key, const uint8_t *data, size_t len) {
    std::string e;
    e.push_back((char)kMeta);
    put_bytes(e, key);
    put_bytes(e, std::string(reinterpret_cast<const char *>(data), len));
    return e;
}
std::string build_meta_u64(const std::string &key, uint64_t v) {
    uint8_t b[8];
    store_u64le(b, v);
    return build_meta(key, b, sizeof b);
}
std::string build_entity(const std::string &ns, const std::string &ent,
                         bool present, const Hlc &hlc, const PubKey &au,
                         const Sig &sg) {
    std::string e;
    e.push_back((char)kEntity);
    put_bytes(e, ns);
    put_bytes(e, ent);
    e.push_back((char)(present ? 1 : 0));
    put_u64le(e, hlc.physical);
    put_u32le(e, hlc.logical);
    put_raw(e, au.data(), au.size());
    put_raw(e, sg.data(), sg.size());
    return e;
}
std::string build_field(const std::string &ns, const std::string &ent,
                        const std::string &field, const Register &r) {
    std::string e;
    e.push_back((char)kField);
    put_bytes(e, ns);
    put_bytes(e, ent);
    put_bytes(e, field);
    put_bytes(e, r.value);
    put_u64le(e, r.hlc.physical);
    put_u32le(e, r.hlc.logical);
    put_raw(e, r.author.data(), r.author.size());
    put_raw(e, r.sig.data(), r.sig.size());
    return e;
}
std::string build_cap(const std::string &blob) {
    std::string e;
    e.push_back((char)kCap);
    put_bytes(e, blob);
    return e;
}
std::string build_rev(const std::string &blob) {
    std::string e;
    e.push_back((char)kRev);
    put_bytes(e, blob);
    return e;
}

/* Wrap an assembled body ([count][entries]) into a plaintext on-disk frame:
 * [len:u32le][full][sha8]. */
std::string make_frame_full(const std::string &full) {
    uint8_t digest[32];
    sync_engine_detail::sha256(full.data(), full.size(), digest);
    std::string framed;
    put_u32le(framed, (uint32_t)full.size());
    framed += full;
    framed.append(reinterpret_cast<const char *>(digest), 8);
    return framed;
}

} // namespace

/* See storage.h: debug/test-only fsync accounting. Function-local static so
 * there is exactly one definition (unity-build-safe, no init-order hazard);
 * std::atomic because the counter is process-global while engines are only
 * per-instance single-threaded — two independent durable engines on two
 * threads (a supported, TSan-clean configuration) increment it concurrently.
 * Relaxed ordering: it is a statistic, not a synchronization point. */
std::atomic<uint64_t> &storage_fsync_count() {
    static std::atomic<uint64_t> count{0};
    return count;
}

Storage::~Storage() {
    if (fd_ >= 0) ::close(fd_);
    secure_wipe(seed_, sizeof seed_);
    secure_wipe(key_, sizeof key_);
}

Storage *Storage::open(const char *path, sync_error *err, const uint8_t *key) {
    if (err) *err = SYNC_OK;
    if (!path) {
        if (err) *err = SYNC_ERR_INVALID;
        return nullptr;
    }
    Storage *s = new (std::nothrow) Storage();
    if (!s) {
        if (err) *err = SYNC_ERR_NOMEM;
        return nullptr;
    }
    s->path_ = path;
    if (key) {
        s->encrypted_ = true;
        std::memcpy(s->key_, key, 32);
    }

    /* The log holds this node's private identity seed; make it owner-only,
     * best-effort (FS-level protection is the embedder's job). */
    int fd = ::open(path, O_RDWR | O_CREAT, S_IRUSR | S_IWUSR);
    if (fd < 0) {
        if (err) *err = SYNC_ERR_INTERNAL;
        delete s;
        return nullptr;
    }
    s->fd_ = fd;
    ::fchmod(fd, S_IRUSR | S_IWUSR);

    off_t size = ::lseek(fd, 0, SEEK_END);
    if (size == 0) {
        /* Fresh file: write the header (magic [+ key-check]) and fsync. */
        std::string hdr = s->header_bytes();
        if (!write_all(fd, hdr.data(), hdr.size()) || ::fsync(fd) != 0) {
            if (err) *err = SYNC_ERR_INTERNAL;
            delete s;
            return nullptr;
        }
        s->file_size_ = hdr.size();
    } else {
        const char *want = s->encrypted_ ? kMagicEnc : kMagic;
        char magic[8];
        ::lseek(fd, 0, SEEK_SET);
        if (!read_exact(fd, magic, sizeof magic) ||
            std::memcmp(magic, want, sizeof magic) != 0) {
            /* Wrong format / mode mismatch (plaintext-vs-encrypted, or a SQLite
             * db). */
            if (err) *err = SYNC_ERR_INVALID;
            delete s;
            return nullptr;
        }
        if (s->encrypted_) {
            /* Verify the key against the header key-check before reading any
             * frame, so a wrong key fails the open instead of truncating data. */
            uint8_t ct[16], mac[16], pt[16], nonce[24] = {0};
            if (!read_exact(fd, ct, sizeof ct) ||
                !read_exact(fd, mac, sizeof mac) ||
                !aead_decrypt(s->key_, nonce, nullptr, 0, ct, sizeof ct, mac, pt) ||
                std::memcmp(pt, kKeyCheck, sizeof kKeyCheck) != 0) {
                if (err) *err = SYNC_ERR_INVALID; /* wrong key / corrupt header */
                delete s;
                return nullptr;
            }
        }
        s->file_size_ = (uint64_t)size;
    }
    return s;
}

/* Wrap a body+count into one on-disk frame. Plaintext: [plen][full][sha8].
 * Encrypted: [plen][nonce:24][ciphertext:plen][mac:16] — the AEAD tag both
 * authenticates and detects torn writes, replacing the SHA checksum. */
std::string Storage::seal_frame(const std::string &body, uint32_t count) const {
    std::string full;
    put_u32le(full, count);
    full += body;
    /* The frame length is a u32le prefix and 0 is RESERVED in it: load()'s
     * replay loop reads `body_len == 0` as a clean end of log, the same break
     * as real EOF. `full.size()` is a size_t, so a narrowing cast does not
     * merely mis-frame an oversized body -- at an exact 4 GiB multiple it MINTS
     * that terminator, and every frame after it (on the compaction path, the
     * whole capability and revocation set, which put_revocation fsyncs
     * synchronously precisely so it cannot be dropped) is silently discarded on
     * the next open, with load() still returning SYNC_OK. Off-multiple sizes
     * fare no better: the wrong prefix fails the digest/AEAD check and replay
     * stops there just the same.
     *
     * Refuse instead of truncating. An empty return is this function's existing
     * hard-failure signal (write_frame's `if (framed.empty()) return false;`
     * and add_frame's `sink.ok = false`, both used for the F2 RNG failure), so
     * the caller surfaces SYNC_ERR_INTERNAL or aborts the compaction with the
     * old log intact -- never a lying SYNC_OK over bytes that vanish on reopen.
     *
     * NOTE: an entity whose records exceed this in one frame becomes
     * uncompactable (rewrite_log_streamed packs one entity plus all its fields
     * into a single frame). That is fail-closed and stuck rather than silent
     * loss; splitting the per-entity compaction frame is the follow-up. */
    if (frame_body_too_large((uint64_t)full.size())) return std::string();
    if (!encrypted_) return make_frame_full(full);

    uint8_t nonce[24];
    /* Fail closed on RNG failure: random_bytes wipes the buffer to all-zeros on a
     * short read, which would reuse a zero nonce under key_ (catastrophic for
     * XChaCha20-Poly1305, and colliding with the fixed-nonce header key-check that
     * seals a known constant). Return "" so the caller aborts the write (F2). */
    if (!random_bytes(nonce, sizeof nonce)) return std::string();
    std::string ct(full.size(), '\0');
    uint8_t mac[16];
    aead_encrypt(key_, nonce, nullptr, 0, (const uint8_t *)full.data(),
                 full.size(), (uint8_t *)ct.data(), mac);
    std::string framed;
    put_u32le(framed, (uint32_t)full.size());
    framed.append((const char *)nonce, sizeof nonce);
    framed += ct;
    framed.append((const char *)mac, sizeof mac);
    return framed;
}

/* File header: the magic, plus (encrypted) a key-check block = a fixed plaintext
 * sealed under the key so the wrong key is detected up front. */
std::string Storage::header_bytes() const {
    std::string h(kMagic, sizeof kMagic);
    if (!encrypted_) return h;
    h.assign(kMagicEnc, sizeof kMagicEnc);
    uint8_t nonce[24] = {0}; /* fixed nonce; frames use random ones */
    uint8_t ct[16], mac[16];
    aead_encrypt(key_, nonce, nullptr, 0, kKeyCheck, sizeof kKeyCheck, ct, mac);
    h.append((const char *)ct, sizeof ct);
    h.append((const char *)mac, sizeof mac);
    return h;
}

bool Storage::write_frame(const std::string &body, uint32_t entry_count) {
    std::string framed = seal_frame(body, entry_count);
    if (framed.empty()) return false; /* seal failed (RNG); never write a bad frame (F2) */
    if (tail_torn_) {
        /* First write since load stopped short of the physical end: drop the
         * torn tail now so this frame lands where replay stopped (load capped
         * file_size_ there). Deferred from load — see the comment there. */
        if (::ftruncate(fd_, (off_t)file_size_) != 0) return false;
        ::fsync(fd_);
        tail_torn_ = false;
    }
    if (::lseek(fd_, 0, SEEK_END) < 0) return false;
    if (!write_all(fd_, framed.data(), framed.size())) {
        /* A short/failed write leaves partial frame bytes on disk PAST
         * file_size_ — garbage in what is now the middle of the append
         * stream. Left there, the next append would land after it: replay
         * stops at the first bad frame, so every later "successful" write
         * would silently vanish on reopen. Mark the tail torn so the next
         * write_frame first truncates back to file_size_ (the last good
         * frame) — the same deferred-cleanup mechanism load() uses; a crash
         * before that next write is equally safe, since load() rejects the
         * partial frame as a torn tail. */
        tail_torn_ = true;
        return false;
    }
    int rc = ::fsync(fd_);
    storage_fsync_count().fetch_add(1, std::memory_order_relaxed);
    if (rc != 0) {
        /* fsync failed: the frame's durability is unknown and the kernel may
         * have dropped the dirty pages. The caller was told this write
         * failed, so the log must not keep a frame the caller will retry or
         * re-derive — treat it exactly like a short write and truncate it
         * away before the next append. */
        tail_torn_ = true;
        return false;
    }
    file_size_ += framed.size();
    return true;
}

bool Storage::emit(const std::string &entry) {
    if (in_tx_) {
        /* A poisoned batch's tail is GUARANTEED to be discarded at the
         * outermost close — never stage into one. Without this refusal every
         * post-poison mutation would keep appending records that
         * batch_maybe_flush (which bails out on poison before its size
         * check) will never flush, growing staging_ without bound — the
         * exact unbounded RAM transient the mandatory-flush amendment
         * exists to prevent (spec §3.3). batch_failed_ is only ever set
         * while a batch is open, so the plain begin()/commit() path is
         * unaffected. */
        if (batch_failed_) return false;
        staging_ += entry;
        staged_count_++;
        return true;
    }
    return write_frame(entry, 1);
}

bool Storage::begin() {
    in_tx_ = true;
    staging_.clear();
    staged_count_ = 0;
    return true;
}

bool Storage::commit() {
    in_tx_ = false;
    if (staged_count_ == 0) return true;
    bool ok = write_frame(staging_, staged_count_);
    staging_.clear();
    staged_count_ = 0;
    return ok;
}

bool Storage::rollback() {
    in_tx_ = false;
    staging_.clear();
    staged_count_ = 0;
    return true;
}

/* Nesting-safe batches — see the contract in storage.h. Only the 0->1 begin
 * opens the transaction; inner begins just join it.
 *
 * The depth is CAPPED rather than left to wrap. 0 is the reserved "no batch
 * open" sentinel (in_batch(), batch_commit, batch_abort, batch_maybe_flush and
 * batch_poison all read it), so an unbounded uint32 increment mints that
 * sentinel while in_tx_ is still set and staging_ still holds the batch's
 * records: the tx_* helpers then take their non-batch branch into begin(),
 * which clears staging_ and silently drops records the caller was told were
 * staged, and maybe_compact's `if (in_tx_) return;` no longer blocks the
 * mid-batch compaction storage.h forbids by design. Runaway nesting is API
 * misuse either way; failing closed turns it into a clean SYNC_ERR_INTERNAL at
 * the ABI instead of silent data loss. */
bool Storage::batch_begin() {
    if (batch_depth_ > 0) {
        if (batch_depth_ >= kMaxBatchDepth) return false; /* refuse, never wrap */
        batch_depth_++;
        return true;
    }
    if (!begin()) return false;
    batch_depth_ = 1;
    batch_failed_ = false;
    return true;
}

/* The three clock-meta entries every batch (sub-)frame must carry, so replay
 * never sees a durable record whose HLC exceeds the persisted clock. */
bool Storage::stamp_clock_meta(sync_engine *e) {
    return put_meta_u64("hlc_physical", e->clock.physical) &&
           put_meta_u64("hlc_logical", e->clock.logical) &&
           put_meta_u64("db_clock", e->db_clock);
}

bool Storage::batch_commit(sync_engine *e) {
    if (batch_depth_ == 0) return false; /* unbalanced commit */
    if (batch_depth_ > 1) {
        /* Inner commit: bookkeeping only — writes nothing, fsyncs nothing.
         * Durability arrives only at the outermost commit. Report poison so
         * a nested holder can learn its mutations are condemned. */
        batch_depth_--;
        return !batch_failed_;
    }
    batch_depth_ = 0;
    if (batch_failed_) {
        /* Poisoned (a nested abort or an in-batch write failure): discard
         * the un-flushed staged tail. Sub-frames already force-flushed are
         * durable and stay — a batch is a durability boundary, not a
         * rollback mechanism. */
        batch_failed_ = false;
        rollback();
        std::string().swap(staging_); /* release the batch's capacity */
        return false;
    }
    bool ok = false;
    try {
        /* Cover the tail sub-frame with the clock meta, then one fsync'd
         * frame (crash-prefix invariant, as in batch_maybe_flush). */
        ok = stamp_clock_meta(e) && commit();
    } catch (...) {
        rollback();
        std::string().swap(staging_);
        throw; /* callers map bad_alloc etc. at the ABI boundary */
    }
    if (!ok) rollback(); /* stamp failed with the tx still open: close it */
    std::string().swap(staging_); /* release the batch's staging capacity
                                   * (clear() would retain it — a permanent
                                   * kBatchFlushBytes floor per engine) */
    if (!ok) return false;
    maybe_compact(e);
    return true;
}

/* See storage.h: poison = fail-fast flag + immediate drop of the condemned
 * staged tail (bytes and capacity), so a poisoned batch holds no staging for
 * the rest of its lifetime and emit() cannot grow it back. */
void Storage::batch_poison() {
    if (batch_depth_ == 0) return;
    batch_failed_ = true;
    std::string().swap(staging_);
    staged_count_ = 0;
}

bool Storage::batch_abort() {
    if (batch_depth_ == 0) return false; /* unbalanced abort */
    /* Engine-global poison: an abort at ANY depth condemns the whole
     * outermost batch — depth cannot distinguish holders, so the un-flushed
     * tail of every enclosing caller is dropped right here (batch_poison)
     * and the outermost batch_commit reports failure. */
    batch_poison();
    if (--batch_depth_ == 0) {
        batch_failed_ = false;
        rollback(); /* close the tx (staging already dropped by the poison) */
    }
    return true;
}

bool Storage::batch_maybe_flush(sync_engine *e) {
    if (batch_depth_ == 0) return true; /* not in a batch: nothing to bound */
    if (batch_failed_) return false;    /* poisoned: fail the write path now
                                         * (emit() already refused to stage,
                                         * so there is nothing here to bound
                                         * — staging was dropped at poison
                                         * time and stays empty) */
    if (staging_.size() < kBatchFlushBytes) return true;
    /* Force a sub-frame: stamp the three clock-meta entries first so ANY
     * durable frame with records also carries a covering clock (a crash
     * between sub-frames must not persist records whose HLC exceeds the
     * persisted clock meta), then write + fsync. The transaction stays open
     * for the batch's remaining records; staging keeps its capacity until
     * the outermost commit/abort releases it. */
    bool ok = false;
    try {
        ok = stamp_clock_meta(e) && write_frame(staging_, staged_count_);
    } catch (...) {
        batch_poison(); /* drops the staged tail too — see storage.h */
        throw;
    }
    staging_.clear(); /* flushed: keep capacity for the batch's next fill */
    staged_count_ = 0;
    if (!ok) batch_poison(); /* releases the retained capacity as well */
    return ok;
}

bool Storage::put_meta_u64(const char *key, uint64_t v) {
    return emit(build_meta_u64(key, v));
}

bool Storage::put_meta_blob(const char *key, const uint8_t *data, size_t len) {
    return emit(build_meta(key, data, len));
}

/* Capability writes are EXCLUDED from batch staging (spec §3.3 point 5), so
 * they bypass emit() and always write their own immediately-fsync'd frame,
 * in_batch() or not. Security rationale: sync_engine_grant/sync_engine_revoke
 * return SYNC_OK only once the grant/revocation is durable, and a revocation
 * in particular must never sit in a staging buffer where a later batch_abort
 * could discard it — that would silently undo a "remove a stolen device"
 * cut-off the caller was told succeeded. Grant/revoke therefore keep today's
 * synchronous fsync durability unconditionally.
 *
 * Durable-ORDER caveat of that bypass: inside an open batch, a capability/
 * revocation frame lands on disk BEFORE records staged earlier in program
 * order (those wait in staging_ for the next sub-frame flush or the
 * outermost commit). Replay is insensitive to this — load() collects signed
 * records across the whole log and merges only after the full replay, cap/rev
 * blobs are order-independent sets, and clock meta stays monotone across
 * frames — but it does mean "the durable log preserves append order" only
 * holds among the RECORD stream, not across these frames. */
bool Storage::put_capability(const std::string &blob) {
    return write_frame(build_cap(blob), 1);
}

bool Storage::put_revocation(const std::string &blob) {
    return write_frame(build_rev(blob), 1);
}

bool Storage::put_entity(const std::string &ns, const std::string &ent,
                         bool present, const Hlc &presence_hlc,
                         const PubKey &ex_author, const Sig &ex_sig,
                         uint64_t /*db_clock*/) {
    return emit(build_entity(ns, ent, present, presence_hlc, ex_author, ex_sig));
}

bool Storage::put_field(const std::string &ns, const std::string &ent,
                        const std::string &field, const std::string &value,
                        const Hlc &hlc, const PubKey &author, const Sig &sig,
                        uint64_t /*db_clock*/) {
    Register r;
    r.value = value;
    r.hlc = hlc;
    r.author = author;
    r.sig = sig;
    return emit(build_field(ns, ent, field, r));
}

namespace {

/* State accumulated while replaying the log, finalized in load(). */
struct Replay {
    bool have_schema = false, have_seed = false;
    uint64_t schema_version = 0, hlc_physical = 0, db_clock = 0;
    uint32_t hlc_logical = 0;
    uint8_t seed[32];
};

} // namespace

/* See storage.h. (In ke, not the anonymous namespace, so tests can link it;
 * existence_cmp stays anonymous above.) */
void merge_record(sync_engine *e, const DecodedChange &dc, const Hash256 &h) {
    Hlc hlc{dc.hlc.physical, dc.hlc.logical};
    if (dc.kind == SYNC_CHANGE_EXISTENCE) {
        /* Same {0,0}-sentinel refusal as ke::apply_change (sync_engine.cpp):
         * {0,0} means "no assertion", so it can never BE one. apply_entry's
         * kEntity branch already filters these out before they are queued, so
         * this is defence in depth for the second, independent apply path --
         * and it also stops the operator[] below from materialising a shell
         * entity for a record that must not land. */
        if (hlc.physical == 0 && hlc.logical == 0) return;
        Entity &en = e->ns[dc.ns][dc.entity];
        if (existence_cmp(hlc, dc.author, en.presence_hlc, en.ex_author) > 0) {
            en.present_v = (dc.causal_length != 0);
            en.presence_hlc = hlc;
            en.ex_author = dc.author;
            en.ex_sig = dc.signature;
            en.ex_hash = h;
        }
    } else { /* REGISTER */
        Register r;
        r.value = dc.value;
        r.hlc = hlc;
        r.author = dc.author;
        r.sig = dc.signature;
        r.elem_hash = h;
        auto &fields = e->ns[dc.ns][dc.entity].fields;
        auto fi = fields.find(dc.field);
        if (fi != fields.end()) {
            if (register_cmp(r, fi->second) > 0)
                fi->second = std::move(r); /* non-throwing move-assign */
            return;
        }
        /* Fresh cell: decide against the default Register it would otherwise
         * tie with, WITHOUT committing that default first. On a win the
         * incoming record lands already carrying its own hash. On the
         * degenerate tie/loss (all-zero hlc/author, empty value) the default
         * cell is what lands — hash what will actually be stored, via the
         * same shared construction build_snapshot uses, into the still-local
         * cell BEFORE the insert (hoisting rule, §3.2 point 1: element_hash
         * allocates, and a throw must not leave a committed zero-hashed
         * cell). Either way try_emplace's node allocation is the only
         * remaining throw point, and it fails before anything is linked. */
        if (register_cmp(r, Register{}) > 0) {
            fields.try_emplace(dc.field, std::move(r));
        } else {
            Register def;
            def.elem_hash = element_hash(
                change_from_register(dc.ns, dc.entity, dc.field, def));
            fields.try_emplace(dc.field, std::move(def));
        }
    }
}

namespace {

/* Re-verify the signatures of the collected records in parallel (native) and
 * merge the valid ones. Verification is the dominant load cost (~150 us each),
 * so a many-record reopen is otherwise serial-bound. A forged record is dropped;
 * the merge is order-independent so parallel verification is safe. The same
 * pass computes each record's element hash into a side vector (streaming over
 * the signing bytes it already encoded; per-index disjoint writes, exactly the
 * ok[] pattern) — unconditionally, not gated on ok[i]: branchless, and a
 * dropped record's hash is simply never installed. */
void verify_and_merge(sync_engine *e, std::vector<DecodedChange> &pending) {
    const size_t n = pending.size();
    if (n == 0) return;
    std::vector<char> ok(n, 0);
    std::vector<Hash256> hashes(n);
    auto verify_range = [&](size_t lo, size_t hi) {
        for (size_t i = lo; i < hi; i++) {
            std::string signing;
            sync_change c = pending[i].view();
            encode_signing(c, signing);
            ok[i] = verify(c.author, signing.data(), signing.size(),
                           c.signature) ? 1 : 0;
            element_hash(signing, c.signature, hashes[i]);
        }
    };
#ifndef __EMSCRIPTEN__
    unsigned hw = std::thread::hardware_concurrency();
    unsigned workers = std::min<unsigned>(hw ? hw : 1, 8u);
    if (n >= 64 && workers > 1) {
        std::vector<std::thread> pool;
        const size_t chunk = (n + workers - 1) / workers;
        for (unsigned w = 0; w < workers; w++) {
            size_t lo = (size_t)w * chunk, hi = std::min(n, lo + chunk);
            if (lo >= hi) break;
            pool.emplace_back([&, lo, hi] {
                try { verify_range(lo, hi); } catch (...) {}
            });
        }
        for (auto &t : pool) t.join();
    } else
#endif
        verify_range(0, n);

    for (size_t i = 0; i < n; i++)
        if (ok[i]) merge_record(e, pending[i], hashes[i]);
}

/* Decode one entry. META/CAP are handled immediately; signed existence/register
 * records are appended to `pending` for batched parallel verification. Returns
 * false only on a malformed entry (caller treats the frame as corrupt). */
bool apply_entry(sync_engine *e, Replay &rp, const uint8_t *&p,
                 const uint8_t *end, std::vector<DecodedChange> &pending) {
    if (p >= end) return false;
    uint8_t type = *p++;
    switch (type) {
    case kMeta: {
        std::string k, v;
        if (!get_blob(p, end, k) || !get_blob(p, end, v)) return false;
        if (k == "schema_version" && v.size() == 8) {
            rp.schema_version = read_u64le((const uint8_t *)v.data());
            rp.have_schema = true;
        } else if (k == "seed" && v.size() == 32) {
            std::memcpy(rp.seed, v.data(), 32);
            rp.have_seed = true;
        } else if (k == "hlc_physical" && v.size() == 8) {
            rp.hlc_physical = read_u64le((const uint8_t *)v.data());
        } else if (k == "hlc_logical" && v.size() == 8) {
            /* Persisted as 8 bytes (put_meta_u64) but held as uint32_t in
             * memory, so the restore has to narrow. CLAMP, don't truncate: a
             * truncating cast can restore a clock strictly SMALLER than the one
             * persisted, and a clock that moves backwards lets the next local
             * write tie or lose LWW against a record already on disk -- which
             * drops that write silently, the same failure mode this file's
             * {0,0} reservation exists to prevent. Clamping keeps the restore
             * monotone-non-decreasing, and Hlc::tick still makes progress from
             * UINT32_MAX by carrying into physical (bump_logical). A log written
             * by this code can never store more than UINT32_MAX here, so this
             * only ever fires on a corrupt or hand-edited file. */
            const uint64_t l = read_u64le((const uint8_t *)v.data());
            rp.hlc_logical = l > 0xFFFFFFFFull ? 0xFFFFFFFFu : (uint32_t)l;
        } else if (k == "db_clock" && v.size() == 8) {
            rp.db_clock = read_u64le((const uint8_t *)v.data());
        }
        return true;
    }
    case kEntity: {
        std::string ns, ent;
        PubKey a{};
        Sig sg{};
        if (!get_blob(p, end, ns) || !get_blob(p, end, ent)) return false;
        if (p >= end) return false;
        bool present = (*p++ != 0);
        Hlc hlc{};
        if (!get_u64le(p, end, hlc.physical) || !get_u32le(p, end, hlc.logical) ||
            !get_raw(p, end, a.data(), a.size()) ||
            !get_raw(p, end, sg.data(), sg.size()))
            return false;
        bool asserted = (hlc.physical != 0 || hlc.logical != 0);
        if (asserted) {
            /* Signed presence record — queue for parallel re-verification. */
            DecodedChange dc;
            dc.kind = SYNC_CHANGE_EXISTENCE;
            dc.ns = std::move(ns);
            dc.entity = std::move(ent);
            dc.causal_length = present ? 1 : 0;
            dc.hlc.physical = hlc.physical;
            dc.hlc.logical = hlc.logical;
            dc.author = a;
            dc.signature = sg;
            pending.push_back(std::move(dc));
        } else {
            /* An unasserted kEntity entry carries no signed content and no
             * assertion to replay. Do NOT materialise a shell for it: an entity
             * that still has fields is re-created on demand by its kField
             * records (merge_record indexes e->ns[ns][ent]), while one with no
             * fields carries no reconciliation element at all.
             *
             * This is hygiene, not correctness -- and deliberately NOT
             * justified by the digest: sync_engine_digest now gates its
             * presence block on asserted(), so a materialised shell would
             * contribute nothing to it either way. What dropping it buys is
             * that the entity-key set actually equals the element-carrying set:
             * no map node retained for a key nothing can ever reference, and no
             * write-back of it on the next compaction (rewrite_log_streamed
             * re-emits every entity in e->ns unconditionally, so a shell would
             * otherwise persist itself forever). It is also what lets a
             * database poisoned by a pre-fix binary shed the phantom entirely
             * on upgrade rather than keeping it as an empty shell. */
        }
        return true;
    }
    case kField: {
        std::string ns, ent, field;
        DecodedChange dc;
        uint64_t phys = 0;
        uint32_t logi = 0;
        PubKey a{};
        Sig sg{};
        if (!get_blob(p, end, dc.ns) || !get_blob(p, end, dc.entity) ||
            !get_blob(p, end, dc.field) || !get_blob(p, end, dc.value) ||
            !get_u64le(p, end, phys) || !get_u32le(p, end, logi) ||
            !get_raw(p, end, a.data(), a.size()) ||
            !get_raw(p, end, sg.data(), sg.size()))
            return false;
        dc.kind = SYNC_CHANGE_REGISTER;
        dc.hlc.physical = phys;
        dc.hlc.logical = logi;
        dc.author = a;
        dc.signature = sg;
        pending.push_back(std::move(dc)); /* queued for parallel verification */
        return true;
    }
    case kCap: {
        std::string blob;
        if (!get_blob(p, end, blob)) return false;
        Capability cap;
        if (cap_decode((const uint8_t *)blob.data(), blob.size(), cap) &&
            cap_sig_valid(cap)) {
            if (!e->caps) e->caps = new CapStore();
            e->caps->add(cap);
        }
        return true;
    }
    case kRev: {
        std::string blob;
        if (!get_blob(p, end, blob)) return false;
        Revocation rev;
        if (rev_decode((const uint8_t *)blob.data(), blob.size(), rev) &&
            rev_sig_valid(rev)) {
            if (!e->caps) e->caps = new CapStore();
            e->caps->add_rev(rev);
        }
        return true;
    }
    default:
        return false; /* unknown entry type → corrupt frame */
    }
}

} // namespace

bool Storage::load(sync_engine *e, const uint8_t seed[32], sync_error *err) {
    if (err) *err = SYNC_OK;
    Replay rp;
    std::memcpy(rp.seed, seed, 32);
    std::vector<DecodedChange> pending; /* signed records, verified after replay */

    /* Replay every good frame from just past the header. */
    off_t hdr = (off_t)header_size();
    off_t file_end = ::lseek(fd_, 0, SEEK_END);
    if (file_end < 0 || ::lseek(fd_, hdr, SEEK_SET) < 0) {
        if (err) *err = SYNC_ERR_INTERNAL;
        return false;
    }
    off_t good_end = hdr;
    for (;;) {
        uint8_t lenbuf[4];
        if (!read_exact(fd_, lenbuf, 4)) break; /* clean EOF or torn length */
        uint32_t body_len = read_u32le(lenbuf);
        if (body_len == 0) break;
        /* A whole, intact frame must physically fit in the remaining file: the
         * body plus its trailer (sha8, or nonce+mac when encrypted). A length
         * larger than that is a torn/corrupt trailing frame — or a crafted file
         * trying to make us allocate gigabytes for bytes that aren't there — so
         * stop here rather than sizing the buffer off the untrusted length. */
        off_t avail = file_end - good_end - 4; /* bytes after this length field */
        off_t need = (off_t)body_len + (encrypted_ ? 24 + 16 : 8);
        if (need > avail) break;
        std::string body(body_len, '\0');
        off_t frame_bytes;
        if (encrypted_) {
            /* [nonce:24][ciphertext:body_len][mac:16]; the AEAD tag verifies. */
            uint8_t nonce[24], mac[16];
            std::string ct(body_len, '\0');
            if (!read_exact(fd_, nonce, sizeof nonce) ||
                !read_exact(fd_, &ct[0], body_len) ||
                !read_exact(fd_, mac, sizeof mac))
                break; /* torn trailing frame */
            if (!aead_decrypt(key_, nonce, nullptr, 0, (const uint8_t *)ct.data(),
                              body_len, mac, (uint8_t *)&body[0]))
                break; /* tampered/torn tail */
            frame_bytes = 4 + 24 + (off_t)body_len + 16;
        } else {
            uint8_t sum[8];
            if (!read_exact(fd_, &body[0], body_len) || !read_exact(fd_, sum, 8))
                break; /* torn trailing frame */
            uint8_t digest[32];
            sync_engine_detail::sha256(body.data(), body.size(), digest);
            if (std::memcmp(digest, sum, 8) != 0) break; /* corrupt/torn tail */
            frame_bytes = 4 + (off_t)body_len + 8;
        }

        /* Frame is intact: apply its entries. */
        const uint8_t *p = (const uint8_t *)body.data();
        const uint8_t *bend = p + body.size();
        if ((size_t)(bend - p) < 4) break;
        uint32_t count = read_u32le(p);
        p += 4;
        bool frame_ok = true;
        for (uint32_t i = 0; i < count && frame_ok; i++)
            frame_ok = apply_entry(e, rp, p, bend, pending);
        if (!frame_ok) break; /* malformed body → treat as tail, stop */

        good_end += frame_bytes;
    }

    /* Bytes past the last good frame are either a torn write from a crash or
     * an append racing this open from the live owning process. Truncating them
     * here would make merely *opening* a database destructive: a concurrent
     * reader (a monitoring tool, `komed --identity`, a test poller) could chop
     * a frame the owner just committed — the owner's in-memory state keeps the
     * change and it never re-appends, so the record is silently gone from disk
     * with nothing left to heal it. Record where the good frames end and defer
     * the truncation to the first write (write_frame): read-only opens never
     * modify the file, while a writer still cleans a genuinely torn tail
     * before its first append. */
    off_t end = ::lseek(fd_, 0, SEEK_END);
    tail_torn_ = (end != good_end);
    file_size_ = (uint64_t)good_end;

    /* Re-verify all collected records in parallel, then merge the valid ones. */
    verify_and_merge(e, pending);

    /* Version guard: unknown/newer format is rejected cleanly. */
    if (rp.have_schema && rp.schema_version != kSchemaVersion) {
        if (err) *err = SYNC_ERR_INVALID;
        return false;
    }

    /* Keep the seed: the persistence layer re-writes it on every compaction
     * (the file already holds it in plaintext, so this is not new exposure).
     * Wiped in ~Storage. */
    std::memcpy(seed_, rp.seed, 32);

    if (!rp.have_schema) {
        /* Fresh log: stamp the format version and identity seed atomically. */
        if (!begin() ||
            !put_meta_u64("schema_version", kSchemaVersion) ||
            !put_meta_blob("seed", rp.seed, 32) || !commit()) {
            if (err) *err = SYNC_ERR_INTERNAL;
            return false;
        }
    }
    (void)rp.have_seed;

    /* Derive identity + clock, then wipe the transient seed. The log holds this
     * node's private identity (like an SSH key); protect the file accordingly. */
    e->identity = keypair_from_seed(rp.seed);
    secure_wipe(rp.seed, sizeof rp.seed);
    site_id_from_pubkey(e->identity.sign_pk.data(), e->site_id.data());
    /* Clamp the restored physical to the same ceiling receive() adopts under.
     * The clock is persisted verbatim, so a database written by a binary
     * without that ceiling -- or a corrupt/hand-edited meta frame -- would
     * otherwise restore an engine straight onto bump_logical's saturating fixed
     * point, where tick() stops being strictly monotonic and every local write
     * lands locally but is dropped by every peer (see kMaxAdoptablePhysical,
     * engine.hpp). Clamping here is what lets such a database heal on upgrade
     * instead of carrying the pin forever. RAM-only, exactly like the
     * hlc_logical clamp above: the on-disk format is unchanged, and the next
     * stamp_clock_meta simply persists the healed value. */
    e->clock.physical = rp.hlc_physical > ke::kMaxAdoptablePhysical
                            ? ke::kMaxAdoptablePhysical
                            : rp.hlc_physical;
    e->clock.logical = rp.hlc_logical;
    e->db_clock = rp.db_clock;

    /* A bloated log (live image much smaller than the file) used to be
     * rewritten right here so reopen stays O(state). Deferred to the first
     * mutation (maybe_compact) for the same reason as the torn tail above:
     * open must never write, or a read-only consumer rewrites the file out
     * from under a live owner. */
    compacted_size_ = file_size_;
    open_compact_pending_ = file_size_ > 65536;
    return true;
}

/* Stream a complete compacted log image of the engine's current state — one
 * meta frame, one frame per entity (its existence record + field registers,
 * in byte-lexicographic (ns, entity) order: std::map iteration), one frame of
 * granted capabilities and one of revocations (each only when non-empty) —
 * directly to `<path_>.tmp` through a FrameSink, then commit it with the
 * exact sequence the full-image rewrite used: fsync(tmp) -> close -> rename
 * -> reopen -> fsync(dir). Replaying the image reconstructs exactly the
 * current state, so the digest is unchanged; the rename stays the sole commit
 * point, so a crash or failure anywhere mid-stream leaves the original log
 * untouched (at most an orphan `<path>.tmp`, which open() never reads and the
 * next compaction O_TRUNCs). RAM transient: kCompactBufSize + O(one frame) —
 * where "one frame" may be a single entity with all its fields OR the entire
 * cap/rev blob set sealed as a unit — never a full log image (§3.4).
 *
 * WASM (§3.4 amendment 7, corrected claim): the CI WASM leg links with
 * -sNODERAWFS=1 (CMakeLists.txt), i.e. real Node filesystem calls, so
 * streaming bounds the compaction transient there exactly as natively. Only
 * the *shipped* npm/browser module (tools/wasm_flags.sh: MEMFS+IDBFS, no
 * NODERAWFS) still sees MEMFS's geometric expandFileStorage keep the old and
 * new backing arrays alive while the temp file grows, making streaming
 * roughly neutral there rather than a win. If a MEMFS win is wanted later,
 * pre-size the temp with ftruncate(tmp.fd, compacted_image_size(e)) so MEMFS
 * allocates once — the MANDATORY final ftruncate(tmp.fd, sink.total) below
 * already guarantees a size misprediction could never commit a log with
 * trailing zero bytes. */
bool Storage::rewrite_log_streamed(sync_engine *e) {
    TmpFile tmp;
    tmp.path = path_ + ".tmp";
    tmp.fd = ::open(tmp.path.c_str(), O_RDWR | O_CREAT | O_TRUNC,
                    S_IRUSR | S_IWUSR);
    if (tmp.fd < 0) return false;
    tmp.armed = true;
    ::fchmod(tmp.fd, S_IRUSR | S_IWUSR);

    FrameSink sink(tmp.fd);
    sink.append(header_bytes());

    /* Seal + stream one frame. F2: seal_frame's empty return (RNG failure on
     * the encrypted path) is checked BEFORE any append, so a zero-nonce frame
     * never reaches even the temp file; the sink latches !ok and the stream
     * aborts, leaving the existing log in place. */
    auto add_frame = [&](const std::string &body, uint32_t count) {
        if (!sink.ok) return;
        std::string f = seal_frame(body, count);
        if (f.empty()) {
            sink.ok = false;
            return;
        }
        sink.append(f);
    };

    {
        std::string mbody;
        uint32_t mc = 0;
        auto add_meta = [&](const std::string &entry) { mbody += entry; mc++; };
        add_meta(build_meta_u64("schema_version", kSchemaVersion));
        add_meta(build_meta("seed", seed_, 32));
        add_meta(build_meta_u64("hlc_physical", e->clock.physical));
        add_meta(build_meta_u64("hlc_logical", e->clock.logical));
        add_meta(build_meta_u64("db_clock", e->db_clock));
        add_frame(mbody, mc);
    }

    /* sink.ok gates the loop conditions AND each build/seal (§3.4 amendment
     * 2): the first write/seal failure stops the stream immediately instead
     * of continuing to build, seal, and buffer every remaining entity —
     * which would re-create the full-image RAM transient on the error path. */
    for (auto np = e->ns.cbegin(); sink.ok && np != e->ns.cend(); ++np) {
        const std::string &ns = np->first;
        for (auto ep = np->second.cbegin();
             sink.ok && ep != np->second.cend(); ++ep) {
            const std::string &ent = ep->first;
            const Entity &en = ep->second;
            std::string body = build_entity(ns, ent, en.present_v,
                                            en.presence_hlc, en.ex_author,
                                            en.ex_sig);
            uint32_t c = 1;
            for (const auto &fp : en.fields) {
                body += build_field(ns, ent, fp.first, fp.second);
                c++;
            }
            add_frame(body, c);
        }
    }

    if (sink.ok && e->caps) {
        std::vector<std::string> blobs;
        e->caps->export_blobs(blobs);
        if (!blobs.empty()) {
            std::string body;
            for (const auto &b : blobs) body += build_cap(b);
            add_frame(body, (uint32_t)blobs.size());
        }
        if (sink.ok) {
            std::vector<std::string> rblobs;
            e->caps->export_rev_blobs(rblobs);
            if (!rblobs.empty()) {
                std::string body;
                for (const auto &b : rblobs) body += build_rev(b);
                add_frame(body, (uint32_t)rblobs.size());
            }
        }
    }

    sink.flush();
    if (!sink.ok) return false; /* TmpFile closes the fd and unlinks .tmp */

#ifndef NDEBUG
    /* Exactness check, live on every Debug compaction: the arithmetic image
     * size must match the streamed bytes to the byte, or maybe_compact's
     * open-time heuristic is deciding on a lie. */
    assert(sink.total == compacted_image_size(e));
#endif

    /* MANDATORY final truncate to the streamed size (§3.4 amendment 7): a
     * no-op today (the temp was opened O_TRUNC and only appended), it exists
     * so any future pre-sizing ftruncate can never commit trailing zero
     * bytes on a size misprediction. */
    if (::ftruncate(tmp.fd, (off_t)sink.total) != 0) return false;

    int rc = ::fsync(tmp.fd);
    storage_fsync_count().fetch_add(1, std::memory_order_relaxed);
    if (rc != 0) return false;
    tmp.close_fd();
    if (::rename(tmp.path.c_str(), path_.c_str()) != 0) return false;
    tmp.disarm(); /* the rename consumed the path; nothing left to unlink */

    /* The rename IS the commit: record the new on-disk truth IMMEDIATELY,
     * before attempting the reopen (§3.4 amendment 10). The old epilogue
     * returned from a failed reopen with file_size_ still holding the OLD
     * (larger) size while the on-disk file was the new, correct, smaller one
     * — every later write_frame then failed at lseek(-1) against stale
     * bookkeeping. The rewrite also superseded any deferred tail cleanup /
     * open-time compact. */
    file_size_ = sink.total;
    tail_torn_ = false;
    open_compact_pending_ = false;

    /* Best-effort: fsync the directory so the rename is durable across a
     * crash. This runs BEFORE the reopen: the rename already committed, so
     * making it durable must not be skipped just because the reopen below
     * fails (that failure costs this handle its fd, not the on-disk truth),
     * and the counted fsync total stays 2 on every path past the rename. A
     * path with no directory component means the cwd; one whose only slash
     * is at index 0 ("/x.db") means the root, not the empty string. */
    std::string dir = path_;
    size_t slash = dir.find_last_of('/');
    dir = slash == std::string::npos ? std::string(".")
          : slash == 0               ? std::string("/")
                                     : dir.substr(0, slash);
    int d = ::open(dir.c_str(), O_RDONLY);
    if (d >= 0) {
        ::fsync(d);
        storage_fsync_count().fetch_add(1, std::memory_order_relaxed);
        ::close(d);
    }

    /* Reopen the now-replaced file for continued appends. */
    if (fd_ >= 0) ::close(fd_);
    fd_ = ::open(path_.c_str(), O_RDWR);
    if (fd_ < 0) return false;

    return true;
}

/* Exact byte size rewrite_log_streamed will produce — pure arithmetic over
 * the engine's state, no allocation, mirroring the stream frame for frame and
 * entry for entry (the Debug assert above keeps the two in lockstep). Lets
 * maybe_compact's deferred open-time heuristic ask "would compaction halve
 * the file?" without building an image just to measure it. */
uint64_t Storage::compacted_image_size(const sync_engine *e) const {
    /* Fixed bytes wrapping one body's entries: the u32le length prefix + the
     * in-body u32le entry count, then sha8 (plaintext) or nonce24 + mac16
     * (encrypted — the per-frame AEAD overhead). */
    const uint64_t frame_overhead = 4 + 4 + (encrypted_ ? 24u + 16u : 8u);
    /* One [type][key][value] meta entry (build_meta). */
    auto meta_entry = [](size_t klen, size_t vlen) -> uint64_t {
        return 1 + frame_field_len(klen) + frame_field_len(vlen);
    };

    uint64_t total = header_size();

    /* Meta frame: schema_version, seed, hlc_physical, hlc_logical, db_clock. */
    total += frame_overhead + meta_entry(sizeof "schema_version" - 1, 8) +
             meta_entry(sizeof "seed" - 1, 32) +
             meta_entry(sizeof "hlc_physical" - 1, 8) +
             meta_entry(sizeof "hlc_logical" - 1, 8) +
             meta_entry(sizeof "db_clock" - 1, 8);

    /* One frame per entity: a build_entity entry ([type][ns][ent][present]
     * [hlc u64+u32][author 32][sig 64]) plus one build_field entry per
     * register ([type][ns][ent][field][value][hlc u64+u32][author][sig]). */
    for (const auto &np : e->ns) {
        const uint64_t ns_f = frame_field_len(np.first.size());
        for (const auto &ep : np.second) {
            const uint64_t ent_f = frame_field_len(ep.first.size());
            uint64_t body = 1 + ns_f + ent_f + 1 + 8 + 4 + SYNC_PUBKEY_LEN +
                            SYNC_SIG_LEN;
            for (const auto &fp : ep.second.fields)
                body += 1 + ns_f + ent_f + frame_field_len(fp.first.size()) +
                        frame_field_len(fp.second.value.size()) + 8 + 4 +
                        SYNC_PUBKEY_LEN + SYNC_SIG_LEN;
            total += frame_overhead + body;
        }
    }

    /* Cap / rev frames, each emitted only when its set is non-empty. Entry =
     * [type][varint(blob_len)][blob]; blob sizes per cap_blob_size /
     * rev_blob_size (mirrors of cap_encode / rev_encode). */
    if (e->caps) {
        if (!e->caps->caps().empty()) {
            uint64_t body = 0;
            for (const auto &c : e->caps->caps())
                body += 1 + frame_field_len(cap_blob_size(c));
            total += frame_overhead + body;
        }
        if (!e->caps->revs().empty()) {
            uint64_t body = 0;
            for (const auto &r : e->caps->revs())
                body += 1 + frame_field_len(rev_blob_size(r));
            total += frame_overhead + body;
        }
    }
    return total;
}

void Storage::gc_tombstones(sync_engine *e) {
    uint64_t now = now_ms();
    uint64_t cutoff = now > kTombstoneTtlMs ? now - kTombstoneTtlMs : 0;
    bool removed = false;
    for (auto &np : e->ns) {
        auto &ents = np.second;
        for (auto it = ents.begin(); it != ents.end();) {
            const Entity &en = it->second;
            /* An asserted absence (tombstone) past the horizon: drop the entity
             * and its hidden field registers. Live entities, unasserted shells,
             * and fresh tombstones are kept. */
            if (en.asserted() && !en.present_v &&
                en.presence_hlc.physical < cutoff) {
                it = ents.erase(it);
                removed = true;
            } else {
                ++it;
            }
        }
    }
    if (removed) e->content_gen++; /* entities left the element set: invalidate
                                    * the cached reconcile snapshot */
}

bool Storage::compact(sync_engine *e) {
    /* Never rewrite mid-transaction. A batch (batch_begin) holds in_tx_ for
     * its WHOLE lifetime, so compaction refuses mid-batch BY DESIGN —
     * sync_engine_compact maps this to SYNC_ERR_INTERNAL, and the erase-then-
     * tombstone-then-compact physical-erasure pairing must therefore run
     * outside any batch (documented at the ABI). */
    if (in_tx_) return false;
    gc_tombstones(e); /* purge expired tombstones before rewriting */
    if (!rewrite_log_streamed(e)) return false; /* incl. seal failure (F2):
                                                 * the existing log is kept */
    compacted_size_ = file_size_;
    return true;
}

void Storage::maybe_compact(sync_engine *e) {
    /* Never rewrite mid-transaction (spec §3.3 point 8). compact() below has
     * its own in_tx_ refusal, but the open_compact_pending_ branch bypasses
     * compact() — it used to be safe only by accident (no caller reached it
     * with in_tx_ set). The batch machinery holds in_tx_ for a batch's whole
     * lifetime and adds mid-batch write paths, so make the guard explicit. */
    if (in_tx_) return;
    if (open_compact_pending_) {
        /* Deferred open-time compaction (see load): now that the owner is
         * actually writing, rewrite a bloated log if the live image is much
         * smaller than the file. Same condition open() used to apply, now
         * computed arithmetically (compacted_image_size) instead of
         * serializing a full image just to measure it. Deliberately no
         * gc_tombstones here — this branch keeps its historical no-gc
         * semantics (route through compact() to change that). */
        open_compact_pending_ = false;
        if (compacted_image_size(e) * 2 < file_size_ &&
            rewrite_log_streamed(e))
            compacted_size_ = file_size_;
        return;
    }
    uint64_t threshold = compacted_size_ * 2;
    if (threshold < 65536) threshold = 65536; /* don't churn tiny logs */
    if (file_size_ > threshold) compact(e); /* best-effort */
}

} // namespace ke
