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
    if (!write_all(fd_, framed.data(), framed.size())) return false;
    if (::fsync(fd_) != 0) return false;
    file_size_ += framed.size();
    return true;
}

bool Storage::emit(const std::string &entry) {
    if (in_tx_) {
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

bool Storage::batch_begin() {
    if (batching_) return true;
    if (!begin()) return false;
    batching_ = true;
    return true;
}

bool Storage::batch_commit(sync_engine *e) {
    if (!batching_) return true;
    batching_ = false;
    /* One clock record for the whole batch, then a single fsync'd frame. */
    bool ok = put_meta_u64("hlc_physical", e->clock.physical) &&
              put_meta_u64("hlc_logical", e->clock.logical) &&
              put_meta_u64("db_clock", e->db_clock);
    if (!ok) { rollback(); return false; }
    if (!commit()) return false;
    maybe_compact(e);
    return true;
}

bool Storage::put_meta_u64(const char *key, uint64_t v) {
    return emit(build_meta_u64(key, v));
}

bool Storage::put_meta_blob(const char *key, const uint8_t *data, size_t len) {
    return emit(build_meta(key, data, len));
}

bool Storage::put_capability(const std::string &blob) {
    return emit(build_cap(blob));
}

bool Storage::put_revocation(const std::string &blob) {
    return emit(build_rev(blob));
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

/* Merge one already-verified record into engine state by the same LWW rule the
 * engine uses, so replay is order-independent and idempotent. */
void merge_decoded(sync_engine *e, const DecodedChange &dc) {
    Hlc hlc{dc.hlc.physical, dc.hlc.logical};
    if (dc.kind == SYNC_CHANGE_EXISTENCE) {
        Entity &en = e->ns[dc.ns][dc.entity];
        if (existence_cmp(hlc, dc.author, en.presence_hlc, en.ex_author) > 0) {
            en.present_v = (dc.causal_length != 0);
            en.presence_hlc = hlc;
            en.ex_author = dc.author;
            en.ex_sig = dc.signature;
        }
    } else { /* REGISTER */
        Register r;
        r.value = dc.value;
        r.hlc = hlc;
        r.author = dc.author;
        r.sig = dc.signature;
        Register &cur = e->ns[dc.ns][dc.entity].fields[dc.field];
        if (register_cmp(r, cur) > 0) cur = std::move(r);
    }
}

/* Re-verify the signatures of the collected records in parallel (native) and
 * merge the valid ones. Verification is the dominant load cost (~150 us each),
 * so a many-record reopen is otherwise serial-bound. A forged record is dropped;
 * the merge is order-independent so parallel verification is safe. */
void verify_and_merge(sync_engine *e, std::vector<DecodedChange> &pending) {
    const size_t n = pending.size();
    if (n == 0) return;
    std::vector<char> ok(n, 0);
    auto verify_range = [&](size_t lo, size_t hi) {
        for (size_t i = lo; i < hi; i++) {
            std::string signing;
            sync_change c = pending[i].view();
            encode_signing(c, signing);
            ok[i] = verify(c.author, signing.data(), signing.size(),
                           c.signature) ? 1 : 0;
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
        if (ok[i]) merge_decoded(e, pending[i]);
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
            rp.hlc_logical = (uint32_t)read_u64le((const uint8_t *)v.data());
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
            /* Unasserted shell carries no signed content — just hold the entity
             * for its (separately verified) fields. */
            (void)e->ns[ns][ent];
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
    e->clock.physical = rp.hlc_physical;
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

/* Build a complete log image (magic + frames) of the engine's current state:
 * one meta frame, one frame per entity (its existence record + field
 * registers), and one frame for granted capabilities. Replaying it reconstructs
 * exactly the current state, so the digest is unchanged. */
void Storage::serialize_state(sync_engine *e, std::string &out) {
    out = header_bytes();

    /* Append one sealed frame; on a seal failure (RNG, encrypted path) clear out
     * to signal the whole image is invalid so callers don't write a partial /
     * zero-nonce file (F2). A valid image always has at least the header + meta
     * frame, so empty is an unambiguous failure sentinel. */
    bool failed = false;
    auto add_frame = [&](const std::string &body, uint32_t count) {
        if (failed) return;
        std::string f = seal_frame(body, count);
        if (f.empty()) { failed = true; return; }
        out += f;
    };

    std::string mbody;
    uint32_t mc = 0;
    auto add_meta = [&](const std::string &entry) { mbody += entry; mc++; };
    add_meta(build_meta_u64("schema_version", kSchemaVersion));
    add_meta(build_meta("seed", seed_, 32));
    add_meta(build_meta_u64("hlc_physical", e->clock.physical));
    add_meta(build_meta_u64("hlc_logical", e->clock.logical));
    add_meta(build_meta_u64("db_clock", e->db_clock));
    add_frame(mbody, mc);

    for (const auto &np : e->ns) {
        const std::string &ns = np.first;
        for (const auto &ep : np.second) {
            const std::string &ent = ep.first;
            const Entity &en = ep.second;
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

    if (e->caps) {
        std::vector<std::string> blobs;
        e->caps->export_blobs(blobs);
        if (!blobs.empty()) {
            std::string body;
            for (const auto &b : blobs) body += build_cap(b);
            add_frame(body, (uint32_t)blobs.size());
        }
        std::vector<std::string> rblobs;
        e->caps->export_rev_blobs(rblobs);
        if (!rblobs.empty()) {
            std::string body;
            for (const auto &b : rblobs) body += build_rev(b);
            add_frame(body, (uint32_t)rblobs.size());
        }
    }

    if (failed) out.clear();
}

bool Storage::atomic_replace(const std::string &content) {
    std::string tmp = path_ + ".tmp";
    int t = ::open(tmp.c_str(), O_RDWR | O_CREAT | O_TRUNC, S_IRUSR | S_IWUSR);
    if (t < 0) return false;
    ::fchmod(t, S_IRUSR | S_IWUSR);
    if (!write_all(t, content.data(), content.size()) || ::fsync(t) != 0) {
        ::close(t);
        ::unlink(tmp.c_str());
        return false;
    }
    ::close(t);
    if (::rename(tmp.c_str(), path_.c_str()) != 0) {
        ::unlink(tmp.c_str());
        return false;
    }
    /* Reopen the now-replaced file for continued appends. */
    if (fd_ >= 0) ::close(fd_);
    fd_ = ::open(path_.c_str(), O_RDWR);
    if (fd_ < 0) return false;
    file_size_ = content.size();
    /* The rewrite superseded any deferred tail cleanup / open-time compact. */
    tail_torn_ = false;
    open_compact_pending_ = false;

    /* Best-effort: fsync the directory so the rename is durable across a crash. */
    std::string dir = path_;
    size_t slash = dir.find_last_of('/');
    dir = (slash == std::string::npos) ? std::string(".") : dir.substr(0, slash);
    int d = ::open(dir.c_str(), O_RDONLY);
    if (d >= 0) {
        ::fsync(d);
        ::close(d);
    }
    return true;
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
    if (removed) e->state_gen++; /* invalidate the cached reconcile snapshot */
}

bool Storage::compact(sync_engine *e) {
    if (in_tx_) return false; /* never rewrite mid-transaction */
    gc_tombstones(e); /* purge expired tombstones before rewriting */
    std::string fresh;
    serialize_state(e, fresh);
    if (fresh.empty()) return false; /* seal failed (RNG); keep the existing log (F2) */
    if (!atomic_replace(fresh)) return false;
    compacted_size_ = file_size_;
    return true;
}

void Storage::maybe_compact(sync_engine *e) {
    if (open_compact_pending_) {
        /* Deferred open-time compaction (see load): now that the owner is
         * actually writing, rewrite a bloated log if the live image is much
         * smaller than the file. Same condition open() used to apply. */
        open_compact_pending_ = false;
        std::string fresh;
        serialize_state(e, fresh);
        if (!fresh.empty() && (uint64_t)fresh.size() * 2 < file_size_ &&
            atomic_replace(fresh))
            compacted_size_ = file_size_;
        return;
    }
    uint64_t threshold = compacted_size_ * 2;
    if (threshold < 65536) threshold = 65536; /* don't churn tiny logs */
    if (file_size_ > threshold) compact(e); /* best-effort */
}

} // namespace ke
