/* storage.cpp — append-only log persistence (replaces the SQLite layer).
 *
 * On-disk format
 * --------------
 *   file   = MAGIC(8) frame*
 *   MAGIC  = "KOMELOG1"
 *   frame  = body_len:u32le  body(body_len)  checksum(8)
 *   body   = entry_count:u32le  entry*
 *   entry  = type:u8  payload
 *     META(1)   : key:bytes  value:bytes
 *     ENTITY(2) : ns:bytes ent:bytes  causal_length:u64le  ex_author[32] ex_sig[64]
 *     FIELD(3)  : ns:bytes ent:bytes field:bytes value:bytes
 *                 hlc_physical:u64le hlc_logical:u32le  author[32] sig[64]
 *     CAP(4)    : blob:bytes
 *   bytes  = varint(len) raw
 *   checksum = SHA-256(body)[0:8]
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

#include "byteorder.h"
#include "capability.h"
#include "codec.h"
#include "crypto.h"
#include "sha256.h"

namespace ke {

namespace {

constexpr char kMagic[8] = {'K', 'O', 'M', 'E', 'L', 'O', 'G', '1'};

enum EntryType : uint8_t { kMeta = 1, kEntity = 2, kField = 3, kCap = 4 };

/* Re-verify a record's signature on load. Persisted rows are NOT trusted just
 * because they're on disk — a crafted/swapped file could otherwise inject forged
 * records that bypass the signature gate the network path enforces. */
bool record_sig_ok(const sync_change &c) {
    std::string signing;
    encode_signing(c, signing);
    return verify(c.author, signing.data(), signing.size(), c.signature);
}

/* (hlc, author) order on presence assertions: same total order apply() uses. */
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

bool get_bytes(const uint8_t *&p, const uint8_t *end, std::string &out) {
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

/* Wrap a body of `count` entries into a full on-disk frame. */
std::string make_frame(const std::string &body, uint32_t count) {
    std::string full;
    put_u32le(full, count);
    full += body;
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
}

Storage *Storage::open(const char *path, sync_error *err) {
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
        /* Fresh file: write the magic header and fsync. */
        if (!write_all(fd, kMagic, sizeof kMagic) || ::fsync(fd) != 0) {
            if (err) *err = SYNC_ERR_INTERNAL;
            delete s;
            return nullptr;
        }
        s->file_size_ = sizeof kMagic;
    } else {
        char magic[sizeof kMagic];
        ::lseek(fd, 0, SEEK_SET);
        if (!read_exact(fd, magic, sizeof magic) ||
            std::memcmp(magic, kMagic, sizeof kMagic) != 0) {
            if (err) *err = SYNC_ERR_INVALID; /* not our format (e.g. a SQLite db) */
            delete s;
            return nullptr;
        }
        s->file_size_ = (uint64_t)size;
    }
    return s;
}

bool Storage::write_frame(const std::string &body, uint32_t entry_count) {
    std::string framed = make_frame(body, entry_count);
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

bool Storage::put_meta_u64(const char *key, uint64_t v) {
    return emit(build_meta_u64(key, v));
}

bool Storage::put_meta_blob(const char *key, const uint8_t *data, size_t len) {
    return emit(build_meta(key, data, len));
}

bool Storage::put_capability(const std::string &blob) {
    return emit(build_cap(blob));
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

/* Apply one decoded entry to engine state + replay accumulator. Returns false
 * only on a malformed entry (caller treats the frame as corrupt). */
bool apply_entry(sync_engine *e, Replay &rp, const uint8_t *&p,
                 const uint8_t *end) {
    if (p >= end) return false;
    uint8_t type = *p++;
    switch (type) {
    case kMeta: {
        std::string k, v;
        if (!get_bytes(p, end, k) || !get_bytes(p, end, v)) return false;
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
        if (!get_bytes(p, end, ns) || !get_bytes(p, end, ent)) return false;
        if (p >= end) return false;
        bool present = (*p++ != 0);
        Hlc hlc{};
        if (!get_u64le(p, end, hlc.physical) || !get_u32le(p, end, hlc.logical) ||
            !get_raw(p, end, a.data(), a.size()) ||
            !get_raw(p, end, sg.data(), sg.size()))
            return false;
        bool asserted = (hlc.physical != 0 || hlc.logical != 0);
        /* An asserted entity carries a signed presence record — re-verify;
         * ignore if forged. An unasserted shell only holds fields. */
        if (asserted) {
            sync_change c;
            std::memset(&c, 0, sizeof c);
            c.kind = SYNC_CHANGE_EXISTENCE;
            c.ns = (const uint8_t *)ns.data(); c.ns_len = ns.size();
            c.entity = (const uint8_t *)ent.data(); c.entity_len = ent.size();
            c.causal_length = present ? 1 : 0;
            c.hlc.physical = hlc.physical;
            c.hlc.logical = hlc.logical;
            std::memcpy(c.author, a.data(), SYNC_PUBKEY_LEN);
            std::memcpy(c.signature, sg.data(), SYNC_SIG_LEN);
            if (!record_sig_ok(c)) return true; /* skip forged, frame still valid */
        }
        Entity &en = e->ns[ns][ent];
        /* LWW presence merge so replay is order-independent and idempotent. */
        if (existence_cmp(hlc, a, en.presence_hlc, en.ex_author) > 0) {
            en.present_v = present;
            en.presence_hlc = hlc;
            en.ex_author = a;
            en.ex_sig = sg;
        }
        return true;
    }
    case kField: {
        std::string ns, ent, field;
        Register r;
        uint64_t phys = 0;
        uint32_t logi = 0;
        if (!get_bytes(p, end, ns) || !get_bytes(p, end, ent) ||
            !get_bytes(p, end, field) || !get_bytes(p, end, r.value) ||
            !get_u64le(p, end, phys) || !get_u32le(p, end, logi) ||
            !get_raw(p, end, r.author.data(), r.author.size()) ||
            !get_raw(p, end, r.sig.data(), r.sig.size()))
            return false;
        r.hlc.physical = phys;
        r.hlc.logical = logi;
        sync_change c;
        std::memset(&c, 0, sizeof c);
        c.kind = SYNC_CHANGE_REGISTER;
        c.ns = (const uint8_t *)ns.data(); c.ns_len = ns.size();
        c.entity = (const uint8_t *)ent.data(); c.entity_len = ent.size();
        c.field = (const uint8_t *)field.data(); c.field_len = field.size();
        c.value = (const uint8_t *)r.value.data(); c.value_len = r.value.size();
        c.hlc.physical = phys;
        c.hlc.logical = logi;
        std::memcpy(c.author, r.author.data(), SYNC_PUBKEY_LEN);
        std::memcpy(c.signature, r.sig.data(), SYNC_SIG_LEN);
        if (!record_sig_ok(c)) return true; /* skip forged */
        Register &cur = e->ns[ns][ent].fields[field];
        if (register_cmp(r, cur) > 0) cur = std::move(r);
        return true;
    }
    case kCap: {
        std::string blob;
        if (!get_bytes(p, end, blob)) return false;
        Capability cap;
        if (cap_decode((const uint8_t *)blob.data(), blob.size(), cap) &&
            cap_sig_valid(cap)) {
            if (!e->caps) e->caps = new CapStore();
            e->caps->add(cap);
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

    /* Replay every good frame from just past the magic header. */
    if (::lseek(fd_, (off_t)sizeof kMagic, SEEK_SET) < 0) {
        if (err) *err = SYNC_ERR_INTERNAL;
        return false;
    }
    off_t good_end = (off_t)sizeof kMagic;
    for (;;) {
        uint8_t lenbuf[4];
        if (!read_exact(fd_, lenbuf, 4)) break; /* clean EOF or torn length */
        uint32_t body_len = read_u32le(lenbuf);
        std::string body(body_len, '\0');
        uint8_t sum[8];
        if (body_len == 0 || !read_exact(fd_, &body[0], body_len) ||
            !read_exact(fd_, sum, 8))
            break; /* torn trailing frame */

        uint8_t digest[32];
        sync_engine_detail::sha256(body.data(), body.size(), digest);
        if (std::memcmp(digest, sum, 8) != 0) break; /* corrupt/torn tail */

        /* Frame is intact: apply its entries. */
        const uint8_t *p = (const uint8_t *)body.data();
        const uint8_t *bend = p + body.size();
        if ((size_t)(bend - p) < 4) break;
        uint32_t count = read_u32le(p);
        p += 4;
        bool frame_ok = true;
        for (uint32_t i = 0; i < count && frame_ok; i++)
            frame_ok = apply_entry(e, rp, p, bend);
        if (!frame_ok) break; /* malformed body → treat as tail, stop */

        good_end += 4 + (off_t)body_len + 8;
    }

    /* Drop any torn trailing bytes so future appends start clean. */
    off_t end = ::lseek(fd_, 0, SEEK_END);
    if (end != good_end) {
        if (::ftruncate(fd_, good_end) != 0) {
            if (err) *err = SYNC_ERR_INTERNAL;
            return false;
        }
        ::fsync(fd_);
    }
    file_size_ = (uint64_t)good_end;

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

    /* Compact a bloated log up front so reopen stays O(state): if the live
     * image is much smaller than the file, rewrite it now. */
    compacted_size_ = file_size_;
    if (file_size_ > 65536) {
        std::string fresh;
        serialize_state(e, fresh);
        if ((uint64_t)fresh.size() * 2 < file_size_ && atomic_replace(fresh))
            compacted_size_ = file_size_;
    }
    return true;
}

/* Build a complete log image (magic + frames) of the engine's current state:
 * one meta frame, one frame per entity (its existence record + field
 * registers), and one frame for granted capabilities. Replaying it reconstructs
 * exactly the current state, so the digest is unchanged. */
void Storage::serialize_state(sync_engine *e, std::string &out) {
    out.assign(kMagic, sizeof kMagic);

    std::string mbody;
    uint32_t mc = 0;
    auto add_meta = [&](const std::string &entry) { mbody += entry; mc++; };
    add_meta(build_meta_u64("schema_version", kSchemaVersion));
    add_meta(build_meta("seed", seed_, 32));
    add_meta(build_meta_u64("hlc_physical", e->clock.physical));
    add_meta(build_meta_u64("hlc_logical", e->clock.logical));
    add_meta(build_meta_u64("db_clock", e->db_clock));
    out += make_frame(mbody, mc);

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
            out += make_frame(body, c);
        }
    }

    if (e->caps) {
        std::vector<std::string> blobs;
        e->caps->export_blobs(blobs);
        if (!blobs.empty()) {
            std::string body;
            for (const auto &b : blobs) body += build_cap(b);
            out += make_frame(body, (uint32_t)blobs.size());
        }
    }
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
    if (!atomic_replace(fresh)) return false;
    compacted_size_ = file_size_;
    return true;
}

void Storage::maybe_compact(sync_engine *e) {
    uint64_t threshold = compacted_size_ * 2;
    if (threshold < 65536) threshold = 65536; /* don't churn tiny logs */
    if (file_size_ > threshold) compact(e); /* best-effort */
}

} // namespace ke
