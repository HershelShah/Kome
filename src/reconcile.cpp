/* reconcile.cpp — range-based set reconciliation session (M3).
 *
 * The reconciliation set is the engine's current change-records: one existence
 * element per entity, one register element per field. Elements sort by
 * (ns, entity, existence-first, field). A range's fingerprint is a combinable
 * sum of per-element hashes (so any sub-range is an O(1) prefix-sum delta).
 *
 * Protocol (one message in flight, reliable channel):
 *   - The initiator sends a single FP descriptor covering the whole key space.
 *   - On an FP descriptor: if our fingerprint of the range matches, the range
 *     is in sync (drop it); else if the range holds few local elements, send a
 *     LEAF carrying our full content; else split into ~16 buckets, one FP each.
 *   - On a LEAF descriptor: apply the peer's records, then reply HAVE with the
 *     records the peer is missing or has staler.
 *   - On a HAVE descriptor: apply the records. Terminal.
 * Convergence is the union of both sides' snapshots merged into each engine.
 * Descriptors are self-contained (explicit lo/hi bounds), so the protocol is
 * robust to reordered/duplicated descriptors. */
#include "reconcile.h"

#include <algorithm>
#include <array>
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
#include <new>
#include <string>
#include <vector>

#include "byteorder.h"
#include "capability.h"
#include "codec.h"
#include "engine.hpp"
#include "sha256.h"
#include "sync_engine.h"

using sync_engine_detail::Sha256;
using sync_engine_detail::sha256;

namespace ke {

using Hash256 = std::array<uint8_t, 32>;

/* ---- sort key ---------------------------------------------------------- */

struct SortKey {
    std::string ns, entity, field;
    bool existence = false; /* existence sorts before registers of an entity */
};

/* A reconciliation element: a cell's sort key, its canonical record bytes, and
 * the per-element hash the combinable fingerprint sums. */
struct Element {
    SortKey     key;
    std::string bytes;
    Hash256     hash;
};

/* The sorted snapshot a session reconciles over; cached on the engine and
 * shared by sessions (see sync_engine::recon_cache). Named (external linkage)
 * so the engine can hold a shared_ptr<const ReconSnapshot>. */
struct ReconSnapshot {
    uint64_t             gen = 0;
    std::vector<Element> snap;
    std::vector<Hash256> prefix; /* prefix[i] = sum of snap[0..i).hash */
};

namespace {

enum Mode : uint8_t { MODE_FP = 0, MODE_LEAF = 1, MODE_HAVE = 2 };

int key_cmp(const SortKey &a, const SortKey &b) {
    if (a.ns != b.ns) return a.ns < b.ns ? -1 : 1;
    if (a.entity != b.entity) return a.entity < b.entity ? -1 : 1;
    if (a.existence != b.existence) return a.existence ? -1 : 1;
    if (a.field != b.field) return a.field < b.field ? -1 : 1;
    return 0;
}

SortKey key_of(const sync_change &c) {
    SortKey k;
    k.ns.assign((const char *)c.ns, c.ns_len);
    k.entity.assign((const char *)c.entity, c.entity_len);
    k.existence = (c.kind == SYNC_CHANGE_EXISTENCE);
    if (!k.existence) k.field.assign((const char *)c.field, c.field_len);
    return k;
}

/* Compact serialization of a key, used to match an element across peers (the
 * fingerprint is over content; this identifies the cell). */
std::string serialize_key(const std::string &ns, const std::string &entity,
                          bool existence, const std::string &field) {
    std::string kk;
    put_varint(kk, ns.size());     kk += ns;
    put_varint(kk, entity.size()); kk += entity;
    kk.push_back(existence ? 1 : 0);
    put_varint(kk, field.size());  kk += field;
    return kk;
}
std::string serialize_key(const SortKey &k) {
    return serialize_key(k.ns, k.entity, k.existence, k.field);
}

/* ---- bounds ------------------------------------------------------------ */

struct Bound {
    enum Type : uint8_t { NEG_INF = 0, KEY = 1, POS_INF = 2 } type = NEG_INF;
    SortKey key;
};

/* ---- 256-bit combinable fingerprint ------------------------------------ */

void add256(Hash256 &acc, const Hash256 &x) {
    uint16_t carry = 0;
    for (int i = 0; i < 32; i++) {
        uint16_t s = (uint16_t)acc[i] + x[i] + carry;
        acc[i] = (uint8_t)s;
        carry = s >> 8;
    }
}
void sub256(Hash256 &acc, const Hash256 &x) {
    int borrow = 0;
    for (int i = 0; i < 32; i++) {
        int v = (int)acc[i] - x[i] - borrow;
        if (v < 0) { v += 256; borrow = 1; } else borrow = 0;
        acc[i] = (uint8_t)v;
    }
}

/* ---- varint / wire helpers --------------------------------------------- */

void encode_bound(std::string &o, const Bound &b) {
    o.push_back((char)b.type);
    if (b.type == Bound::KEY) {
        put_varint(o, b.key.ns.size());
        o.append(b.key.ns);
        put_varint(o, b.key.entity.size());
        o.append(b.key.entity);
        o.push_back((char)(b.key.existence ? 1 : 0));
        put_varint(o, b.key.field.size());
        o.append(b.key.field);
    }
}

bool decode_bound(const uint8_t *&p, const uint8_t *end, Bound &b) {
    if (p >= end) return false;
    uint8_t t = *p++;
    if (t > 2) return false;
    b.type = (Bound::Type)t;
    if (b.type == Bound::KEY) {
        auto rd = [&](std::string &s) -> bool {
            uint64_t n = 0;
            if (!get_varint(p, end, n)) return false;
            if ((uint64_t)(end - p) < n) return false;
            s.assign((const char *)p, (size_t)n);
            p += n;
            return true;
        };
        if (!rd(b.key.ns) || !rd(b.key.entity)) return false;
        if (p >= end) return false;
        b.key.existence = (*p++ != 0);
        if (!rd(b.key.field)) return false;
    }
    return true;
}

struct Desc {
    uint8_t                  mode = MODE_FP;
    Bound                    lo, hi;
    Hash256                  fp{};
    std::vector<std::string> records; /* canonical record bytes (LEAF/HAVE) */
};

void encode_desc(std::string &o, const Desc &d) {
    o.push_back((char)d.mode);
    encode_bound(o, d.lo);
    encode_bound(o, d.hi);
    if (d.mode == MODE_FP) {
        o.append((const char *)d.fp.data(), d.fp.size());
    } else {
        put_varint(o, d.records.size());
        for (auto &r : d.records) {
            put_varint(o, r.size());
            o.append(r);
        }
    }
}

bool decode_desc(const uint8_t *&p, const uint8_t *end, Desc &d) {
    if (p >= end) return false;
    uint8_t m = *p++;
    if (m > 2) return false;
    d.mode = m;
    if (!decode_bound(p, end, d.lo)) return false;
    if (!decode_bound(p, end, d.hi)) return false;
    if (d.mode == MODE_FP) {
        if ((size_t)(end - p) < 32) return false;
        std::memcpy(d.fp.data(), p, 32);
        p += 32;
    } else {
        uint64_t cnt = 0;
        if (!get_varint(p, end, cnt)) return false;
        for (uint64_t i = 0; i < cnt; i++) {
            uint64_t rl = 0;
            if (!get_varint(p, end, rl)) return false;
            if ((uint64_t)(end - p) < rl) return false;
            d.records.emplace_back((const char *)p, (size_t)rl);
            p += rl;
        }
    }
    return true;
}

/* Wire form: [caps][descriptors]. caps carries delegation capabilities so the
 * peer can authorize records authored by keys it hasn't been told about. */
std::string encode_message(const std::vector<Desc> &descs,
                           const std::vector<std::string> &caps) {
    std::string o;
    put_varint(o, caps.size());
    for (auto &c : caps) {
        put_varint(o, c.size());
        o += c;
    }
    put_varint(o, descs.size());
    for (auto &d : descs) encode_desc(o, d);
    return o;
}

bool decode_message(const uint8_t *buf, size_t len, std::vector<Desc> &out,
                    std::vector<std::string> &caps) {
    const uint8_t *p = buf;
    const uint8_t *end = buf + len;
    uint64_t nc = 0;
    if (!get_varint(p, end, nc)) return false;
    for (uint64_t i = 0; i < nc; i++) {
        uint64_t cl = 0;
        if (!get_varint(p, end, cl)) return false;
        if ((uint64_t)(end - p) < cl) return false;
        caps.emplace_back((const char *)p, (size_t)cl);
        p += cl;
    }
    uint64_t n = 0;
    if (!get_varint(p, end, n)) return false;
    for (uint64_t i = 0; i < n; i++) {
        Desc d;
        if (!decode_desc(p, end, d)) return false;
        out.push_back(std::move(d));
    }
    return true;
}

} // namespace
} // namespace ke

using namespace ke;

/* ---- the session ------------------------------------------------------- */

struct sync_session {
    sync_engine *engine = nullptr;
    bool         initiator = false;
    bool         sent_initial = false;
    bool         sent_caps = false; /* delegation caps sent once */

    /* The point-in-time snapshot this session reconciles over. Held by
     * shared_ptr so it stays stable even as records applied mid-session bump
     * the engine's state_gen and replace its cached snapshot. */
    std::shared_ptr<const ReconSnapshot> ss;

    const std::vector<Element> &snap() const { return ss->snap; }
    const std::vector<Hash256> &prefix() const { return ss->prefix; }

    /* First snapshot index whose key >= bound. */
    size_t lower_index(const Bound &b) const {
        const auto &sn = snap();
        if (b.type == Bound::NEG_INF) return 0;
        if (b.type == Bound::POS_INF) return sn.size();
        size_t lo = 0, hi = sn.size();
        while (lo < hi) {
            size_t mid = (lo + hi) / 2;
            if (key_cmp(sn[mid].key, b.key) < 0) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }

    Hash256 fingerprint(size_t lo, size_t hi) const {
        Hash256 sum = prefix()[hi];
        sub256(sum, prefix()[lo]);
        Sha256 h;
        uint8_t cnt[8];
        store_u64le(cnt, (uint64_t)(hi - lo));
        h.update(cnt, 8);
        h.update(sum.data(), sum.size());
        Hash256 out;
        h.finish(out.data());
        return out;
    }

    Bound key_bound(size_t idx) const {
        Bound b;
        b.type = Bound::KEY;
        b.key = snap()[idx].key;
        return b;
    }
};

namespace {

void apply_records(sync_engine *e, const std::vector<std::string> &recs) {
    for (auto &r : recs) {
        DecodedChange d;
        size_t used = 0;
        if (!decode_record((const uint8_t *)r.data(), r.size(), d, used)) continue;
        sync_change c = d.view();
        sync_engine_apply(e, &c);
    }
}

/* Process one incoming descriptor, applying records and appending any reply
 * descriptors to out. */
void process_desc(sync_session *s, const Desc &d, std::vector<Desc> &out) {
    size_t lo = s->lower_index(d.lo);
    size_t hi = s->lower_index(d.hi);
    if (hi < lo) hi = lo;

    if (d.mode == MODE_FP) {
        Hash256 myfp = s->fingerprint(lo, hi);
        if (myfp == d.fp) return; /* range already in sync */

        size_t cnt = hi - lo;
        if (cnt <= kLeafThreshold) {
            Desc leaf;
            leaf.mode = MODE_LEAF;
            leaf.lo = d.lo;
            leaf.hi = d.hi;
            for (size_t i = lo; i < hi; i++)
                leaf.records.push_back(s->snap()[i].bytes);
            out.push_back(std::move(leaf));
            return;
        }
        /* Split into up to kBuckets equal-count buckets, one FP each. */
        size_t groups = std::min(kBuckets, cnt);
        for (size_t g = 0; g < groups; g++) {
            size_t gs = lo + (cnt * g) / groups;
            size_t ge = lo + (cnt * (g + 1)) / groups;
            if (ge <= gs) continue;
            Desc f;
            f.mode = MODE_FP;
            f.lo = (g == 0) ? d.lo : s->key_bound(gs);
            f.hi = (g == groups - 1) ? d.hi : s->key_bound(ge);
            f.fp = s->fingerprint(gs, ge);
            out.push_back(std::move(f));
        }
        return;
    }

    if (d.mode == MODE_LEAF) {
        /* Peer gave its full content for the range. Apply, then reply with the
         * records the peer is missing or has staler. */
        apply_records(s->engine, d.records);

        std::map<std::string, Hash256> peer; /* serialized-key -> elem hash */
        for (auto &r : d.records) {
            DecodedChange dc;
            size_t used = 0;
            if (!decode_record((const uint8_t *)r.data(), r.size(), dc, used))
                continue;
            std::string kk = serialize_key(dc.ns, dc.entity,
                                           dc.kind == SYNC_CHANGE_EXISTENCE,
                                           dc.field);
            Hash256 hh;
            sha256(r.data(), r.size(), hh.data());
            peer[kk] = hh;
        }

        Desc have;
        have.mode = MODE_HAVE;
        have.lo = d.lo;
        have.hi = d.hi;
        for (size_t i = lo; i < hi; i++) {
            const SortKey &k = s->snap()[i].key;
            std::string kk = serialize_key(k);
            auto it = peer.find(kk);
            if (it == peer.end() || it->second != s->snap()[i].hash)
                have.records.push_back(s->snap()[i].bytes);
        }
        if (!have.records.empty()) out.push_back(std::move(have));
        return;
    }

    /* MODE_HAVE: terminal — just apply. */
    apply_records(s->engine, d.records);
}

} // namespace

namespace {

/* Snapshot the engine as sorted elements with per-element hashes. Records in
 * namespaces peer may not read are excluded (peer == NULL == no scoping).
 * Returns false only on export failure (OOM). */
bool build_snapshot(sync_engine *e, const uint8_t *peer,
                    std::vector<Element> &out) {
    sync_change *recs = nullptr;
    size_t n = 0;
    if (sync_engine_export(e, &recs, &n) != SYNC_OK) return false;
    out.reserve(n);
    for (size_t i = 0; i < n; i++) {
        if (peer) {
            std::string ns((const char *)recs[i].ns, recs[i].ns_len);
            if (!cap_authorize_read(e, peer, ns)) continue; /* read-scoped out */
        }
        Element el;
        el.key = key_of(recs[i]);
        encode_record(recs[i], el.bytes);
        sha256(el.bytes.data(), el.bytes.size(), el.hash.data());
        out.push_back(std::move(el));
    }
    sync_changes_free(recs, n);
    std::sort(out.begin(), out.end(), [](const Element &a, const Element &b) {
        return key_cmp(a.key, b.key) < 0;
    });
    return true;
}

/* prefix[i] = combinable sum of the first i element hashes. */
void build_prefix(const std::vector<Element> &snap,
                  std::vector<Hash256> &prefix) {
    prefix.resize(snap.size() + 1);
    prefix[0] = Hash256{};
    for (size_t i = 0; i < snap.size(); i++) {
        prefix[i + 1] = prefix[i];
        add256(prefix[i + 1], snap[i].hash);
    }
}

/* The engine's cached full snapshot, rebuilt only when state_gen advanced since
 * it was taken. Returns NULL on build failure. */
std::shared_ptr<const ReconSnapshot> ensure_cache(sync_engine *e) {
    if (e->recon_cache && e->recon_cache->gen == e->state_gen)
        return e->recon_cache;
    auto snap = std::make_shared<ReconSnapshot>();
    snap->gen = e->state_gen;
    if (!build_snapshot(e, nullptr, snap->snap)) return nullptr;
    build_prefix(snap->snap, snap->prefix);
    e->recon_cache = snap;
    return snap;
}

/* Build a session, optionally read-scoped to peer (NULL == no scoping). The
 * unscoped snapshot is cached on the engine and shared across sessions; a
 * scoped session builds its own filtered snapshot (not cached — it's per-peer). */
sync_session *begin_session(sync_engine *e, int as_initiator,
                            const uint8_t *peer) {
    if (!e) return nullptr;
    sync_session *s = new (std::nothrow) sync_session();
    if (!s) return nullptr;
    s->engine = e;
    s->initiator = as_initiator != 0;

    if (peer) {
        auto snap = std::make_shared<ReconSnapshot>();
        if (!build_snapshot(e, peer, snap->snap)) { delete s; return nullptr; }
        build_prefix(snap->snap, snap->prefix);
        s->ss = snap;
    } else {
        s->ss = ensure_cache(e);
        if (!s->ss) { delete s; return nullptr; }
    }
    return s;
}

} // namespace

extern "C" {

sync_session *sync_session_begin(sync_engine *e, int as_initiator) {
    try {
        return begin_session(e, as_initiator, nullptr);
    } catch (...) {
        return nullptr;
    }
}

sync_session *sync_session_begin_scoped(sync_engine *e, int as_initiator,
                                        const uint8_t peer_pubkey[32]) {
    if (!peer_pubkey) return nullptr;
    try {
        return begin_session(e, as_initiator, peer_pubkey);
    } catch (...) {
        return nullptr;
    }
}

int sync_session_step(sync_session *s, const uint8_t *in, size_t in_len,
                      uint8_t **out, size_t *out_len, int *done) {
    if (!s || !out || !out_len || !done) return SYNC_ERR_INVALID;
    *out = nullptr;
    *out_len = 0;
    *done = 0;
    try {
        std::vector<Desc> reply;

        if (s->initiator && !s->sent_initial) {
            s->sent_initial = true;
            /* Whole-key-space fingerprint kicks things off. */
            Desc f;
            f.mode = MODE_FP;
            f.lo.type = Bound::NEG_INF;
            f.hi.type = Bound::POS_INF;
            f.fp = s->fingerprint(0, s->snap().size());
            reply.push_back(std::move(f));
        } else {
            s->sent_initial = true;
            std::vector<Desc> incoming;
            std::vector<std::string> caps_in;
            if (in && in_len) {
                if (!decode_message(in, in_len, incoming, caps_in))
                    return SYNC_ERR_INVALID;
            }
            /* Ingest the peer's delegations before applying its records. */
            cap_ingest_delegations(s->engine, caps_in);
            for (auto &d : incoming) process_desc(s, d, reply);
        }

        if (reply.empty()) {
            *done = 1;
            return SYNC_OK;
        }

        /* Attach our delegation capabilities to the first message we send. */
        std::vector<std::string> caps_out;
        if (!s->sent_caps && s->engine->caps) {
            s->engine->caps->export_blobs(caps_out);
            s->sent_caps = true;
        }
        std::string msg = encode_message(reply, caps_out);
        uint8_t *buf = (uint8_t *)std::malloc(msg.size() ? msg.size() : 1);
        if (!buf) return SYNC_ERR_NOMEM;
        std::memcpy(buf, msg.data(), msg.size());
        *out = buf;
        *out_len = msg.size();
        return SYNC_OK;
    } catch (const std::bad_alloc &) {
        return SYNC_ERR_NOMEM;
    } catch (...) {
        return SYNC_ERR_INTERNAL;
    }
}

void sync_session_end(sync_session *s) { delete s; }

} // extern "C"
