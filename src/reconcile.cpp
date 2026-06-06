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
#include <new>
#include <string>
#include <vector>

#include "codec.h"
#include "engine.hpp"
#include "sha256.h"
#include "sync_engine.h"

using sync_engine_detail::Sha256;
using sync_engine_detail::sha256;

namespace ke {
namespace {

using Hash256 = std::array<uint8_t, 32>;

enum Mode : uint8_t { MODE_FP = 0, MODE_LEAF = 1, MODE_HAVE = 2 };

/* ---- sort key ---------------------------------------------------------- */

struct SortKey {
    std::string ns, entity, field;
    bool existence = false; /* existence sorts before registers of an entity */
};

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

/* ---- element ----------------------------------------------------------- */

struct Element {
    SortKey     key;
    std::string bytes; /* canonical record serialization */
    Hash256     hash;
};

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

std::string encode_message(const std::vector<Desc> &descs) {
    std::string o;
    put_varint(o, descs.size());
    for (auto &d : descs) encode_desc(o, d);
    return o;
}

bool decode_message(const uint8_t *buf, size_t len, std::vector<Desc> &out) {
    const uint8_t *p = buf;
    const uint8_t *end = buf + len;
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

    std::vector<Element> snap;   /* sorted local snapshot */
    std::vector<Hash256> prefix; /* prefix[i] = sum of snap[0..i).hash */

    /* First snapshot index whose key >= bound. */
    size_t lower_index(const Bound &b) const {
        if (b.type == Bound::NEG_INF) return 0;
        if (b.type == Bound::POS_INF) return snap.size();
        size_t lo = 0, hi = snap.size();
        while (lo < hi) {
            size_t mid = (lo + hi) / 2;
            if (key_cmp(snap[mid].key, b.key) < 0) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }

    Hash256 fingerprint(size_t lo, size_t hi) const {
        Hash256 sum = prefix[hi];
        sub256(sum, prefix[lo]);
        Sha256 h;
        uint8_t cnt[8];
        uint64_t c = (uint64_t)(hi - lo);
        for (int i = 0; i < 8; i++) cnt[i] = (uint8_t)(c >> (i * 8));
        h.update(cnt, 8);
        h.update(sum.data(), sum.size());
        Hash256 out;
        h.finish(out.data());
        return out;
    }

    Bound key_bound(size_t idx) const {
        Bound b;
        b.type = Bound::KEY;
        b.key = snap[idx].key;
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
            for (size_t i = lo; i < hi; i++) leaf.records.push_back(s->snap[i].bytes);
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
            std::string kk;
            put_varint(kk, dc.ns.size()); kk += dc.ns;
            put_varint(kk, dc.entity.size()); kk += dc.entity;
            kk.push_back(dc.kind == SYNC_CHANGE_EXISTENCE ? 1 : 0);
            put_varint(kk, dc.field.size()); kk += dc.field;
            Hash256 hh;
            sha256(r.data(), r.size(), hh.data());
            peer[kk] = hh;
        }

        Desc have;
        have.mode = MODE_HAVE;
        have.lo = d.lo;
        have.hi = d.hi;
        for (size_t i = lo; i < hi; i++) {
            const SortKey &k = s->snap[i].key;
            std::string kk;
            put_varint(kk, k.ns.size()); kk += k.ns;
            put_varint(kk, k.entity.size()); kk += k.entity;
            kk.push_back(k.existence ? 1 : 0);
            put_varint(kk, k.field.size()); kk += k.field;
            auto it = peer.find(kk);
            if (it == peer.end() || it->second != s->snap[i].hash)
                have.records.push_back(s->snap[i].bytes);
        }
        if (!have.records.empty()) out.push_back(std::move(have));
        return;
    }

    /* MODE_HAVE: terminal — just apply. */
    apply_records(s->engine, d.records);
}

} // namespace

extern "C" {

sync_session *sync_session_begin(sync_engine *e, int as_initiator) {
    if (!e) return nullptr;
    try {
        sync_session *s = new (std::nothrow) sync_session();
        if (!s) return nullptr;
        s->engine = e;
        s->initiator = as_initiator != 0;

        /* Snapshot the current state as sorted elements with hashes. */
        sync_change *recs = nullptr;
        size_t n = 0;
        if (sync_engine_export(e, &recs, &n) != SYNC_OK) {
            delete s;
            return nullptr;
        }
        s->snap.reserve(n);
        for (size_t i = 0; i < n; i++) {
            Element el;
            el.key = key_of(recs[i]);
            encode_record(recs[i], el.bytes);
            sha256(el.bytes.data(), el.bytes.size(), el.hash.data());
            s->snap.push_back(std::move(el));
        }
        sync_changes_free(recs, n);

        std::sort(s->snap.begin(), s->snap.end(),
                  [](const Element &a, const Element &b) {
                      return key_cmp(a.key, b.key) < 0;
                  });

        s->prefix.resize(s->snap.size() + 1);
        s->prefix[0] = Hash256{};
        for (size_t i = 0; i < s->snap.size(); i++) {
            s->prefix[i + 1] = s->prefix[i];
            add256(s->prefix[i + 1], s->snap[i].hash);
        }
        return s;
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
            f.fp = s->fingerprint(0, s->snap.size());
            reply.push_back(std::move(f));
        } else {
            s->sent_initial = true;
            std::vector<Desc> incoming;
            if (in && in_len) {
                if (!decode_message(in, in_len, incoming))
                    return SYNC_ERR_INVALID;
            }
            for (auto &d : incoming) process_desc(s, d, reply);
        }

        if (reply.empty()) {
            *done = 1;
            return SYNC_OK;
        }

        std::string msg = encode_message(reply);
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
