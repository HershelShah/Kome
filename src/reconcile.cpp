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
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <map>
#include <memory>
#include <new>
#include <string>
#include <vector>
#ifndef __EMSCRIPTEN__
#include <thread> /* parallel batch signature verification (native only) */
#endif

#include "byteorder.h"
#include "capability.h"
#include "codec.h"
#include "crypto.h"
#include "engine.hpp"
#include "sha256.h"
#include "storage.h"
#include "sync_engine.h"

using sync_engine_detail::Sha256;
using sync_engine_detail::sha256;

namespace ke {

/* Hash256 comes from engine.hpp (promoted there for the per-cell caches). */

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
    /* The content_gen the snapshot was built at — content-only, even for a
     * scoped snapshot (the field's sole consumer is ensure_cache's equality
     * check on the unscoped cache). Scoped-cache validity is a property of the
     * engine, not the snapshot: it lives on sync_engine::scoped_cache_gens as
     * a full (content, scope) GenPair. */
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

/* acc/x are a 256-bit little-endian integer; add/subtract mod 2^256. Done four
 * 64-bit limbs at a time (read_/store_u64le compile to a single load/store on
 * little-endian, a bswap on big-endian) instead of 32 byte steps — same bytes
 * out, endianness-independent, ~8x fewer iterations on the prefix-sum build. */
void add256(Hash256 &acc, const Hash256 &x) {
    uint64_t carry = 0;
    for (int i = 0; i < 32; i += 8) {
        uint64_t a = read_u64le(acc.data() + i), b = read_u64le(x.data() + i);
        uint64_t s = a + b;
        uint64_t c = (s < a) ? 1 : 0; /* a+b overflowed */
        s += carry;
        c += (s < carry) ? 1 : 0; /* adding the incoming carry overflowed */
        store_u64le(acc.data() + i, s);
        carry = c;
    }
}
void sub256(Hash256 &acc, const Hash256 &x) {
    uint64_t borrow = 0;
    for (int i = 0; i < 32; i += 8) {
        uint64_t a = read_u64le(acc.data() + i), b = read_u64le(x.data() + i);
        uint64_t d = a - b;
        uint64_t bo = (a < b) ? 1 : 0; /* a-b underflowed */
        uint64_t d2 = d - borrow;
        bo += (d < borrow) ? 1 : 0; /* subtracting the incoming borrow underflowed */
        store_u64le(acc.data() + i, d2);
        borrow = bo;
    }
}

/* Fold a range's combinable hash sum into the wire fingerprint. The ONLY
 * construction of a fingerprint: the plain-snapshot path and the read-scoped
 * range-view path both come through here with (sum over the range, element
 * count), so a view produces byte-identical fingerprints to a dense snapshot of
 * the same visible set — the RBSR wire-parity invariant. */
Hash256 fp_of(const Hash256 &lo_sum, const Hash256 &hi_sum, size_t count) {
    Hash256 sum = hi_sum;
    sub256(sum, lo_sum);
    Sha256 h;
    uint8_t cnt[8];
    store_u64le(cnt, (uint64_t)count);
    h.update(cnt, 8);
    h.update(sum.data(), sum.size());
    Hash256 out;
    h.finish(out.data());
    return out;
}

/* First index in a sorted element vector whose key >= bound. Shared by the plain
 * snapshot path and (as the base-space step of) the range-view path. */
size_t base_lower_index(const std::vector<Element> &sn, const Bound &b) {
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

/* Approximate encoded size of a descriptor, for per-message budgeting. */
size_t desc_size(const Desc &d) {
    size_t n = 1 + 18; /* mode + two bounds (generous) */
    if (d.mode == MODE_FP) {
        n += 32;
    } else {
        n += 5; /* record count varint */
        for (const auto &r : d.records) n += 5 + r.size();
    }
    return n;
}

bool decode_desc(const uint8_t *&p, const uint8_t *end, Desc &d,
                 uint64_t &elem_budget) {
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
        /* Each record needs >=1 byte, so a count beyond the remaining buffer is
         * bogus — reject before reserving/allocating (allocation-DoS guard). */
        if (cnt > (uint64_t)(end - p)) return false;
        /* Charge records against the message-wide element budget so a flood of
         * tiny records can't amplify into a huge vector (F3). */
        if (cnt > elem_budget) return false;
        elem_budget -= cnt;
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

/* Wire form: [caps][revocations][descriptors]. caps carries delegation
 * capabilities so the peer can authorize records authored by keys it hasn't been
 * told about; revocations carry the owner's signed cut-offs for lost/stolen
 * keys, propagating them replica-to-replica the same way. */
std::string encode_message(const std::vector<Desc> &descs,
                           const std::vector<std::string> &caps,
                           const std::vector<std::string> &revs) {
    std::string o;
    put_varint(o, caps.size());
    for (auto &c : caps) {
        put_varint(o, c.size());
        o += c;
    }
    put_varint(o, revs.size());
    for (auto &r : revs) {
        put_varint(o, r.size());
        o += r;
    }
    put_varint(o, descs.size());
    for (auto &d : descs) encode_desc(o, d);
    return o;
}

bool decode_message(const uint8_t *buf, size_t len, std::vector<Desc> &out,
                    std::vector<std::string> &caps,
                    std::vector<std::string> &revs) {
    /* Reject an over-large message before parsing: each input byte can expand to
     * a heap object, so an unbounded message is a memory amplifier (F3). */
    if (len > kMaxRecvMessageBytes) return false;
    const uint8_t *p = buf;
    const uint8_t *end = buf + len;
    /* Shared element budget across caps + revocations + all descriptors' records. */
    uint64_t elem_budget = kMaxWireElements;
    uint64_t nc = 0;
    if (!get_varint(p, end, nc)) return false;
    if (nc > (uint64_t)(end - p)) return false; /* each cap >=1 byte */
    if (nc > elem_budget) return false;         /* element-count amplifier (F3) */
    elem_budget -= nc;
    for (uint64_t i = 0; i < nc; i++) {
        uint64_t cl = 0;
        if (!get_varint(p, end, cl)) return false;
        if ((uint64_t)(end - p) < cl) return false;
        caps.emplace_back((const char *)p, (size_t)cl);
        p += cl;
    }
    uint64_t nr = 0;
    if (!get_varint(p, end, nr)) return false;
    if (nr > (uint64_t)(end - p)) return false; /* each revocation >=1 byte */
    if (nr > elem_budget) return false;         /* element-count amplifier (F3) */
    elem_budget -= nr;
    for (uint64_t i = 0; i < nr; i++) {
        uint64_t rl = 0;
        if (!get_varint(p, end, rl)) return false;
        if ((uint64_t)(end - p) < rl) return false;
        revs.emplace_back((const char *)p, (size_t)rl);
        p += rl;
    }
    uint64_t n = 0;
    if (!get_varint(p, end, n)) return false;
    if (n > (uint64_t)(end - p)) return false;       /* each descriptor >=1 byte */
    if (n > kMaxWireDescriptors) return false;        /* Desc-object amplifier (F3) */
    for (uint64_t i = 0; i < n; i++) {
        Desc d;
        if (!decode_desc(p, end, d, elem_budget)) return false;
        out.push_back(std::move(d));
    }
    /* The framing is CANONICAL: a message is exactly its three blocks and
     * nothing else. Without this the decoder silently ignored anything after the
     * last descriptor, which (a) let a peer piggyback unbounded uninspected
     * bytes on every message, and (b) made the round-trip guard in
     * tests/recon_wire.hpp blind in the two directions that matter for wire
     * drift -- an appended field, and an under-reported block count (whose
     * unread items become trailing bytes). encode_message never emits a trailing
     * byte and every caller hands us an exactly-sized message
     * (transport/connection.cpp decrypts into one), so this rejects only input
     * no honest peer produces. */
    if (p != end) return false;
    return true;
}

} // namespace

/* ---- read-scoped range view -------------------------------------------- */

/* An immutable read-scoped VIEW over the engine's shared unscoped snapshot
 * (§3.5). A peer whose visible set depends on a capability expiry used to be
 * excluded from the scoped cache entirely, so every gossip cycle — idle,
 * converged ones included — re-encoded its whole visible set. A view instead
 * records, per readable namespace, the half-open base-index range that
 * namespace occupies in the base snapshot, plus prefix sums over those ranges;
 * building it is O(namespaces * log N) with no encode and no SHA-256 per
 * element, and it is cached per peer until the earliest capability expiry it
 * depends on (sync_engine::scoped_view_cache).
 *
 * Layout invariants (all established by build_view, none re-derivable later):
 *   - `base` is the unscoped snapshot the ranges index, held by shared_ptr so an
 *     in-flight session's view stays valid after the engine replaces its cache;
 *   - `ranges` are ascending, disjoint, non-empty and COALESCED (adjacent
 *     readable namespaces merge into one range), so `visible` == sum of range
 *     lengths and a whole-space fingerprint is one subtraction;
 *   - `vstart[r]` is the visible index of `ranges[r].lo`, with a trailing entry
 *     equal to `visible`;
 *   - `cum[r]` is the combinable sum of the first `vstart[r]` visible element
 *     hashes, with the same trailing entry, so any visible sub-range sum is one
 *     add and two subtractions.
 * Everything a session touches is expressed in VISIBLE index space; the base
 * index is never handed out (see sync_session's accessors). */
struct ReconView {
    struct Range { size_t lo = 0, hi = 0; }; /* half-open base-index interval */

    GenPair                              gen;              /* built at */
    uint64_t                             valid_until_ms = 0; /* inclusive */
    std::shared_ptr<const ReconSnapshot> base;
    std::vector<Range>                   ranges;
    std::vector<size_t>                  vstart; /* ranges.size() + 1 entries */
    std::vector<Hash256>                 cum;    /* ranges.size() + 1 entries */
    size_t                               visible = 0;

    size_t size() const { return visible; }

    /* Index of the range holding visible index v. */
    size_t range_of(size_t v) const {
        assert(v < visible && "ReconView::range_of past the visible set");
        size_t r = (size_t)(std::upper_bound(vstart.begin(), vstart.end(), v) -
                            vstart.begin()) - 1;
        assert(r < ranges.size());
        return r;
    }

    /* Visible index -> base index. Bounds-asserted (§3.5 fix 6): at v == visible
     * the arithmetic below yields a valid-but-wrong base index — the first
     * element of the NEXT, possibly denied, namespace — which is in bounds and
     * therefore invisible to UBSan and to the sanitizer legs. */
    size_t base_index(size_t v) const {
        assert(v < visible && "ReconView::base_index past the visible set");
        size_t r = range_of(v);
        return ranges[r].lo + (v - vstart[r]);
    }

    const Element &elem(size_t v) const {
        assert(v < visible && "ReconView::elem past the visible set");
        return base->snap[base_index(v)];
    }

    /* Combinable sum of the first v visible element hashes. v == visible is
     * legitimate here (it is the exclusive end of the whole visible range) and is
     * deliberately a SEPARATE, unguarded path rather than a relaxed bound on
     * elem()/base_index(): those two must keep rejecting it. */
    Hash256 vsum(size_t v) const {
        assert(v <= visible && "ReconView::vsum past the visible set");
        if (v == visible) return cum.back(); /* whole-set sum; no element read */
        size_t r = range_of(v);
        Hash256 s = cum[r];
        Hash256 d = base->prefix[ranges[r].lo + (v - vstart[r])];
        sub256(d, base->prefix[ranges[r].lo]);
        add256(s, d);
        return s;
    }

    Hash256 fingerprint(size_t lo, size_t hi) const {
        return fp_of(vsum(lo), vsum(hi), hi - lo);
    }

    /* First VISIBLE index whose key >= bound. Exact because the visible sequence
     * is the base sequence restricted to `ranges`: the base is sorted, so every
     * element at or after the base bound has key >= bound and every element
     * before it has key < bound, and that split carries over to the subsequence.
     * O(log N + log ranges), no per-probe range lookup. */
    size_t lower_index(const Bound &b) const {
        if (b.type == Bound::NEG_INF) return 0;
        if (b.type == Bound::POS_INF) return visible;
        size_t bi = base_lower_index(base->snap, b);
        size_t r = (size_t)(std::lower_bound(
                       ranges.begin(), ranges.end(), bi,
                       [](const Range &x, size_t v) { return x.hi <= v; }) -
                   ranges.begin());
        if (r == ranges.size()) return visible; /* bound is past every range */
        if (bi <= ranges[r].lo) return vstart[r];
        return vstart[r] + (bi - ranges[r].lo);
    }
};

} // namespace ke

using namespace ke;

/* ---- the session ------------------------------------------------------- */

struct sync_session {
    sync_engine *engine = nullptr;
    bool         initiator = false;
    bool         sent_initial = false;
    bool         sent_caps = false; /* delegation caps sent once */
    uint64_t     steps = 0;          /* processed-message counter (DoS bound) */

    /* Descriptors produced but not yet sent: a step emits at most
     * kMaxMessageBytes of them and keeps the rest here for the next round, so no
     * single message exceeds the relay/UDP size bound. */
    std::deque<Desc> outq;

    /* ---- the point-in-time source this session reconciles over ----------
     * Exactly one of the two is held, and both are PRIVATE (§3.5 fix 7):
     * privatizing only the accessors left `ss` itself assignable and, worse,
     * readable as `s->ss->snap[i]` from anywhere in this file — raw BASE
     * indexing that silently ignores read scope. With the members private and
     * every accessor below expressed in VISIBLE index space, a missed
     * conversion is a compile error rather than a scope leak.
     *
     * Both are held by shared_ptr, so the source stays stable for an in-flight
     * session even as records applied mid-session bump content_gen and replace
     * the engine's cached snapshot, or a capability expiry evicts the cached
     * view. begin_session is the sole writer (see set_source). */
    void set_source(std::shared_ptr<const ReconSnapshot> s,
                    std::shared_ptr<const ReconView> v) {
        assert(!ss_ && !vw_ && "session source is written exactly once");
        assert(!(s && v) && "a session reconciles over one source, not two");
        ss_ = std::move(s);
        vw_ = std::move(v);
    }
    bool has_source() const { return ss_ != nullptr || vw_ != nullptr; }

    /* Number of elements VISIBLE to this session's peer. Every bound derived
     * from the element count — descriptor splitting, the reply-amplification cap
     * — must come from here and never from the base snapshot, which for a scoped
     * session also counts elements the peer may not read. */
    size_t size() const { return vw_ ? vw_->size() : ss_->snap.size(); }

    /* Element at VISIBLE index i. */
    const Element &elem(size_t i) const {
        assert(i < size() && "sync_session::elem past the visible set");
        return vw_ ? vw_->elem(i) : ss_->snap[i];
    }

    /* First visible index whose key >= bound. */
    size_t lower_index(const Bound &b) const {
        return vw_ ? vw_->lower_index(b) : base_lower_index(ss_->snap, b);
    }

    /* Fingerprint of the visible half-open range [lo, hi). Identical bytes on
     * both paths — see fp_of. */
    Hash256 fingerprint(size_t lo, size_t hi) const {
        return vw_ ? vw_->fingerprint(lo, hi)
                   : fp_of(ss_->prefix[lo], ss_->prefix[hi], hi - lo);
    }

    Bound key_bound(size_t idx) const {
        Bound b;
        b.type = Bound::KEY;
        b.key = elem(idx).key;
        return b;
    }

private:
    std::shared_ptr<const ReconSnapshot> ss_;
    std::shared_ptr<const ReconView>     vw_;
};

namespace {

#ifndef __EMSCRIPTEN__
/* Verify a decoded record's signature and compute its element hash from the
 * same signing buffer (streaming — the ~1.6 us encode+hash rides along with
 * the ~130 us verify, and apply_change is handed the hash so the bulk path
 * never re-encodes the record). Pure (no engine/global state), so it is safe
 * to run concurrently across worker threads. (Only the parallel path uses it;
 * the serial path verifies and hashes inside apply_change.) */
bool change_sig_ok(const sync_change &c, Hash256 &eh) {
    std::string signing;
    encode_signing(c, signing);
    element_hash(signing, c.signature, eh);
    return verify(c.author, signing.data(), signing.size(), c.signature);
}

/* Batches at/above this size verify in parallel (small batches — the steady-
 * state gossip diff — stay serial; thread spawn would cost more than it saves).
 * EdDSA verify is ~130us, so even a few-record batch dwarfs the spawn cost. */
constexpr size_t kParallelVerifyMin = 16;
constexpr unsigned kMaxVerifyThreads = 8;
#endif

/* Apply a batch of received records. For a large batch (a bulk transfer / big
 * diff) the signatures are verified in parallel and the valid records applied
 * with already_verified=true; small batches take the plain verify-on-win path.
 * Either way every applied record is signature-checked and the merge decides
 * acceptance, so a forged record is dropped and cannot suppress a legitimate
 * one in the same batch. */
void apply_records(sync_engine *e, const std::vector<std::string> &recs) {
    std::vector<DecodedChange> decoded;
    decoded.reserve(recs.size());
    for (auto &r : recs) {
        DecodedChange d;
        size_t used = 0;
        /* Require an exact (canonical) encoding: trailing bytes would let a peer
         * craft distinct wire records that decode to the same logical record,
         * evading dedup and churning the fingerprint. */
        if (decode_record((const uint8_t *)r.data(), r.size(), d, used) &&
            used == r.size())
            decoded.push_back(std::move(d));
    }

    /* Stage the whole batch into one fsync'd frame (one fsync instead of N). */
    bool batched = e->store && decoded.size() > 1;
    if (batched) e->store->batch_begin();

#ifndef __EMSCRIPTEN__
    unsigned hw = std::thread::hardware_concurrency();
    unsigned workers = std::min<unsigned>(hw ? hw : 1, kMaxVerifyThreads);
    if (decoded.size() >= kParallelVerifyMin && workers > 1) {
        const size_t n = decoded.size();
        std::vector<char> ok(n, 0); /* distinct index per worker: no races */
        std::vector<Hash256> hashes(n); /* same per-index pattern as ok[] */
        std::vector<std::thread> pool;
        const size_t chunk = (n + workers - 1) / workers;
        for (unsigned w = 0; w < workers; w++) {
            size_t lo = (size_t)w * chunk, hi = std::min(n, lo + chunk);
            if (lo >= hi) break;
            pool.emplace_back([&decoded, &ok, &hashes, lo, hi] {
                /* An exception escaping a std::thread calls std::terminate;
                 * encode_signing can throw bad_alloc on a huge record. Treat
                 * any failure as not-verified (fail-closed). */
                try {
                    for (size_t i = lo; i < hi; i++)
                        ok[i] = change_sig_ok(decoded[i].view(), hashes[i])
                                    ? 1 : 0;
                } catch (...) {
                }
            });
        }
        for (auto &t : pool) t.join();
        for (size_t i = 0; i < n; i++) {
            if (!ok[i]) continue;
            sync_change c = decoded[i].view();
            apply_change(e, &c, /*already_verified=*/true, &hashes[i]);
        }
        if (batched) e->store->batch_commit(e);
        return;
    }
#endif
    for (auto &d : decoded) {
        sync_change c = d.view();
        apply_change(e, &c, /*already_verified=*/false);
    }
    if (batched) e->store->batch_commit(e);
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
                leaf.records.push_back(s->elem(i).bytes);
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
            if (!decode_record((const uint8_t *)r.data(), r.size(), dc, used) ||
                used != r.size())
                continue;
            std::string kk = serialize_key(dc.ns, dc.entity,
                                           dc.kind == SYNC_CHANGE_EXISTENCE,
                                           dc.field);
            Hash256 hh;
            sha256(r.data(), r.size(), hh.data());
            peer[kk] = hh;
        }

        /* Reply with the records the peer is missing or has staler. Split into
         * several HAVE descriptors so no one of them (and so no one message)
         * exceeds the size bound: a cold peer's empty LEAF over the whole range
         * would otherwise produce a single HAVE carrying every record. */
        Desc have;
        have.mode = MODE_HAVE;
        have.lo = d.lo;
        have.hi = d.hi;
        size_t bytes = 0;
        for (size_t i = lo; i < hi; i++) {
            std::string kk = serialize_key(s->elem(i).key);
            auto it = peer.find(kk);
            if (it != peer.end() && it->second == s->elem(i).hash) continue;
            const std::string &rec = s->elem(i).bytes;
            if (!have.records.empty() && bytes + rec.size() > kMaxMessageBytes) {
                out.push_back(std::move(have)); /* flush this chunk */
                have = Desc{};
                have.mode = MODE_HAVE;
                have.lo = d.lo;
                have.hi = d.hi;
                bytes = 0;
            }
            have.records.push_back(rec);
            bytes += rec.size();
        }
        if (!have.records.empty()) out.push_back(std::move(have));
        return;
    }

    /* MODE_HAVE: terminal — just apply. */
    apply_records(s->engine, d.records);
}

} // namespace

namespace {

/* Append the element for one change (key + canonical bytes + hash) to out. The
 * change borrows the engine's strings; only the Element's key/bytes are copied.
 * `hash` is the cell's cached element hash (Register::elem_hash /
 * Entity::ex_hash), maintained at every mutation point — copying it here is
 * what lets a snapshot rebuild skip re-running SHA-256 per element. */
void emit_element(const sync_change &c, const std::string &nsk,
                  const std::string &entk, const std::string &fk, bool existence,
                  const Hash256 &hash, std::vector<Element> &out) {
    Element el;
    el.key.ns = nsk;
    el.key.entity = entk;
    el.key.existence = existence;
    if (!existence) el.key.field = fk;
    encode_record(c, el.bytes);
    el.hash = hash;
#ifndef NDEBUG
    /* Debug cross-check: the cached hash must equal a fresh hash of the wire
     * bytes just encoded — a stale cache here is a permanent, silent
     * fingerprint divergence in Release. Full per-element for now; sampling
     * is the pre-agreed fallback only if CI wall time forces it (§3.2). */
    {
        Hash256 fresh;
        sha256(el.bytes.data(), el.bytes.size(), fresh.data());
        assert(fresh == el.hash && "cached element hash is stale");
    }
#endif
    out.push_back(std::move(el));
}

/* Snapshot the engine as sorted elements with per-element hashes. Records in
 * namespaces peer may not read are excluded (peer == NULL == no scoping).
 * `now` is the caller's single wall-clock instant for the whole build (see
 * begin_session); it is consulted only through cap_authorize_read, i.e. only
 * when peer != NULL.
 *
 * Iterates the engine's maps directly rather than via sync_engine_export — the
 * export path mallocs an N-element array plus four field copies per record and
 * then we free it all (profiled at ~55% of the build). Here each change borrows
 * the map's strings and is encoded straight into its Element. */
bool build_snapshot(sync_engine *e, const uint8_t *peer, uint64_t now,
                    std::vector<Element> &out) {
    static const std::string kEmpty;
    /* Reserve exactly: one element per present-or-tombstoned entity + one per
     * field, so the push_backs below never regrow (and move) the vector. */
    size_t count = 0;
    for (const auto &np : e->ns)
        for (const auto &ep : np.second)
            count += (ep.second.asserted() ? 1 : 0) + ep.second.fields.size();
    out.reserve(count);

    for (const auto &np : e->ns) {
        const std::string &nsk = np.first;
        if (peer && !cap_authorize_read(e, peer, nsk, now))
            continue; /* whole namespace read-scoped out */
        for (const auto &ep : np.second) {
            const std::string &entk = ep.first;
            const Entity &ent = ep.second;

            /* change_from_entity/change_from_register (codec) are the one
             * shared construction of a cell's canonical change — the same one
             * the mutation-time hashing contract is defined against. */
            if (ent.asserted()) { /* existence element (present or tombstone) */
                emit_element(change_from_entity(nsk, entk, ent), nsk, entk,
                             kEmpty, true, ent.ex_hash, out);
            }
            for (const auto &fp : ent.fields) { /* register element per field */
                const std::string &fk = fp.first;
                const Register &r = fp.second;
                emit_element(change_from_register(nsk, entk, fk, r), nsk, entk,
                             fk, false, r.elem_hash, out);
            }
        }
    }
    /* No sort: std::map yields (ns, entity) ascending and fields ascending, and
     * we emit each entity's existence element before its registers — which is
     * exactly SortKey order (existence sorts before registers). Checked in debug. */
    assert(std::is_sorted(out.begin(), out.end(),
                          [](const Element &a, const Element &b) {
                              return key_cmp(a.key, b.key) < 0;
                          }));
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

/* Build a fresh snapshot stamped at the current content_gen — full when
 * peer==NULL, else read-scoped to peer as of `now`. NULL on build failure.
 * Shared by the unscoped (ensure_cache) and per-peer (ensure_scoped_source)
 * paths, and by the Debug cross-check in build_view. */
std::shared_ptr<ReconSnapshot> build_filtered(sync_engine *e, const uint8_t *peer,
                                              uint64_t now) {
    auto snap = std::make_shared<ReconSnapshot>();
    snap->gen = e->content_gen;
    if (!build_snapshot(e, peer, now, snap->snap)) return nullptr;
    build_prefix(snap->snap, snap->prefix);
    return snap;
}

/* The engine's cached full snapshot, rebuilt only when content_gen advanced
 * since it was taken — the snapshot is a pure function of e->ns, so a
 * capability change (scope_gen) no longer discards and re-encodes/re-hashes
 * it. Returns NULL on build failure. */
std::shared_ptr<const ReconSnapshot> ensure_cache(sync_engine *e, uint64_t now) {
    if (e->recon_cache && e->recon_cache->gen == e->content_gen)
        return e->recon_cache;
    /* peer==NULL: `now` is threaded for signature uniformity only — the unscoped
     * build consults no capability and so no clock. */
    auto snap = build_filtered(e, nullptr, now);
    if (snap) e->recon_cache = snap;
    return snap;
}

/* True when the engine's shared unscoped snapshot is already built and current,
 * so a range view over it costs no element encoding at all. See build_view. */
bool base_is_current(const sync_engine *e) {
    return e->recon_cache && e->recon_cache->gen == e->content_gen;
}

/* Build the read-scoped range view for `peer`, valid (inclusively) until
 * `valid_until_ms`. NULL on build failure.
 *
 * TWO bases, chosen by `share_base` -- this is §3.5 fix 3's gate, and it is
 * measured rather than assumed (numbers in docs/PERF.md):
 *
 *  - share_base: range the peer's readable namespaces over the engine's SHARED
 *    unscoped snapshot. The base is ns-major sorted, so each readable namespace
 *    occupies one contiguous half-open base range, located with a pair of
 *    partition_points -- no encode, no hash, no per-element work at all.
 *    Adjacent readable namespaces are coalesced as they are appended (e->ns
 *    iterates ascending, so ranges come out ascending and disjoint by
 *    construction), keeping the common "everything readable" and "one denied
 *    namespace" shapes at one or two ranges.
 *
 *  - otherwise: build this peer's own filtered snapshot and wrap it in a single
 *    full-span range. Same view type, same deadline, same accessors; it simply
 *    owns its base instead of sharing one.
 *
 * The caller passes share_base only when the shared base is already current
 * (some other consumer built it, or no write has landed since this peer's last
 * cycle) or when the peer may read everything anyway. Forcing the O(N) base
 * build for a restricted peer instead measured 2x-15x SLOWER per write-active
 * cycle than the O(N_visible) filtered build it replaced, worst at the small
 * visible fractions this phase exists to serve (BM_ScopedSessionBeginTimeBound
 * vs BM_ScopedSessionBeginPermanent, docs/PERF.md). The per-cycle win this
 * phase is actually about -- an idle, converged link stops re-encoding
 * everything -- comes from the DEADLINE-keyed cache, which both bases get; the
 * shared base is the additional win when the snapshot is there for free.
 *
 * Either way the element sequence a view exposes is exactly what
 * build_snapshot(e, peer) would emit: build_snapshot walks e->ns in ascending
 * order, skips denied namespaces wholesale, and emits each kept namespace's
 * elements in map order -- which is the base's order restricted to that
 * namespace's range. */
std::shared_ptr<const ReconView> build_view(sync_engine *e, const uint8_t *peer,
                                            uint64_t now,
                                            uint64_t valid_until_ms,
                                            bool share_base) {
    auto base = share_base ? ensure_cache(e, now) : build_filtered(e, peer, now);
    if (!base) return nullptr;

    auto v = std::make_shared<ReconView>();
    v->gen = e->gens();
    v->valid_until_ms = valid_until_ms;
    v->base = base;

    const std::vector<Element> &sn = base->snap;
    if (!share_base) {
        /* The base IS the visible set: one full-span range (empty bases get no
         * range at all, keeping every range non-empty). */
        if (!sn.empty()) v->ranges.push_back(ReconView::Range{0, sn.size()});
    } else {
        for (const auto &np : e->ns) {
            const std::string &nsk = np.first;
            if (!cap_authorize_read(e, peer, nsk, now)) continue;
            size_t lo = (size_t)(std::partition_point(
                                     sn.begin(), sn.end(),
                                     [&nsk](const Element &x) {
                                         return x.key.ns < nsk;
                                     }) -
                                 sn.begin());
            size_t hi = (size_t)(std::partition_point(
                                     sn.begin() + (std::ptrdiff_t)lo, sn.end(),
                                     [&nsk](const Element &x) {
                                         return x.key.ns <= nsk;
                                     }) -
                                 sn.begin());
            if (hi == lo) continue; /* readable but contributes no element */
            if (!v->ranges.empty() && v->ranges.back().hi == lo)
                v->ranges.back().hi = hi; /* coalesce with the previous range */
            else
                v->ranges.push_back(ReconView::Range{lo, hi});
        }
    }

    v->vstart.reserve(v->ranges.size() + 1);
    v->cum.reserve(v->ranges.size() + 1);
    size_t vis = 0;
    Hash256 acc{};
    v->vstart.push_back(vis);
    v->cum.push_back(acc);
    for (const auto &r : v->ranges) {
        vis += r.hi - r.lo;
        Hash256 d = base->prefix[r.hi];
        sub256(d, base->prefix[r.lo]);
        add256(acc, d);
        v->vstart.push_back(vis);
        v->cum.push_back(acc);
    }
    v->visible = vis;

#ifndef NDEBUG
    /* Debug cross-check (§3.5): read scoping now rests on index arithmetic
     * rather than on the denied bytes being physically absent, so every view
     * build is compared against a from-scratch build_filtered with the SAME
     * `now` -- element for element (key, wire bytes, element hash) and prefix
     * sum for prefix sum. A divergence here is a scope leak or a wire-parity
     * break, and it must fail the build, not a fuzzer.
     *
     * Cost is live on every sanitizer leg (all four CI legs build Debug), which
     * is accepted for this rollout. Pre-agreed downgrade trigger, documented
     * before the first CI run rather than discovered on a red one (§3.5 fix 9):
     * if measured CI wall time regresses materially, sample the cross-check
     * once `visible > 4096` (i.e. run it for every small view, and for large
     * ones only on a deterministic sample) instead of removing it. NOT
     * implemented yet -- the unsampled check is what ships until the wall-time
     * measurement says otherwise. */
    {
        auto chk = build_filtered(e, peer, now);
        assert(chk && "cross-check build failed");
        assert(chk->snap.size() == v->visible &&
               "range view exposes a different element count than a filtered build");
        for (size_t i = 0; i < v->visible; i++) {
            assert(key_cmp(chk->snap[i].key, v->elem(i).key) == 0 &&
                   "range view element key diverges from a filtered build");
            assert(chk->snap[i].bytes == v->elem(i).bytes &&
                   "range view element bytes diverge from a filtered build");
            assert(chk->snap[i].hash == v->elem(i).hash &&
                   "range view element hash diverges from a filtered build");
            assert(chk->prefix[i] == v->vsum(i) &&
                   "range view prefix sum diverges from a filtered build");
        }
        assert(chk->prefix[v->visible] == v->vsum(v->visible) &&
               "range view total sum diverges from a filtered build");
    }
#endif
    return v;
}

/* The source a scoped session reconciles over: exactly one of a plain snapshot
 * (time-independent scope) or a range view (scope bounded by a capability
 * expiry). Both null on build failure. */
struct ScopedSource {
    std::shared_ptr<const ReconSnapshot> snap;
    std::shared_ptr<const ReconView>     view;
};

/* Upper bound on cached per-peer scoped snapshots/views. Both maps are cleared
 * wholesale on every state change, so this only matters for a burst of distinct
 * restricted peers between writes; fully-open peers cache a cheap shared alias,
 * so the expensive entries are the few genuinely read-restricted peers. */
constexpr size_t kMaxScopedCache = 256;

/* The per-peer read-scoped source, cached on the engine the same way
 * ensure_cache caches the unscoped snapshot, and classified by ONE pre-scan over
 * the namespaces:
 *
 *   deadline == UINT64_MAX (no namespace's answer can move with the clock alone)
 *     fully open -> alias the shared unscoped snapshot (scoped_cache)
 *     restricted -> a distinct filtered snapshot     (scoped_cache)
 *   deadline <  UINT64_MAX (some namespace's answer moves with the clock)
 *     -> a range view, cached in scoped_view_cache until `deadline` inclusive.
 *        Whether that view ranges over the shared unscoped snapshot or over its
 *        own filtered one is build_view's measured gate, not a scope question:
 *        both expose exactly the same visible elements.
 *
 * The deadline is the MINIMUM over EVERY namespace scanned, denied ones included
 * (§3.5 fix 1). A denied namespace is time-dependent too: CapStore::owned()
 * ignores expiry, so a namespace whose only root capability carries a finite
 * expiry flips from denied to open (== world-readable) the moment that root
 * lapses, and nothing bumps content_gen or scope_gen when it does. Keying the
 * deadline off readable-time-bound namespaces alone would serve that denial
 * forever. Both directions are sound by the same monotonicity argument: an
 * earlier-than-necessary rebuild costs one range recompute, never a wrong
 * answer.
 *
 * Neither cache is consulted without its guard: the GenPair guard below covers
 * writes/applies/GC and grants/revokes/ingest; the per-view deadline covers the
 * one thing no counter sees, the passage of time. */
ScopedSource ensure_scoped_source(sync_engine *e, const uint8_t *peer,
                                  uint64_t now) {
    ScopedSource out;
    /* No capability system engaged -> every namespace is open -> the scoped
     * source is exactly the unscoped snapshot. */
    if (!e->caps) {
        out.snap = ensure_cache(e, now);
        return out;
    }

    /* Cache-first: a hit is one map lookup (plus, for a view, one deadline
     * compare) and skips the per-namespace authorization pre-scan below -- so a
     * converged, idle link costs O(1) per cycle regardless of how the peer is
     * scoped. Both maps are cleared whenever engine state advances: a content
     * bump (writes, applies, tombstone GC) or a scope bump (capability
     * grants/revokes/ingest). A fully-open peer then cheaply re-runs the
     * pre-scan and re-aliases the still-valid unscoped snapshot. */
    if (e->scoped_cache_gens != e->gens()) {
        e->scoped_cache.clear();
        e->scoped_view_cache.clear();
        e->scoped_cache_gens = e->gens();
    }
    std::string key((const char *)peer, SYNC_PUBKEY_LEN);

    auto vit = e->scoped_view_cache.find(key);
    if (vit != e->scoped_view_cache.end()) {
        /* TWO independent guards, and a hit needs BOTH:
         *
         *  - `gen`: the GenPair the view was built at must still be the engine's.
         *    The map-wide clear above already guarantees that, so this compare
         *    never fires in correct operation -- it is here so the per-view stamp
         *    is LOAD-BEARING rather than decorative. A view carrying a validity
         *    stamp that nothing reads invites a future refactor to trust the
         *    stamp and drop the map-wide clear, which is exactly how a revoked
         *    peer gets served from its grant-era view; with the compare here,
         *    that refactor degrades to an extra rebuild instead of a leak. The
         *    stamp is checked BEFORE the deadline because scope changes are the
         *    security-relevant direction.
         *  - the deadline: inclusive, matching usable()'s `now <= c.expiry` in
         *    capability.cpp -- a capability is usable through its expiry
         *    millisecond, so a view built from it is too. This is the guard no
         *    counter can replace, because expiry moves neither generation. */
        if (vit->second && vit->second->gen == e->gens() &&
            now <= vit->second->valid_until_ms) {
            out.view = vit->second;
            return out;
        }
        /* Stale stamp or passed deadline. Drop it and rebuild right here -- no
         * dependence on a content_gen or scope_gen bump, because expiry moves
         * neither. */
        e->scoped_view_cache.erase(vit);
    }
    /* A snapshot entry is only ever stored for a peer whose scope carries NO
     * deadline at all, so unlike a view it cannot go stale with time; the
     * GenPair guard above is its whole invalidation. (The two maps are disjoint
     * per peer for the same reason: the classification that files a peer under
     * one rules out the other, and any change to that classification goes
     * through a grant/revoke/ingest, which clears both.) */
    auto it = e->scoped_cache.find(key);
    if (it != e->scoped_cache.end()) {
        out.snap = it->second;
        return out;
    }

    /* Miss: classify the peer's scope. The O(namespaces) pre-scan (each
     * cap_authorize_read is O(caps)) runs only here, not on cache hits, and
     * scans EVERY namespace with no early break -- a namespace sorted after a
     * denied one still contributes both its readability and its deadline. */
    bool fully_open = true;
    uint64_t deadline = UINT64_MAX;
    for (const auto &np : e->ns) {
        bool tb = false;
        uint64_t vu = UINT64_MAX;
        if (!cap_authorize_read(e, peer, np.first, now, &tb, &vu))
            fully_open = false;
        /* A time-bound ALLOW must always carry a deadline; the reverse does not
         * hold (a time-dependent DENY carries one and is not `time_bound`). */
        assert((!tb || vu != UINT64_MAX) && "time-bound scope without a deadline");
        (void)tb;
        if (vu < deadline) deadline = vu;
    }

    if (deadline != UINT64_MAX) {
        /* Time-dependent scope: a range view, cached until the deadline. Range
         * it over the shared unscoped snapshot only when that costs nothing --
         * the snapshot is already current, or this peer may read all of it
         * anyway (§3.5 fix 3; see build_view). */
        out.view = build_view(e, peer, now, deadline,
                              /*share_base=*/base_is_current(e) || fully_open);
        if (out.view && e->scoped_view_cache.size() < kMaxScopedCache)
            e->scoped_view_cache[key] = out.view;
        return out;
    }

    out.snap = fully_open ? ensure_cache(e, now) : build_filtered(e, peer, now);
    if (out.snap && e->scoped_cache.size() < kMaxScopedCache)
        e->scoped_cache[key] = out.snap;
    return out;
}

/* Build a session, optionally read-scoped to peer (NULL == no scoping). The
 * unscoped snapshot is cached on the engine and shared across sessions; a scoped
 * session gets a per-peer source from ensure_scoped_source. */
sync_session *begin_session(sync_engine *e, int as_initiator,
                            const uint8_t *peer) {
    if (!e) return nullptr;
    /* ONE clock read per session begin, threaded through the scope pre-scan, the
     * range-view build, the filtered build and the Debug cross-check, so all of
     * them classify against the same instant (§3.5 fix 2). Reading the clock
     * separately in each of them is not merely redundant: the pre-scan could
     * classify a peer as time-independent and a microsecond later the build
     * could drop a namespace whose capability expired in between, caching that
     * narrower set as if it were permanent. */
    const uint64_t now = now_ms();
    /* Acquire the source BEFORE allocating the session: the build can throw
     * bad_alloc, and an already-allocated session would leak out through
     * sync_session_begin's catch. */
    ScopedSource src;
    if (peer) src = ensure_scoped_source(e, peer, now);
    else src.snap = ensure_cache(e, now);
    if (!src.snap && !src.view) return nullptr;

    sync_session *s = new (std::nothrow) sync_session();
    if (!s) return nullptr;
    s->engine = e;
    s->initiator = as_initiator != 0;
    /* set_source is the ONLY writer of the session's snapshot/view members
     * (§3.5 fix 7) and asserts it is called exactly once. */
    s->set_source(src.snap, src.view);
    assert(s->has_source());
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
        /* Bound a non-terminating peer: give up cleanly after too many steps. */
        if (++s->steps > kMaxSessionSteps) {
            *done = 1;
            return SYNC_OK;
        }
        std::vector<Desc> reply;

        if (s->initiator && !s->sent_initial) {
            s->sent_initial = true;
            /* Whole-key-space fingerprint kicks things off. */
            Desc f;
            f.mode = MODE_FP;
            f.lo.type = Bound::NEG_INF;
            f.hi.type = Bound::POS_INF;
            f.fp = s->fingerprint(0, s->size());
            reply.push_back(std::move(f));
        } else {
            s->sent_initial = true;
            std::vector<Desc> incoming;
            std::vector<std::string> caps_in, revs_in;
            if (in && in_len) {
                if (!decode_message(in, in_len, incoming, caps_in, revs_in))
                    return SYNC_ERR_INVALID;
            }
            /* Ingest the peer's delegations and revocations before applying its
             * records, so a revoked key's *writes* in this very message are
             * rejected (write authorization is re-checked live per record). Read-
             * scope is bound to this session's snapshot and refreshes at the next
             * reconcile cycle (SecurePeerSession::poll rebuilds when either
             * gen advances) — i.e. read cut-off is eventually consistent, not mid-
             * session, because re-snapshotting mid-protocol would break the
             * in-flight reconcile (see SECURITY.md and transport/connection.cpp). */
            cap_ingest_delegations(s->engine, caps_in);
            rev_ingest(s->engine, revs_in);
            /* Bound reply amplification: a legit round emits at most ~kBuckets
             * descriptors per differing sub-range, so the reply never exceeds
             * ~kBuckets * (our element count). A peer flooding many whole-range
             * FPs can't force more than that — its excess descriptors are
             * dropped (only that malicious connection fails to converge). */
            /* VISIBLE count, never the base snapshot's: for a read-scoped
             * session the base also counts elements this peer may not read, and
             * sizing the cap off it would both leak the hidden count's magnitude
             * through reply volume and hand a restricted peer a larger
             * amplification budget than its own visible set justifies. */
            const size_t reply_cap = (s->size() + 1) * kBuckets + 64;
            for (auto &d : incoming) {
                if (reply.size() >= reply_cap) break;
                process_desc(s, d, reply);
            }
        }

        /* Queue this round's descriptors, then emit at most kMaxMessageBytes of
         * them — the rest drain on later steps, so no single message exceeds the
         * relay/UDP size bound (P0). When nothing is queued, we're done. */
        for (auto &d : reply) s->outq.push_back(std::move(d));
        if (s->outq.empty()) {
            *done = 1;
            return SYNC_OK;
        }

        /* Attach our delegation capabilities and revocations to the first message
         * we send.
         *
         * These two blocks are DELEGATION GOSSIP and are deliberately outside
         * read scoping, which governs the reconciliation element set (records,
         * their count, and every fingerprint derived from them). A blob here may
         * name a namespace this peer cannot read — a peer must learn delegations
         * to authorize records authored by keys it has not been told about, and
         * revocations must propagate replica-to-replica. Nothing about a denied
         * namespace's CONTENT may appear anywhere, and the scoped-view leak
         * assertions in tests/scoped_view_test.cpp compare the descriptor
         * section for exactly that reason (see descriptor_offset there, and
         * §3.5 of docs/IMPROVEMENT_PLAN.md). */
        std::vector<std::string> caps_out, revs_out;
        if (!s->sent_caps && s->engine->caps) {
            s->engine->caps->export_blobs(caps_out);
            s->engine->caps->export_rev_blobs(revs_out);
            s->sent_caps = true;
        }

        std::vector<Desc> batch;
        size_t used = 0;
        while (!s->outq.empty()) {
            size_t sz = desc_size(s->outq.front());
            if (!batch.empty() && used + sz > kMaxMessageBytes) break;
            used += sz;
            batch.push_back(std::move(s->outq.front()));
            s->outq.pop_front();
        }
        std::string msg = encode_message(batch, caps_out, revs_out);
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
