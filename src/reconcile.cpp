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
        /* Each record needs >=1 byte, so a count beyond the remaining buffer is
         * bogus — reject before reserving/allocating (allocation-DoS guard). */
        if (cnt > (uint64_t)(end - p)) return false;
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
    if (nc > (uint64_t)(end - p)) return false; /* each cap >=1 byte */
    for (uint64_t i = 0; i < nc; i++) {
        uint64_t cl = 0;
        if (!get_varint(p, end, cl)) return false;
        if ((uint64_t)(end - p) < cl) return false;
        caps.emplace_back((const char *)p, (size_t)cl);
        p += cl;
    }
    uint64_t n = 0;
    if (!get_varint(p, end, n)) return false;
    if (n > (uint64_t)(end - p)) return false; /* each descriptor >=1 byte */
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
    uint64_t     steps = 0;          /* processed-message counter (DoS bound) */

    /* Descriptors produced but not yet sent: a step emits at most
     * kMaxMessageBytes of them and keeps the rest here for the next round, so no
     * single message exceeds the relay/UDP size bound. */
    std::deque<Desc> outq;

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

#ifndef __EMSCRIPTEN__
/* Verify a decoded record's signature. Pure (no engine/global state), so it is
 * safe to run concurrently across worker threads. (Only the parallel path uses
 * it; the serial path verifies inside apply_change.) */
bool change_sig_ok(const sync_change &c) {
    std::string signing;
    encode_signing(c, signing);
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
        std::vector<std::thread> pool;
        const size_t chunk = (n + workers - 1) / workers;
        for (unsigned w = 0; w < workers; w++) {
            size_t lo = (size_t)w * chunk, hi = std::min(n, lo + chunk);
            if (lo >= hi) break;
            pool.emplace_back([&decoded, &ok, lo, hi] {
                /* An exception escaping a std::thread calls std::terminate;
                 * encode_signing can throw bad_alloc on a huge record. Treat
                 * any failure as not-verified (fail-closed). */
                try {
                    for (size_t i = lo; i < hi; i++)
                        ok[i] = change_sig_ok(decoded[i].view()) ? 1 : 0;
                } catch (...) {
                }
            });
        }
        for (auto &t : pool) t.join();
        for (size_t i = 0; i < n; i++) {
            if (!ok[i]) continue;
            sync_change c = decoded[i].view();
            apply_change(e, &c, /*already_verified=*/true);
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
            std::string kk = serialize_key(s->snap()[i].key);
            auto it = peer.find(kk);
            if (it != peer.end() && it->second == s->snap()[i].hash) continue;
            const std::string &rec = s->snap()[i].bytes;
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
 * change borrows the engine's strings; only the Element's key/bytes are copied. */
void emit_element(const sync_change &c, const std::string &nsk,
                  const std::string &entk, const std::string &fk, bool existence,
                  std::vector<Element> &out) {
    Element el;
    el.key.ns = nsk;
    el.key.entity = entk;
    el.key.existence = existence;
    if (!existence) el.key.field = fk;
    encode_record(c, el.bytes);
    sha256(el.bytes.data(), el.bytes.size(), el.hash.data());
    out.push_back(std::move(el));
}

/* Snapshot the engine as sorted elements with per-element hashes. Records in
 * namespaces peer may not read are excluded (peer == NULL == no scoping).
 *
 * Iterates the engine's maps directly rather than via sync_engine_export — the
 * export path mallocs an N-element array plus four field copies per record and
 * then we free it all (profiled at ~55% of the build). Here each change borrows
 * the map's strings and is encoded straight into its Element. */
bool build_snapshot(sync_engine *e, const uint8_t *peer,
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
        if (peer && !cap_authorize_read(e, peer, nsk))
            continue; /* whole namespace read-scoped out */
        for (const auto &ep : np.second) {
            const std::string &entk = ep.first;
            const Entity &ent = ep.second;

            sync_change c;
            std::memset(&c, 0, sizeof c);
            c.ns = (const uint8_t *)nsk.data(); c.ns_len = nsk.size();
            c.entity = (const uint8_t *)entk.data(); c.entity_len = entk.size();

            if (ent.asserted()) { /* existence element (present or tombstone) */
                c.kind = SYNC_CHANGE_EXISTENCE;
                c.causal_length = ent.present_v ? 1 : 0; /* present bit */
                c.hlc.physical = ent.presence_hlc.physical;
                c.hlc.logical = ent.presence_hlc.logical;
                std::memcpy(c.author, ent.ex_author.data(), SYNC_PUBKEY_LEN);
                std::memcpy(c.signature, ent.ex_sig.data(), SYNC_SIG_LEN);
                emit_element(c, nsk, entk, kEmpty, true, out);
            }
            for (const auto &fp : ent.fields) { /* register element per field */
                const std::string &fk = fp.first;
                const Register &r = fp.second;
                c.kind = SYNC_CHANGE_REGISTER;
                c.causal_length = 0;
                c.field = (const uint8_t *)fk.data(); c.field_len = fk.size();
                c.value = (const uint8_t *)r.value.data();
                c.value_len = r.value.size();
                c.hlc.physical = r.hlc.physical;
                c.hlc.logical = r.hlc.logical;
                std::memcpy(c.author, r.author.data(), SYNC_PUBKEY_LEN);
                std::memcpy(c.signature, r.sig.data(), SYNC_SIG_LEN);
                emit_element(c, nsk, entk, fk, false, out);
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

/* Build a fresh snapshot stamped at the current state_gen — full when peer==NULL,
 * else read-scoped to peer. NULL on build failure. Shared by the unscoped
 * (ensure_cache) and per-peer (ensure_scoped_cache) paths. */
std::shared_ptr<ReconSnapshot> build_filtered(sync_engine *e, const uint8_t *peer) {
    auto snap = std::make_shared<ReconSnapshot>();
    snap->gen = e->state_gen;
    if (!build_snapshot(e, peer, snap->snap)) return nullptr;
    build_prefix(snap->snap, snap->prefix);
    return snap;
}

/* The engine's cached full snapshot, rebuilt only when state_gen advanced since
 * it was taken. Returns NULL on build failure. */
std::shared_ptr<const ReconSnapshot> ensure_cache(sync_engine *e) {
    if (e->recon_cache && e->recon_cache->gen == e->state_gen)
        return e->recon_cache;
    auto snap = build_filtered(e, nullptr);
    if (snap) e->recon_cache = snap;
    return snap;
}

/* The per-peer read-scoped snapshot, cached on the engine (engine.hpp
 * scoped_cache) the same way ensure_cache caches the unscoped one: rebuilt only
 * when state_gen advanced since it was taken — which now includes capability
 * grants/ingest (capability.cpp). A converged, idle gossip link therefore stops
 * re-encoding and re-hashing every record each cycle. Snapshots whose scope is
 * time-bound (a finite-expiry read cap) are returned but NOT cached, so capability
 * expiry stays exact (that peer rebuilds each cycle, as before). Returns NULL on
 * build failure. */
/* Upper bound on cached per-peer scoped snapshots. Cleared wholesale on every
 * state change, so this only matters for a burst of distinct restricted peers
 * between writes; fully-open peers cache a cheap shared alias, so the expensive
 * (distinct O(N) snapshot) entries are the few genuinely read-restricted peers. */
constexpr size_t kMaxScopedCache = 256;

std::shared_ptr<const ReconSnapshot> ensure_scoped_cache(sync_engine *e,
                                                         const uint8_t *peer) {
    /* No capability system engaged → every namespace is open → the scoped
     * snapshot is exactly the unscoped one. */
    if (!e->caps) return ensure_cache(e);

    /* Cache-first: a hit is one map lookup and skips the per-namespace
     * authorization pre-scan below — so a converged, idle link costs O(1) per
     * cycle regardless of how the peer is scoped. The cache holds both restricted
     * peers (a distinct filtered snapshot) and fully-open peers (an alias to the
     * shared unscoped snapshot). It is cleared whenever engine state advances —
     * writes, applies, and capability grants/ingest all bump state_gen. */
    if (e->scoped_cache_gen != e->state_gen) {
        e->scoped_cache.clear();
        e->scoped_cache_gen = e->state_gen;
    }
    std::string key((const char *)peer, SYNC_PUBKEY_LEN);
    auto it = e->scoped_cache.find(key);
    if (it != e->scoped_cache.end()) return it->second;

    /* Miss: classify the peer's scope. The O(namespaces) pre-scan (each
     * cap_authorize_read is O(caps)) runs only here, not on cache hits.
     *   fully_open  -> snapshot equals the unscoped one; alias the shared cache.
     *   time_bound  -> scope depends on a finite-expiry cap; rebuild every cycle
     *                  (never cached) so expiry stays exact. */
    /* Scan EVERY namespace (no early break): a readable, time-bound namespace
     * sorted after a denied one must still set time_bound, or its scope would be
     * wrongly cached and served past the cap's expiry. Only readable namespaces
     * (those that end up in the snapshot) contribute time_bound. */
    bool fully_open = true, time_bound = false;
    for (const auto &np : e->ns) {
        bool tb = false;
        if (!cap_authorize_read(e, peer, np.first, &tb)) fully_open = false;
        else time_bound = time_bound || tb;
    }

    if (time_bound) return build_filtered(e, peer); /* exact expiry: never cache */

    std::shared_ptr<const ReconSnapshot> snap =
        fully_open ? ensure_cache(e) : build_filtered(e, peer);
    if (snap && e->scoped_cache.size() < kMaxScopedCache)
        e->scoped_cache[key] = snap;
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
        s->ss = ensure_scoped_cache(e, peer);
    } else {
        s->ss = ensure_cache(e);
    }
    if (!s->ss) { delete s; return nullptr; }
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
            /* Bound reply amplification: a legit round emits at most ~kBuckets
             * descriptors per differing sub-range, so the reply never exceeds
             * ~kBuckets * (our element count). A peer flooding many whole-range
             * FPs can't force more than that — its excess descriptors are
             * dropped (only that malicious connection fails to converge). */
            const size_t reply_cap = (s->snap().size() + 1) * kBuckets + 64;
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

        /* Attach our delegation capabilities to the first message we send. */
        std::vector<std::string> caps_out;
        if (!s->sent_caps && s->engine->caps) {
            s->engine->caps->export_blobs(caps_out);
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
        std::string msg = encode_message(batch, caps_out);
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
