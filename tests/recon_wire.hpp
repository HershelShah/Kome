/* recon_wire.hpp — a minimal builder for reconcile *session messages*, for
 * tests that must hand the engine a message no honest peer would send.
 *
 * Why this exists (improvement plan §3.5 fix 4): the real encoders
 * (`encode_message`/`encode_desc`/`encode_bound`) and the `Desc`/`Bound` types
 * live in an anonymous namespace inside `src/reconcile.cpp`, so they have
 * internal linkage and no test can call them; and no other test file has a
 * reconcile-message builder to borrow (hardening_test.cpp mutates *record*
 * bytes via sync_change_encode — a different wire format entirely). An
 * adversarial test that hand-rolls the bytes inline would silently stop
 * exercising anything the day the wire format moves.
 *
 * The divergence guard: every message this builder produces is fed through the
 * REAL decoder before it is returned — `sync_session_step` on a throwaway
 * engine calls `decode_message`, and a message the decoder rejects fails the
 * test at the point it was built. That pins the framing (block order, varint
 * counts, bound layout, descriptor payloads) against the shipping decoder.
 *
 * What the guard can and cannot see, stated precisely so it is not read as more
 * than it is:
 *   - CAUGHT: truncation, a reordered or resized field, an inserted byte, a new
 *     field in the middle of a bound or descriptor — anything that makes the
 *     shipping decoder run off the end or misread a length.
 *   - CAUGHT (only because `decode_message` requires `p == end`, i.e. canonical
 *     framing): a field APPENDED after the last descriptor, and a block count
 *     this builder under-reports — both leave trailing bytes. Remove that check
 *     from reconcile.cpp and this guard goes blind in exactly those two
 *     directions, which is the drift a builder is most likely to accumulate.
 *   - NOT CAUGHT: semantics. A well-formed message that means something other
 *     than the caller intended passes, so a test relying on a descriptor doing
 *     something (eliciting a reply, covering a range) must still assert that
 *     observable directly. */
#ifndef SYNC_TEST_RECON_WIRE_HPP
#define SYNC_TEST_RECON_WIRE_HPP

#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <string>
#include <vector>

#include "codec.h" /* ke::put_varint — the same varint the real encoder emits */

namespace recon_wire {

/* Mirrors reconcile.cpp's Mode. */
enum Mode : uint8_t { MODE_FP = 0, MODE_LEAF = 1, MODE_HAVE = 2 };

/* Mirrors reconcile.cpp's SortKey. Elements sort by
 * (ns, entity, existence-before-registers, field). */
struct Key {
    std::string ns, entity, field;
    bool        existence = false;
};

/* Mirrors reconcile.cpp's Bound. */
struct Bound {
    enum Type : uint8_t { NEG_INF = 0, KEY = 1, POS_INF = 2 } type = NEG_INF;
    Key key;

    static Bound neg() { return Bound{}; }
    static Bound pos() {
        Bound b;
        b.type = POS_INF;
        return b;
    }
    static Bound at(const std::string &ns, const std::string &entity,
                    bool existence, const std::string &field) {
        Bound b;
        b.type = KEY;
        b.key.ns = ns;
        b.key.entity = entity;
        b.key.existence = existence;
        b.key.field = field;
        return b;
    }
    /* The first possible key in `ns` (existence element of the empty entity):
     * a lower bound that covers the whole namespace. */
    static Bound ns_start(const std::string &ns) {
        return at(ns, "", true, "");
    }
};

/* Mirrors reconcile.cpp's Desc. */
struct Desc {
    uint8_t                  mode = MODE_FP;
    Bound                    lo, hi;
    std::array<uint8_t, 32>  fp{};
    std::vector<std::string> records; /* LEAF/HAVE only */
};

inline void encode_bound(std::string &o, const Bound &b) {
    o.push_back((char)b.type);
    if (b.type == Bound::KEY) {
        ke::put_varint(o, b.key.ns.size());
        o.append(b.key.ns);
        ke::put_varint(o, b.key.entity.size());
        o.append(b.key.entity);
        o.push_back((char)(b.key.existence ? 1 : 0));
        ke::put_varint(o, b.key.field.size());
        o.append(b.key.field);
    }
}

inline void encode_desc(std::string &o, const Desc &d) {
    o.push_back((char)d.mode);
    encode_bound(o, d.lo);
    encode_bound(o, d.hi);
    if (d.mode == MODE_FP) {
        o.append((const char *)d.fp.data(), d.fp.size());
    } else {
        ke::put_varint(o, d.records.size());
        for (const auto &r : d.records) {
            ke::put_varint(o, r.size());
            o.append(r);
        }
    }
}

/* True if the shipping decoder accepts `msg` as a well-formed session message.
 * Runs it through a throwaway engine so the caller's engines see no side
 * effects: a responder session decodes the message before doing anything with
 * it, and only a decode failure surfaces as SYNC_ERR_INVALID. */
inline bool decoder_accepts(const std::string &msg) {
    std::array<uint8_t, SYNC_SEED_LEN> seed{};
    for (auto &b : seed) b = 0xD7; /* fixed: this engine holds no state */
    sync_engine *tmp = sync_engine_create(seed.data());
    if (!tmp) return false;
    sync_session *s = sync_session_begin(tmp, /*as_initiator=*/0);
    if (!s) {
        sync_engine_destroy(tmp);
        return false;
    }
    uint8_t *out = nullptr;
    size_t   outlen = 0;
    int      done = 0;
    int rc = sync_session_step(s, (const uint8_t *)msg.data(), msg.size(), &out,
                               &outlen, &done);
    if (out) sync_free(out);
    sync_session_end(s);
    sync_engine_destroy(tmp);
    return rc != SYNC_ERR_INVALID;
}

/* Wire form: [caps][revocations][descriptors] (reconcile.cpp encode_message).
 * Fails the calling test if the shipping decoder would reject the result. */
inline std::string message(const std::vector<Desc>        &descs,
                           const std::vector<std::string> &caps = {},
                           const std::vector<std::string> &revs = {}) {
    std::string o;
    ke::put_varint(o, caps.size());
    for (const auto &c : caps) {
        ke::put_varint(o, c.size());
        o += c;
    }
    ke::put_varint(o, revs.size());
    for (const auto &r : revs) {
        ke::put_varint(o, r.size());
        o += r;
    }
    ke::put_varint(o, descs.size());
    for (const auto &d : descs) encode_desc(o, d);
    EXPECT_TRUE(decoder_accepts(o))
        << "recon_wire built a message the shipping decoder rejects: the "
           "builder has diverged from reconcile.cpp's wire format";
    return o;
}

/* One FP descriptor over [lo, hi) whose fingerprint is deliberately wrong, so a
 * responder must treat the range as differing and answer with real content. */
inline Desc mismatching_fp(const Bound &lo, const Bound &hi) {
    Desc d;
    d.mode = MODE_FP;
    d.lo = lo;
    d.hi = hi;
    d.fp.fill(0xAB); /* no empty-or-otherwise range hashes to this */
    return d;
}

/* An empty LEAF over [lo, hi): "I have nothing in this range", which asks the
 * responder to reply with everything it holds there. */
inline Desc empty_leaf(const Bound &lo, const Bound &hi) {
    Desc d;
    d.mode = MODE_LEAF;
    d.lo = lo;
    d.hi = hi;
    return d;
}

} // namespace recon_wire

#endif /* SYNC_TEST_RECON_WIRE_HPP */
