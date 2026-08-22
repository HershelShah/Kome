/* elemhash_test.cpp — Phase 2 (element-hash-cache) merge-gate tests.
 *
 * Each cell's reconciliation-element hash (SHA-256 of its canonical
 * encode_record bytes = encode_signing bytes + raw 64 B signature) is now
 * cached on the cell itself (Register::elem_hash / Entity::ex_hash,
 * engine.hpp) and maintained at every mutation point, so build_snapshot
 * copies it instead of re-hashing. A stale or wrongly-computed cached hash is
 * a *permanent, silent* wire-fingerprint divergence in Release builds (no
 * code path ever recomputes it from bytes again), so every oracle here is
 * Release-safe: nothing below relies on the #ifndef NDEBUG recompute-assert
 * in emit_element.
 *
 * Verification strategy (two ends that together pin the snapshot's elements,
 * since ReconSnapshot/Element are private to reconcile.cpp):
 *   - White-box cell walk: for every cell in e->ns, rebuild the canonical
 *     record via the SHARED change_from_entity/change_from_register helpers
 *     (codec.h — the same single construction build_snapshot encodes), then
 *     hash the bytes with a direct sync_engine_detail::sha256 call (NOT
 *     element_hash, so the check shares no hashing code with what it audits)
 *     and memcmp against the stored cell hash.
 *   - Black-box wire check: a real sync_session_begin + first step emits the
 *     whole-range fingerprint = SHA-256(LE64(count) || sum256(element
 *     hashes)) over the session's actual Element vector. The test recomputes
 *     that fingerprint from scratch (own varint parser, own 256-bit adder,
 *     fresh per-cell SHA-256) and compares bytes — any single wrong el.hash
 *     in the served snapshot breaks the sum.
 * White-box access to engine internals follows the storage_test /
 * gen_split_test precedent of including internal headers. */
#include "sync_engine.h"

#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <random>
#include <string>
#include <vector>

#include "cluster.hpp"
#include "codec.h"     /* change_from_* / element_hash / encode_record */
#include "engine.hpp"  /* white-box: ns map, Register/Entity, cached hashes */
#include "sha256.h"    /* independent fresh recompute */
#include "tempdir.hpp" /* MEMFS-safe under WASM (resilience_test pattern) */

namespace {

using cluster::B;
using synctest::TempDir;

/* ---- independent recompute helpers -------------------------------------- */

/* Fresh, from-scratch hash of an entity's existence element: the SHARED
 * change_from_entity construction (the contract anchor — exactly what
 * build_snapshot encodes), hashed by a direct sha256 call. */
ke::Hash256 fresh_entity_hash(const std::string &ns, const std::string &ent,
                              const ke::Entity &en) {
    std::string rec;
    ke::encode_record(ke::change_from_entity(ns, ent, en), rec);
    ke::Hash256 h;
    sync_engine_detail::sha256(rec.data(), rec.size(), h.data());
    return h;
}

ke::Hash256 fresh_register_hash(const std::string &ns, const std::string &ent,
                                const std::string &field,
                                const ke::Register &r) {
    std::string rec;
    ke::encode_record(ke::change_from_register(ns, ent, field, r), rec);
    ke::Hash256 h;
    sync_engine_detail::sha256(rec.data(), rec.size(), h.data());
    return h;
}

/* Walk EVERY cell in the engine and memcmp its stored cached hash against the
 * fresh recompute. An unasserted entity shell (a register arrived before any
 * existence record) emits no existence element, so its ex_hash is skipped —
 * mirroring build_snapshot's `if (ent.asserted())`. Returns the number of
 * cells checked so callers can assert non-vacuity. */
size_t verify_all_cell_hashes(sync_engine *e, const char *ctx) {
    size_t checked = 0;
    for (const auto &np : e->ns) {
        for (const auto &ep : np.second) {
            const ke::Entity &en = ep.second;
            if (en.asserted()) {
                ke::Hash256 f = fresh_entity_hash(np.first, ep.first, en);
                EXPECT_EQ(0, std::memcmp(f.data(), en.ex_hash.data(), 32))
                    << ctx << ": stale existence hash at ns=" << np.first
                    << " entity=" << ep.first;
                checked++;
            }
            for (const auto &fp : en.fields) {
                ke::Hash256 f =
                    fresh_register_hash(np.first, ep.first, fp.first, fp.second);
                EXPECT_EQ(0, std::memcmp(f.data(), fp.second.elem_hash.data(), 32))
                    << ctx << ": stale register hash at ns=" << np.first
                    << " entity=" << ep.first << " field=" << fp.first;
                checked++;
            }
        }
    }
    return checked;
}

/* ---- independent wire-fingerprint recompute ------------------------------ */

/* 256-bit little-endian add mod 2^256 — deliberately a byte-wise
 * implementation, independent of reconcile.cpp's 64-bit-limb add256 (same
 * math, different code, so a bug can't be shared). */
void add256_bytes(ke::Hash256 &acc, const ke::Hash256 &x) {
    unsigned carry = 0;
    for (int i = 0; i < 32; i++) {
        unsigned s = (unsigned)acc[i] + x[i] + carry;
        acc[i] = (uint8_t)s;
        carry = s >> 8;
    }
}

/* The whole-range fingerprint an initiator's first message must carry:
 * SHA-256(LE64(element count) || sum256 of per-element hashes), with every
 * per-element hash recomputed fresh here (never read from the cells). */
ke::Hash256 expected_first_fp(sync_engine *e) {
    ke::Hash256 sum{};
    uint64_t count = 0;
    for (const auto &np : e->ns) {
        for (const auto &ep : np.second) {
            const ke::Entity &en = ep.second;
            if (en.asserted()) {
                ke::Hash256 h = fresh_entity_hash(np.first, ep.first, en);
                add256_bytes(sum, h);
                count++;
            }
            for (const auto &fp : en.fields) {
                ke::Hash256 h =
                    fresh_register_hash(np.first, ep.first, fp.first, fp.second);
                add256_bytes(sum, h);
                count++;
            }
        }
    }
    uint8_t cnt[8];
    for (int i = 0; i < 8; i++) cnt[i] = (uint8_t)(count >> (8 * i));
    sync_engine_detail::Sha256 h;
    h.update(cnt, 8);
    h.update(sum.data(), sum.size());
    ke::Hash256 out;
    h.finish(out.data());
    return out;
}

/* Minimal LEB128 reader, local on purpose (the gen_split_test convention):
 * the test must not lean on the codec it is checking the wire against. */
bool read_varint(const uint8_t *&p, const uint8_t *end, uint64_t &v) {
    v = 0;
    for (int shift = 0; p < end && shift < 64; shift += 7) {
        uint8_t byte = *p++;
        v |= (uint64_t)(byte & 0x7f) << shift;
        if (!(byte & 0x80)) return true;
    }
    return false;
}

/* The initiator's first session message (caps/revs attached in front). */
std::string first_message(sync_engine *e) {
    sync_session *s = sync_session_begin(e, 1);
    EXPECT_NE(s, nullptr);
    if (!s) return "";
    uint8_t *o = nullptr;
    size_t ol = 0;
    int d = 0;
    EXPECT_SYNC_OK(sync_session_step(s, nullptr, 0, &o, &ol, &d));
    std::string m((const char *)o, ol);
    if (o) sync_free(o);
    sync_session_end(s);
    return m;
}

/* Parse an initiator first message — [caps][revs][descriptors] with exactly a
 * whole-range MODE_FP descriptor first: mode=0, lo=NEG_INF(0), hi=POS_INF(2),
 * then the 32 fingerprint bytes. false on any shape mismatch. */
bool extract_first_fp(const std::string &m, ke::Hash256 &fp) {
    const uint8_t *p = (const uint8_t *)m.data();
    const uint8_t *end = p + m.size();
    for (int block = 0; block < 2; block++) { /* caps, then revocations */
        uint64_t cnt = 0;
        if (!read_varint(p, end, cnt)) return false;
        for (uint64_t i = 0; i < cnt; i++) {
            uint64_t len = 0;
            if (!read_varint(p, end, len)) return false;
            if ((uint64_t)(end - p) < len) return false;
            p += len;
        }
    }
    uint64_t nd = 0;
    if (!read_varint(p, end, nd) || nd == 0) return false;
    if (p >= end || *p++ != 0) return false; /* MODE_FP */
    if (p >= end || *p++ != 0) return false; /* lo = NEG_INF */
    if (p >= end || *p++ != 2) return false; /* hi = POS_INF */
    if ((size_t)(end - p) < 32) return false;
    std::memcpy(fp.data(), p, 32);
    return true;
}

/* Sign-and-apply an EXISTENCE record with a chosen HLC/present bit (the
 * cluster::apply_register analogue for presence assertions). */
int apply_existence(sync_engine *e, const std::string &ns,
                    const std::string &ent, bool present, uint64_t physical,
                    uint32_t logical, uint32_t seed) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_EXISTENCE;
    c.ns = B(ns);
    c.ns_len = ns.size();
    c.entity = B(ent);
    c.entity_len = ent.size();
    c.causal_length = present ? 1 : 0;
    c.hlc.physical = physical;
    c.hlc.logical = logical;
    auto s = cluster::seed_from(seed);
    EXPECT_SYNC_OK(sync_change_sign(&c, s.data()));
    return sync_engine_apply(e, &c);
}

/* ---- every mutation kind maintains the cache ----------------------------- */
/* For EVERY kind of mutation the cell(s) it touches must end up holding a
 * hash byte-identical to a fresh recompute of the cell's canonical encoding —
 * and, after the whole sequence, EVERY cell in the engine (touched or not)
 * still verifies, so no path leaked a zero/stale hash anywhere. */
TEST(ElemHash, CachedHashMatchesWireHashEveryMutationKind) {
    sync_engine *e = cluster::make(0xE1);

    /* (1) fresh set: creates presence + register cells. */
    cluster::put(e, "ns", "ent", "f", "v1");
    EXPECT_EQ(verify_all_cell_hashes(e, "fresh set"), 2u);

    /* (2) overwrite: replaces the register (new hlc/value -> new hash). */
    ke::Hash256 rh1 = e->ns["ns"]["ent"].fields["f"].elem_hash;
    cluster::put(e, "ns", "ent", "f", "v2");
    EXPECT_NE(0, std::memcmp(rh1.data(),
                             e->ns["ns"]["ent"].fields["f"].elem_hash.data(), 32))
        << "overwrite did not refresh the register hash";
    EXPECT_EQ(verify_all_cell_hashes(e, "overwrite"), 2u);

    /* (3) erase_field (routes through set with an empty value). */
    cluster::put(e, "ns", "ent", "g", "gv");
    ASSERT_EQ(sync_engine_erase_field(e, B(std::string("ns")), 2,
                                      B(std::string("ent")), 3,
                                      B(std::string("g")), 1),
              SYNC_OK);
    EXPECT_TRUE(e->ns["ns"]["ent"].fields["g"].value.empty());
    EXPECT_EQ(verify_all_cell_hashes(e, "erase_field"), 3u);

    /* (4) delete: re-signs the presence register as a tombstone. */
    cluster::put(e, "ns", "gone", "f", "x");
    ke::Hash256 gh1 = e->ns["ns"]["gone"].ex_hash;
    cluster::del(e, "ns", "gone");
    EXPECT_NE(0, std::memcmp(gh1.data(), e->ns["ns"]["gone"].ex_hash.data(), 32))
        << "tombstone did not refresh the existence hash";
    verify_all_cell_hashes(e, "delete");

    /* (5)+(6) apply-existence accept and apply-register accept, both the
     * live and the tombstone shape, via another engine's exported signed
     * records (sync_engine_apply's verify-then-hash-then-commit path). */
    sync_engine *b = cluster::make(0xE2);
    cluster::put(b, "ns", "remote", "rf", "rv");
    cluster::put(b, "ns", "remote2", "rf", "rv2");
    cluster::del(b, "ns", "remote2");
    cluster::replicate(b, e);
    ASSERT_TRUE(cluster::exists(e, "ns", "remote"));
    verify_all_cell_hashes(e, "apply accept");

    /* (7) dominated apply: SYNC_OK no-op — cell bytes AND cached hash must be
     * untouched (an over-eager hash update here would be just as fatal as a
     * missed one, since the cell content did not change). */
    ke::Hash256 keep_r = e->ns["ns"]["ent"].fields["f"].elem_hash;
    ke::Hash256 keep_x = e->ns["ns"]["ent"].ex_hash;
    cluster::apply_register(e, "ns", "ent", "f", "stale", /*physical=*/1,
                            /*logical=*/0, 0xE3);
    ASSERT_EQ(apply_existence(e, "ns", "ent", false, 1, 0, 0xE3), SYNC_OK)
        << "dominated existence should be a clean no-op";
    EXPECT_EQ(cluster::get(e, "ns", "ent", "f"), "v2");
    EXPECT_TRUE(cluster::exists(e, "ns", "ent"));
    EXPECT_EQ(0, std::memcmp(keep_r.data(),
                             e->ns["ns"]["ent"].fields["f"].elem_hash.data(), 32))
        << "dominated register apply touched the cached hash";
    EXPECT_EQ(0, std::memcmp(keep_x.data(), e->ns["ns"]["ent"].ex_hash.data(), 32))
        << "dominated existence apply touched the cached hash";
    verify_all_cell_hashes(e, "dominated no-op");

    /* (8) blob put/erase (route through set/delete: chunk + manifest cells,
     * then zeroed payloads + tombstones). ~70 KB -> 3 chunk entities. */
    std::vector<uint8_t> data(70000);
    uint32_t x = 0xBEEF;
    for (auto &d : data) {
        x ^= x << 13; x ^= x >> 17; x ^= x << 5;
        d = (uint8_t)x;
    }
    uint8_t id[SYNC_BLOB_ID_LEN];
    ASSERT_EQ(sync_blob_put(e, B(std::string("bl")), 2, data.data(), data.size(),
                            id),
              SYNC_OK);
    verify_all_cell_hashes(e, "blob put");
    ASSERT_EQ(sync_blob_erase(e, B(std::string("bl")), 2, id), SYNC_OK);

    /* Final: EVERY cell in the engine, not just the touched ones. */
    size_t n = verify_all_cell_hashes(e, "final walk");
    EXPECT_GE(n, 14u) << "walk was vacuous — expected the full cell population";

    sync_engine_destroy(e);
    sync_engine_destroy(b);
}

/* ---- one set touches two cells; erase touches exactly one ---------------- */
TEST(ElemHash, TwoCellSetUpdatesBothHashes) {
    sync_engine *e = cluster::make(0xE5);

    /* One set on a fresh entity signs BOTH a presence assertion and the
     * register — both cached hashes must be correct immediately. */
    cluster::put(e, "ns", "e1", "f", "v");
    ke::Entity &en = e->ns["ns"]["e1"];
    ASSERT_TRUE(en.asserted());
    ASSERT_TRUE(en.present());
    ke::Hash256 ph = en.ex_hash;
    ke::Hash256 rh = en.fields["f"].elem_hash;
    EXPECT_EQ(0, std::memcmp(ph.data(),
                             fresh_entity_hash("ns", "e1", en).data(), 32))
        << "presence hash wrong after the two-cell set";
    EXPECT_EQ(0, std::memcmp(
                     rh.data(),
                     fresh_register_hash("ns", "e1", "f", en.fields["f"]).data(),
                     32))
        << "register hash wrong after the two-cell set";

    /* erase_field rewrites only the register: its hash must change (and match
     * a fresh recompute of the now-empty value), while the presence cell —
     * untouched by the erase — keeps its exact hash bytes. */
    ASSERT_EQ(sync_engine_erase_field(e, B(std::string("ns")), 2,
                                      B(std::string("e1")), 2,
                                      B(std::string("f")), 1),
              SYNC_OK);
    EXPECT_TRUE(en.fields["f"].value.empty());
    EXPECT_NE(0, std::memcmp(rh.data(), en.fields["f"].elem_hash.data(), 32))
        << "erase_field did not refresh the register hash";
    EXPECT_EQ(0, std::memcmp(
                     en.fields["f"].elem_hash.data(),
                     fresh_register_hash("ns", "e1", "f", en.fields["f"]).data(),
                     32));
    EXPECT_EQ(0, std::memcmp(ph.data(), en.ex_hash.data(), 32))
        << "erase_field must leave the presence hash untouched";
    EXPECT_EQ(0, std::memcmp(ph.data(),
                             fresh_entity_hash("ns", "e1", en).data(), 32));

    sync_engine_destroy(e);
}

/* ---- the phase's real safety net: randomized differential oracle --------- */
/* A few hundred randomized ops across every mutation family — local sets /
 * deletes / erase_field, records exported from a second engine (including
 * dominated and tying re-deliveries), crafted applies at chosen HLCs, blob
 * put + erase, and disk reopens of the store-backed engine — then every cell
 * hash is verified against a fresh recompute AND a real session's first
 * fingerprint is compared against a from-scratch rebuild. Fixed seed for
 * reproducibility. Release-safe: all recomputes are the test's own. */
TEST(ElemHash, RandomizedDifferentialOracle) {
    TempDir dir;
    std::string db = dir.file("oracle.db");
    auto site = cluster::seed_from(0xD1);

    sync_engine *e = sync_engine_open(db.c_str(), site.data());
    ASSERT_NE(e, nullptr);
    sync_engine *src = cluster::make(0xD2); /* record feeder */

    std::mt19937 rng(0xC0FFEE); /* fixed seed: reproducible */
    const char *nss[] = {"a", "b"};
    std::vector<std::array<uint8_t, SYNC_BLOB_ID_LEN>> blob_ids;
    int n_set = 0, n_del = 0, n_erase = 0, n_src = 0, n_craft = 0, n_bput = 0,
        n_berase = 0, n_reopen = 0;

    const int kOps = 300;
    for (int i = 0; i < kOps; i++) {
        std::string ns = nss[rng() % 2];
        std::string ent = "e" + std::to_string(rng() % 12);
        std::string field = "f" + std::to_string(rng() % 3);
        switch (rng() % 12) {
        case 0: case 1: case 2: case 3: { /* local set */
            cluster::put(e, ns, ent, field, "v" + std::to_string(rng() % 50));
            n_set++;
            break;
        }
        case 4: case 5: { /* feeder write (exported/applied below) */
            cluster::put(src, ns, ent, field, "s" + std::to_string(rng() % 50));
            n_src++;
            break;
        }
        case 6: { /* delete (may be an absent-entity no-op) */
            cluster::del(e, ns, ent);
            n_del++;
            break;
        }
        case 7: { /* erase_field (NOTFOUND on absent/tombstoned is fine) */
            int rc = sync_engine_erase_field(e, B(ns), ns.size(), B(ent),
                                             ent.size(), B(field), field.size());
            ASSERT_TRUE(rc == SYNC_OK || rc == SYNC_ERR_NOTFOUND)
                << "erase_field rc=" << rc;
            n_erase++;
            break;
        }
        case 8: { /* crafted signed record at a chosen HLC: wins or loses
                   * depending on the cell's current state; a low HLC against a
                   * live cell is a dominated no-op, a register on a fresh
                   * entity creates an unasserted shell (register-before-
                   * existence). */
            cluster::apply_register(e, ns, ent, field,
                                    "c" + std::to_string(rng() % 50),
                                    /*physical=*/1 + rng() % 20000,
                                    /*logical=*/rng() % 4, 0xD3);
            n_craft++;
            break;
        }
        case 9: { /* blob put (1..3000 bytes: manifest + 1 chunk) */
            std::vector<uint8_t> data(1 + rng() % 3000);
            for (auto &d : data) d = (uint8_t)rng();
            std::array<uint8_t, SYNC_BLOB_ID_LEN> id{};
            ASSERT_EQ(sync_blob_put(e, B(std::string("bl")), 2, data.data(),
                                    data.size(), id.data()),
                      SYNC_OK);
            blob_ids.push_back(id);
            n_bput++;
            break;
        }
        case 10: { /* blob erase (double-erase NOTFOUND is fine) */
            if (!blob_ids.empty()) {
                auto &id = blob_ids[rng() % blob_ids.size()];
                int rc = sync_blob_erase(e, B(std::string("bl")), 2, id.data());
                ASSERT_TRUE(rc == SYNC_OK || rc == SYNC_ERR_NOTFOUND)
                    << "blob erase rc=" << rc;
                n_berase++;
            }
            break;
        }
        case 11: { /* reopen from disk: the load path re-verifies and
                   * re-hashes every persisted record */
            if (n_reopen < 6) {
                sync_engine_destroy(e);
                e = sync_engine_open(db.c_str(), site.data());
                ASSERT_NE(e, nullptr) << "reopen " << n_reopen << " failed";
                n_reopen++;
            }
            break;
        }
        }
        /* Periodic full export/apply: later rounds re-deliver every earlier
         * record, so this batch is dense with dominated and tying records. */
        if (i % 60 == 59) cluster::replicate(src, e);
    }

    /* Guaranteed dominated + tying coverage, independent of the rng draw:
     * the same signed record twice (the second ties register_cmp exactly and
     * must be a no-op), then a strictly older one (dominated). */
    cluster::apply_register(e, "a", "dup", "f", "dv", 7, 3, 0xD3);
    cluster::apply_register(e, "a", "dup", "f", "dv", 7, 3, 0xD3); /* tie */
    cluster::apply_register(e, "a", "dup", "f", "old", 1, 0, 0xD3); /* dominated */
    EXPECT_EQ(e->ns["a"]["dup"].fields["f"].value, "dv");

    /* Non-vacuity: with the fixed seed every op family actually ran. */
    EXPECT_GT(n_set, 0);    EXPECT_GT(n_del, 0);
    EXPECT_GT(n_erase, 0);  EXPECT_GT(n_src, 0);
    EXPECT_GT(n_craft, 0);  EXPECT_GT(n_bput, 0);
    EXPECT_GT(n_berase, 0); EXPECT_GT(n_reopen, 0);

    /* Full re-delivery (all dominated/tying) + a real reconcile session both
     * ways. */
    cluster::replicate(src, e);
    cluster::sync2(src, e);
    EXPECT_EQ(cluster::digest(e), cluster::digest(src));

    /* Cold-peer bulk sync: a fresh engine against e's full state. The empty
     * peer answers the whole-range fingerprint with an (empty) LEAF, so e
     * replies with HAVE descriptors packed to kMaxMessageBytes — dozens to
     * hundreds of records per apply_records call, which is the ONLY route
     * into the batched parallel-verify path (>= kParallelVerifyMin) where
     * apply_change runs with already_verified=true and installs the element
     * hash the verify worker precomputed from its signing buffer
     * (change_sig_ok's streaming element_hash — the incremental sync2 above
     * never reaches it: its subdivided leaf ranges carry only a couple of
     * records each). */
    sync_engine *cold = cluster::make(0xD4);
    cluster::sync2(e, cold);
    EXPECT_EQ(cluster::digest(cold), cluster::digest(e));

    /* Oracle 1: every cell's cached hash matches a fresh recompute. */
    size_t n_e = verify_all_cell_hashes(e, "store-backed engine");
    size_t n_s = verify_all_cell_hashes(src, "feeder engine");
    size_t n_c = verify_all_cell_hashes(cold, "cold bulk-sync engine");
    EXPECT_GT(n_e, 40u) << "oracle walk vacuous (too few cells)";
    EXPECT_GT(n_s, 40u);
    EXPECT_GT(n_c, 40u);

    /* Oracle 2: a REAL session's first wire fingerprint is byte-identical to
     * a from-scratch rebuild (fresh per-element hashes, own 256-bit sum). */
    for (sync_engine *eng : {e, src, cold}) {
        std::string m = first_message(eng);
        ASSERT_FALSE(m.empty());
        ke::Hash256 got{};
        ASSERT_TRUE(extract_first_fp(m, got)) << "unexpected first-message shape";
        ke::Hash256 want = expected_first_fp(eng);
        EXPECT_EQ(0, std::memcmp(got.data(), want.data(), 32))
            << "served fingerprint diverges from the from-scratch rebuild";
    }

    sync_engine_destroy(e);
    sync_engine_destroy(src);
    sync_engine_destroy(cold);
}

/* ---- Release-safe cross-path oracle -------------------------------------- */
/* Build the SAME state three ways under ONE identity/seed:
 *   (a) local writes            (author_sign streaming-hash path),
 *   (b) applying (a)'s exported signed records
 *                               (verify_change streaming-hash path),
 *   (c) a durable engine fed the same records, closed, reopened from disk
 *                               (verify_and_merge load-path hashing +
 *                                merge_record install),
 * and assert the first sync_session_step message is BYTE-IDENTICAL across all
 * three. Same initiator role everywhere, nothing stripped: the engines share
 * one identity and one granted capability blob, so the leading caps/revs
 * blocks are equal by construction and the comparison covers the whole
 * message. Divergence on ANY of the three mutation-time hashing paths (or in
 * the load path) changes that message's fingerprint bytes in Release, where
 * no debug assert exists to catch it first. */
TEST(ElemHash, CrossPathOracleFirstMessageByteIdentical) {
    TempDir dir;
    std::string db = dir.file("xpath.db");
    auto seed = cluster::seed_from(0xAB); /* the ONE identity for all three */

    /* (a) local writes. Mint one root capability and grant the same blob to
     * all three engines so the message's caps block is engaged and equal. */
    sync_engine *a = sync_engine_create(seed.data());
    ASSERT_NE(a, nullptr);
    sync_capability *root =
        sync_capability_root(a, "cx", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    ASSERT_NE(root, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(a, root));
    cluster::put(a, "cx", "e1", "f", "v1");
    cluster::put(a, "cx", "e1", "g", "v2");
    cluster::put(a, "open", "o1", "f", "w");
    cluster::put(a, "open", "o2", "f", "w2");
    cluster::del(a, "open", "o2"); /* tombstone */
    ASSERT_EQ(sync_engine_erase_field(a, B(std::string("cx")), 2,
                                      B(std::string("e1")), 2,
                                      B(std::string("g")), 1),
              SYNC_OK); /* empty-value register */

    /* (b) same identity, state built by applying (a)'s exported records. */
    sync_engine *b = sync_engine_create(seed.data());
    ASSERT_NE(b, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(b, root));
    cluster::replicate(a, b);

    /* (c) durable engine: same records applied, then close + reopen so the
     * state (and every cached hash) is rebuilt by the storage load path. */
    sync_engine *c = sync_engine_open(db.c_str(), seed.data());
    ASSERT_NE(c, nullptr);
    ASSERT_SYNC_OK(sync_engine_grant(c, root));
    cluster::replicate(a, c);
    sync_engine_destroy(c);
    c = sync_engine_open(db.c_str(), seed.data());
    ASSERT_NE(c, nullptr);

    /* Precondition (aids debugging a failure): the three states agree. */
    cluster::Digest d0 = cluster::digest(a);
    EXPECT_EQ(cluster::digest(b), d0);
    EXPECT_EQ(cluster::digest(c), d0);

    std::string ma = first_message(a);
    std::string mb = first_message(b);
    std::string mc = first_message(c);
    ASSERT_FALSE(ma.empty());

    /* Non-vacuity: the message really carries a caps block and a whole-range
     * fingerprint over a non-empty element set. */
    {
        const uint8_t *p = (const uint8_t *)ma.data();
        uint64_t ncaps = 0;
        ASSERT_TRUE(read_varint(p, p + ma.size(), ncaps));
        EXPECT_GE(ncaps, 1u) << "caps block empty — grant did not attach";
        ke::Hash256 fp{};
        ASSERT_TRUE(extract_first_fp(ma, fp));
        EXPECT_NE(fp, ke::Hash256{});
    }

    EXPECT_EQ(ma, mb)
        << "local-write and apply-path constructions serve different bytes";
    EXPECT_EQ(ma, mc)
        << "local-write and disk-reload constructions serve different bytes";

    sync_capability_free(root);
    sync_engine_destroy(a);
    sync_engine_destroy(b);
    sync_engine_destroy(c);
}

/* ---- converged peers quiesce immediately --------------------------------- */
/* DIRECTIONAL oracle only, deliberately narrow: two engines holding the same
 * records must agree on the whole-range fingerprint in the very first
 * exchange, so the responder replies empty-and-done to the initiator's
 * opening FP descriptor. This catches ASYMMETRIC divergence (the two engines'
 * mutation paths hashing the same record differently). It CANNOT catch a
 * systematically wrong hash formula: converged peers agree on the (equally
 * wrong) fingerprints and never enter MODE_LEAF — the only place the true
 * wire-bytes hash is compared — so both sides still quiesce. The
 * CrossPathOracle and RandomizedDifferentialOracle above cover the
 * systematic direction. */
TEST(ElemHash, InSyncPeersQuiesceInOneRound) {
    sync_engine *a = cluster::make(0xF1);
    sync_engine *b = cluster::make(0xF2);
    for (int i = 0; i < 8; i++) {
        cluster::put(a, "ns", "a" + std::to_string(i), "f", "va" + std::to_string(i));
        cluster::put(b, "ns", "b" + std::to_string(i), "f", "vb" + std::to_string(i));
    }
    cluster::del(a, "ns", "a0");
    cluster::replicate(a, b);
    cluster::replicate(b, a);
    ASSERT_EQ(cluster::digest(a), cluster::digest(b)) << "peers not converged";

    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    ASSERT_NE(sa, nullptr);
    ASSERT_NE(sb, nullptr);

    uint8_t *o = nullptr;
    size_t ol = 0;
    int done = 0;
    ASSERT_SYNC_OK(sync_session_step(sa, nullptr, 0, &o, &ol, &done));
    ASSERT_GT(ol, 0u) << "initiator sent no opening fingerprint";
    std::vector<uint8_t> m1(o, o + ol);
    if (o) sync_free(o);

    /* The responder's very first step: fingerprints match, so it must have
     * nothing to send and be done — one round, zero record exchange. */
    o = nullptr; ol = 0; done = 0;
    ASSERT_SYNC_OK(sync_session_step(sb, m1.data(), m1.size(), &o, &ol, &done));
    EXPECT_EQ(ol, 0u) << "converged responder produced traffic: cached element "
                         "hashes disagree between the two engines";
    EXPECT_EQ(done, 1);
    if (o) sync_free(o);

    /* And the initiator, fed nothing back, is done too. */
    o = nullptr; ol = 0; done = 0;
    ASSERT_SYNC_OK(sync_session_step(sa, nullptr, 0, &o, &ol, &done));
    EXPECT_EQ(ol, 0u);
    EXPECT_EQ(done, 1);
    if (o) sync_free(o);

    sync_session_end(sa);
    sync_session_end(sb);
    sync_engine_destroy(a);
    sync_engine_destroy(b);
}

} // namespace
