/* bench_main.cpp — GoogleBenchmark microbenchmarks over the engine's hot paths.
 *
 * Chapter 1 of the optimization story: a measured baseline so later changes are
 * judged, not guessed. Covers the crypto primitives, the record codec, the
 * engine ops (set/apply/get/export/digest), and range reconciliation — the
 * scaling cases use Range()+Complexity() to report big-O in N.
 *
 *   cmake -B build -DCMAKE_BUILD_TYPE=Release -DSYNC_BENCH=ON
 *   cmake --build build --target bench
 *   ./build/bench                          # --benchmark_format=json for tooling
 *
 * Pair with tools/profile.sh (callgrind) for per-function attribution.
 */
#include "sync_engine.h"

#include <benchmark/benchmark.h>

#include <array>
#include <cstring>
#include <string>
#include <vector>

#include "codec.h"
#include "crypto.h"
#include "engine.hpp"
#include "sha256.h"

using namespace ke;
using sync_engine_detail::sha256;

namespace {

const uint8_t *B(const std::string &s) { return (const uint8_t *)s.data(); }

std::array<uint8_t, 32> seed_of(uint32_t v) {
    std::array<uint8_t, 32> s{};
    for (size_t i = 0; i < s.size(); i++) s[i] = (uint8_t)(v >> ((i % 4) * 8));
    return s;
}

sync_change make_signed(const std::string &ns, const std::string &ent,
                        const std::string &field, const std::string &val,
                        const std::array<uint8_t, 32> &seed) {
    sync_change c;
    std::memset(&c, 0, sizeof c);
    c.kind = SYNC_CHANGE_REGISTER;
    c.ns = B(ns); c.ns_len = ns.size();
    c.entity = B(ent); c.entity_len = ent.size();
    c.field = B(field); c.field_len = field.size();
    c.value = B(val); c.value_len = val.size();
    c.hlc.physical = 1; c.hlc.logical = 0;
    sync_change_sign(&c, seed.data());
    return c;
}

void populate(sync_engine *e, int n, const char *prefix = "e") {
    const std::string ns = "ns", f = "f", v = "value-data";
    for (int i = 0; i < n; i++) {
        std::string ent = prefix + std::to_string(i);
        sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(), B(f), f.size(),
                        B(v), v.size());
    }
}

/* Wire metrics for one full convergence: how many messages crossed, how many
 * total bytes (both directions), and the largest single message. The last one
 * matters operationally: a reconcile message above the relay's 64 KiB blob cap
 * (S6a kMaxBlobBytes) would be dropped, so relay-routed sync would fail at a
 * scale where direct sync still works. */
struct WireStats {
    long messages = 0;     /* non-empty session messages exchanged */
    long bytes = 0;        /* sum of all message sizes, both directions */
    long max_msg = 0;      /* largest single message */
};

/* Drive two engines to convergence; returns step count, and (if `ws`) the
 * bytes/messages/max-message that crossed the wire. */
int converge(sync_engine *a, sync_engine *b, WireStats *ws = nullptr) {
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    uint8_t *out = nullptr; size_t ol = 0; int done = 0;
    sync_session_step(sa, nullptr, 0, &out, &ol, &done);
    if (ws && ol) { ws->messages++; ws->bytes += (long)ol;
                    if ((long)ol > ws->max_msg) ws->max_msg = (long)ol; }
    std::vector<uint8_t> msg(out, out + ol);
    if (out) sync_free(out);
    sync_session *turn = sb, *other = sa;
    int empties = ol == 0 ? 1 : 0, steps = 0;
    for (; steps < 100000; steps++) {
        out = nullptr; ol = 0; done = 0;
        sync_session_step(turn, msg.data(), msg.size(), &out, &ol, &done);
        if (ws && ol) { ws->messages++; ws->bytes += (long)ol;
                        if ((long)ol > ws->max_msg) ws->max_msg = (long)ol; }
        std::vector<uint8_t> next(out, out + ol);
        if (out) sync_free(out);
        empties = ol == 0 ? empties + 1 : 0;
        if (empties >= 2) break;
        msg.swap(next);
        std::swap(turn, other);
    }
    sync_session_end(sa);
    sync_session_end(sb);
    return steps;
}

/* Attach wire metrics from one convergence as GoogleBenchmark counters, so the
 * report carries bytes/rounds/max-message alongside CPU time. `raw_diff_bytes`
 * (if > 0) lets us also report the amplification factor: wire bytes divided by
 * the raw payload that genuinely had to move. */
void report_wire(benchmark::State &st, const WireStats &ws,
                 long raw_diff_bytes = 0) {
    st.counters["rounds"] = (double)ws.messages;
    st.counters["wire_bytes"] = (double)ws.bytes;
    st.counters["max_msg"] = (double)ws.max_msg;
    /* Headroom under the 64 KiB relay blob cap (S6a). <1.0 would mean a single
     * message is too big to relay. */
    st.counters["relay_cap_frac"] = (double)ws.max_msg / 65536.0;
    if (raw_diff_bytes > 0)
        st.counters["amplification"] = (double)ws.bytes / (double)raw_diff_bytes;
}

/* ---- crypto primitives ------------------------------------------------- */

void BM_Sign(benchmark::State &st) {
    KeyPair kp = keypair_from_seed(seed_of(1).data());
    std::string msg(64, 'm');
    uint8_t sig[64];
    for (auto _ : st) {
        sign(kp.sign_sk.data(), msg.data(), msg.size(), sig);
        benchmark::DoNotOptimize(sig);
    }
    st.SetItemsProcessed(st.iterations());
}
BENCHMARK(BM_Sign);

void BM_Verify(benchmark::State &st) {
    KeyPair kp = keypair_from_seed(seed_of(1).data());
    std::string msg(64, 'm');
    uint8_t sig[64];
    sign(kp.sign_sk.data(), msg.data(), msg.size(), sig);
    for (auto _ : st) {
        bool ok = verify(kp.sign_pk.data(), msg.data(), msg.size(), sig);
        benchmark::DoNotOptimize(ok);
    }
    st.SetItemsProcessed(st.iterations());
}
BENCHMARK(BM_Verify);

void BM_Blake2b_1K(benchmark::State &st) {
    std::string d(1024, 'x');
    uint8_t o[32];
    for (auto _ : st) { blake2b(d.data(), d.size(), o, 32); benchmark::DoNotOptimize(o); }
    st.SetBytesProcessed(st.iterations() * 1024);
}
BENCHMARK(BM_Blake2b_1K);

void BM_Sha256(benchmark::State &st) {
    std::string d((size_t)st.range(0), 'x');
    uint8_t o[32];
    for (auto _ : st) { sha256(d.data(), d.size(), o); benchmark::DoNotOptimize(o); }
    st.SetBytesProcessed(st.iterations() * st.range(0));
}
BENCHMARK(BM_Sha256)->Arg(64)->Arg(1024);

void BM_X25519(benchmark::State &st) {
    KeyPair kp = keypair_from_seed(seed_of(1).data());
    uint8_t sh[32];
    for (auto _ : st) { x25519(kp.dh_sk.data(), kp.dh_pk.data(), sh); benchmark::DoNotOptimize(sh); }
    st.SetItemsProcessed(st.iterations());
}
BENCHMARK(BM_X25519);

void BM_AeadEncrypt_1K(benchmark::State &st) {
    uint8_t key[32] = {1}, nonce[24] = {2}, ct[1024], mac[16];
    std::string pt(1024, 'p');
    for (auto _ : st) {
        aead_encrypt(key, nonce, nullptr, 0, (const uint8_t *)pt.data(),
                     pt.size(), ct, mac);
        benchmark::DoNotOptimize(ct);
    }
    st.SetBytesProcessed(st.iterations() * 1024);
}
BENCHMARK(BM_AeadEncrypt_1K);

/* ---- record codec ------------------------------------------------------ */

void BM_EncodeRecord(benchmark::State &st) {
    sync_change c = make_signed("ns", "entity-42", "field", "value-data", seed_of(1));
    for (auto _ : st) {
        std::string o;
        encode_record(c, o);
        benchmark::DoNotOptimize(o.data());
    }
}
BENCHMARK(BM_EncodeRecord);

void BM_DecodeRecord(benchmark::State &st) {
    sync_change c = make_signed("ns", "entity-42", "field", "value-data", seed_of(1));
    std::string enc;
    encode_record(c, enc);
    for (auto _ : st) {
        DecodedChange d;
        size_t used = 0;
        decode_record((const uint8_t *)enc.data(), enc.size(), d, used);
        benchmark::DoNotOptimize(used);
    }
}
BENCHMARK(BM_DecodeRecord);

/* ---- engine ops -------------------------------------------------------- */

void BM_SetNewCell(benchmark::State &st) {
    sync_engine *e = sync_engine_create(seed_of(1).data());
    const std::string ns = "ns", f = "f", v = "v";
    uint64_t i = 0;
    for (auto _ : st) {
        std::string ent = "k" + std::to_string(i++);
        sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(), B(f), f.size(),
                        B(v), v.size());
    }
    st.SetItemsProcessed(st.iterations());
    sync_engine_destroy(e);
}
BENCHMARK(BM_SetNewCell);

void BM_SetOverwrite(benchmark::State &st) {
    sync_engine *e = sync_engine_create(seed_of(1).data());
    const std::string ns = "ns", ent = "hot", f = "f", v = "v";
    for (auto _ : st)
        sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(), B(f), f.size(),
                        B(v), v.size());
    st.SetItemsProcessed(st.iterations());
    sync_engine_destroy(e);
}
BENCHMARK(BM_SetOverwrite);

void BM_ApplyRegister(benchmark::State &st) {
    sync_engine *e = sync_engine_create(seed_of(1).data());
    sync_change rc = make_signed("ns", "applied", "f", "value-data", seed_of(2));
    sync_engine_apply(e, &rc);
    for (auto _ : st) benchmark::DoNotOptimize(sync_engine_apply(e, &rc));
    st.SetItemsProcessed(st.iterations());
    sync_engine_destroy(e);
}
BENCHMARK(BM_ApplyRegister);

void BM_Get(benchmark::State &st) {
    sync_engine *e = sync_engine_create(seed_of(1).data());
    const std::string ns = "ns", ent = "hot", f = "f", v = "v";
    sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(), B(f), f.size(),
                    B(v), v.size());
    for (auto _ : st) {
        uint8_t *out = nullptr; size_t ol = 0;
        sync_engine_get(e, B(ns), ns.size(), B(ent), ent.size(), B(f), f.size(),
                        &out, &ol);
        if (out) sync_free(out);
        benchmark::DoNotOptimize(ol);
    }
    st.SetItemsProcessed(st.iterations());
    sync_engine_destroy(e);
}
BENCHMARK(BM_Get);

void BM_Export(benchmark::State &st) {
    int n = (int)st.range(0);
    sync_engine *e = sync_engine_create(seed_of(3).data());
    populate(e, n);
    for (auto _ : st) {
        sync_change *r = nullptr; size_t cnt = 0;
        sync_engine_export(e, &r, &cnt);
        benchmark::DoNotOptimize(cnt);
        sync_changes_free(r, cnt);
    }
    st.SetComplexityN(n);
    sync_engine_destroy(e);
}
BENCHMARK(BM_Export)->RangeMultiplier(4)->Range(64, 16384)->Complexity();

void BM_Digest(benchmark::State &st) {
    int n = (int)st.range(0);
    sync_engine *e = sync_engine_create(seed_of(3).data());
    populate(e, n);
    uint8_t d[32];
    for (auto _ : st) { sync_engine_digest(e, d); benchmark::DoNotOptimize(d); }
    st.SetComplexityN(n);
    sync_engine_destroy(e);
}
BENCHMARK(BM_Digest)->RangeMultiplier(4)->Range(64, 16384)->Complexity();

/* ---- reconciliation ---------------------------------------------------- */

void BM_SessionBegin(benchmark::State &st) {
    int n = (int)st.range(0);
    sync_engine *e = sync_engine_create(seed_of(10).data());
    populate(e, n);
    for (auto _ : st) {
        sync_session *s = sync_session_begin(e, 1); /* export+sort+prefix+hash */
        benchmark::DoNotOptimize(s);
        sync_session_end(s);
    }
    st.SetComplexityN(n);
    sync_engine_destroy(e);
}
BENCHMARK(BM_SessionBegin)->RangeMultiplier(4)->Range(64, 16384)->Complexity();

void BM_SessionBeginCold(benchmark::State &st) {
    /* Force a snapshot rebuild each iteration (one overwrite bumps content_gen),
     * so this measures the cold build_snapshot path, not the cached hit. The
     * constant ~one-sign overwrite cost cancels in before/after comparisons; the
     * N-scaling part is the snapshot build. */
    int n = (int)st.range(0);
    sync_engine *e = sync_engine_create(seed_of(12).data());
    populate(e, n);
    const std::string ns = "ns", f = "f", v = "v";
    uint64_t i = 0;
    for (auto _ : st) {
        std::string ent = "e" + std::to_string(i++ % (uint64_t)n);
        sync_engine_set(e, B(ns), ns.size(), B(ent), ent.size(), B(f), f.size(),
                        B(v), v.size());
        sync_session *s = sync_session_begin(e, 1);
        benchmark::DoNotOptimize(s);
        sync_session_end(s);
    }
    st.SetComplexityN(n);
    sync_engine_destroy(e);
}
BENCHMARK(BM_SessionBeginCold)->RangeMultiplier(4)->Range(64, 4096)->Complexity();

void BM_SessionBeginAfterGrant(benchmark::State &st) {
    /* A capability change bumps scope_gen only, and the unscoped snapshot is
     * keyed on content_gen — so a session begun right after a grant must hit
     * the still-valid cached snapshot. Each iteration re-grants a prepared
     * delegation (a CapStore dedup no-op, but an unconditional scope_gen bump)
     * and then begins a session. Before the gen split, every grant discarded
     * the snapshot and this benchmark scaled like BM_SessionBeginCold's O(N)
     * rebuild; now the begin costs a cached hit, and the timing is dominated
     * by the grant's constant ~130us EdDSA signature verify — so compare the
     * *scaling* (flat vs. O(N)), not the absolute floor. */
    int n = (int)st.range(0);
    sync_engine *e = sync_engine_create(seed_of(14).data());
    populate(e, n);
    sync_capability *root =
        sync_capability_root(e, "ns", SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
    sync_engine_grant(e, root);
    uint8_t sub[SYNC_PUBKEY_LEN];
    std::memset(sub, 0x42, sizeof sub);
    sync_capability *d =
        sync_capability_delegate(e, root, sub, SYNC_ACCESS_READ, 0);
    { /* warm the snapshot cache */
        sync_session *s = sync_session_begin(e, 1);
        sync_session_end(s);
    }
    for (auto _ : st) {
        sync_engine_grant(e, d); /* scope-only invalidation */
        sync_session *s = sync_session_begin(e, 1); /* cached-snapshot hit */
        benchmark::DoNotOptimize(s);
        sync_session_end(s);
    }
    st.SetComplexityN(n);
    sync_capability_free(root);
    sync_capability_free(d);
    sync_engine_destroy(e);
}
BENCHMARK(BM_SessionBeginAfterGrant)->RangeMultiplier(4)->Range(64, 16384)->Complexity();

/* ---- scoped session begin for a time-bound peer (improvement plan §3.5) ---
 *
 * The device this phase is for: one gossip peer whose read scope depends on a
 * finite-expiry capability, seeing a small fraction of the engine's data, on a
 * link that keeps taking writes. Before Phase 5 such a peer was excluded from
 * caching entirely and rebuilt a FILTERED snapshot every cycle — O(N_visible)
 * encodes. It now builds the shared unscoped base (O(N) encodes, amortized
 * across every other consumer of that base) plus O(namespaces·log N) range
 * work, and is then cached until the capability's expiry.
 *
 * The two benchmarks below are the A/B for that trade at a given visible
 * fraction, measured in one binary at one revision:
 *   ...TimeBound  — the peer's cap has a finite expiry: the new view path.
 *   ...Permanent  — the same shape, same visible fraction, but a never-expiring
 *                   cap, so the peer is permanently restricted and each write
 *                   forces exactly the filtered O(N_visible) rebuild the
 *                   time-bound peer used to pay. This is the "before" number.
 * Both are write-active (one overwrite per iteration bumps content_gen and so
 * invalidates the per-peer cache), so both include the same constant ~one-sign
 * overwrite cost; compare the difference between them, not the absolute floor.
 * The crossover in visible fraction is recorded in docs/PERF.md. */
struct ScopedFixture {
    sync_engine     *e = nullptr;
    sync_capability *root0 = nullptr;
    sync_capability *deleg = nullptr;
    std::vector<sync_capability *> roots;
    uint8_t          peer[SYNC_PUBKEY_LEN];
    std::string      hot_ns, hot_ent;
};

/* n elements-ish spread over `denom` namespaces; the peer may read exactly one
 * of them, i.e. a visible fraction of 1/denom. `expiry` 0 == permanent. */
void scoped_setup(ScopedFixture &fx, int n, int denom, uint64_t expiry,
                  uint32_t seed) {
    fx.e = sync_engine_create(seed_of(seed).data());
    sync_engine *peer_engine = sync_engine_create(seed_of(seed + 1).data());
    sync_engine_identity(peer_engine, fx.peer);
    sync_engine_destroy(peer_engine); /* only its identity is needed */

    const std::string f = "f", v = "value-data";
    const int per = n / denom > 0 ? n / denom : 1;
    for (int k = 0; k < denom; k++) {
        std::string ns = "ns" + std::to_string(k);
        for (int i = 0; i < per; i++) {
            std::string ent = "e" + std::to_string(i);
            sync_engine_set(fx.e, B(ns), ns.size(), B(ent), ent.size(), B(f),
                            f.size(), B(v), v.size());
        }
        sync_capability *r = sync_capability_root(
            fx.e, ns.c_str(), SYNC_ACCESS_READ | SYNC_ACCESS_WRITE);
        sync_engine_grant(fx.e, r);
        fx.roots.push_back(r);
        if (k == 0) fx.root0 = r;
    }
    fx.deleg = sync_capability_delegate(fx.e, fx.root0, fx.peer,
                                        SYNC_ACCESS_READ, expiry);
    sync_engine_grant(fx.e, fx.deleg);
    fx.hot_ns = "ns0";
    fx.hot_ent = "e0";
}

void scoped_teardown(ScopedFixture &fx) {
    for (auto *r : fx.roots) sync_capability_free(r);
    sync_capability_free(fx.deleg);
    sync_engine_destroy(fx.e);
}

void scoped_run(benchmark::State &st, uint64_t expiry, uint32_t seed) {
    const int n = (int)st.range(0);
    const int denom = (int)st.range(1);
    ScopedFixture fx;
    scoped_setup(fx, n, denom, expiry, seed);
    const std::string f = "f";
    uint64_t i = 0;
    for (auto _ : st) {
        std::string v = "v" + std::to_string(i++);
        sync_engine_set(fx.e, B(fx.hot_ns), fx.hot_ns.size(), B(fx.hot_ent),
                        fx.hot_ent.size(), B(f), f.size(), B(v), v.size());
        sync_session *s = sync_session_begin_scoped(fx.e, 1, fx.peer);
        benchmark::DoNotOptimize(s);
        sync_session_end(s);
    }
    st.SetComplexityN(n);
    scoped_teardown(fx);
}

void BM_ScopedSessionBeginTimeBound(benchmark::State &st) {
    scoped_run(st, /*expiry=*/4000000000000ull /* ~2096, finite */, 16);
}
BENCHMARK(BM_ScopedSessionBeginTimeBound)
    ->Args({4096, 100})->Args({4096, 10})->Args({4096, 2})
    ->Args({16384, 100})->Args({16384, 10})->Args({16384, 2});

void BM_ScopedSessionBeginPermanent(benchmark::State &st) {
    scoped_run(st, /*expiry=*/0 /* never */, 18);
}
BENCHMARK(BM_ScopedSessionBeginPermanent)
    ->Args({4096, 100})->Args({4096, 10})->Args({4096, 2})
    ->Args({16384, 100})->Args({16384, 10})->Args({16384, 2});

/* The steady state this phase is named for: an IDLE, converged link. No write
 * lands between cycles, so the only question is what a repeated
 * sync_session_begin_scoped costs for a peer whose scope is deadline-bearing.
 *   ...IdleTimeBound — now: one map lookup plus one deadline compare.
 *   ...IdleUncached  — before: the same peer, but the deadline-keyed entry is
 *                      dropped each cycle, which is exactly the pre-phase
 *                      "a time-bound scope is never cached" behaviour: a full
 *                      filtered rebuild (encode every visible record) per
 *                      cycle. Uses the internal cache map directly (engine.hpp
 *                      is already included here) purely to reproduce that
 *                      path; nothing in the engine clears it this way. */
void BM_ScopedSessionBeginIdleTimeBound(benchmark::State &st) {
    ScopedFixture fx;
    scoped_setup(fx, (int)st.range(0), (int)st.range(1),
                 /*expiry=*/4000000000000ull, 20);
    for (auto _ : st) {
        sync_session *s = sync_session_begin_scoped(fx.e, 1, fx.peer);
        benchmark::DoNotOptimize(s);
        sync_session_end(s);
    }
    st.SetComplexityN((int)st.range(0));
    scoped_teardown(fx);
}
BENCHMARK(BM_ScopedSessionBeginIdleTimeBound)
    ->Args({4096, 100})->Args({4096, 10})->Args({4096, 2})
    ->Args({16384, 100})->Args({16384, 10})->Args({16384, 2});

void BM_ScopedSessionBeginIdleUncached(benchmark::State &st) {
    ScopedFixture fx;
    scoped_setup(fx, (int)st.range(0), (int)st.range(1),
                 /*expiry=*/4000000000000ull, 22);
    for (auto _ : st) {
        fx.e->scoped_view_cache.clear(); /* pre-phase: never cached */
        sync_session *s = sync_session_begin_scoped(fx.e, 1, fx.peer);
        benchmark::DoNotOptimize(s);
        sync_session_end(s);
    }
    st.SetComplexityN((int)st.range(0));
    scoped_teardown(fx);
}
BENCHMARK(BM_ScopedSessionBeginIdleUncached)
    ->Args({4096, 100})->Args({4096, 10})->Args({4096, 2})
    ->Args({16384, 100})->Args({16384, 10})->Args({16384, 2});

/* Canonical encoded size of one representative record (the shape populate()
 * writes), used as the amplification denominator. */
long record_wire_size() {
    sync_change c = make_signed("ns", "e0", "f", "value-data", seed_of(1));
    std::string o;
    encode_record(c, o);
    return (long)o.size();
}

void BM_ConvergeInSync(benchmark::State &st) {
    /* Already-converged engines: the fingerprint matches at the top, so this is
     * the "nothing to send" fast path (dominated by the two session snapshots).
     * Pre-converge once so the timed runs are genuinely a no-op — note the two
     * sides start with different wall-clock HLCs, so they only become byte-
     * identical *after* a reconcile. */
    int n = (int)st.range(0);
    sync_engine *a = sync_engine_create(seed_of(10).data());
    sync_engine *b = sync_engine_create(seed_of(11).data());
    populate(a, n);
    populate(b, n);
    converge(a, b); /* now identical */
    for (auto _ : st) benchmark::DoNotOptimize(converge(a, b));
    WireStats ws; converge(a, b, &ws); /* in-sync poll: should be tiny & flat */
    report_wire(st, ws);
    st.SetComplexityN(n);
    sync_engine_destroy(a);
    sync_engine_destroy(b);
}
BENCHMARK(BM_ConvergeInSync)->RangeMultiplier(4)->Range(64, 16384)->Complexity();

void BM_ConvergeAllConflict(benchmark::State &st) {
    /* Same keys, different per-cell HLCs on each side -> every cell conflicts and
     * is exchanged + LWW-merged both ways. Dominated by ~2N signature verifies.
     * Rebuilt each iteration (the merge mutates state). */
    int n = (int)st.range(0);
    for (auto _ : st) {
        st.PauseTiming();
        sync_engine *a = sync_engine_create(seed_of(10).data());
        sync_engine *b = sync_engine_create(seed_of(11).data());
        populate(a, n);
        populate(b, n);
        st.ResumeTiming();
        benchmark::DoNotOptimize(converge(a, b));
        st.PauseTiming();
        sync_engine_destroy(a);
        sync_engine_destroy(b);
        st.ResumeTiming();
    }
    /* One un-timed run on a fresh all-conflict pair to capture wire metrics:
     * every one of the n cells differs and is exchanged + LWW-merged both ways. */
    {
        sync_engine *a = sync_engine_create(seed_of(10).data());
        sync_engine *b = sync_engine_create(seed_of(11).data());
        populate(a, n);
        populate(b, n);
        WireStats ws; converge(a, b, &ws);
        report_wire(st, ws, (long)n * record_wire_size());
        sync_engine_destroy(a);
        sync_engine_destroy(b);
    }
    st.SetComplexityN(n);
}
BENCHMARK(BM_ConvergeAllConflict)->RangeMultiplier(8)->Range(64, 4096)->Complexity()->UseRealTime();

void BM_ConvergeFullTransfer(benchmark::State &st) {
    int n = (int)st.range(0);
    for (auto _ : st) {
        st.PauseTiming();
        sync_engine *a = sync_engine_create(seed_of(20).data());
        sync_engine *b = sync_engine_create(seed_of(21).data());
        populate(a, n); /* b empty -> full transfer of n records */
        st.ResumeTiming();
        benchmark::DoNotOptimize(converge(a, b));
        st.PauseTiming();
        sync_engine_destroy(a);
        sync_engine_destroy(b);
        st.ResumeTiming();
    }
    /* Un-timed run for wire metrics: a cold node pulling all n records. The
     * amplification denominator is the raw payload that genuinely had to move. */
    {
        sync_engine *a = sync_engine_create(seed_of(20).data());
        sync_engine *b = sync_engine_create(seed_of(21).data());
        populate(a, n);
        WireStats ws; converge(a, b, &ws);
        report_wire(st, ws, (long)n * record_wire_size());
        sync_engine_destroy(a);
        sync_engine_destroy(b);
    }
    st.SetComplexityN(n);
}
BENCHMARK(BM_ConvergeFullTransfer)->RangeMultiplier(8)->Range(64, 4096)->Complexity()->UseRealTime();

/* ---- wire efficiency: bytes/rounds vs. divergence ---------------------- *
 * The headline claim of range reconciliation is that cost tracks the *diff*,
 * not the dataset. Hold N fixed and sweep D = number of differing records:
 * both nodes start byte-identical with N records, then A overwrites D of them
 * with a newer value (newer HLC), so exactly D cells differ. We expect
 * wire_bytes ~ O(D * record_size) plus an O(log N) descent overhead, and rounds
 * ~ O(log N) — NOT O(N). args: {N, D}. */
void BM_WireSparseDiff(benchmark::State &st) {
    int n = (int)st.range(0);
    int d = (int)st.range(1);
    const std::string ns = "ns", f = "f";
    for (auto _ : st) {
        st.PauseTiming();
        sync_engine *a = sync_engine_create(seed_of(30).data());
        sync_engine *b = sync_engine_create(seed_of(31).data());
        populate(a, n);
        populate(b, n);
        converge(a, b); /* identical baseline of N records */
        for (int i = 0; i < d; i++) { /* A diverges D cells with a newer write */
            std::string ent = "e" + std::to_string(i);
            std::string v = "updated-value";
            sync_engine_set(a, B(ns), ns.size(), B(ent), ent.size(), B(f),
                            f.size(), B(v), v.size());
        }
        st.ResumeTiming();
        WireStats ws;
        converge(a, b, &ws);
        st.PauseTiming();
        report_wire(st, ws, (long)d * record_wire_size());
        st.counters["N"] = n;
        st.counters["D"] = d;
        sync_engine_destroy(a);
        sync_engine_destroy(b);
        st.ResumeTiming();
    }
}
/* Fixed large N=4096, sweep D across three orders of magnitude (+ the D=0
 * no-op and the D=N all-changed endpoints). */
BENCHMARK(BM_WireSparseDiff)
    ->Args({4096, 0})->Args({4096, 1})->Args({4096, 4})->Args({4096, 16})
    ->Args({4096, 64})->Args({4096, 256})->Args({4096, 1024})->Args({4096, 4096})
    ->UseRealTime();

} // namespace

BENCHMARK_MAIN();
