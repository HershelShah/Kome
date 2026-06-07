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

/* Drive two engines to convergence; returns step count. */
int converge(sync_engine *a, sync_engine *b) {
    sync_session *sa = sync_session_begin(a, 1);
    sync_session *sb = sync_session_begin(b, 0);
    uint8_t *out = nullptr; size_t ol = 0; int done = 0;
    sync_session_step(sa, nullptr, 0, &out, &ol, &done);
    std::vector<uint8_t> msg(out, out + ol);
    if (out) sync_free(out);
    sync_session *turn = sb, *other = sa;
    int empties = ol == 0 ? 1 : 0, steps = 0;
    for (; steps < 100000; steps++) {
        out = nullptr; ol = 0; done = 0;
        sync_session_step(turn, msg.data(), msg.size(), &out, &ol, &done);
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
    st.SetComplexityN(n);
}
BENCHMARK(BM_ConvergeAllConflict)->RangeMultiplier(8)->Range(64, 4096)->Complexity();

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
    st.SetComplexityN(n);
}
BENCHMARK(BM_ConvergeFullTransfer)->RangeMultiplier(8)->Range(64, 4096)->Complexity();

} // namespace

BENCHMARK_MAIN();
