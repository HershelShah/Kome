# Performance — baseline & optimization story

Chapter 1: **measure before optimizing.** This is the committed baseline that
later changes are judged against. Numbers below are from one machine (Intel Xeon
@ 2.10 GHz, GCC, `-O3` Release) — treat the *ratios and big-O*, not the absolute
ns, as the signal; re-run locally for your hardware.

## Running it

```bash
# Microbenchmarks (GoogleBenchmark, fetched like GoogleTest; dev-only).
cmake -B build -DCMAKE_BUILD_TYPE=Release -DSYNC_BENCH=ON
cmake --build build --target bench
./build/bench                          # --benchmark_format=json for tooling

# Deterministic per-function attribution (callgrind; perf is blocked in the
# sandbox/CI containers). Counts instructions, so it's stable run-to-run.
tools/profile.sh 'BM_ApplyRegister' 3000
```

## Baseline (per-op)

| Operation | Cost | Notes |
|-----------|-----:|-------|
| `sign` (Ed25519) | **44 µs** | every `set` signs |
| `verify` (Ed25519) | **130 µs** | every `apply`/received record verifies — 3× sign |
| `x25519` DH | 86 µs | Noise handshake only (once per connection) |
| `blake2b` 1 KB | 1.2 µs | 820 MB/s |
| `sha256` 1 KB / 64 B | 4.8 µs / 0.8 µs | ~200 MB/s |
| `aead_encrypt` 1 KB | 2.9 µs | 340 MB/s |
| `encode_record` / `decode_record` | 130 ns / 34 ns | codec is negligible |
| `set` (new cell) | **86 µs** | signs **twice** (existence + register) |
| `set` (overwrite) | 42 µs | one sign |
| `apply` (register) | **124 µs** | ≈ one verify |
| `get` | 48 ns | map lookup + copy |

## Baseline (scaling in N records)

| Operation | Big-O | @ N=1024 | per-record |
|-----------|-------|---------:|-----------:|
| `export` | O(N) | 0.20 ms | 270 ns |
| `digest` | O(N) | 0.78 ms | 784 ns (SHA-256 over all state) |
| `session begin` | O(N log N) | 2.6 ms | export + sort + prefix sums + **per-element SHA-256** |
| converge **in-sync** | O(N log N) | 5.2 ms | ≈ two session snapshots; *no* records exchanged |
| converge **full-transfer** | O(N) | — | **263 µs/record** (verify-bound) |
| converge **all-conflict** | O(N) | — | **540 µs/record** (≈4 verifies/cell, verify-bound) |

## The finding

`tools/profile.sh BM_ApplyRegister` (callgrind, instruction counts):

```
56.8%  monocypher fe_mul     ┐
31.6%  monocypher fe_sq      ├ Curve25519 field arithmetic inside EdDSA verify
 4.1%  monocypher ge_double  ┘
 ...   (>99% total in monocypher EdDSA)
```

**Signature work dominates everything.** `verify` (130 µs) gates every applied
record, so all convergence is verify-bound; `sign` (44 µs) gates every write.
The codec, maps, digest, and reconciliation bookkeeping are rounding error next
to it. Two structural facts amplify it:

- **Every received record is verified before the merge decides whether to keep
  it** — so a record that loses LWW, or that we already hold, still costs a full
  130 µs verify. In the in-sync and high-overlap cases that's pure waste.
- **`session begin` re-exports and re-hashes the entire state every sync**, so
  even a no-op gossip round is O(N log N).

## Chapter 2 — verify only records that would change state ✅

`sync_engine_apply` now runs the cheap LWW/existence comparison *first* and
verifies the signature **only if the record would be accepted**. A record that
loses LWW or that we already hold is dropped without verifying — and reaches no
state at all (no entity insertion, no clock perturbation), so it's safe; a
record forged to *win* still gets verified and rejected. (Contract locked by
`Defensive.VerifyOnlyWhenRecordWouldChangeState`.)

| Case | Before | After | |
|------|-------:|------:|--|
| `apply` a record we already hold | 124 µs | **44 ns** | ~2800× — was a wasted verify |
| converge **all-conflict** | 540 µs/rec | **275 µs/rec** | ~2× — verify only the winners |
| converge **full-transfer** | 263 µs/rec | 263 µs/rec | unchanged — all records are new, so all must verify |
| converge **in-sync** | O(N log N) | O(N log N) | unchanged — now purely *snapshot*-bound (→ item 2) |
| full test suite wall-time | ~62 s | ~50 s | fewer verifies in the convergence suites |

Net: the duplicate/overlap paths (LEAF re-sends, partial sync, concurrent
edits) get dramatically cheaper; the genuinely-new-data path is untouched
(there's nothing to skip). The remaining convergence cost is now dominated by
the per-sync snapshot — exactly backlog item 2.

## Chapter 3 — cache the reconciliation snapshot ✅

`session_begin` used to re-`export` + re-encode + re-SHA-256 + re-sort the whole
state every time. The engine now keeps that sorted, hashed snapshot in a
`shared_ptr<const ReconSnapshot>`, rebuilt lazily only when a `state_gen`
counter (bumped on every write/delete/accepted-apply) shows it's stale. A
session holds the snapshot by `shared_ptr`, so it stays stable even as records
applied mid-sync replace the engine's cached copy. (Invalidation pinned by
`Reconcile.SnapshotCacheInvalidatesOnWrite`.)

| Case (steady-state, syncs between writes) | Before | After @ N=1024 | @ N=16384 |
|---|---:|---:|---:|
| `session_begin` | O(N log N) | **15 ns** (was 2.5 ms, ~170,000×) | 21 ns (was 47 ms) |
| converge **in-sync** | O(N log N) | **1.0 µs** (was 5.2 ms, ~5000×) | 1.4 µs (was 96 ms, ~68,000×) |

Both dropped from O(N log N) to **O(1)** on the cache-hit (gossip) path: a sync
that changes nothing is two refcount bumps plus one O(1) prefix-sum fingerprint
compare. The first sync after a write still pays one O(N log N) rebuild, so a
write→sync→write→sync workload is unchanged; a gossip mesh that syncs with many
peers between writes is now essentially free. Full-transfer/all-conflict are
unchanged (they mutate, so they rebuild — and are verify-bound anyway).

## Chapter 4 — parallel batch verification ✅

The one path still irreducibly verify-bound is bulk transfer: every genuinely-
new record must be verified once, and chapters 2–3 can't skip work that's real.
True batch Ed25519 (~2×) needs primitives monocypher doesn't expose, and hand-
rolling EdDSA is a security non-starter — so we parallelize instead. A large
received batch has all its signatures verified across worker threads (a pure,
stateless monocypher call — no shared mutable state), then the valid records are
applied serially with `already_verified=true`. Forgery-safe: every record is
still verified and the merge still decides acceptance, so a forged record is
dropped and can't suppress a legitimate one in the same batch. Small batches
(the steady-state gossip diff) stay on the serial verify-on-win path; threads
only engage at/above 16 records, where verify work dwarfs spawn cost. Compiled
out under Emscripten (WASM is single-threaded).

| Case (wall time, 4 cores) | ch.3 | ch.4 | |
|---|---:|---:|--|
| converge **full-transfer** N=4096 | 1076 ms | **309 ms** | ~3.5× (scales with cores) |
| converge **full-transfer** N=512 | 134 ms | 36 ms | ~3.7× |
| converge **all-conflict** | 275 µs/rec | 275 µs/rec | unchanged — batches are tiny (≤2 recs/leaf), stay serial |
| full test suite wall-time | ~50 s | ~44 s | bulk syncs in multinode/resilience parallelize |

Per-record `verify` is unchanged (130 µs); we just run N of them on all cores.
Initial sync of a large dataset — the last expensive case — now scales with
hardware. (TSan-clean: the parallel region touches only per-index outputs and
const inputs.)

## Chapter 5 — allocation & code-level cleanups ✅

After the algorithmic wins, profiling the cold snapshot build (callgrind,
`BM_Export`-style) showed **~55% of it was malloc/free/memset/memcpy**, not
compute — the build round-tripped through the public `sync_engine_export`, which
`calloc`s an N-element array and `dup_field`-mallocs four copies per record, all
freed right after re-encoding.

- **`build_snapshot` iterates the engine's maps directly** and encodes each
  element in place — the change borrows the map's strings, so the export array,
  the 4×N field mallocs, and the matching frees are all gone. Byte-identical
  output (verified by the reconcile/convergence oracle).
- **`encode_record` reserves** its buffer once instead of regrowing on each
  field append.
- **`add256`/`sub256` work 64-bit limbs at a time** (4 iterations, not 32) via
  the LE byte helpers — portable (single load/store on LE, bswap on BE),
  byte-identical, ~8× fewer iterations on the prefix-sum build.
- **No sort in the snapshot build.** `std::map` already yields `(ns, entity)`
  and fields ascending, and we emit each entity's existence element before its
  registers — exactly `SortKey` order. The `std::sort` (≈7% of the cold build:
  `key_cmp` string compares + moving large `Element`s) is gone; a debug
  `assert(is_sorted)` guards the invariant.
- **`reserve` the snapshot vector** to its exact element count (one counting
  pass over the maps) so the `push_back`s never regrow/move it.

| Case | before | after | |
|------|-------:|------:|--|
| cold `session_begin` (rebuild) N=4096 | 11.3 ms | **8.2 ms** | ~28% (export-bypass + no-sort + reserve) |
| cold `session_begin` (rebuild) N=1024 | 2.68 ms | 2.02 ms | ~25% |

This is the *cold* path (first sync after a write); the cached gossip path
(chapter 3) is untouched. The remainder is now ~63% per-element SHA-256 — see
backlog item 7 (BLAKE2b, version-gated).

## Optimization backlog (data-driven, in priority order)

1. ~~**Verify only records that would change state.**~~ ✅ done (chapter 2).
2. ~~**Cache the reconciliation snapshot.**~~ ✅ done (chapter 3).
3. ~~**Faster verify** — parallel batch verification.~~ ✅ done (chapter 4).
   (True batch-Ed25519 / a faster backend remain possible but need a different
   vendored crypto lib; parallelism captured most of the win safely.)
4. ~~**Allocation & code-level cleanups.**~~ ✅ done (chapter 5).

Remaining, lower-priority:
5. **One sign per new cell.** A fresh cell signs the existence assertion *and*
   the first register (86 µs). Explore deferring/coalescing.
6. **Incremental digest** — maintain a running combinable digest so `digest` is
   O(changed) rather than O(N) SHA-256 each call.
7. **Faster per-element hash** — the snapshot build SHA-256s every element
   (~35% of the cold build); BLAKE2b is ~4× faster. It's an internal fingerprint
   detail, but changing it shifts the on-wire fingerprint, so version-gate it.

Each subsequent chapter takes one item, re-runs `./build/bench` against this
baseline, and records the delta here.
