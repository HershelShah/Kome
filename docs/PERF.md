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
`shared_ptr<const ReconSnapshot>`, rebuilt lazily only when a `content_gen`
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
backlog item 7 (BLAKE2b, version-gated). (Chapter 6 measures that share
properly across N — 63% turns out to be the small-N point of a curve that
reaches ~85% at N=4096 — and then removes it.)

## Chapter 6 — cache per-element reconciliation hashes ✅

Store each cell's 32-byte reconciliation-element hash (SHA-256 of its
canonical `encode_record` bytes) on the cell itself — `Register::elem_hash`,
`Entity::ex_hash` — computed at every point that installs or replaces a cell,
so the cold snapshot build copies a cached hash per element instead of
re-running SHA-256 over every record. Mutation-time hashing reuses the
signing/verify buffer each path already builds (the streaming `element_hash`
overload; the parallel verifiers hash alongside the signature check), so it
adds no re-encode and no allocation; every hash computation is hoisted above
the first committed byte so an OOM mid-mutation can never strand a committed
cell with a stale or zero hash (see the invariant note in `engine.hpp` and
§3.2 of `docs/IMPROVEMENT_PLAN.md`). Wire bytes, fingerprints, `digest`, and
the on-disk format are byte-identical; the cache is RAM-only and recomputed
during the load-verify pass at open.

Measured on the same machine/flags discipline as chapter 1 (Intel Xeon @
2.10 GHz, GCC, `-O3` Release — as there, treat the ratios and big-O as the
signal, not the absolute ns): **before** = the P1 baseline at branch point
`claude/improve-p1-gen-split` (this branch's parent), **after** = this
change; one `./build/bench` run per side (the harness's own complexity fit
reports 2% RMS on the before curve); N entities × 2 elements each, and each
iteration also pays one overwrite `set` to force the rebuild — which is why
the small-N removed share is lower than the large-N one:

| `BM_SessionBeginCold` | before | after | ratio | share removed |
|---|---:|---:|---:|---:|
| N=64 | 220.4 µs | 80.1 µs | **2.75×** | 63.7% |
| N=256 | 704.5 µs | 159.6 µs | 4.41× | 77.3% |
| N=1024 | 2.719 ms | 0.499 ms | 5.45× | 81.7% |
| N=4096 | 13.426 ms | 1.998 ms | **6.72×** | 85.1% |

The complexity fit drops from ~273·N·log N ns (272.96 coefficient, before) to
~488·N ns (488.39 coefficient, after): with per-element hashing gone the
rebuild is a pure encode+copy pass.

**Reconciling the earlier ~63% / ~35% share claims.** Both prior figures were
frame-dependent and both understated the asymptote. Backlog item 7's "~35% of
the cold build" dated from before chapter 5, when the total still carried the
export/sort/allocation overhead chapter 5 removed — that is the stale figure;
this measurement does not support it, and it is corrected in place below
rather than deleted, so the estimate's history stays visible. Chapter 5's
"~63%" is the one the new measurement supports: it lines up almost exactly
with the measured share at N=64 (63.7%) — the smallest, constant-overhead-
heaviest point. But SHA-256 sat in the N-scaling term, so its share grows
with N: 77.3% at N=256, 81.7% at N=1024, and 85.1% at N=4096 — the point that
motivates cold-sync work — where removing it is worth 6.72×, not the
~1.5–2.7× the ~35% figure implied.

Write-path cost — a new cell now computes two element hashes (presence +
register); an overwrite and an applied register each compute one (medians
from the same `./build/bench` run):

| | before | after | delta |
|---|---:|---:|---:|
| `BM_SetNewCell` | 104.4 µs | 107.3 µs | **+2.9 µs (+2.76%)** |
| `BM_SetOverwrite` | 59.6 µs | 54.0 µs | −5.6 µs (−9.31%) |
| `BM_ApplyRegister` | 93.5 ns | 75.3 ns | −18.2 ns (−19.45%) |

`BM_SetNewCell`'s regression is the expected one: two streaming SHA-256
computations (presence + register) against the ~86 µs Ed25519 double-sign
that already dominates a new-cell `set` (backlog item 5) — +2.76% is a cheap
trade for the cold-build win above. `BM_SetOverwrite` and `BM_ApplyRegister`
move the other way and measure *faster*, not slower: both paths already build
a `signing` buffer for sign/verify, and the streaming `element_hash` overload
plus the compute-then-commit reordering (§3.2's throw-safety amendment) sit
on that same buffer, so the net effect measures as an improvement rather than
a flat per-record tax. For scale, streaming SHA-256 over that buffer costs
`BM_Sha256/64` = 1065 ns (57.3 MB/s) and `BM_Sha256/1024` = 5956 ns
(164.0 MB/s) on this machine — the same ~1 µs neighborhood as the deltas
above.

**Debug-assert cost (pre-agreed hazard, measured).** The `emit_element`
recompute-assert (full per-element, not sampled) re-adds one SHA-256 per
element on every Debug snapshot build. On the two slowest Debug suites:
`stress_test` 137.0 s → 141.6 s (+3.4%), `multinode_test` 49.5 s → 50.4 s
(+1.9%) — nowhere near the feared doubling, so the full assert ships;
sampling (first/last + every 64th) remains the documented fallback only if CI
wall time ever forces it. (`Stress.DataScale` exceeds its hard-coded 2 s
Debug snapshot bound in this container on the *base* tree too — ~3.0 s both
before and after — a pre-existing environment failure, not a regression.)

## Chapter 7 — batched blob writes (§3.3, Phase 3) ✅

Expose the storage layer's internal batching as the nestable
`sync_engine_batch_begin/commit/abort` ABI and wrap the three blob write
paths in it, so a large put stages records into few clock-covered, fsync'd
sub-frames (mandatory flush every `kBatchFlushBytes` = 2 MiB, enforced from
the engine's own write path) instead of paying one fsync'd frame per record.

**fsync collapse (CI-gated via the debug/test counter, not benched).** The
pre-batching baseline measured in the Phase-3 design review: an 8 MiB
`sync_blob_put` cost **273 fsyncs + 7 compaction renames** (one
frame+fsync per chunk/manifest record, with the log repeatedly tripping the
doubling heuristic mid-put). Batched, the same put costs **7 counted fsyncs
and exactly 1 rename**: 4 mandatory sub-frame flushes (8 MiB /
`kBatchFlushBytes`) + 1 outermost-commit frame + the 2 counted fsyncs (temp
file + directory) of the single compaction rewrite that the outermost
commit's `maybe_compact` runs. `Storage.BlobPutFrameBounded` asserts that
exact count — on the fsync counter, not on-disk frame count, because the
compaction wrote ~258 frames under a single fsync pair (via the then-current
`atomic_replace`; Phase 4 replaced it with the streamed writer of chapter 8,
which keeps the same two counted fsyncs — so the arithmetic below is unchanged)
(spec §3.3 amendment 1).

**Peak memory — the corrected claim (spec §3.3 hazard table).** Naive
batching (stage everything, one commit) measured **+41.7 MB** VmHWM for the
8 MiB put and was rejected; the mandatory sub-frame flush caps staging at
~`kBatchFlushBytes` + one record, which **restored roughly today's +17.9 MB
peak** at the time this chapter shipped — it did **not** drop below it yet,
because that peak's residual was not the batch's: `maybe_compact`'s
`serialize_state` still allocated a full log image at the outermost commit's
compaction. That residual transient is gone as of Phase 4 (stream-compaction,
chapter 8): the bounded streaming writer replaces the full-image build
everywhere `serialize_state` used to run, including at this batch's outermost
commit. The 8 MiB batched-put figure above has not itself been re-measured
end-to-end against the streaming compactor; chapter 8 records the isolated
compaction-transient collapse instead (34.1 MB → 0.33 MB plaintext, 1.8 MB →
0.26 MB encrypted, at the 50k-entity shape) — that is the figure that no
longer rides on top of the +17.9 MB peak above. Numbers are the design
review's measurements (manual VmHWM around `sync_blob_put`); process-global
RSS is not CI-asserted.

The staging bound holds for POISONED batches too: poisoning drops the
condemned staged tail immediately and the write path refuses to stage into
a poisoned batch, so a caller looping over failing post-poison writes holds
zero staging (pinned by `Storage.PoisonedBatchHoldsNoStaging`), not an
unbounded transient.

## Chapter 8 — stream compaction (§3.4, Phase 4) ✅

Replace `Storage::serialize_state` (built the whole compacted image as one
`std::string` before handing it to `atomic_replace`) with `Storage::
rewrite_log_streamed`: header and sealed frames stream straight to
`<path>.tmp` through a `FrameSink` buffer pinned at `kCompactBufSize` = 256
KiB for the whole run, committed with the unchanged sequence — `fsync(tmp) →
close → rename → reopen → fsync(dir)`. A companion `compacted_image_size`
computes the exact final byte count arithmetically (no allocation) for
`maybe_compact`'s open-time heuristic. On-disk bytes, the digest, and the
erase→tombstone→compact shrink proofs are all unchanged; only how the
replacement image gets built differs.

**VmHWM at 50k entities × 3 fields, before vs. after (manual RSS harness, same
machine/flags discipline as chapter 1; not CI-asserted).** Plaintext and
encrypted variants run in one process, so VmHWM — a high-water mark — carries
over between them; the per-variant **delta** isolates the compaction
transient, which is the figure Phase 4 targets, not the absolute level:

| | before Phase 4 (Δ, before→after compact) | after Phase 4 (Δ, before→after compact) | reduction |
|---|---:|---:|---:|
| plaintext | 34.1 MB (87.9→122.0 MB) | 0.33 MB (56.3→56.6 MB) | **−99.0%** |
| encrypted | 1.8 MB (129.8→131.7 MB) | 0.26 MB (56.6→56.9 MB) | −85.9% |

Log sizes before/after compaction are byte-identical to the pre-Phase-4
numbers (32,247,058→27,172,382 B plaintext; 30,992,794→28,772,446 B
encrypted): the streamed writer produces the same image `serialize_state`
did — it just never holds all of it in RAM at once. The encrypted delta was
already small pre-Phase-4 (the AEAD path's own per-frame transients dwarfed
the plaintext gap); Phase 4 still cuts it by 85.9%, and the cap/rev frame is
exactly why encrypted doesn't collapse as far as plaintext's −99.0% — see the
peak-allocation bound below.

**Peak single allocation during compaction (`compact_stream_test`, CI-gated
`if(NOT SYNC_SANITIZER)` per §3.4 amendment 8, not benched — same discipline
as chapter 7's fsync counts).** A 50k-entity engine holding granted
capabilities *and* a revocation (so the cap/rev frame — the largest possible
single frame — actually streams through the writer under the probe) compacts
to a 27,172,851 B (plaintext) / 28,772,979 B (encrypted) image. Measured
largest single allocation on **both** paths: **262,145 B** — essentially the
`FrameSink` buffer itself — against the corrected bound of **2,056,336 B**
(`kCompactBufSize` + 3× the largest single frame; at `kMaxIngestedCaps`=4096
the capability/revocation blob set, not an entity frame, sets that bound —
~1.8 MB of `seal_frame` transients on the encrypted path, §3.4 amendment 4)
and over 100× below the compacted image itself. That gap is the
discriminator: the pre-Phase-4 `serialize_state` built the whole image as one
`std::string`, so its single largest allocation was >= the image size — this
test fails on that code in both directions the assertions pin (bound
exceeded; image not large enough relative to the bound).

## Chapter 9 — deadline-cached read-scoped range views ✅

A peer whose read scope depends on a finite-expiry capability used to be
excluded from the per-peer snapshot cache entirely (`ensure_scoped_cache`
returned an uncached `build_filtered`), so **every** gossip cycle — idle,
converged ones included — re-encoded that peer's whole visible set. Phase 5
(`docs/IMPROVEMENT_PLAN.md` §3.5) gives such a peer a `ReconView`: an immutable
set of base-index ranges over a `ReconSnapshot`, plus prefix sums over those
ranges, cached per peer in `sync_engine::scoped_view_cache` under two
invalidations — the `GenPair` guard (writes/applies/GC, grants/revokes/ingest)
and a wall-clock `valid_until_ms` deadline, since capability expiry moves no
counter.

Measured in this container (4 × 2.8 GHz, GCC, `-O2` bench TU against a Release
engine, `--benchmark_min_time=0.5s`; treat ratios as the signal, not absolute
ns). N is the total element count target, and `/D` is the visible fraction
1/D — D namespaces, of which the peer may read one.

**The win — an idle, converged link** (`BM_ScopedSessionBeginIdleTimeBound`,
against `...IdleUncached`, which drops the deadline-keyed entry each cycle and
so reproduces the pre-phase "never cache a time-bound scope" path exactly):

| shape | before (uncached) | after (deadline-cached) | ratio |
|---|---|---|---|
| 4096 /100 | 253.7 µs | 144 ns | 1762× |
| 4096 /10 | 265.8 µs | 141 ns | 1885× |
| 4096 /2 | 950.1 µs | 144 ns | 6597× |
| 16384 /100 | 674.2 µs | 147 ns | 4584× |
| 16384 /10 | 1133.2 µs | 141 ns | 8039× |
| 16384 /2 | 4741.5 µs | 147 ns | 32254× |

The "after" column is flat in both N and the visible fraction, as it should be:
a cache hit is one map lookup plus one deadline compare.

**The regression that had to be gated first (§3.5 fix 3).** Ranging over the
engine's *shared* unscoped snapshot means building that snapshot — O(N)
encodes — where the old filtered path encoded only O(N_visible). Measured
write-active (one overwrite per iteration, so every cycle rebuilds), against
`BM_ScopedSessionBeginPermanent` — a permanently-restricted peer of the same
shape and visible fraction, which pays exactly the filtered rebuild the
time-bound peer used to — as the "before", with `build_view`'s gate
(`share_base = base_is_current(e) || fully_open`, `reconcile.cpp`) forced to
`share_base = true` unconditionally to measure the ungated path directly
(reverted immediately after measurement — this is not a shipped mode):

| shape | filtered rebuild (before) | shared-base view, **ungated** | ungated loss |
|---|---|---|---|
| 4096 /100 | 310.4 µs | 2070.0 µs | 6.67× |
| 4096 /10 | 316.3 µs | 1889.3 µs | 5.97× |
| 4096 /2 | 1004.6 µs | 1893.8 µs | 1.88× |
| 16384 /100 | 708.9 µs | 11109.1 µs | 15.65× |
| 16384 /10 | 1205.5 µs | 10836.5 µs | 8.99× |
| 16384 /2 | 4340.3 µs | 10518.0 µs | 2.42× |

Material, and worst exactly at the small visible fractions this item exists to
serve. **Measured crossover:** the ungated loss falls as the visible fraction
rises, but does not reach parity anywhere tested — even at the largest
fraction measured (1/2 visible), the ungated path is still 1.88–2.42×
regressive; it only approaches 1.0× in the limit as the visible fraction
approaches 1.0 (the peer reads everything, so filtering and sharing converge
to the same work). There is no visible fraction below "reads everything" at
which sharing the base for free is safe to assume — so `build_view` ships
**gated**: it ranges over the shared unscoped snapshot only when that snapshot
is already current (`base_is_current(e)` — `recon_cache` built by any other
consumer, or no write since this peer's last cycle) or when the peer may read
all of it anyway (`fully_open`); otherwise the view wraps its **own** filtered
snapshot in one full-span range — same view type, same accessors, same
deadline cache. This binary "is the base already paid for" gate is both
necessary (the measured 6.67–15.65× ungated loss above) and sufficient (no
further visible-fraction or multi-consumer threshold is needed on top of it,
per the gated numbers below) — the design's open question from fix 3 is
closed by measurement, not left as a tunable. With the gate in place,
write-active cost is at parity with the old filtered rebuild:

| shape | filtered rebuild (before) | **gated** view (after) | ratio |
|---|---|---|---|
| 4096 /100 | 329.8 µs | 311.9 µs | 0.95 |
| 4096 /10 | 339.4 µs | 313.8 µs | 0.92 |
| 4096 /2 | 1021.9 µs | 1019.9 µs | 1.00 |
| 16384 /100 | 714.0 µs | 719.2 µs | 1.01 |
| 16384 /10 | 1223.7 µs | 1229.3 µs | 1.00 |
| 16384 /2 | 4603.6 µs | 4616.8 µs | 1.00 |

(Ratios in [0.92, 1.01] are run-to-run noise in this container at these sizes;
the before/after columns come from separate `./build/bench` invocations.) Note
that both write-active columns are dominated by the one ~86 µs EdDSA sign the
overwrite pays; the idle table above is the honest measure of the phase's
steady state.

**Debug cross-check cost.** Every `build_view` compares itself element-for-
element and prefix-sum-for-prefix-sum against a from-scratch `build_filtered`
under `#ifndef NDEBUG`, so it is live on all four sanitizer legs (they build
`Debug`). Pre-agreed downgrade trigger, documented before the first CI run
(§3.5 fix 9): if measured CI wall time regresses materially, sample the check
once `visible > 4096` rather than remove it. Not implemented — the unsampled
check is what ships.

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
7. **Faster per-element hash** — ~~the snapshot build SHA-256s every element~~
   this item proposed swapping to BLAKE2b for the per-element hash; chapter 6
   shipped the element-hash **cache** instead — same SHA-256, wire-compatible
   (fingerprints, `digest`, and the on-disk format are all byte-identical, no
   schema bump) — because the snapshot build no longer hashes at all (measured
   63.7–85.1% of the cold build depending on N, [not the ~35% this item
   originally estimated pre-chapter-5 — that figure is stale; see chapter 6's
   reconciliation for the corrected, measured shares]). What remains
   hash-bound is mutation-time (~1–2 µs per signed record, ~3% of a new-cell
   `set`), where BLAKE2b's ~4× would now buy little against the ~86 µs sign
   that already dominates that path. Still an internal fingerprint detail if
   ever revisited: any hash-algorithm change would shift the on-wire
   fingerprint, so it would need version-gating.

Each subsequent chapter takes one item, re-runs `./build/bench` against this
baseline, and records the delta here.
