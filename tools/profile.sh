#!/usr/bin/env bash
# Profile a benchmark under callgrind for deterministic per-function instruction
# counts — the right tool here since `perf` needs kernel perf_event access the
# sandbox/CI containers don't grant. callgrind counts instructions, so results
# are stable run to run (unlike wall-clock).
#
#   tools/profile.sh [benchmark_filter] [iters]
#     filter : GoogleBenchmark --benchmark_filter regex (default a full transfer)
#     iters  : iterations to run under callgrind (default 1; counts are exact)
#
# Prints the top self-cost functions; full annotation is in the callgrind out
# file (open with kcachegrind for a call graph).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
command -v valgrind >/dev/null || { echo "valgrind not found"; exit 1; }

BUILD=build-profile
FILTER="${1:-BM_ConvergeFullTransfer/256}"
ITERS="${2:-1}"
JOBS="$(nproc 2>/dev/null || echo 4)"

# RelWithDebInfo: optimized (realistic) but with symbols callgrind can attribute.
cmake -B "$BUILD" -DCMAKE_BUILD_TYPE=RelWithDebInfo -DSYNC_BENCH=ON \
      -DSYNC_BUILD_TESTS=OFF >/dev/null
cmake --build "$BUILD" -j"$JOBS" --target bench >/dev/null

OUT="$BUILD/callgrind.out"
echo "profiling '$FILTER' (${ITERS} iter) under callgrind — this is ~50x slower..."
valgrind --tool=callgrind --callgrind-out-file="$OUT" --quiet \
    "$BUILD/bench" --benchmark_filter="$FILTER" \
    --benchmark_min_time="${ITERS}x" >/dev/null 2>&1

echo
echo "=== top self-cost functions (instruction reads) ==="
callgrind_annotate --threshold=95 --auto=no "$OUT" 2>/dev/null \
    | sed -n '/Ir *file:function/,/^[0-9]* .*PROGRAM TOTALS/d' \
    | grep -E '^\s*[0-9,]+\s' | head -25
echo
echo "full report: callgrind_annotate $OUT   (or kcachegrind $OUT)"
