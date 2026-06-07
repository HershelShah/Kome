#!/usr/bin/env bash
# Build with gcov instrumentation, run the test suite, and produce a coverage
# report: HTML in coverage-html/ and a committed summary in docs/COVERAGE.md.
#
#   tools/coverage.sh
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BUILD=build-cov
IGN="--ignore-errors=mismatch,source,gcov,unused,empty,negative,inconsistent,corrupt"

JOBS="$(nproc 2>/dev/null || echo 4)"
cmake -B "$BUILD" -DSYNC_COVERAGE=ON -DSYNC_BUILD_TESTS=ON -DSYNC_OOM_TEST=ON >/dev/null
cmake --build "$BUILD" -j"$JOBS" >/dev/null
lcov --directory "$BUILD" --zerocounters -q

# Fail the report if the suite fails — coverage from a red suite is misleading.
ctest --test-dir "$BUILD" --output-on-failure

lcov --capture --directory "$BUILD" --base-directory "$ROOT" \
     --output-file "$BUILD/cov.info" -q $IGN --rc geninfo_unexecuted_blocks=1
lcov --remove "$BUILD/cov.info" \
     '*/third_party/*' '*/tests/*' '*/_deps/*' '/usr/*' \
     --output-file "$BUILD/cov.info" -q $IGN
GENIGN="--ignore-errors=source,mismatch,inconsistent,corrupt,category"; genhtml "$BUILD/cov.info" --output-directory "$ROOT/coverage-html" -q $GENIGN || true

echo
lcov --summary "$BUILD/cov.info" $IGN
python3 "$ROOT/tools/cov_to_md.py" "$BUILD/cov.info" > "$ROOT/docs/COVERAGE.md"
echo "wrote docs/COVERAGE.md and coverage-html/"
