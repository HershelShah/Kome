#!/usr/bin/env bash
# Build and run one module's test main (its dependency closure only), then run
# gnatprove on it when the prover is installed. Exit non-zero on any failure.
#   formal/spark/check.sh <module>        # builds tests/test_<module>.adb
#   formal/spark/check.sh all             # every tests/test_*.adb
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
run_one() {
  local m="$1"
  echo "== $m: build"
  gprbuild -q -p -P kome_spark.gpr "tests/test_$m.adb" -XKOME_OBJ="$m"
  echo "== $m: run"
  "./bin/$m/test_$m"
  if command -v gnatprove >/dev/null 2>&1; then
    echo "== $m: prove"
    gnatprove -P kome_spark.gpr -XKOME_OBJ="$m" -u "src/kome-$m.adb" --level=2 --mode=all --report=fail
  else
    echo "== $m: gnatprove not installed; proof skipped (contracts were checked at run time via -gnata)"
  fi
}
if [ "${1:-}" = "all" ]; then
  for f in tests/test_*.adb; do m="${f#tests/test_}"; run_one "${m%.adb}"; done
else
  run_one "$1"
fi
