#!/usr/bin/env bash
# Build and run one module's test main (its dependency closure only), then
# prove the module with gnatprove. Exit non-zero on any failure.
#   spark/check.sh <module>        # builds tests/test_<module>.adb
#   spark/check.sh all             # every tests/test_*.adb
#   PROVE=0 spark/check.sh ...     # skip the proof step
# Toolchain: gnat, gprbuild and gnatprove on PATH; otherwise they are taken
# from nixpkgs (gnat14 + gnatprove), the same set CI uses.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

if ! command -v gnatprove >/dev/null 2>&1 || ! command -v gprbuild >/dev/null 2>&1; then
  if [ -z "${KOME_IN_NIX:-}" ]; then
    exec env KOME_IN_NIX=1 nix --extra-experimental-features 'nix-command flakes' \
      shell nixpkgs#gnat14 nixpkgs#gnat14Packages.gprbuild nixpkgs#gnat14Packages.gnatprove nixpkgs#cvc5 nixpkgs#z3 \
      --command "$0" "$@"
  fi
fi

run_one() {
  local m="$1"
  if [ -f "tests/test_$m.adb" ]; then
    echo "== $m: build"
    gprbuild -q -p -P kome_spark.gpr "tests/test_$m.adb" -XKOME_OBJ="$m"
    echo "== $m: run"
    "./bin/$m/test_$m"
  else
    echo "== $m: no test main (proof only)"
  fi
  if [ "${PROVE:-1}" = "1" ] && command -v gnatprove >/dev/null 2>&1; then
    echo "== $m: prove"
    gnatprove -P kome_spark.gpr -XKOME_OBJ="$m" -u "kome-$m.adb" \
      --level=3 --mode=all --report=fail --warnings=continue
  else
    echo "== $m: proof skipped (contracts checked at run time via -gnata)"
  fi
}
if [ "${1:-}" = "all" ]; then
  for f in src/kome-*.adb; do m="${f#src/kome-}"; run_one "${m%.adb}"; done
else
  run_one "$1"
fi
