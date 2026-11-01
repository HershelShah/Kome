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

# gnatwhy3 hangs if TMPDIR names a missing directory, and concurrent runs that
# share the default why3server socket in /tmp crash; give each run its own.
if [ -z "${KOME_TMPDIR_SET:-}" ]; then
  export KOME_TMPDIR_SET=1
  TMPDIR="$(mktemp -d "${TMPDIR:-/tmp}/kome-check.XXXXXX")"
  export TMPDIR
  trap 'rm -rf -- "$TMPDIR"' EXIT
fi

# PROOF_WIP lists modules whose unproved checks are not fatal. Unset means
# the default list; set and empty means none.
PROOF_WIP_LIST="${PROOF_WIP-store}"

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
    # gnatprove exits 0 even with unproved checks; read the summary and fail
    # unless the module is listed in PROOF_WIP (proof known incomplete).
    local total unproved
    total=$(grep -E '^Total ' "obj/$m/gnatprove/gnatprove.out" | head -1)
    unproved=$(echo "$total" | awk '{ if ($NF == ".") print 0; else print $(NF-1) }')
    echo "== $m: $(echo "$total" | sed 's/  */ /g')"
    if [ "$unproved" != "0" ]; then
      case " $PROOF_WIP_LIST " in
        *" $m "*) echo "== $m: $unproved unproved checks (listed in PROOF_WIP, not fatal)" ;;
        *) echo "== $m: $unproved UNPROVED checks"; return 1 ;;
      esac
    fi
  else
    echo "== $m: proof skipped (contracts checked at run time via -gnata)"
  fi
}
if [ "${1:-}" = "all" ]; then
  # Run every module even after a failure, then report all failures.
  failed=""
  for f in src/kome-*.adb; do
    m="${f#src/kome-}"; m="${m%.adb}"
    if ! "$0" "$m"; then failed="$failed $m"; fi
  done
  if [ -n "$failed" ]; then echo "== FAILED:$failed"; exit 1; fi
  echo "== all modules green"
else
  run_one "$1"
fi
