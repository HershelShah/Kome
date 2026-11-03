#!/usr/bin/env bash
# Build and run one module's test main (its dependency closure only), then
# prove the module with gnatprove. Exit non-zero on any failure.
#   spark/check.sh <module>        # builds tests/test_<module>.adb
#   spark/check.sh all             # every tests/test_*.adb
#   PROVE=0 spark/check.sh ...     # skip the proof step
# Toolchain: gnat, gprbuild and gnatprove on PATH; otherwise they are taken
# from the pinned nixpkgs (../nixpkgs.pin), the same set CI uses.
set -euo pipefail
# Absolute path to this script: it re-runs itself (inside nix, and once per
# module for "all") after the cd below, where a relative path would not resolve.
SELF="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
cd "$(dirname "$SELF")"

if ! command -v gnatprove >/dev/null 2>&1 || ! command -v gprbuild >/dev/null 2>&1; then
  if [ -z "${KOME_IN_NIX:-}" ]; then
    # The nixpkgs revision is pinned (../nixpkgs.pin) so the provers do
    # not change under the proofs.
    P="$(cat ../nixpkgs.pin)"
    exec env KOME_IN_NIX=1 nix --extra-experimental-features 'nix-command flakes' \
      shell "$P#gnat14" "$P#gnat14Packages.gprbuild" "$P#gnat14Packages.gnatprove" "$P#cvc5" "$P#z3" \
      --command "$SELF" "$@"
  fi
fi

# gnatwhy3 hangs if TMPDIR names a missing directory, and concurrent runs that
# share the default why3server socket in /tmp crash; give each run its own,
# existing directory. The why3server socket and gnatprove's semaphore live
# there, and a long path fails ("failed to open semaphore": sockets are
# limited to about 100 bytes of path), so an inherited TMPDIR that is
# missing, not writable or longer than 40 bytes is replaced by /tmp.
if [ -z "${KOME_TMPDIR_SET:-}" ]; then
  export KOME_TMPDIR_SET=1
  base="${TMPDIR:-/tmp}"
  if [ ! -d "$base" ] || [ ! -w "$base" ] || [ "${#base}" -gt 40 ]; then
    base=/tmp
  fi
  TMPDIR="$(mktemp -d "$base/kome-check.XXXXXX")"
  export TMPDIR
  trap 'rm -rf -- "$TMPDIR"' EXIT
fi

# PROOF_WIP lists modules whose unproved checks are not fatal. Unset means
# the default list, which is empty (every module proves completely); set and
# empty means none.
PROOF_WIP_LIST="${PROOF_WIP-}"

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
  if [ "${PROVE:-1}" = "1" ]; then
    if ! command -v gnatprove >/dev/null 2>&1; then
      echo "== $m: gnatprove not found (set PROVE=0 to run the tests only)"; return 1
    fi
    echo "== $m: prove"
    # gnatprove 14 names its job semaphore without regard to TMPDIR
    # (/dev/shm/sem.why3server<hash>), so two runs at once still crash with
    # "failed to open semaphore" and leave gnatwhy3 orphans spinning. A
    # private TMPDIR is not enough: serialize the prove step.
    mkdir -p obj
    exec 9>obj/.prove.lock
    if command -v flock >/dev/null 2>&1; then flock 9; fi
    gnatprove -P kome_spark.gpr -XKOME_OBJ="$m" -u "kome-$m.adb" \
      --level=3 --mode=all --report=fail --warnings=continue
    exec 9>&-
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
    if ! "$SELF" "$m"; then failed="$failed $m"; fi
  done
  if [ -n "$failed" ]; then echo "== FAILED:$failed"; exit 1; fi
  echo "== all modules green"
else
  run_one "$1"
fi
