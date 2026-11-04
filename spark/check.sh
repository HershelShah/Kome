#!/usr/bin/env bash
# Build and run the test main of one module (only its dependency closure),
# then prove the module with gnatprove. If a step fails, exit non-zero.
#   spark/check.sh <module>        # builds tests/test_<module>.adb, proves
#                                  # the unit src/kome-<module>.adb
#   spark/check.sh kome            # the root package: no test main, proves
#                                  # the unit src/kome.ads
#   spark/check.sh all             # every module of --list, then the sum
#   spark/check.sh --list          # print the module list, one per line
#   PROVE=0 spark/check.sh ...     # skip the proof step
# A module is a child package Kome.<Module> in src/kome-<module>.adb with
# its test main in tests/test_<module>.adb. The module list is the union of
# the two sets, plus kome. A name that is on one side only (a source
# without a test main, or a test main without a source) is an error, in
# --list as well as in every run. ci.yml builds its matrix from --list.
# Toolchain: gnat, gprbuild, gnatprove and nm on PATH. If gnatprove or
# gprbuild is not on PATH, the script gets the set from the pinned nixpkgs
# (../nixpkgs.pin). CI uses the same set. The proof switches are in
# kome_spark.gpr (package Prove); this script adds only the unit and the
# report switches.
set -euo pipefail
# Absolute path to this script. The script runs itself again after the cd
# below: inside nix, and once for each module for "all". A relative path
# would not resolve there.
SELF="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
cd "$(dirname "$SELF")"

# The module list: kome, then the sorted union of src/kome-*.adb and
# tests/test_*.adb. Fails (exit 1, the reason on stderr) if a name is on
# one side only, or if src/kome.ads is missing.
modules() {
  local names n bad=0
  names="$( { ls src/kome-*.adb tests/test_*.adb 2>/dev/null || true; } \
    | sed 's|^src/kome-||; s|^tests/test_||; s|\.adb$||' | sort -u )"
  if [ ! -f src/kome.ads ]; then
    echo "== kome: src/kome.ads is missing" >&2; bad=1
  fi
  for n in $names; do
    if [ ! -f "src/kome-$n.adb" ]; then
      echo "== $n: tests/test_$n.adb has no src/kome-$n.adb" >&2; bad=1
    fi
    if [ ! -f "tests/test_$n.adb" ]; then
      echo "== $n: src/kome-$n.adb has no tests/test_$n.adb" >&2; bad=1
    fi
  done
  if [ "$bad" != 0 ]; then return 1; fi
  echo kome
  echo "$names"
}

# --list needs no toolchain, so handle it before the nix shell below.
if [ "${1:-}" = "--list" ]; then
  modules
  exit 0
fi
if [ -z "${1:-}" ]; then
  echo "usage: $0 <module> | kome | all | --list" >&2
  exit 2
fi

if ! command -v gnatprove >/dev/null 2>&1 || ! command -v gprbuild >/dev/null 2>&1; then
  if [ -z "${KOME_IN_NIX:-}" ]; then
    # The nixpkgs revision is pinned (../nixpkgs.pin), so the provers do
    # not change under the proofs. binutils gives nm for the symbol check.
    P="$(cat ../nixpkgs.pin)"
    exec env KOME_IN_NIX=1 nix --extra-experimental-features 'nix-command flakes' \
      shell "$P#gnat14" "$P#gnat14Packages.gprbuild" "$P#gnat14Packages.gnatprove" \
      "$P#cvc5" "$P#z3" "$P#binutils" \
      --command "$SELF" "$@"
  fi
fi

# gnatwhy3 hangs if TMPDIR names a missing directory. Concurrent runs that
# share the default why3server socket in /tmp crash. Thus give each run its
# own existing directory. The why3server socket and the gnatprove semaphore
# are in that directory. A long path fails ("failed to open semaphore"),
# because a socket path is limited to about 100 bytes. Thus if an inherited
# TMPDIR is missing, is not writable or is longer than 40 bytes, the script
# uses /tmp in its place.
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

# Proof hygiene: no source may contain a pragma Assume (a hypothesis that
# gnatprove takes without proof) or a pragma Annotate (an instruction to
# gnatprove that hides, skips or accepts a check). Either would make a
# "0 unproved" summary mean less than it says, and the proof-hygiene rules
# of CONVENTIONS.md have no place for them. The grep skips the part of a
# line after "--", so a comment may name them.
hygiene() {
  local hits
  hits="$(grep -rniE --include='*.ads' --include='*.adb' \
    '^([^-]|-[^-])*pragma[[:space:]]+(Assume|Annotate)\b' src tests || true)"
  if [ -n "$hits" ]; then
    echo "== pragma Assume or pragma Annotate in the sources (not allowed):"
    echo "$hits"
    return 1
  fi
}

# The monocypher functions that Kome.Crypto does not bind and that no bound
# function reaches: the Argon2 password hash and the BLAKE2b-512 EdDSA API.
# -ffunction-sections and --gc-sections (kome_spark.gpr) drop them from
# each test binary. The other crypto_eddsa_* functions (trim_scalar,
# reduce, mul_add, scalarbase, check_equation) are the curve arithmetic
# that the bound crypto_ed25519_* functions call, so they stay linked.
# third_party/monocypher/README lists the bound symbols.
# (\.|$): gcc may split a function into name.part.N.
UNBOUND_RE='^crypto_(argon2|eddsa_(key_pair|sign|check|to_x25519))(\.|$)'

run_one() {
  local m="$1" unit
  if ! modules | grep -qx -- "$m"; then
    echo "== $m: not a module (see check.sh --list)"; return 1
  fi
  if [ "$m" = kome ]; then
    unit=kome.ads
    echo "== kome: root package (no test main), unit $unit"
  else
    unit="kome-$m.adb"
    echo "== $m: build"
    gprbuild -q -p -P kome_spark.gpr "tests/test_$m.adb" -XKOME_OBJ="$m"
    echo "== $m: run"
    "./bin/$m/test_$m"
    echo "== $m: unbound monocypher symbols"
    local linked
    linked="$(nm --defined-only "./bin/$m/test_$m" | awk '{ print $NF }' \
      | grep -E "$UNBOUND_RE" || true)"
    if [ -n "$linked" ]; then
      echo "== $m: unbound monocypher symbols are linked:"
      echo "$linked"
      return 1
    fi
  fi
  if [ "${PROVE:-1}" = "1" ]; then
    if ! command -v gnatprove >/dev/null 2>&1; then
      echo "== $m: gnatprove not found (set PROVE=0 to run the tests only)"; return 1
    fi
    echo "== $m: prove"
    # gnatprove 14 names its job semaphore without regard to TMPDIR
    # (/dev/shm/sem.why3server<hash>). Thus two runs at the same time still
    # crash with "failed to open semaphore", and orphan gnatwhy3 processes
    # continue to spin. A private TMPDIR is not sufficient, so serialize
    # the prove step.
    # The lock file is machine-wide (KOME_PROVE_LOCK), not per checkout,
    # because the semaphore is machine-wide too.
    mkdir -p obj
    exec 9>"${KOME_PROVE_LOCK:-/tmp/kome-prove.lock}"
    if command -v flock >/dev/null 2>&1; then flock 9; fi
    gnatprove -P kome_spark.gpr -XKOME_OBJ="$m" -u "$unit" \
      --report=fail --warnings=continue
    exec 9>&-
    # gnatprove exits 0 even with unproved checks. Thus read the summary,
    # and fail on any unproved check.
    local total unproved
    total=$(grep -E '^Total ' "obj/$m/gnatprove/gnatprove.out" | head -1)
    unproved=$(echo "$total" | awk '{ if ($NF == ".") print 0; else print $(NF-1) }')
    echo "== $m: $(echo "$total" | sed 's/  */ /g')"
    if [ "$unproved" != "0" ]; then
      echo "== $m: $unproved UNPROVED checks"; return 1
    fi
  else
    echo "== $m: proof skipped (contracts checked at run time via -gnata)"
  fi
}

hygiene
if [ "$1" = "all" ]; then
  # The list fails on a half-module, before any build.
  list="$(modules)"
  # Run every module even after a failure, then report all failures.
  failed=""
  for m in $list; do
    if ! "$SELF" "$m"; then failed="$failed $m"; fi
  done
  if [ -n "$failed" ]; then echo "== FAILED:$failed"; exit 1; fi
  echo "== all modules green"
else
  run_one "$1"
fi
