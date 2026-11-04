#!/usr/bin/env bash
# Build and check the Lean development. If `lake` is not on the PATH, use
# the Lean 4 toolchain from the pinned nixpkgs (../nixpkgs.pin). If elan is
# installed, plain `lake build --wfail` also works.
#
# `--wfail` turns every warning into a build failure, so a `sorry` (which
# Lean reports as a warning) fails the build. `Kome/Axioms.lean`, which the
# build includes, fails the build when a declaration of `Kome.Frontier`
# uses an axiom outside `propext`, `Classical.choice` and `Quot.sound`.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
if command -v lake >/dev/null 2>&1; then
  lake build --wfail
else
  nix --extra-experimental-features 'nix-command flakes' shell "$(cat ../nixpkgs.pin)#lean4" --command lake build --wfail
fi
