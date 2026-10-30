#!/usr/bin/env bash
# Build and check the Lean development. Uses the Lean 4 toolchain from nixpkgs
# when `lake` is not on the PATH (as in the authoring environment, where elan
# could not be installed). With elan installed, plain `lake build` also works.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
if command -v lake >/dev/null 2>&1; then
  lake build
else
  nix --extra-experimental-features 'nix-command flakes' shell nixpkgs#lean4 --command lake build
fi
