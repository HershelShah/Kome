#!/usr/bin/env bash
# Build and check the Lean development. Uses the Lean 4 toolchain from the
# pinned nixpkgs (../nixpkgs.pin) when `lake` is not on the PATH; with elan
# installed, plain `lake build` also works.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
if command -v lake >/dev/null 2>&1; then
  lake build
else
  nix --extra-experimental-features 'nix-command flakes' shell "$(cat ../nixpkgs.pin)#lean4" --command lake build
fi
