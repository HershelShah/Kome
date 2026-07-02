#!/usr/bin/env bash
# The one shell answer to "what version is the engine?" (P7.0c): parses CMake
# project(VERSION), the single source of truth. Python consumers use
# tools/amalgamate.py --print-version (same parse); the wheel metadata uses
# pyproject.toml's regex provider over the same line.
set -euo pipefail
v="$(sed -n 's/^project(sync_engine VERSION \([0-9.]*\).*/\1/p' \
     "$(dirname "${BASH_SOURCE[0]}")/../CMakeLists.txt")"
test -n "$v" || { echo "version.sh: could not parse project(VERSION)" >&2; exit 1; }
echo "$v"
