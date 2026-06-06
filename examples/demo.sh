#!/usr/bin/env bash
# Two-node end-to-end demo: two separate processes, two SQLite files, syncing
# over real UDP through the encrypted (Noise XX) + reliable + reconciliation
# stack. Each node writes 3 local records offline, then they converge.
#
#   cmake -B build && cmake --build build --target node
#   examples/demo.sh
set -euo pipefail

BIN="${NODE_BIN:-build/node}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

PA=$(( (RANDOM % 20000) + 20000 ))
PB=$(( PA + 1 ))

echo "=== launching two nodes (A:$PA  B:$PB), dbs in $TMP ==="
"$BIN" --role responder --db "$TMP/b.db" --seed 2 --listen "$PB" --peer "$PA" &
BPID=$!
sleep 0.2
"$BIN" --role initiator --db "$TMP/a.db" --seed 1 --listen "$PA" --peer "$PB" &
APID=$!

wait "$APID"
wait "$BPID"
echo "=== done ==="
