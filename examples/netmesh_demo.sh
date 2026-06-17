#!/usr/bin/env bash
# Secure multi-process mesh demo: launch N netmesh daemons in a ring on
# localhost, each connected to its two neighbours over the *secure* path (Noise
# XX + identity proof + capability-scoped reconcile). Data written on each node
# propagates multi-hop around the ring; all N converge to one digest. This is
# the localhost smoke for the real-network scale runbook (docs/REAL_NETWORK_TESTING.md).
#
#   cmake -B build && cmake --build build --target netmesh
#   examples/netmesh_demo.sh [N] [seconds]
set -euo pipefail

BIN="${NETMESH_BIN:-build/netmesh}"
VERIFY="$(dirname "$0")/../tools/netmesh_verify.sh"
N="${1:-8}"
SECS="${2:-8}"
BASE=$(( (RANDOM % 10000) + 50000 ))
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# Keys are deterministic from --seed, so each node can learn its neighbours'
# keys up front without running.
declare -a KEY
for i in $(seq 0 $((N-1))); do
    KEY[$i]="$("$BIN" --seed $((i + 1)) --print-key)"
done

echo "=== $N-process secure ring on ports $BASE..$((BASE+N-1)), ${SECS}s gossip ==="
pids=()
for i in $(seq 0 $((N-1))); do
    port=$((BASE + i))
    nxt=$(( (i + 1) % N )); prv=$(( (i + N - 1) % N ))
    peers="127.0.0.1:$((BASE+nxt))=${KEY[$nxt]},127.0.0.1:$((BASE+prv))=${KEY[$prv]}"
    "$BIN" --db "$TMP/n$i.db" --seed $((i + 1)) --bind 127.0.0.1 --port "$port" \
           --peers "$peers" --seconds "$SECS" > "$TMP/out$i.txt" 2>&1 &
    pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done

sort "$TMP"/out*.txt | grep -E '^\[node'
echo "---"
"$VERIFY" "$N" "$TMP"/out*.txt
