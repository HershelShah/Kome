#!/usr/bin/env bash
# Multi-process mesh demo: launch N gossip daemons (examples/meshnode) in a
# ring, each connected only to its two neighbours. Data written on each node
# propagates multi-hop around the ring; all N converge to one digest.
#
#   cmake -B build && cmake --build build --target meshnode
#   examples/mesh_demo.sh [N] [seconds]
set -euo pipefail

BIN="${MESHNODE_BIN:-build/meshnode}"
N="${1:-5}"
SECS="${2:-6}"
BASE=$(( (RANDOM % 10000) + 50000 ))
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

echo "=== $N-process ring on ports $BASE..$((BASE+N-1)), ${SECS}s gossip ==="
pids=()
for i in $(seq 0 $((N-1))); do
    port=$((BASE + i))
    nxt=$((BASE + (i + 1) % N))
    prv=$((BASE + (i + N - 1) % N))
    "$BIN" --db "$TMP/n$i.db" --seed $((i + 1)) --listen "$port" \
           --peers "$nxt,$prv" --seconds "$SECS" > "$TMP/out$i.txt" 2>&1 &
    pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done

sort "$TMP"/out*.txt
echo "--- distinct digests (1 = fully converged) ---"
grep -ho 'digest=[0-9a-f]*' "$TMP"/out*.txt | sort -u | wc -l
