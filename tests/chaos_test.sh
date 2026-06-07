#!/usr/bin/env bash
# Multi-process CHAOS test: launch N meshnode daemons (durable SQLite, real UDP
# + Noise + reconciliation) in a ring, then repeatedly SIGKILL and restart
# random nodes mid-gossip. After the chaos settles, verify every node's
# database reopens cleanly, holds every node's record (no data loss of
# committed data), and all converge to one digest.
#
#   cmake -B build && cmake --build build --target meshnode sync_engine_shared
#   tests/chaos_test.sh [N] [chaos_secs] [settle_secs]
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${MESHNODE_BIN:-$ROOT/build/meshnode}"
LIB="${SYNC_ENGINE_LIB:-$ROOT/build/libsync_engine.so}"
PYPATH="$ROOT/bindings/python"
N="${1:-6}"
CHAOS="${2:-15}"
SETTLE="${3:-12}"
BASE=$(( (RANDOM % 8000) + 40000 ))
TMP="$(mktemp -d)"
RUNSECS=$(( CHAOS + SETTLE + 30 ))
trap 'for p in "${PID[@]:-}"; do kill -9 "$p" 2>/dev/null; done; rm -rf "$TMP"' EXIT

declare -A PID

start_node() {
    local i=$1
    local port=$((BASE + i))
    local nxt=$((BASE + (i + 1) % N))
    local prv=$((BASE + (i + N - 1) % N))
    "$BIN" --db "$TMP/n$i.db" --seed $((i + 1)) --listen "$port" \
           --peers "$nxt,$prv" --seconds "$RUNSECS" >/dev/null 2>&1 &
    PID[$i]=$!
}

echo "=== launching $N nodes (ports $BASE..$((BASE+N-1))) ==="
for i in $(seq 0 $((N - 1))); do start_node "$i"; done
sleep 2  # initial convergence

echo "=== chaos: ${CHAOS}s of random SIGKILL + restart ==="
END=$(( $(date +%s) + CHAOS ))
cycles=0
while [ "$(date +%s)" -lt "$END" ]; do
    i=$(( RANDOM % N ))
    kill -9 "${PID[$i]}" 2>/dev/null && cycles=$((cycles + 1))
    sleep 0.4
    start_node "$i"     # restart from its persisted database
    sleep 0.6
done
echo "    performed $cycles kill/restart cycles"

echo "=== settle: ${SETTLE}s with all nodes up ==="
for i in $(seq 0 $((N - 1))); do
    kill -0 "${PID[$i]}" 2>/dev/null || start_node "$i"
done
sleep "$SETTLE"

echo "=== stopping all nodes ==="
for i in $(seq 0 $((N - 1))); do kill -9 "${PID[$i]}" 2>/dev/null; done
wait 2>/dev/null

echo "=== verifying (reopen each DB, check convergence + no data loss) ==="
PYTHONPATH="$PYPATH" SYNC_ENGINE_LIB="$LIB" python3 - "$TMP" "$N" "$BASE" <<'PY'
import sys, os
import sync_engine as se
tmp, n, base = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
digests, ok = set(), True
for i in range(n):
    db = os.path.join(tmp, f"n{i}.db")
    try:
        e = se.Engine(b'\x00' * 32, path=db)   # reopen after the crashes
    except Exception as ex:
        print(f"  node {i}: DB FAILED TO OPEN ({ex})"); ok = False; continue
    present = [p for p in range(n)
              if e.exists(b"mesh", ("node-%d" % (base + p)).encode())]
    digests.add(e.digest())
    miss = [base + p for p in range(n) if p not in present]
    print(f"  node {i}: {len(present)}/{n} records"
          + ("" if not miss else f"  MISSING {miss}"))
    if len(present) != n:
        ok = False
    e.close()
print(f"distinct digests across {n} nodes: {len(digests)} (1 = fully converged)")
if len(digests) != 1:
    ok = False
print("RESULT:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
PY
rc=$?
[ "$rc" -eq 0 ] && echo "=== CHAOS TEST PASSED ===" || echo "=== CHAOS TEST FAILED ==="
exit "$rc"
