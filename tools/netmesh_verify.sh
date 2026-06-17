#!/usr/bin/env bash
# netmesh_verify.sh — pass/fail check for a secure mesh (netmesh) run.
#
# Each netmesh node prints a report line on exit:
#   [node <port>] knows <n> records (<p> peers)  digest=xxxxxxxx
# Full convergence of an N-node mesh means every node printed the *same* digest
# and `knows N records` (each node contributes one). Collect every node's log
# onto one machine, then:
#
#   tools/netmesh_verify.sh <N> node0.log node1.log ... nodeN-1.log
#
# Exit 0 = PASS (all converged), 1 = FAIL.
set -uo pipefail

[ $# -ge 2 ] || { echo "usage: $0 <expected-record-count> <log>..."; exit 2; }
WANT="$1"; shift

digests=""
fail=0
for f in "$@"; do
    [ -r "$f" ] || { echo "cannot read $f"; exit 2; }
    line=$(grep -E '^\[node .* knows .* records' "$f" | tail -1)
    dig=$(printf '%s' "$line" | grep -o 'digest=[0-9a-f]*' | head -1)
    recs=$(printf '%s' "$line" | grep -o 'knows [0-9]*' | grep -o '[0-9]*')
    echo "  $f: ${line:-<no report line>}"
    [ -n "$dig" ] || { echo "    ✗ no digest"; fail=1; continue; }
    [ "${recs:-0}" -eq "$WANT" ] || { echo "    ✗ knows ${recs:-0}, want $WANT"; fail=1; }
    digests="$digests$dig
"
done

uniq_count=$(printf '%s' "$digests" | grep -c 'digest=')
distinct=$(printf '%s' "$digests" | sort -u | grep -c 'digest=')
echo "--- $uniq_count nodes, $distinct distinct digest(s) (1 = fully converged) ---"
[ "$distinct" -eq 1 ] || { echo "  ✗ digests differ"; fail=1; }

if [ "$fail" = 0 ]; then echo "PASS: mesh converged"; exit 0; fi
echo "FAIL: mesh did not converge — inspect the logs"; exit 1
