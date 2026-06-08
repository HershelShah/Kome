#!/usr/bin/env bash
# realnet_verify.sh — pass/fail check for a real-network netnode run.
#
# Each netnode prints `after sync:  digest=<hex>...` and `records known: <n>` on
# exit. Convergence for a two-node test means BOTH printed the *same* digest and
# each knows all 6 records (3 local + 3 from the peer). Run each node with its
# stdout captured to a file, copy both logs to one machine, then:
#
#   tools/realnet_verify.sh node_a.log node_b.log
#
# Exit 0 = PASS (converged), 1 = FAIL. Works for any pair of netnode logs
# regardless of mode (direct / relay / rendezvous).
set -uo pipefail

[ $# -eq 2 ] || { echo "usage: $0 <node_a.log> <node_b.log>"; exit 2; }
A="$1"; B="$2"
for f in "$A" "$B"; do [ -r "$f" ] || { echo "cannot read $f"; exit 2; }; done

# Pull the post-sync digest and record count from each log.
dig()  { grep -o 'after sync:  digest=[0-9a-f]*' "$1" | head -1; }
recs() { grep -o 'records known: [0-9]*' "$1" | head -1 | grep -o '[0-9]*'; }
how()  { grep -oE '(direct|managed) sync: [a-z/]*' "$1" | head -1; }

da=$(dig "$A"); db=$(dig "$B")
ra=$(recs "$A"); rb=$(recs "$B")
ha=$(how "$A"); hb=$(how "$B")

echo "node A: ${ha:-<no sync line>}  ${da:-<no digest>}  records=${ra:-?}"
echo "node B: ${hb:-<no sync line>}  ${db:-<no digest>}  records=${rb:-?}"

fail=0
[ -n "$da" ] && [ "$da" = "$db" ] || { echo "  ✗ digests differ or missing"; fail=1; }
[ "${ra:-0}" -ge 6 ] && [ "${rb:-0}" -ge 6 ] || { echo "  ✗ a node is missing records (want >=6 each)"; fail=1; }

if [ "$fail" = 0 ]; then
    echo "PASS: converged — both at $da with all records"
    exit 0
fi
echo "FAIL: did not converge — inspect the two logs"
exit 1
