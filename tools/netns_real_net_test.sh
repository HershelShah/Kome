#!/usr/bin/env bash
# netns_real_net_test.sh — exercise the real cross-host path on a SINGLE Linux
# host using network namespaces, so two nodes talk over the real kernel network
# stack (real sockets, real routing) rather than loopback or the in-process sim.
#
# Topology: two isolated client segments + a public segment for infra. The two
# node namespaces have NO route to each other, so they can only converge via the
# relay — modelling two peers that can't punch a direct path (the relay-fallback
# case). relayd + rendezvousd run in the public namespace.
#
#     ns-a (10.1.0.2) --- ns-pub (10.1.0.1 / 10.2.0.1 / relay+rdv) --- ns-b (10.2.0.2)
#
# Requires: root, iproute2 (`ip`). NOT run in CI (the sandbox lacks `ip`); run on
# a real Linux host:  sudo tools/netns_real_net_test.sh
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
NN="$ROOT/build/netnode"; RELAY="$ROOT/build/relayd"; RDV="$ROOT/build/rendezvousd"
[ -x "$NN" ] && [ -x "$RELAY" ] && [ -x "$RDV" ] || {
    echo "build first: cmake --build build --target netnode relayd rendezvousd"; exit 1; }
command -v ip >/dev/null || { echo "needs iproute2 (ip)"; exit 1; }
[ "$(id -u)" = 0 ] || { echo "needs root (network namespaces)"; exit 1; }

cleanup() {
    for ns in ke_a ke_b ke_pub; do ip netns del "$ns" 2>/dev/null; done
    rm -f /tmp/ke_na.db /tmp/ke_nb.db
}
trap cleanup EXIT
cleanup

# --- namespaces + veth wiring ----------------------------------------------
ip netns add ke_pub; ip netns add ke_a; ip netns add ke_b
ip netns exec ke_pub ip link set lo up
ip netns exec ke_a   ip link set lo up
ip netns exec ke_b   ip link set lo up

# a <-> pub on 10.1.0.0/24
ip link add veth_a type veth peer name veth_ap
ip link set veth_a  netns ke_a
ip link set veth_ap netns ke_pub
ip netns exec ke_a   ip addr add 10.1.0.2/24 dev veth_a
ip netns exec ke_pub ip addr add 10.1.0.1/24 dev veth_ap
ip netns exec ke_a   ip link set veth_a up
ip netns exec ke_pub ip link set veth_ap up
ip netns exec ke_a   ip route add default via 10.1.0.1

# b <-> pub on 10.2.0.0/24
ip link add veth_b type veth peer name veth_bp
ip link set veth_b  netns ke_b
ip link set veth_bp netns ke_pub
ip netns exec ke_b   ip addr add 10.2.0.2/24 dev veth_b
ip netns exec ke_pub ip addr add 10.2.0.1/24 dev veth_bp
ip netns exec ke_b   ip link set veth_b up
ip netns exec ke_pub ip link set veth_bp up
ip netns exec ke_b   ip route add default via 10.2.0.1

# pub does NOT forward between 10.1 and 10.2 (so a and b can't reach each other
# directly — they must use the relay reachable at their own gateway IP).
ip netns exec ke_pub sysctl -q net.ipv4.ip_forward=0

# --- infra in the public namespace -----------------------------------------
ip netns exec ke_pub "$RELAY" --listen 9001 >/tmp/ke_relay.log 2>&1 &
ip netns exec ke_pub "$RDV"   --listen 9002 >/tmp/ke_rdv.log   2>&1 &
sleep 0.5

KA=$("$NN" --seed 1 --print-key)
KB=$("$NN" --seed 2 --print-key)

# b reaches relay/rdv at its gateway 10.2.0.1; a at 10.1.0.1.
ip netns exec ke_b "$NN" --db /tmp/ke_nb.db --seed 2 --port 0 --role responder \
    --rendezvous 10.2.0.1:9002 --relay 10.2.0.1:9001 --peer-key "$KA" \
    >/tmp/ke_nb.out 2>&1 &
sleep 0.5
ip netns exec ke_a "$NN" --db /tmp/ke_na.db --seed 1 --port 0 --role initiator \
    --rendezvous 10.1.0.1:9002 --relay 10.1.0.1:9001 --peer-key "$KB" \
    >/tmp/ke_na.out 2>&1
sleep 1
kill %1 %2 2>/dev/null

echo "===== node A ====="; cat /tmp/ke_na.out
echo "===== node B ====="; cat /tmp/ke_nb.out

da=$(grep -o 'after sync:  digest=[0-9a-f]*' /tmp/ke_na.out | head -1)
db=$(grep -o 'after sync:  digest=[0-9a-f]*' /tmp/ke_nb.out | head -1)
if [ -n "$da" ] && [ "$da" = "$db" ]; then
    echo "PASS: both converged over the real kernel network ($da)"
else
    echo "FAIL: digests differ or missing (A='$da' B='$db')"; exit 1
fi
