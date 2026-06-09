# Real-network testing (M5 validation)

The in-container tests use real localhost UDP and an in-process NAT simulator,
which can't exercise actual cross-host paths, kernel NAT, or hole punching. This
is the runbook for validating those on a real network before shipping.

The vehicle is **`netnode`** — the deployable node that drives the *production*
path (`connect_and_sync`: Noise XX + transcript-bound identity proof +
capability-scoped reconcile + authenticated reliability) and, for NATed peers,
`ConnectionManager` (rendezvous discovery → direct/hole-punch → relay fallback).
The two infrastructure daemons are `relayd` and `rendezvousd`.

```bash
cmake -B build && cmake --build build --target netnode relayd rendezvousd
```

**Pass criterion (every scenario):** after sync, both nodes print the *same*
`after sync: digest=…` and `records known: 6` (3 local + 3 from the peer). Each
node prints its public key on startup; `netnode --seed N --print-key` prints it
without running.

> **Status of each M5 acceptance test** is tracked below. What's validated
> in-container vs. what this runbook covers vs. what's not yet implemented.

---

## Scenario 1 — LAN direct (T5.1)

Two hosts on the same network; each knows the other's `ip:port`.

```bash
# host B (192.168.1.20)
./build/netnode --db b.db --seed 2 --bind 0.0.0.0 --port 7002 \
                --role responder --peer 192.168.1.10:7001

# host A (192.168.1.10)
./build/netnode --db a.db --seed 1 --bind 0.0.0.0 --port 7001 \
                --role initiator --peer 192.168.1.20:7002
```

Expect `direct sync: converged` and matching digests. Open udp/7001–7002 in any
host firewall.

---

## Scenario 2 — across NAT, relay fallback (T5.5, T5.7)

Two hosts behind (different) NATs, plus one **publicly reachable** host running
the infrastructure. Tests store-and-forward + relay blindness when a direct path
can't be established.

```bash
# public host P (e.g. 203.0.113.5)
./build/relayd --listen 9001
./build/rendezvousd --listen 9002      # in another shell

# host B (behind NAT 2)   — print A's key first with --print-key
./build/netnode --db b.db --seed 2 --port 0 --role responder \
                --rendezvous 203.0.113.5:9002 --relay 203.0.113.5:9001 \
                --peer-key <A's key>

# host A (behind NAT 1)
./build/netnode --db a.db --seed 1 --port 0 --role initiator \
                --rendezvous 203.0.113.5:9002 --relay 203.0.113.5:9001 \
                --peer-key <B's key>
```

Expect `managed sync: relay` (or `direct` if the punch succeeds — Scenario 3)
and matching digests. The relay only ever sees ciphertext.

---

## Scenario 3 — NAT hole punching (T5.3, T5.4)

Same setup as Scenario 2. The outcome depends on the NATs:

- **Full-cone / address-restricted NATs:** the rendezvous-learned reflexive
  endpoints let the two sides punch a direct path → `managed sync: direct`.
- **Symmetric NATs:** the punch fails and it falls back to `managed sync: relay`.

Run it from behind real consumer routers (full-cone is common) to see `direct`;
run it from behind a symmetric NAT (some mobile carriers) to see the relay
fallback. Both must still converge.

> Reproducible single-box version: `tools/netns_nat_test.sh` builds two NATed
> network namespaces + a public segment on one Linux host (root + iproute2) and
> runs this scenario through the real kernel network stack. See that script.

---

## Scenario 4 — durability & reconnection (T5.6)

Validates offline-first + that a restarted node resumes from its log file.

1. Run Scenario 1 to convergence; stop both nodes.
2. On host A, write while "offline" (no peer running) — re-run with new local
   data, or use the Python/C API against `a.db`.
3. Restart both nodes (same `--db`, same `--seed`); they reconnect and converge,
   and the offline writes propagate. The pre-existing data loads from disk
   (and is re-verified — see SECURITY.md S2).

---

## Multi-hop mesh

`meshnode` (the gossip-ring demo) is **localhost-only** (binds `127.0.0.1`,
addresses peers by port) and hand-rolls the pre-security channel — use it only
for the local `examples/mesh_demo.sh`. For a real multi-node mesh, run several
`netnode` instances and point each at its neighbours (Scenario 1 pairwise), or
script `ConnectionManager` against multiple peer keys.

---

## Multi-node scaling

Cross-host convergence at scale (N = 2, 4, 8, 16, 32, 64) is covered
deterministically in the automated suite by `PowersOfTwo/MultiNodeScale` in
`tests/multinode_test.cpp` — ring, star, mesh, and enforced-namespace
topologies at each N, run both natively and under WASM. To exercise the same
scaling over *real* sockets, run that many `netnode` instances and wire each to
its neighbours (Scenario 1 pairwise around a ring, or a star through one hub).

## Backlog

- **IPv6 (T5.9).** The UDP layer is currently IPv4-only (`AF_INET`/`sockaddr_in`
  in `src/transport/udp.cpp`); `--bind ::` won't work. IPv6 needs `AF_INET6`
  support added to `UdpSocket` (and `netnode`'s `ip:port` parser extended for
  `[v6]:port`) before T5.9 can be validated. This is a feature gap, not a test
  gap, and is **deferred to the backlog** for now.

## Reporting results

For each scenario record: the NAT types, whether it went `direct` or `relay`,
the two post-sync digests (must match), and `records known`. File anything that
doesn't converge with the node logs.
