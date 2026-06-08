# Real-network testing on a $0 stack

A concrete, copy-paste runbook for validating M5 over the real internet for
**free, permanently** — no Lightsail/VPS spend, no trial clock. It pairs an
Oracle Cloud *Always Free* VM (the only thing that needs a public IP) with two
machines you already own behind two different NATs.

What this proves: direct WAN sync (T5.1), relay store-and-forward + blindness
(T5.5/T5.7), NAT hole-punch *and* symmetric fallback (T5.3/T5.4), and durability
(T5.6). The only gap is IPv6 (T5.9), which is backlogged (the UDP layer is
IPv4-only).

> See also `docs/REAL_NETWORK_TESTING.md` (the per-scenario M5 runbook) and
> `tools/netns_real_net_test.sh` (a single-box, zero-cost approximation of the
> relay path on real kernel networking).

---

## The stack

```
  laptop on home WiFi          Oracle Always Free VM            laptop/phone on
  (NAT 1 ≈ full-cone)          (public IP, relay+rdv)           cellular hotspot
        node A  ───────────────────►  relayd :9001  ◄───────────────  node B
                                       rendezvousd :9002
                                       (reflexive discovery may use a
                                        public STUN server, see below)
```

- **Public host:** one Oracle "Always Free" `VM.Standard.E2.1.Micro` (AMD; the
  ARM Ampere shape is nicer but often "out of capacity"). Free for the life of
  the account. Runs `relayd` + `rendezvousd`.
- **Two NATs:** home WiFi (consumer routers are commonly full-cone → you'll see
  `managed sync: direct` via hole-punch) and a phone hotspot / cellular
  (carrier CGNAT is commonly symmetric → you'll see `managed sync: relay`).
  Using two *different* NATs is what makes both code paths fire.

---

## 0. Smoke test first (each client machine, 10 seconds)

Before any of the multi-host dance, confirm UDP egress + reflexive discovery
work from each client, using the engine's own STUN client against a free public
server:

```bash
cmake -B build && cmake --build build --target stun_interop
./build/stun_interop                 # default stun.l.google.com:19302
# -> reflexive (public) endpoint: <your.public.ip>:<port>
# -> PASS: real STUN interop over the internet
```

If this FAILs, your network blocks outbound UDP (some corporate/VM sandboxes
do — e.g. this repo's CI sandbox) and the rest won't work from that host; switch
networks. If it PASSes, that host can do the real test.

---

## 1. Oracle VM: open the UDP ports

Two layers must allow inbound **UDP 9001–9002**:

**VCN security list** (Console → Networking → VCN → your subnet → Security
List → Add Ingress Rule), for each of 9001 and 9002:
- Source CIDR `0.0.0.0/0`, IP Protocol **UDP**, Destination Port `9001` (then
  `9002`).

**Host firewall** (Oracle Linux images ship with a default-deny iptables):
```bash
sudo iptables -I INPUT -p udp --dport 9001 -j ACCEPT
sudo iptables -I INPUT -p udp --dport 9002 -j ACCEPT
sudo netfilter-persistent save 2>/dev/null || true   # or iptables-save
```

---

## 2. Oracle VM: build & run the infra

Either build from source, or paste this as the instance **cloud-init**
(Console → Create Instance → Show advanced → Cloud-init script) to have it ready
on boot:

```yaml
#cloud-config
packages: [git, cmake, g++, make]
runcmd:
  - [ bash, -lc, "cd /opt && git clone https://github.com/hershelshah/kome && cd kome && cmake -B build && cmake --build build --target relayd rendezvousd" ]
  - [ bash, -lc, "iptables -I INPUT -p udp --dport 9001 -j ACCEPT; iptables -I INPUT -p udp --dport 9002 -j ACCEPT" ]
  - [ bash, -lc, "cd /opt/kome && setsid ./build/relayd --listen 9001 >/var/log/relayd.log 2>&1 < /dev/null; setsid ./build/rendezvousd --listen 9002 >/var/log/rdv.log 2>&1 < /dev/null" ]
```

Manual equivalent (SSH'd into the VM):
```bash
cd /opt/kome
./build/relayd      --listen 9001 &      # blind store-and-forward
./build/rendezvousd --listen 9002 &      # signed endpoint broker
```

Note the VM's **public IP** (call it `PUB`).

---

## 3. Clients: exchange keys, then run

Keys are deterministic from `--seed` here, so each side can print the other's
key offline:

```bash
KA=$(./build/netnode --seed 1 --print-key)   # node A's key
KB=$(./build/netnode --seed 2 --print-key)   # node B's key
```

**Node B** — laptop/phone on cellular, capture output to a log:
```bash
./build/netnode --db b.db --seed 2 --port 0 --role responder \
    --rendezvous PUB:9002 --relay PUB:9001 --peer-key "$KA" \
    | tee node_b.log
```

**Node A** — laptop on home WiFi:
```bash
./build/netnode --db a.db --seed 1 --port 0 --role initiator \
    --rendezvous PUB:9002 --relay PUB:9001 --peer-key "$KB" \
    | tee node_a.log
```

(For the **LAN-direct** T5.1 variant instead, skip the VM entirely and use
`--peer <other-lan-ip>:<port>` on both — see `REAL_NETWORK_TESTING.md` §1.)

---

## 4. Verify

Copy both logs to one machine (`scp`), then:

```bash
tools/realnet_verify.sh node_a.log node_b.log
```

**PASS** = both printed the *same* `after sync: digest=…` and `records known: ≥6`
(3 local + 3 from the peer). The verifier prints whether each side went
`direct` (hole-punch succeeded) or `relay` (fell back) — record which, per NAT
pair.

---

## What to record per run

NAT types of each client (from `stun_interop`'s reflexive endpoint, or
`stun stun.l.google.com:19302`), whether it went `direct` or `relay`, the two
post-sync digests (must match), and `records known`. File anything that doesn't
converge with both logs attached.

---

## Free alternatives to the Oracle VM

- **Reflexive discovery only:** free public STUN (`stun.l.google.com:19302`,
  `stun.cloudflare.com:3478`) — the client is RFC 5389-compatible. This removes
  the need to self-host STUN, but you still self-host `rendezvous`+`relay`.
- **Other always-free VMs:** Google Cloud `e2-micro` (us-west1), AWS Free Tier
  `t3.micro` (12 months) — same role as the Oracle box.
- **Direct + multi-node only (no NAT logic):** drop several machines onto a
  free Tailscale tailnet (2 peer relays free) for a flat reachable overlay and
  run a ring of `netnode --peer …`. Good for scale/durability over real hosts;
  it bypasses your own NAT traversal, so it does *not* validate hole-punch/relay.
