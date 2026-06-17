# Kome scenario test campaign — 2026-06-17

Setup: desktop `192.168.50.50` (x86_64) ↔ Raspberry Pi `192.168.50.96` (ARMv6, 1 core), one LAN.
Keys (deterministic from seed): A(seed1)=`e74dec0a…`  B(seed2)=`8247220389…`.
Constraints found: no passwordless sudo on either box (root-gated tools replaced with no-root substitutes); Pi rebuild ≈13 min/binary.

Goal: run the full scenario matrix thoroughly, surface issues.

## Executive summary

Ran 14 scenarios on the real desktop↔Pi LAN. **11 pass, 2 real bugs, 1 partial (perf).**
The engine core is solid across architectures (x86_64 ↔ ARMv6): crash recovery, partition/heal,
degraded links (loss+reorder), clock skew, deletion/tombstones, large divergence, multi-hop, and
at-rest encryption all converge correctly. Two real issues found, **both in the networking/gossip
driver layer, not the engine**:

- **FINDING-1 (medium):** a single *contended* cell written faster than the gossip interval can make a
  long-running netmesh node wedge — permanently diverged on that cell until restart. **Intermittent
  (~50% — a timing race).** Distinct-key workloads always heal on drain; only same-cell-faster-than-
  gossip wedges. Engine/reconcile/scoping are all correct (proven in-process); the bug is in the
  `SecurePeerSession`/`ReliableLink` gossip-driver layer (likely a stop-and-wait desync under rapid
  re-kick).
- **FINDING-2 (high):** `netnode` (the documented production real-network vehicle, single-shot
  `connect_and_sync`) **fails to establish cross-host** (desktop↔Pi) — direct and relay. `netmesh`
  (gossip, with reset-on-silence) converges cross-host every time. Not latency-triggered (proxy 150ms
  fine); needs the real Pi. Almost certainly pre-existing (cross-host netnode was never CI-tested).
  Fix: give `connect_and_sync`/netnode a handshake retry/reset.

Net: **prefer the `netmesh`/gossip path for real-network use** (robust), and the two driver bugs are
the priorities. Test tooling (netmesh `--write-*`/`--key` flags, UDP impairment proxy, clock-skew
shim) is on branch `test/scenario-drivers`.

## Status legend
✅ pass · ◑ partial · ⚠️ issue/anomaly · ⏳ running · ⛔ blocked/skipped (reason)

## Results

| # | Scenario | Status | Notes |
|---|----------|--------|-------|
| 8 | STUN egress (both) | ✅ desktop | reflexive 67.180.163.91; pi pending batch build |
| 2 | Hard crash recovery (kill -9) | ✅ | cross-arch; B reloaded intact after kill -9, reconverged to 1330 recs |
| 1 | Partition & heal (proxy 100% drop) | ✅ | live anti-entropy on heal; converged to union (546 recs) |
| 5 | Relay/rendezvous on LAN | ⚠️ **BUG** | services OK same-host; netnode fails cross-host — see FINDING-2 |
| 3 | Degraded link (proxy: 20% loss + jitter) | ✅ | converged (80 recs, 30c8c459) despite loss+reorder |
| 4 | Clock skew (LD_PRELOAD +1h) | ✅ | converged; A's HLC pulled forward to B's skewed time |
| 9 | Load soak (distinct keys) + drain | ✅ | 98 records, converged after drain |
| 10 | Concurrent same-key write (LWW conflict) | ⚠️ **BUG** | gossip wedges under write-rate > gossip-rate; see FINDING-1 |
| 11 | Deletion / tombstone convergence | ✅ | deletes propagate + converge; export retains tombstoned regs (by design) |
| 13 | At-rest encryption live sync | ✅ | converged; KOMEENC1 magic, no plaintext leak, wrong-key rejected |
| 7 | Large initial divergence | ✅ | 691+691 disjoint → union 1382, converged |
| 6 | Cross-arch bench (perf portability) | ◑ | desktop done (Verify 57µs dominates); Pi ARMv6 build too slow for window |
| 12 | Capability read-scoping | ✅ | connection_test/security_test pass + repro2 scoped converged; no cross-wire CLI |
| 14 | Multi-hop 4-node ring (3 desktop + Pi) | ✅ | converged to union (78 recs) cross-arch; needs drain ≥ load (see note) |

## Detailed findings

### FINDING-1 (⚠️ real bug): gossip wedges on a contended cell written faster than the gossip interval

**Symptom:** two nodes both writing the *same* cell (`load/hot/v`) concurrently, faster than the
gossip interval, end up **permanently diverged on that cell** — and stay diverged even after all
writes stop, until a process restarts.

**Reproduction (desktop, two procs):**
`netmesh … --write-interval 50 --write-key hot --write-for 4 --seconds 14 --interval 300` on both →
A keeps `7301-75`, B keeps `7302-75`, different digests, no recovery in a 10 s same-process drain.

**Write-rate sweep (gossip interval 300 ms):** 50 ms / 150 ms → DIVERGED; 400 ms / 1000 ms → converged.
The trigger is **write period < gossip period on a contended cell.**

**It is a probabilistic timing RACE, not deterministic.** 4 clean repeats of the 50 ms repro gave
DIVERGED / CONVERGED / CONVERGED / DIVERGED (~50%). Adding an `fprintf` to the initiator's `poll()`
made it converge every time (Heisenbug) — perturbing the timing hides it, which is itself strong
evidence of a race rather than a logic error. When it does *not* trigger, the contended cell converges
normally; when it does, the divergence is permanent (until restart). The initiator keeps kicking fresh
cycles fine (`idle=1 -> KICK` every ~300 ms in the instrumented run), so the wedge is **not** a stuck
kick — most likely the per-connection `ReliableLink` (stop-and-wait, lives across reconcile cycles)
desyncs its seq/ack under rapid re-kick in a losing interleaving. `reset()`/fresh process rebuilds the
link and heals.

**Localization (what is NOT broken):**
- Pure-engine reconcile of the identical conflicting state (`/tmp/repro2`, plain *and* scoped sessions)
  → converges to the correct LWW winner. Engine merge + `register_cmp` + scoping are correct.
- Pre-seeded static conflict over the network, `--interval 0` (single `connect_and_sync`) **and**
  `--interval 300` (gossip) → both converge. The transport + single-cycle path are correct.
- Distinct-key fast writes (#9, 100 ms < 300 ms) → converge. Only a *contended* cell triggers it.
- The diverged DBs **heal immediately when reopened by fresh processes** → data is always
  reconcilable; the wedge is in-memory session state of the long-running gossip loop.

**Conclusion:** the bug is in the **`SecurePeerSession` repeated-gossip-cycle logic** (new code on
`test/scenario-drivers`, shared with the merged `netmesh` feature). Strong hypothesis: when writes
arrive faster than a cycle completes, a reconcile cycle is interrupted and the per-peer session is
left holding a stale snapshot (the responder only re-snapshots on `sess_done`; the initiator only
re-kicks when the link is idle) — so it keeps exchanging stale fingerprints and never delivers the
latest contended value, and does not self-heal after writes stop. NOT confirmed to the exact line
yet (no fix attempted, per debugging discipline).

**Impact:** a convergence-*liveness* violation for high-frequency writes to a single shared cell.
Low for Kome's stated use (records/notes/contacts, not high-rate same-cell edits), but real — it
breaks "convergence is the law" for a contended hot cell, and a wedged node needs a restart to heal.
Does **not** affect the `connect_and_sync` path used by `netnode`, nor distinct-key workloads.

**Suggested next step (for a fix PR, not done here):** make the initiator re-kick on a stale
`state_gen` regardless of link-idle, and/or have both sides refresh their snapshot when `state_gen`
advanced since the session began, even mid-cycle. Add a regression test to `securemesh_test`
(contended cell, write-rate > gossip-rate, assert convergence after a drain).

### FINDING-2 (⚠️ real bug, high impact): `connect_and_sync` (netnode) cannot establish cross-host without handshake retry

**Symptom:** every `netnode` cross-host (desktop↔Pi) attempt **failed to converge** — direct (`--peer`)
and relay/rendezvous, with `0.0.0.0` *and* specific-IP binds. Both sides print
`direct/managed sync: failed`, no progress past the handshake. Meanwhile **`netmesh` converges
cross-host every time** (overnight soak, crash→1330, encryption, etc.).

**Isolation:**
- `connection_test` (in-process) and desktop↔desktop relay (`#5c`) via `connect_and_sync` → converge.
  So `connect_and_sync` works same-host.
- `netmesh --interval 0` (a **single** reconcile cycle — same as `connect_and_sync` — but driven by
  netmesh's loop **with reset-on-silence**) → **converges cross-host** (`468e9e22`).
- The only relevant difference between the two drivers is that netmesh re-handshakes a peer after
  `kResetMs` (2 s) of no progress (`reset()`); `connect_and_sync` never resets — it relies solely on
  the reliability-layer retransmit and otherwise waits out its 20 s timeout.

- **Latency is NOT the trigger:** `netnode` direct desktop↔desktop *through the impairment proxy*
  at 0/50/150 ms delay all **converged**. So FINDING-2 needs the real Pi — most likely its slow ARMv6
  CPU (handshake crypto ~10–50× slower) or a real cross-host stack detail, not RTT.

**Conclusion:** on a real cross-host path the initial handshake gets stuck in a way the reliability
retransmit alone does not recover, but a full re-handshake (reset) does. `connect_and_sync` lacks
that, so it times out. **`netnode` — the documented "production path for real-network testing" — does
not actually converge cross-host.** Almost certainly **pre-existing** (the refactor is behavior-
preserving and `connect_and_sync` never had reset; cross-host netnode was always "manual, not run in
CI", so likely never exercised). Not introduced by this branch.

**Impact:** HIGH for the real-network story — the very tool the docs point users to (`netnode`) fails
on the exact scenario it's meant to validate (two real hosts). The engine/transport/crypto are fine
(netmesh proves it); the gap is the single-shot driver's lack of retry.

**Suggested fix (not done here):** give `connect_and_sync` a reset-and-retry-handshake on silence
(port `kResetMs`/`reset()` from the gossip loop), or have `netnode` retry `connect_and_sync` on
failure. Then re-run the cross-host runbook. Consider this the reason to prefer the `netmesh`/gossip
path for real-network use.

### #5 services: relay + rendezvous daemons work (same-host); cross-host blocked by FINDING-2
Desktop↔desktop relay-only via `netnode` → both `managed sync: relay`, 6 records (converged).
Rendezvous discovery works cross-host (initiator learned the peer's reflexive endpoint
`192.168.50.96:35500`). But the subsequent `netnode` sync fails cross-host for the FINDING-2 reason.

### #9 (✅): load soak with distinct keys converges after drain
Two nodes, `--write-interval 100 --write-for 5 --seconds 12` → 98 distinct records, identical digest
`1840597d` after the drain. Confirms distinct-key load + the drain methodology. (Note: stopping
*during* writes shows expected eventual-consistency lag, not divergence.)

### #8 (✅ desktop): STUN egress
`stun_interop` on the desktop → reflexive `67.180.163.91:40865`, real interop PASS. Pi side pending
the batch build.

### #14 (✅): multi-hop 4-node ring, cross-arch
Ring n1–n2–n3–n4(Pi)–n1, each node with 2 peers (first multi-peer test; all prior were 2-node).
Distinct-key writes; converged to union (78 recs, `6086fa69`) on the Pi and all desktop nodes.
**Caveat:** the first attempt (writes every 300 ms = gossip interval, only 17 s drain) showed
non-convergence; re-running with a longer drain converged fully. This confirms FINDING-1's scope:
distinct-key/multi-peer workloads heal once writes stop and drain ≥ the accumulated load — only a
*contended cell* faster than gossip wedges permanently.

### #6 (◑): cross-arch bench
Desktop: `Verify` 57.6 µs (dominant), `Sign` 18.9 µs, `ApplyRegister` 21 ns, `Digest` O(N) — matches
the documented "signature work dominates" profile. The Pi (ARMv6) bench build (GoogleBenchmark +
engine) was too slow to finish in the window; ARMv6 *correctness* is already proven by every
convergence scenario above, so only the perf comparison is outstanding.

### Test methodology notes (no-root substitutes built)
- **UDP impairment proxy** (`/tmp/impair.py`): userspace loss/delay/reorder + a control-file drop
  rate (100 % = partition). Replaces `tc netem`/`iptables` (no sudo). One gotcha found & fixed: it
  must be seeded with fixed peer endpoints (a responder never sends first, so endpoint-learning
  deadlocks).
- **Clock-skew shim** (`/tmp/skew.c`, LD_PRELOAD): offsets `CLOCK_REALTIME` only (HLC source), leaves
  `CLOCK_MONOTONIC` (loop timing) intact. Replaces setting the system clock (no sudo).
- **netmesh test-driver flags** (branch `test/scenario-drivers`): `--write-interval/--write-for`
  (load with a drain phase), `--write-key` (contended cell), `--delete-interval`, `--key` (encrypted).
- Harness note: drive a background proxy/daemon with `wait <pids>` not bare `wait` (bare `wait` blocks
  on the immortal daemon); avoid `pkill -f <pattern>` where the pattern matches the running shell.

### Robustness extras (beyond the 14 — all ✅)
- **Severe loss:** 50% packet loss + 150 ms jitter → converged (54 recs, `5349294a`). Reliability
  layer just retransmits more.
- **Connection flapping:** drop toggled 0↔1 every 1.5 s for 18 s (12 partitions) during writes → after
  settle, converged (90 recs, `40622f27`). Reset-storm resilient.

### Overall verdict
The Kome **engine** is robust across architectures and adverse networks — every correctness scenario
converged (crash, partition, 50% loss, reorder, clock skew, deletes, large divergence, multi-hop,
encryption). The two bugs are both in the **driver/transport layer**: FINDING-1 (gossip wedge on a
contended hot cell, medium) and FINDING-2 (netnode single-shot cross-host failure, high). Neither
touches the CRDT core. Recommended priorities: (1) FINDING-2 handshake retry (unblocks the documented
real-network vehicle), (2) FINDING-1 snapshot refresh under concurrent writes, (3) ship the netmesh
test-driver flags. No data-corruption or convergence-correctness bug was found in the engine itself.
