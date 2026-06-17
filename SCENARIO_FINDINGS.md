# Kome scenario test campaign — 2026-06-17

Setup: desktop `192.168.50.50` (x86_64) ↔ Raspberry Pi `192.168.50.96` (ARMv6, 1 core), one LAN.
Keys (deterministic from seed): A(seed1)=`e74dec0a…`  B(seed2)=`8247220389…`.
Constraints found: no passwordless sudo on either box (root-gated tools replaced with no-root substitutes); Pi rebuild ≈13 min/binary.

Goal: run the full scenario matrix thoroughly, surface issues.

## Status legend
✅ pass · ⚠️ issue/anomaly · ⏳ running · ⛔ blocked/skipped (reason)

## Results

| # | Scenario | Status | Notes |
|---|----------|--------|-------|
| 8 | STUN egress (both) | ⏳ | |
| 2 | Hard crash recovery (kill -9) | ⏳ | |
| 1 | Partition & heal (STOP/CONT) | ⏳ | |
| 5 | Relay/rendezvous on LAN | ⏳ | needs netnode on Pi |
| 3 | Degraded link (userspace impairment proxy) | ⏳ | |
| 4 | Clock skew (LD_PRELOAD shim) | ⏳ | |
| 9 | Load soak + compaction + throughput | ⏳ | needs --write-interval |
| 10 | Concurrent same-key write (LWW conflict) | ⏳ | needs --write-key |
| 11 | Deletion / tombstone convergence | ⏳ | needs --delete-interval |
| 13 | At-rest encryption live sync | ⏳ | needs --key |
| 7 | Large initial divergence (reconcile cost) | ⏳ | |
| 6 | Cross-arch bench (perf portability) | ⏳ | |
| 12 | Capability read-scoping over the wire | ⏳ | |

## Detailed findings

(appended as scenarios run)
