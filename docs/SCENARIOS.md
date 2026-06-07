# Scenario matrix & correctness coverage

Every scenario below is backed by a test that asserts **data correctness** —
not just "it converged" but that the *right* values survive (no lost updates,
no rollback, deterministic conflict winners). Dimensions: topology × failure
mode × concurrency × timing × data shape × durability × security.

Legend: test file — `c`=convergence, `r`=reconcile, `sec`=security,
`st`=storage, `net`=network, `rel`=relay, `mn`=multinode, `res`=resilience,
`scn`=scenario, `hd`=hardening, `th`=threading.

## Convergence / CRDT correctness

| Scenario | Covered by |
|----------|------------|
| Order-independence + idempotence (random orders, dup records) | c: OrderIndependenceAndIdempotence |
| Two-way convergence (random writes) | c: TwoWayConvergence |
| Delete vs concurrent edit | c: DeleteVsConcurrentEdit; scn: DeleteVsEditThenReAdd |
| LWW determinism (2-way) | c: LwwDeterminism |
| **N-way conflict, order-independent (4 writers, same cell)** | scn: NWayConflictOrderIndependent |
| **Field-level concurrent edits — no lost update** | scn: FieldLevelConcurrentEditsNoLostUpdate |
| **Concurrent add/add → one present entity** | scn: ConcurrentAddAdd |
| **Concurrent delete/delete → absent, idempotent** | scn: ConcurrentDeleteDelete |
| Re-add after delete (single node) | c: ReAddAfterDelete |
| **Delete vs edit then re-add (across nodes)** | scn: DeleteVsEditThenReAdd |
| Tombstone / value independence | c: TombstoneValueIndependence |
| **Stale write never rolls back a newer value** | scn: StaleWriteDoesNotRollBack |
| HLC receive monotonicity | c: HlcReceiveMonotonicity |
| **Clock skew (far future / far past) still converges** | scn: ClockSkewConverges |

## Incremental sync (range reconciliation)

| Scenario | Covered by |
|----------|------------|
| Reconcile result == full-state oracle | r: CorrectnessVsOracle |
| Difference-proportional / sublinear transfer | r: DifferenceProportionalTransfer |
| ~log16(n) round-trips | r: RoundTripsLogarithmic |
| Edge: identical / empty-vs-full / disjoint | r: Edge* |
| Reordered + duplicated protocol messages | r: MessageRobustness |
| Codec round-trip + golden vector | r: CodecRoundTrip / CodecGoldenVector |

## Topology / propagation

| Scenario | Covered by |
|----------|------------|
| Ring / star / random mesh convergence (to N=250) | mn: RingScaling / StarTopology / RandomMesh |
| **Transitive multi-hop (A-B-C-D chain; A↔D never direct)** | scn: TransitiveChainPropagation |
| **Two converged clusters merge → union** | scn: TwoClustersMerge |
| **Fresh empty node bootstraps from a cluster** | scn: FreshNodeBootstrap |
| Enforced namespace at scale (caps gossiped) | mn: EnforcedRingWithCapabilities |

## Failure / recovery (operational)

| Scenario | Covered by |
|----------|------------|
| Crash mid-write, reopen consistent | st: CrashAtomicity; hd: RepeatedCrashRecovery |
| **Durable node crash → restart → rejoin, no data loss** | res: CrashRestartRejoin |
| **Network partition diverges (with conflict) then heals** | res: PartitionHealWithConflict |
| **Offline node misses + makes edits, rejoins, catches up** | res: OfflineNodeRejoinsAndCatchesUp |
| **Sustained random churn (up/down + writes) → no data loss** | res: RandomChurnNoDataLoss |
| Store-and-forward to an offline peer | rel: StoreAndForward |
| Reconnection after a network/IP change | net: ReconnectionResumesSync |
| Lossy/reordering/duplicating datagram link | net: ReliabilityOverLossyLink |
| **Multi-process chaos: SIGKILL + restart real daemons mid-gossip** | tests/chaos_test.sh (real processes; durable; converges, no data loss) |
| Relay/rendezvous daemons (UDP services) | service: RelayLoopback / RendezvousLoopback |
| Connect-and-sync over direct UDP / over relay | connection: DirectPath / RelayPath |
| Connection manager direct->relay fallback | connection: ManagerRelayFallback |
| Invite encode/decode (discovery) | sec: InviteRoundTrip |
| Optional logging hook (no secrets leaked) | sec: LoggerHook |

## Liveness / concurrency

| Scenario | Covered by |
|----------|------------|
| **Writes during an active sync session** | scn: WritesDuringActiveSync |
| Independent engines across threads (no global state) | th: IndependentEnginesNoSharedState |

## Data shapes

| Scenario | Covered by |
|----------|------------|
| Empty / binary (embedded NUL) values | c, r (codec); scn: BinaryAndLargeValues |
| **Large values (~200 KB) round-trip via sync** | scn: BinaryAndLargeValues |
| **Many entities (1000) merge to union** | scn: ManyEntitiesConverge |

## Security / authorization

| Scenario | Covered by |
|----------|------------|
| Capability chain verify; forged/expired/over-broad rejected | sec: CapabilityVerification / WriteAuthorization |
| Write authorization on apply | sec: WriteAuthorization |
| Read scoping (no existence leak) | sec: ReadScoping |
| Cross-namespace misuse rejected | sec: CrossNamespaceMisuse |
| Tamper detection (channel + AEAD) | sec: TamperDetection; crypto |
| Channel bound to EdDSA identity (no replay/MITM) | sec: ChannelIdentityBinding |
| Capability persisted across reopen | st: CapabilityPersistence |
| Capabilities exchanged during sync | sec: CapabilityExchangeDuringSync; mn: EnforcedRingWithCapabilities |
| Decoders survive arbitrary/mutated input | hd: DecodersNoCrashOnArbitraryInput; fuzz/ |

## Known gaps (need a real multi-host / toolchain)

- Kernel-level NAT hole punching, IPv6 path, public STUN (sandbox can't bind
  IPv6 or run `ip`/`iptables`) — covered by the userspace NAT simulator only.
