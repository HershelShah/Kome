# Candidate A: minimal LWW, made mathematically airtight

## 1. Summary

- One merge rule: per-cell last-writer-wins over a **strict total order on records**, `(t, author, seq, h)`, `h` being the record's own content hash. Totality is by construction, not by a clock invariant.
- `t` is a plain 48-bit wall-clock millisecond, writer-chosen but **capped by a root-signed ceiling** that moves with the roster. No HLC, no engine clock, no adoption of remote time, no saturation point.
- A write to a pinned cell *chases* the cell's floor (`t = floor.t + 1`): read-your-writes holds, and a far-future record shadows a cell only until the next roster refresh or revocation.
- Deletion is a max-register `deleted_at` per entity; fields below it are dominated and physically dropped. Existence is derived from the frontier, never stored.
- The state is the **frontier** `F(H)` of non-dominated records; `F` is a join homomorphism, so dropping dominated records is the GC and is provably invisible.
- The digest *is* the reconciliation fingerprint: a 4096-bit additive accumulator over element hashes, hashed to 32 bytes on the wire.
- Authorization is a root-signed **ROSTER** element (members, wrapped epoch key, ceiling, revocations). Membership = holding the epoch key; record validity never depends on who delivered it.
- Every integer is bounded with no reserved value; exhaustion refuses a write, never wraps.
- Convergence assumes only unforgeable signatures and a collision-free hash; time enters only tombstone expiry, under one liveness assumption.
- Where it breaks: LWW cannot un-ring a wall clock (a chased cell resolves Lamport-style forever), a malicious writer's pre-revocation overwrites stand, and a straggler past the TTL can resurrect.

## 2. Data model

**Identifiers.** `ns` (collection) is 16 bytes, self-certifying: `ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`. `ent` is 16 bytes (app-chosen or random). `field` is 1–32 bytes. `value` is 0–65535 bytes (blobs are chunked into entities above the engine). All lengths are explicit; an empty value is a legal value, not an unset.

**Version.** `v = (t: u48, author: [32]u8, seq: u48, h: [32]u8)`, compared lexicographically, with `author` and `h` as unsigned 256-bit integers. `h` is the record's content hash, so two distinct records never compare equal (Theorem T1). `t = 0` and `seq = 0` are ordinary values.

**Records (canonical content; this is what is hashed and signed).**

```
PUT    0x01 | ns[16] | ent[16] | flen:u8 | field[flen] | t:u48le | seq:u48le | author[32] | vlen:u16le | value[vlen]
DEL    0x02 | ns[16] | ent[16] |                         t:u48le | seq:u48le | author[32]
ROSTER 0x03 | ns[16] | root_pk[32] | salt[16] | gen:u48le | issued_t:u48le | ceiling_t:u48le
            | del_ttl:u48le | epoch:u32le
            | n_members:u8 (≤64)   | members[n]  { sign_pk[32] | dh_pk[32] | role:u8 | nonce[24] | wrapped_key[48] }
            | n_revoked:u16 (≤1024)| revoked[n]  { sign_pk[32] | from_t:u48le }
```

`h = BLAKE2b-256("kome/v4/rec" ‖ content)`. `sig = Ed25519(h)` by `author` (PUT/DEL) or `root_pk` (ROSTER). The element's identity is `h`; the signature is a witness, not part of identity (a signer can mint several valid signatures for one message; they must not be distinct elements). A record is *well-formed* iff bounds hold and its signature verifies; a ROSTER also needs `ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`. Well-formedness is a pure function of the bytes.

**Cells and domination.** A PUT's cell is `(ns, ent, field)`; a DEL's, `(ns, ent)`; a ROSTER's, `ns`. For `H` the set of well-formed records a replica holds:

```
dom(p, H) for PUT p   := ∃ q ∈ H: PUT, cell(q) = cell(p), q.v > p.v
                       ∨ ∃ d ∈ H: DEL, (d.ns, d.ent) = (p.ns, p.ent), d.v > p.v
dom(d, H) for DEL d   := ∃ d' ∈ H: DEL, same (ns, ent), d'.v > d.v
dom(r, H) for ROSTER  := ∃ r' ∈ H: ROSTER, same ns, (r'.gen, r'.h) > (r.gen, r.h)
F(H) := { x ∈ H | ¬dom(x, H) }
```

`F(H)` is the state. `dom` is monotone in `H` (adding records never un-dominates): the one property the GC story rests on (T2, T3).

**Views (pure functions of F).**

```
deleted_at(ns, ent) := max { d.v | d ∈ F, DEL on (ns, ent) }            -- Option
cell(ns, ent, f)    := the unique PUT in F on (ns, ent, f)               -- Option
exists(ns, ent)     := ∃ f. cell(ns, ent, f) ≠ None
void(p)             := ∃ (X, from_t) ∈ ROSTER_max(F).revoked : X = p.author ∧ p.t ≥ from_t
```

There is no presence bit: an entity exists iff it has a live field (an empty record is one field). `void` affects only presentation (a void PUT reads as "cleared, flagged: revoked key"), never membership in `F`; §5 explains why that is forced.

**Example.** Devices A, B; `v` written as `(t, author, seq)`.

```
PUT(E, name,  "Ada")   v=(1000, A, 7)
PUT(E, phone, "555")   v=(1000, A, 8)
DEL(E)                 v=(2000, B, 3)   -> both PUTs dominated, dropped.  F = {DEL@2000}
PUT(E, name, "Ada L.") v=(1500, A, 9)   -> arrives late; 1500 < 2000: dominated on arrival, dropped.
PUT(E, name, "Ada L.") v=(2500, A, 10)  -> F = {DEL@2000, PUT name@2500}; exists(E), phone is gone.
```

Any permutation of these arrivals, with duplicates, yields the same `F` (T3). The concurrent delete-vs-edit resolved by clock, and the resurrected entity carries only the fields newer than the delete: that is the LWW contract, stated plainly.

## 3. Clock and identity

**What a timestamp is.** `t` is the writer's wall clock in ms since the epoch, u48 (range to year 10889), used only through `<`. There is no engine clock, no `tick`, no `receive`. Nothing is adopted from a peer. A remote record can therefore influence a local write in exactly one way: through the floor of the one cell being written.

**Emission (the only clock arithmetic in the system).**

```
floor(cell)  := max(cell(ns,ent,f).v, deleted_at(ns,ent))        -- Option; for DEL: max over all fields of ent and deleted_at
ceil         := ROSTER_max(F).ceiling_t
t_emit       := max(now_ms, floor.t + 1 if floor exists); if t_emit > ceil then t_emit := ceil
seq_emit     := seq_self + 1;  if seq_self = 2^48 − 1 then fail SEQ_EXHAUSTED (no record is produced)
v_emit       := (t_emit, self_pk, seq_emit, h)
status       := SHADOWED if floor exists ∧ v_emit < floor (possible only when t_emit = ceil) else OK
```

A device with no RTC (`now = 0`) works: every write chases, so its cells order Lamport-style. The replica persists `seq_self` and nothing else; a crash cannot mint a reserved value because none exists.

**Ceiling.** `ceiling_t = issued_t + horizon` (≈400 days) in every ROSTER, refreshed by any root-holding device when `now > ceiling_t − horizon/2`. A record with `t > ceil` is **inadmissible**: not applied, as if it had not arrived; the writer holds it and offers it again once the roster propagates. The ceiling makes the order's top unreachable: a malicious writer can pin a cell only to `ceil`, and the next refresh moves `ceil` above it. The root engine refuses to lower a ceiling.

**Identity.** Each device has an Ed25519 key (the `author`) and an X25519 key from one seed. The collection's `root_pk` is a separate owner key that signs only ROSTERs. `seq` is a per-author counter over all its writes. Two distinct records with equal `(author, seq)` are an **equivocation**: ordered deterministically by `h`, both elements if in different cells, and every replica holding both flags the author. A replica receiving a record authored by *itself* with `seq ≥ seq_self + 1` concludes it was restored or cloned, sets `seq_self` past it and raises `SYNC_CLONE_SUSPECTED`.

**H8, case by case.**

| Case | Damage | Bound and recovery |
|---|---|---|
| Clock ahead by δ | Wins conflicts for δ; raises the floor of cells it writes, which then chase and resolve Lamport-style until wall time passes δ. | δ ≤ ceil − now; only cells it wrote. Automatic; the ordering never reverts (§8). |
| Clock behind by δ | Loses concurrent conflicts for δ on cells last written by others; its own cells still chase, so read-your-writes holds. | Same cells only. `t` is not own-monotone, so a fixed clock is effective at once. |
| Backup restore | Equivocates until first sync (ordered by `h`, flagged); re-offers old records, all dominated except entities whose DEL expired (§6), which resurrect. | Bounded by writes before first sync and deletes older than `del_ttl`. Engine jumps `seq`; app wipes and resyncs; user re-deletes zombies. |
| Cloned key | Continuous equivocation; no divergence, every replica computes the same `F`. | Flagged; owner issues a ROSTER with a fresh key and `revoked(old, from_t)`. |
| Malicious | Overwrite or delete any cell (LWW power), pin cells to `ceil`, flood garbage entities. Cannot forge, exceed `ceil`, stall sync, or block another writer except by tie at `ceil`. | Overwrites stand until re-entered. Pins last until refresh or revocation, after which chase (`old ceil + 1 ≤ new ceil`) wins. Revoke hides and flags its post-`from_t` writes. |

## 4. Reconciliation and digest

**Elements** are the records of `F` restricted to one `ns`, sorted by `key(e) = kind:u8 ‖ ent[16] ‖ field[32, zero-padded] ‖ h[32]` with `kind` ROSTER=0, DEL=1, PUT=2, so the roster is in the first range of every session.

**Fingerprint.**

```
acc(e)  := BLAKE2b-XOF("kome/v4/acc", h(e), 512 bytes) as an integer mod 2^4096
ACC(R)  := Σ_{e ∈ R} acc(e)  mod 2^4096
fp(R)   := BLAKE2b-256("kome/v4/fp" ‖ |R|:u64le ‖ ACC(R))
digest(ns) := fp(F restricted to ns)
```

`ACC` is homomorphic over disjoint unions, so a block-level prefix array (one 512-byte sum per 64 elements) gives any sub-range in ≤64 additions; only 32 bytes cross the wire. The 4096-bit modulus makes Wagner's k-sum attack cost ≈2^{2√n} = 2^128; the current 256-bit sum falls in ≈2^32 to a member with write access (SECURITY.md, "additive set-fingerprint"). Digest and fingerprint are one function by definition (T6).

**Protocol.** Range-based set reconciliation as in M3: both sides snapshot `F`, exchange `(lo, hi, fp)` descriptors, split 16-way where fingerprints differ, ship elements for ranges of ≤4, finish with a HAVE round. Descriptors are self-contained, so loss, duplication and reordering cost rounds, not correctness: ≤ ⌈log₁₆ N⌉ + 2 rounds, O(Δ · log N) descriptors plus Δ elements (T7). Inadmissible elements (above `ceil`) are skipped and the session continues.

**Transports.** Interactive sync runs inside Noise XX bound to the device key; a relay sees ciphertext and a routing key. Non-interactive paths (mailbox, BLE broadcast, multicast) carry `BUNDLE = ns ‖ epoch:u32 ‖ nonce[24] ‖ AEAD_{k_epoch}(aad = ns‖epoch, n:u16 ‖ elements)` ≤ 64 KiB: unreadable by a carrier, unforgeable by a non-member.

## 5. Authorization, encryption, revocation

**Membership is key possession.** The ROSTER wraps the current 32-byte epoch key to each member's `dh_pk` (`k_wrap = BLAKE2b-256(X25519(root_dh_sk, dh_pk) ‖ ns ‖ epoch)`, XChaCha20-Poly1305). A replica joins a collection by installing a ROSTER; there is no "open" namespace and no second mode. A peer is admitted to a session for `ns` iff its device key is in the locally held `ROSTER_max.members`; a BUNDLE is readable iff the replica holds its epoch key (current or previous). Both are gates on *transport*, not on records: a record's membership in `F` depends only on the bytes of `H`.

**Revocation = new ROSTER** with `gen + 1`, a fresh epoch, the member removed, and optionally `revoked(X, from_t)`. Replicas holding it stop talking to X and stop opening old-epoch bundles; X's records with `t ≥ from_t` become `void` in every view. Old-epoch keys are not retained beyond one generation; a new member gets the frontier in plaintext over the channel, so there is no keyring to grow.

**Why void is a view, not a drop.** Suppose void records left `F`. Replica A applies `p`, then `p' > p` (drops `p`), then the ROSTER voiding `p'` (drops `p'`): the cell is empty. Replica B applies `p`, the ROSTER, then `p'` (void, dropped): the cell holds `p`. Same set, different states: retroactive invalidation plus eager GC diverges unless history is kept. So a void record stays in `F` and keeps dominating; the view hides its content and flags the cell; an honest write chases above it. The honest cost: a thief's overwrites and deletes before revocation *stand*, flagged, and the previous values are gone (§8).

**The accept/reject lesson** disappears: the ROSTER is itself an element and revocation changes no element's dominance, so replicas that disagree about a revocation agree about `F` after one exchange.

**A removed member retains** what it held in plaintext (unavoidable under H2/H3) and can write, including back-dated records (`t < from_t`, not void), to any lagging member until the new ROSTER reaches it. Afterwards: no channel, no readable bundle.

## 6. Storage and GC

**Layout.** An append-only log of `content ‖ sig` frames, each sealed at rest under the device key (unchanged from T3); an in-memory index `cell → (offset, v)`; a per-author `seq` table (≤ members). Compaction rewrites exactly `F`. Memory per cell: 6 + 6 + 32 bytes of version plus a 32-byte cached `h`; the signature lives only in the log.

**GC predicate (run at apply and at compaction; nothing else ever removes a frame).**

```
drop(x) :=  dom(x, H)                                                  -- deterministic, membership-free
         ∨ (x is DEL ∧ now_local ≥ x.t + ROSTER_max.del_ttl)           -- the one clock-dependent clause
```

The first clause frees a deleted entity's *values* the moment the DEL is held, on every replica, with no oracle (T2, T3): a deleted entity costs one DEL frame (≈180 bytes signed) however many fields it had. The second frees the tombstone. `del_ttl` is a replicated ROSTER parameter, so members share one horizon; an expired DEL is also *not applied* on arrival, so a slow-clocked peer re-offering it costs bytes, never state.

**What the TTL clause can do wrong.** A PUT `p < d.v` arriving after `d` was dropped resurrects the entity with that one stale field. It can come only from a holder that never saw `d`: a member that did not sync within `del_ttl` of `d.t` (A4), a backup or mailbox older than that, or a malicious member (who could write a fresh PUT anyway). Damage is bounded to re-deleting.

**Bounds.** `|F(ns)| ≤ #cells with a live value + #DELs younger than del_ttl + 1`. Nothing else accumulates: no clocks, no version vectors, no per-peer session state, no shells.

## 7. Assumptions

- A1. Ed25519 signatures are existentially unforgeable; the root key is not compromised (a malicious root is the owner).
- A2. BLAKE2b-256 is collision-resistant (element identity, order tie-break) and the 4096-bit additive accumulator is k-sum-hard (fingerprint equality ⇒ set equality).
- A3. Honest roots refresh the ROSTER before `ceiling_t − horizon/2`; if no root device is online for a whole horizon, writes clamp to `ceil` and resolve by author until refresh (degraded, convergent).
- A4. For tombstone GC only: every member device syncs with some member at least once per `del_ttl`, and relays retain bundles for less than `del_ttl`.
- A5. Writers keep their own `seq` persistent across restarts (violations are detected, not assumed away).
- A6. No clock assumption of any kind for convergence; wall-clock quality affects only which concurrent write wins.

## 8. Known weaknesses

- **LWW cannot un-ring the bell.** Once a cell's floor is far-future, every later write to it chases and the cell resolves by arrival order rather than wall time, permanently. The ceiling bounds how far, not whether. The only reset is a new `ent`.
- **A compromised device's writes before revocation stand.** No history is kept; the design flags and hides them but cannot restore what they overwrote. A local undo buffer is outside the model.
- **Tombstone GC is time-bound, not causally stable.** A straggler older than `del_ttl` can resurrect. Per-DEL member acknowledgements were examined and rejected: with ≥3 members a replica can be stranded holding a tombstone whose last ACK everyone else already GC'd, so they add chatter without removing the TTL fallback.
- **Inadmissible records weaken the applied-set phrasing.** A record above a stale ceiling is skipped, so T4 is stated over frontier exchange; honest records are never lost because the writer holds them.
- **The ceiling is a liveness dependency on the root**: a horizon without any root device online degrades writes to author-order ties.
- **Garbage floods** by an authorized writer are bounded only by revocation and the owner's DELs; quotas are not in the core.
- **Fingerprint cost.** 512-byte accumulators, 16× the current sum; 8 bytes amortized per element with block prefixes, ≤64 big-integer additions per sub-range.

## 9. Proof obligations

- **T1 (Total order).** For well-formed records `x ≠ y`, exactly one of `x.v < y.v`, `y.v < x.v` holds, given `h` injective on distinct contents. The relation is irreflexive and transitive.
- **T2 (Monotone domination).** For every record `x` and sets `H ⊆ H'`: `dom(x, H) ⇒ dom(x, H')`.
- **T3 (Frontier homomorphism / GC safety).** For all `H₁, H₂`: `F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))` and `F(F(H)) = F(H)`. Hence dropping dominated records at any time, on any subset of replicas, changes no future frontier.
- **T4 (Convergence).** With `apply(S, r) = F(S ∪ {r})` for admissible well-formed `r`, two replicas that applied the same set of records in any orders with any duplication hold the same `F`. With inadmissible records, after a complete reconciliation (T7) both hold `F(H_A ∪ H_B)`.
- **T5 (View determinism).** `deleted_at`, `cell`, `exists`, `void` are functions of `F` alone.
- **T6 (Digest).** `digest(ns) = fp(F|ns)`; `fp` depends on the element set only; `ACC(R₁ ⊎ R₂) = ACC(R₁) + ACC(R₂)`; under A2, `fp(R₁) = fp(R₂) ⇒ R₁ = R₂`.
- **T7 (Reconciliation).** From `F_A, F_B` over N elements, the FP/LEAF/HAVE protocol (16-way split, leaf bound 4) terminates in ≤ ⌈log₁₆ N⌉ + 2 rounds under reliable delivery and in finitely many under loss/duplication/reorder; both sides then hold `F(F_A ∪ F_B)`.
- **T8 (Chase).** If `floor(cell).t < ceil` then `v_emit > floor` (read-your-writes); always `v_emit.t ≤ ceil` and `v_emit.seq` exceeds every `seq` this device ever emitted.
- **T9 (Bounded pin).** No admissible record has `t > ceiling_t` of the maximal held ROSTER; once a ROSTER with a higher ceiling is held, every honest write to any cell is unshadowed.
- **T10 (Equivocation).** Two distinct records with equal `(author, seq)` are ordered identically on every replica; `F` is unaffected by arrival order.
- **T11 (Tombstone GC).** Under A4, dropping `d` by the TTL clause changes no view on any replica, ever.
- **T12 (Revocation locality).** Applying a ROSTER changes `F` only at the ROSTER cell; it never adds or removes a PUT or DEL.
- **T13 (Bounds).** Every emitted record satisfies the §2 layout bounds; `seq` and `t` never wrap; at `seq = 2^48 − 1` emission fails with no side effect.

## 10. Self-score

- **C1 = 4.** Convergence needs A1, A2 and nothing about clocks; the ceiling forces an exchange-form statement (T4) instead of the pure applied-set form.
- **C2 = 3.** Pins are bounded and recover; overwrites and deletes by a malicious writer stand (flagged), garbage floods need manual cleanup.
- **C3 = 4.** ~44 bytes of version metadata per cell, ~180-byte tombstones freed by TTL, values freed deterministically, O(members) per replica, no vectors.
- **C4 = 4.** Log-rounds RBSR over any datagram transport, k-sum-hard fingerprint, blind relays, epoch-sealed bundles; costs 512-byte accumulators locally.
- **C5 = 3.** Removed member keeps what it saw and can back-date into laggards during propagation; afterwards it reads and writes nothing; `void` flags its post-`from_t` writes.
- **C6 = 4.** Trusted core is `<`, `dom`, `F`, `fp` and the emission rule, all over fixed-size arrays; T1–T13 are finite, first-order statements suited to Lean; TTL is the only non-pure clause.
- **C7 = 4.** Same four primitives plus BLAKE2b-XOF and 4096-bit addition; no HLC module, no capability graph search, one authorization mode.
- **C8 = 3.** One rule to explain; deletes-vs-edits resolve by time with field loss; SHADOWED and CLONE_SUSPECTED statuses and void flags surface what the app must show.
- **C9 = 4.** No sentinel values, no derived presence, explicit Option tags, exhaustion refuses instead of wrapping; the only residual derivation is "exists iff a live field", which is a view, not stored state.
