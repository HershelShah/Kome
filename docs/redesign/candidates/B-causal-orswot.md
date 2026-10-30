# Candidate B — Causal, not temporal (ORSWOT with evidence-backed context)

## 1. Summary

1. No wall clock enters the merge. Every write is a **dot** `(slot, seq)`: the writer's enrollment slot (≤ 256 per collection) and a per-writer sequence number, signed by the writer.
2. Collection state is a bounded ORSWOT: a map `live : dot ⇀ element` plus a **causal context** of one entry per slot. Removal = "dot in context, not in live". No tombstones; removed bytes are freed at once.
3. A context claim about writer W is accepted only with **W-signed evidence** (W's signature on the dot it names) or an **owner-signed fence**. A forged context cannot kill W's future dots (T-NOKILL).
4. Fields are multi-value registers: concurrent writes coexist as separate dots; a pure, pluggable **read-time policy** picks a value. The stored state is causal history only; the policy can change without touching data.
5. Equivocation (same dot, two payloads: clone, bad restore, malice) is resolved by a per-dot lattice (`min` content hash, `removed` on top), so it is deterministic and confined to that writer's dots.
6. Sync = exchange of current context entries + range-based set reconciliation over the live dot set; one session is exactly one lattice join and needs no memory of past sessions (H4).
7. Revocation is a lattice element (a fence on a slot), not an accept/reject gate, so one-sided revocation cannot make record sets differ.
8. Content is end-to-end encrypted under an owner hash-chained epoch key; the sync core is schema-blind and sees only `(dot, ciphertext-hash)`.
9. Every object has an explicit bound; the state model has no sentinels, no counter whose maximum means anything.
10. DATA_MODEL.md §3 rejected ORSWOT because the context "can only be pruned once causally stable". That applies to delta buffers and departed-writer pruning, not to a state-based ORSWOT whose context is one never-pruned `O(W_max)` vector. The rejection does not hold; the real costs are in §8.

## 2. Data model

**Bounds (compile-time constants).** `W_MAX = 256` slots per collection; `Seq ∈ [1, 2^63]`; record id ≤ 64 B; field name ≤ 64 B; value ≤ 65 536 B; key epoch ∈ [0, 2^16); pending buffer ≤ 4 096 elements.

**Element** (the unit of replication, wire and disk; one per field write):

```
slot       u8                      enrollment slot of the writer
seq        u64 LE, decoder rejects 0 and > 2^63
epoch      u16 LE                  collection key epoch used for ct
nonce      24 B
ct_len     u32 LE  (≤ 65 536 + 130 + 16)
ct         XChaCha20-Poly1305(k_epoch, nonce, aad = coll_id‖slot‖seq‖epoch, pt)
sig        64 B  Ed25519_slotkey( coll_id ‖ slot ‖ seq ‖ epoch ‖ BLAKE2b-256(nonce‖ct) )
pt       = rid_len u8 ‖ rid ‖ fld_len u8 ‖ fld ‖ value
```

The signature covers the content *hash*, so `(seq, epoch, H, sig)` — 106 bytes — is a verifiable certificate that the writer issued dot `(slot, seq)` without the payload. That is the evidence a context entry carries.

**Context entry** per slot, a discriminated record (no `0` sentinel; "nothing seen" is the `Unseen` variant):

```
Entry = Unseen
      | Seen { n : Seq,                     -- all dots 1..n of this slot were seen
               ev : (epoch, H, sig),        -- slot-key signature over dot n
               fence : None | Some(f : Seq) } -- owner-signed: dots > f are dead
seen(E, (s,k)) ≜ E[s] = Seen{n, fence} ∧ (k ≤ n ∨ (fence = Some f ∧ k > f))
```

**State** `S = (live : Dot ⇀ Elem, ctx : Slot → Entry)` with invariant `d ∈ dom live ⇒ seen(ctx, d)`.

**Per-dot status lattice.** For each dot, `status_S(d) ∈ {unknown < live(e) < removed}`, where `live(e₁) ⊔ live(e₂) = live(argmin H(e))` (content hash, total on byte strings), `removed` is top, `unknown` bottom. `status_S(d) = removed` iff `seen(S,d) ∧ d ∉ dom live`.

**Exact join.**

```
ctx(S⊔T)[s]  = Unseen ⊔ E = E
             | Seen{n₁,ev₁,f₁} ⊔ Seen{n₂,ev₂,f₂} = Seen{ max(n₁,n₂), ev of the larger n, min_opt(f₁,f₂) }
live(S⊔T)    = { d ↦ argminH(S.live d, T.live d) | d ∈ dom S.live ∩ dom T.live }
             ∪ { d ↦ S.live d | d ∈ dom S.live \ dom T.live ∧ ¬seen(T,d) }
             ∪ { d ↦ T.live d | d ∈ dom T.live \ dom S.live ∧ ¬seen(S,d) }
             minus any d with seen-by-fence(ctx(S⊔T), d)
```

This is the product of per-dot lattices with the entry lattice (`n` max, `fence` min, evidence a function of `n`), hence a join-semilattice (T-JOIN).

**Local write** by slot `s` with `ctx[s] = Seen{n}` (or `Unseen`, then `n = 0`): mint `d = (s, n+1)`, sign, set `ctx[s] := Seen{n+1, ev_d, fence}`, add `d ↦ e` to `live`, and drop from `live` every dot of the same `(rid, fld)` currently visible to `s` (they are already in `ctx`, so dropping is a removal). This *is* the observed-remove multi-value register: only dots the writer observed are superseded.

**Delete record** `rid`: drop every visible dot of `rid` from `live`. A record **exists iff it has at least one live dot**; absence is not a stored fact.

**Read.** For `(rid, fld)` the engine presents the live set `{(slot, seq, value)}`. A policy `π : NonEmptyList(slot, seq, value) → value` must be pure, deterministic and total. Shipped: `max-dot` (tie by `(slot, seq)`), `min-hash`, `app-stamp` (an advisory timestamp inside the value, consulted *only* among true concurrents), `all` (the app shows the conflict). Changing `π` is a UI decision, never a migration.

**Example.** Phone (slot 1), laptop (slot 2). Phone writes `r1.name="Ann"` → `live={(1,1)}`, `ctx[1]=1`. After sync, laptop writes `"Anne"` → `(2,1)` added, `(1,1)` dropped: `live={(2,1)}`, `ctx={1:1,2:1}`. Phone concurrently writes `"Anna"` → `live={(1,2)}`, `ctx={1:2}`. Join: `(1,2)` live at phone, unseen by laptop → live; `(2,1)` symmetric → live; `(1,1)` live at neither → removed. Result `live={(1,2),(2,1)}`: a true conflict, both values shown, `π` chooses. Laptop then deletes `r1`: `live={}`, `ctx={1:2,2:1}`; join with phone removes `(1,2)` because laptop's context has seen it. Both replicas hold `live={}` plus two 128-byte entries. Nothing else remains.

**Add-wins consequence.** If a tablet (slot 3) concurrently wrote `r1.email`, dot `(3,1)` is unseen by the deleter and survives: `r1` exists with only `email`. This is the honest shape of add-wins; §8 says why we do not hide it.

## 3. Clock and identity (H8)

There is no clock. The questions become "what can a writer do to seqs and contexts".

**Wrong clock.** No effect on merge or storage. A far-future advisory stamp can fool the `app-stamp` policy only among genuinely concurrent values of one field, and any causally later write supersedes the dot regardless. Nothing can be pinned.

**Backup restore.** Device W returns with `ctx[s]=Seen{n_b}` while the network holds its dots up to `n > n_b`. If W syncs before writing it sees its own signed dots above `n_b`, adopts `n`, and nothing is lost: its stale live entries are removed by join and its stale removals are valid (it did observe them). If W writes first it mints `(s, n_b+1)` again: an **equivocation**. The per-dot lattice keeps the lower content hash everywhere; W detects it (two valid self-signatures on one dot), jumps to `max+1`, and re-issues the lost write. Damage: W's own post-restore writes; no other writer's dots are affected.

**Cloned key.** Two devices with one key collide on every write until one is re-keyed; each collision deterministically loses one payload. Any replica holding both signatures has a 212-byte **proof of equivocation** for the owner, who fences the slot and enrolls each clone afresh. Damage is bounded to that slot's dots.

**Malicious authorized writer M.** M can (a) write anything and remove any dot *it has seen* (its write authority, as in every design); (b) equivocate on its own dots; (c) burn its own seq space; (d) fill storage within the per-element bounds; (e) attempt fingerprint collisions (§8). M **cannot** (f) advance `ctx[W]` past W's issued maximum, because entries need W's signature on that seq (T-EVID), so W's future dots are never dead on arrival (T-NOKILL); (g) fence anyone; (h) resurrect a removed dot (removal is top of the lattice). (a) is recovered by an owner fence plus a local, non-replicated, bounded quarantine ring of recently removed elements (an undo buffer outside the state).

**Owner misbehaviour** (two enrollments or two fences on one slot) resolves deterministically (lower key hash, lower fence) and is outside the threat model, as today.

## 4. Reconciliation and digest

The sync core is schema-blind. A reconciliation element is `(slot, seq, epoch, H)`; its hash `h(e) = BLAKE2b-256(slot‖seq‖epoch‖H)`. The key space is dots under lexicographic `(slot, seq)`, so one writer's dots are contiguous and a range of missing dots arrives in seq order.

**Fingerprint** of a dot range `R`: `fp(R) = BLAKE2b-256( |R| ‖ Σ_{e∈R} h(e) mod 2^256 )`, prefix-summed so splits are O(1). **Digest of a collection ≜ `fp(all dots)` combined with `BLAKE2b-256(ctx)`** — one definition, used by sync, storage checks and the app (lesson: no second derivation).

**Session** (self-contained messages, idempotent, any byte transport):

1. `HELLO`: `BLAKE2b-256(ctx)` and the peer's enrollment proof. If context hashes differ, each side sends the entries that differ (per-slot compare; ≤ 128 B each; evidence verified on receipt, fences verified against the owner key). Each side snapshots its own pre-session context `ctx₀`.
2. `FP/LEAF/HAVE` over dot ranges exactly as the current engine (16-way split, leaf ≤ 2, ~log₁₆ n rounds). The result of the exchange is the symmetric difference: A learns `A∖B` (dots it holds live that B does not) and receives `B∖A`.
3. **Finalize** at A: for `d ∈ A∖B`: if `seen(ctx_B, d)` and B is write-authorized, drop `d` (B removed it); else send `d`. For `d ∈ B∖A` received: verify signature under slot key, drop if `seen(ctx₀_A, d)` (A removed it) or beyond fence, else add, buffering out-of-order seqs (bounded) until contiguous with `ctx_A[s].n`. Then `ctx_A := ctx_A ⊔ ctx_B`.

The outcome at A is `S_A ⊔ S_B` with the *pre-session* contexts (T-RBSR); the only inputs are the two current states, so no history of earlier sessions is kept. Transfer is proportional to the dot-set difference plus the differing context entries. Relays carry Noise-wrapped frames and learn an opaque routing key, sizes and timing, as today.

## 5. Authorization, encryption, revocation

**Roster.** Collection id `BLAKE2b-256(owner_pk ‖ nonce)`. An enrollment is owner-signed `(coll_id, slot ∈ [0,256), writer_pk, access ∈ {R, RW}, sig)`; slot ≥ 256 is unparseable, so the writer count is bounded *by the type*, not a check. Slots are never reused: after 256 enrollments the owner re-founds the collection (new id, state copied as fresh dots). Readers hold an `R` slot and never mint dots.

**Fence (revocation).** Owner-signed `(coll_id, slot, f)`; joins as `fence := min`. Dots `(slot, k > f)` are dead wherever the fence is held, and a replica that accepted them earlier removes them on join. Writes made before `f` persist: revocation does not destroy a departed contact's contributions.

**Encryption.** The owner holds a hash chain `k_L` random, `k_e = BLAKE2b-256(k_{e+1} ‖ "prev")`, `L = 2^16`. Epoch `e` is published as a keybox record: for each current member, `X25519(owner, member)`-boxed `k_e` (≤ 72 B × members). A member with `k_e` derives every older key, so a new member needs one box; a removed member holding `k_e` cannot derive `k_{e+1}`. Writers encrypt under the highest epoch they know. Removing a reader = fence (if it wrote) + advance epoch.

**Sync admission.** Peers prove an enrolled key on the Noise channel; removals (`seen(ctx_B,d)`, `d ∉ live_B`) are honoured only from `RW` peers, adds from anyone whose elements verify. Gates only delay entry; once in, every fact is a lattice element, so a gate seen on one side only cannot cause divergence (T-GATE).

**What a removed member retains.** Ciphertext and keys up to its last epoch, elements written under a stale epoch by writers who had not yet learned the rotation, and the dot structure. Its fenced key can neither mint accepted dots nor remove anything at an up-to-date peer.

## 6. Storage and GC

Append-only log of checksummed frames `ELEM(e)`, `DROP(d)`, `CTX(slot, entry)`, `ENROLL`, `FENCE`, `KEYBOX`; replay is the join, hence order-independent. Compaction (doubling threshold, atomic rename) rewrites exactly the `live` elements, the 256 context entries, roster, fences and latest keybox.

**Exact rule for when bytes are freed.** The bytes of element `e` with dot `d` are reclaimable iff `status(d) ≠ live(e)`, i.e. `d ∉ dom live` or `live[d] ≠ e` (equivocation loser). This holds the moment the join makes it so: in RAM immediately, on disk at the next compaction. No clock, TTL, epoch horizon or membership knowledge is consulted. Persistent size is always `≤ 2 × (Σ live element bytes + 256·128 B + roster + fences + keybox)`.

The context never shrinks and never needs to: 32 KiB per collection at most, however many removals happened. What DATA_MODEL.md §3 said needed causal stability (pruning a departed writer's entry) is never done; the slot bound makes it unnecessary. Out-of-order elements wait in a bounded pending buffer that is not state: overflow drops them and a later sync refetches.

## 7. Assumptions

A1. Ed25519 signatures are unforgeable; writer private keys are not available to non-writers (a stolen key *is* that writer).
A2. The multiset hash in §4 is collision-resistant against the parties that can insert signed elements (see §8).
A3. BLAKE2b-256 is collision-resistant (content hashes, element identity, key chain).
A4. An honest writer persists its own `ctx[s]` entry before emitting a dot (so seqs are strictly increasing across restarts, modulo the restore case analysed in §3).
A5. Transport delivers bytes eventually to peers that keep retrying; no ordering, no reliability assumed.
A6. The owner key is honest and available for enrollment, fencing and epoch rotation.

## 8. Known weaknesses

1. **Removal has no author.** A removal is "absent from a writer's live set", unverifiable by third parties, so readers cannot propagate deletions and a reader-only path between writers delays them. Signing removals would reintroduce per-removal tombstones.
2. **Add-wins partial records.** Concurrent delete/update leaves the record with the updated field only. A presence register would need either a clock or the "most ops wins" surprise, so we expose it.
3. **Writer lifetime bound.** 256 enrollments per collection, ever; heavy device churn forces re-founding (all dots re-minted).
4. **Equivocation loses writes.** A clone or careless restore drops about half of that writer's colliding writes until re-keyed: confined, but typed data vanishes and must be re-entered.
5. **Additive fingerprint.** `Σ mod 2^256` is not collision-resistant against an authorized writer who chooses content; a collision leaves one range silently unsynced (convergence fails if A2 fails). A lattice hash (1 024 × 16-bit lanes, 2 KiB per fingerprint) fixes it at a cost BLE cannot pay; offer it per transport.
6. **~100 B per field write** (dot 9, epoch 2, nonce 24, sig 64, tag 16), and k concurrent values keep k copies until superseded.
7. **Context exchange is O(writers)** per session, not O(difference); the hash short-circuit makes it 0.6 KiB for five devices, 32 KiB worst case.
8. **A removed reader learns dot structure** (who wrote how much, in what causal order) from any state it retained.
9. **No time ordering of records**: only causality; "latest by clock" is an app policy among concurrents.
10. Deletion is only as universal as sync: a replica that never reconnects keeps its data (inherent to every candidate).

## 9. Proof obligations

T-ENTRY. `Entry` with the join of §2 is a join-semilattice; `Unseen` is its bottom; `seen(·, d)` is monotone in the entry.
T-DOT. `{unknown < live(e) < removed}` with `live(e₁) ⊔ live(e₂) = live(argmin_H)` is a join-semilattice for any total order on `H`.
T-JOIN. `(S, ⊔)` as defined in §2 is a join-semilattice: `S ⊔ S = S`, `S ⊔ T = T ⊔ S`, `(S ⊔ T) ⊔ U = S ⊔ (T ⊔ U)`, and it preserves the invariant `d ∈ dom live ⇒ seen(ctx, d)`.
T-WRITE. A local write by slot `s` minting dot `(s, m)` yields `S' ⊒ S`, and `(s, m)` is unseen by every unfenced state `T` with `T.ctx[s].n < m` (freshness).
T-CONV. Two replicas that have joined the same set of states (local writes and received deltas), in any order, with any duplication, from the same start, are equal. (Corollary of T-JOIN; the analogue of today's `Store.convergence`.)
T-EVID. Under A1, if a replica's `ctx[s] = Seen{n, _, None}` then slot `s`'s key signed a dot with seq `n`. Consequently `n ≤` the maximum seq ever issued by `s`.
T-NOKILL. Under A1, for an unfenced slot `s` and any seq `m` greater than every seq `s` has issued, no reachable state has `seen(ctx, (s, m))`; hence when `s` issues `(s, m)` it is `live` at every replica after join until some replica that observed it drops it.
T-EQUIV. If two elements `e₁ ≠ e₂` carry the same dot, every replica that has joined both holds `live(argmin_H)` or `removed` for that dot, never `live` of the other; the status of every other dot is unaffected.
T-FENCE. The fence is monotone: once a replica's `ctx[s].fence = Some f`, no later state has `(s, k > f)` live, and joining with a replica that lacks the fence cannot resurrect such a dot.
T-GATE. For any admission predicate applied to inputs (signature, enrollment, RW-only removal), the set of states a replica has joined is a subset of the honest set, and joining the remaining ones later yields the same state as joining them all at once (convergence is unaffected by *when* a gate opens).
T-RBSR. The FP/LEAF/HAVE exchange over the dot order terminates in `O(log₁₆ n)` rounds per differing leaf, and finalization computes exactly `S_A ⊔ S_B` with the pre-session contexts, under reorder and duplication of messages.
T-FP. Under A2–A3, `fp(R_A) = fp(R_B)` iff the element multisets are equal; the collection digest is a function of `(live, ctx)` only.
T-GC. Compaction preserves `(live, ctx, roster, fences, keybox)` and therefore the digest; after compaction the log holds no element whose dot status is not `live(e)`.
T-BOUND. For every reachable state, `|ctx| = 256` entries of ≤ 128 B, `|live| ≤` number of live field writes, and every element ≤ 65 682 B; no field of any state has a reserved value.
T-READ. For a fixed pure policy `π`, the application-visible view is a function of `(live, ctx)` alone, so two converged replicas present identical records.

## 10. Self-score

- **C1 — 5.** Convergence needs only A1–A3 (unforgeable signatures, collision-resistant hashes); no clock assumption.
- **C2 — 4.** A rogue writer is confined to its slot and to dots it observed; nobody's future writes can be killed (T-NOKILL); fences recover. Minus one: removal by omission is unattributable.
- **C3 — 4.** ~100 B per field write, 32 KiB fixed per collection; GC is immediate and membership-free. Minus one: per-field signatures and k-way conflict copies.
- **C4 — 4.** Today's RBSR, any transport, blind relays; context exchange adds O(writers) per session.
- **C5 — 4.** Hash-chained epochs give forward secrecy on removal; a removed member keeps old ciphertext, dot structure and stale-epoch writes.
- **C6 — 5.** The core is a product of finite per-dot lattices and a 256-entry array: a SPARK record type directly, and the Lean proofs are lattice algebra plus one signature lemma.
- **C7 — 4.** Same primitives and codec style; the pending buffer and conflict copies cost RAM on tiny devices.
- **C8 — 4.** Conflicts are visible and resolvable by a replaceable policy; deletes are clean; partial records after concurrent delete/update are a documented surprise.
- **C9 — 5.** No sentinels (`Unseen` is a variant), no wrap semantics (`2^63` is just exhausted), bounds in the types, presence is not a stored fact.
