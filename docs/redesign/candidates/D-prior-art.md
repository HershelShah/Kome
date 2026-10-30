# Candidate D — "Best of the field, from the literature"

Angle: take the strongest *proven* idea per sub-problem from shipped systems
and peer-reviewed work and assemble one design satisfying H1–H8. Every
load-bearing claim carries a URL.

## 1. Summary

1. The state is a **set of signed, self-validating records**; the store keeps
   only the **maximal elements under a strict partial "prune" order** (Willow's
   prefix pruning generalised). One merge rule for everything.
2. Every writer owns a **subspace** (Earthstar / Willow): a record can only
   prune records *of the same author*. Cross-author conflicts are resolved in a
   **view**, a pure function of the store, never in the store.
3. Order within a subspace is `(timestamp, hash)`: a content hash breaks every
   tie (Kleppmann), so equivocation and cloned keys cannot diverge replicas.
4. Timestamps are HLC-minted but **only valid inside the writer's capability
   time window** (meadowcap). A far-future clock can pin a cell for at most
   the capability horizon, and only in its own subspace.
5. **Revocation is a record, not a gate**: `Rev(K)` prunes every data record
   of `K`. Two replicas with the same record set hold the same store.
6. Deletion is a prefix tombstone that frees the author's bytes immediately;
   tombstones expire after `T_gc` (Earthstar `deleteAfter`), bounding growth.
7. Sync is **range-based set reconciliation** over `(timestamp, hash)` per
   collection (Meyer; Negentropy at Nostr scale), with session-keyed
   fingerprints and a Negentropy-style frame limit; no version vectors.
8. Read control is a **per-collection epoch key**, sealed to each member's
   X25519 key and rotated on removal (Jazz / Sender Keys), not TreeKEM.
9. Relays carry only Noise-wrapped ciphertext; a private-interest-overlap
   handshake (Willow) hides even which collections a peer holds.
10. Trusted core: a strict partial order, a max-set semilattice, a view
    function and a fingerprint monoid — each a short Lean statement.

## 2. Survey table

| Sub-problem | System | Approach | Verdict for Kome |
|---|---|---|---|
| Merge order | [Willow](https://willowprotocol.org/specs/data-model/index.html) | newer = `timestamp`, then `payload_digest`, then `payload_length`; a newer entry at a path prefix *prunes* older same-subspace entries | **Adopt** prefix pruning + hash tie-break, same-author only |
| Merge order | [Automerge](https://automerge.org/docs/reference/documents/conflicts/) | LWW by opId `(counter, actorId)`, losers kept in `getConflicts` | Adopt "losers visible"; reject writer-chosen counters as order (pinnable) |
| Merge order | [cr-sqlite](https://vlcn.io/docs/cr-sqlite/api-methods/crsql_changes) | column LWW by `col_version`/`db_version` + `site_id`; row presence by causal length `cl` | Reject: causal length is Kome's saturation incident |
| Merge order | [Earthstar es.5](https://earthstar-project.org/specs/data-spec-es5) | newest doc *per author* per path; docs >10 min in the future rejected; `deleteAfter` expiry | **Adopt** per-author docs and expiry; reject the clock-relative gate (non-convergent) |
| Byzantine writers | [Kleppmann 2022](https://martin.kleppmann.com/papers/bft-crdt-papoc22.pdf) | identify updates by hash; validity from the update's own dependencies; version vectors unsafe under equivocation | **Adopt** hash identity and self-contained validity; reject the hash-DAG (GC needs a known replica set, [BEC §7](https://arxiv.org/abs/2012.00472)) |
| Deletion/GC | [ORSWOT](https://christophermeiklejohn.com/erlang/lasp/2019/03/08/monotonicity.html), [δ-CRDTs](https://arxiv.org/abs/1603.01529) | add-wins via dots + causal context; removes pruned when causally stable | Reject: stability needs every actor's ack (membership oracle) |
| Clocks | [HLC](https://cse.buffalo.edu/tech-reports/2014-04.pdf) | `(l, c)`, `l ≥ pt`, `c` bounded; `e hb f ⇒ (l.e,c.e) < (l.f,c.f)` | **Adopt** for minting, never for acceptance |
| Clocks | [Bloom clock](https://arxiv.org/abs/2011.11744) | probabilistic causality with false positives | Reject: H1 forbids probabilistic order |
| Clocks | [Ditto](https://docs.ditto.live/v4-5/sync-concepts) | 48+16-bit HLC; LWW registers, add-wins maps; devices "must have the time and date configured accurately" | Reject the assumption; keep the layout |
| Reconciliation | [Meyer, RBSR](https://arxiv.org/abs/2212.13567) | monoid-lifted fingerprints; `2+2⌈log_b n_min⌉−⌊log_b t⌋` rounds, `O(n_Δ·log n)` bits | **Adopt** |
| Reconciliation | [Negentropy / NIP-77](https://github.com/nostr-protocol/nips/blob/master/77.md), [impl](https://github.com/hoytech/negentropy) | order `(timestamp, id)`; fingerprint `SHA-256(Σ ids mod 2^256 ‖ count)[0:16]`; frame-size limit coalesces deferred ranges | **Adopt** order and frame limit; replace the unkeyed sum |
| Reconciliation | Willow [Confidential Sync](https://willowprotocol.org/specs/sync/index.html) | private interest overlap via salted hashes; read capabilities bound every range | Adopt PIO and cap-bounded ranges |
| Reconciliation | [BEC](https://arxiv.org/abs/2012.00472) | heads + Bloom filter, 1.03 round trips | Reject: remembers per-peer heads (H4) |
| Fingerprint hash | [ECMH](https://arxiv.org/abs/1601.06502), [LtHash](https://github.com/lukechampine/lthash), [2026 attack](https://eprint.iacr.org/2026/2083) | homomorphic set hashes; LtHash has k-sum attacks | ECMH needs curve arithmetic outside the fixed set; **session-keyed sum** instead (§5) |
| Write auth | [Meadowcap](https://willowprotocol.org/specs/meadowcap/index.html) | narrowing delegation chains over (subspace, path, **time range**); expiry instead of revocation | **Adopt** chains and windows; add revocation records |
| Write auth | [Ditto](https://docs.ditto.live/key-concepts/authentication-and-authorization) | query-scoped permissions from an auth webhook | Reject: central authority (H2) |
| Read control | [MLS / TreeKEM](https://www.rfc-editor.org/rfc/rfc9420.html) | epochs; "Applications MUST have an established way to resolve conflicting Commit messages" | Reject: needs an orderer; inactive members break PCS ([eprint 2023/1903](https://eprint.iacr.org/2023/1903)) |
| Read control | [Keyhive / BeeKEM](https://www.inkandswitch.com/keyhive/notebook/02/) | serverless TreeKEM with conflict keys | Reject for now: novel, unaudited |
| Read control | [Jazz](https://jazz.tools/docs/react/reference/encryption), [Sender Keys](https://arxiv.org/abs/2301.07045) | removal makes a new read key revealed to remaining members; O(n) | **Adopt** (n ≤ 64) |
| Membership privacy | [Signal private groups](https://eprint.iacr.org/2019/1416) | membership encrypted under a group key, server-blind | Adopt: member lists live inside the collection |
| Connectivity | [Iroh](https://github.com/n0-computer/iroh) | dial by key; hole-punch first, relay fallback | Adopt over Kome's Noise/relay stack |

## 3. Data model

**Records.** A record is a signed, bounded byte string with fields
`(collection: 32 B, kind, author: Ed25519 pk, path, ts: u64 µs, cap_ref: 32 B,
epoch: 32 B, body)`. `path` is `()`, `(entity)` or `(entity, field)` with
`entity ≤ 64 B`, `field ≤ 32 B`. `kind ∈ {Value, Tomb, Cap, Rev, Clamp, Seal}`.
`Value` carries `body ≤ 16 KiB` ciphertext and exists only at depth 2; `Tomb`
has no body and exists at depth 1 or 2; `Cap`, `Rev`, `Clamp`, `Seal` are
authorization records (§6) at depth 0 in the issuing key's subspace. The
record's identity is `h = BLAKE2b-256(bytes)`.

**Validity** `valid(r)` is a function of `r` alone: signature verifies;
bounds hold; the chain named by `cap_ref` is a narrowing chain (depth ≤ 4)
from the collection root granting `kind`, `path` and `ts ∈ [not_before,
not_after]`. Capabilities are records in the set; a record whose chain is not
yet held waits in a bounded pending buffer (≤ 256) or is dropped and
re-fetched later — Kleppmann's "missing dependency never delivered" rule,
which preserves convergence over the *delivered* set.

**Prune order.** For records `a, b` of the same collection, `a ≻ b` ("a
prunes b") iff either

- `author(a) = author(b)`, both are `Value`/`Tomb`, `path(a) ⊑ path(b)`
  (prefix), and `(ts_a > ts_b)` or `(ts_a = ts_b ∧ path(a) = path(b) ∧ h_a > h_b)`;
- or `kind(a) = Rev`, `subject(a) = author(b)`, and `b` is `Value`/`Tomb`.

`≻` is irreflexive and transitive (T-1). Nothing prunes auth records.

**Store.** `store(S) = { r ∈ S : valid(r) ∧ ¬∃ r' ∈ S. r' ≻ r }`, the
`≻`-maximal valid elements. `join(A, B) = store(A ∪ B)`. Because `≻` is a
strict partial order, `store(store(A) ∪ B) = store(A ∪ B)` (T-2): applying
records in any order, with any duplication, yields the same store (T-3). This
is Willow's store invariant ("no pair (old, new) … new is newer than old")
made into a lattice and restricted to same-author pruning.

**View.** For cell `(E, f)`, `cand = { r ∈ store : kind ∈ {Value, Tomb},
path(r) ⊑ (E, f), ¬revoked(author), ts_r ≤ clamp(author) }` (clamp defaults to
`2^64−1`), and `win = max_{(ts, h)} cand`. The cell shows `body(win)` if `win`
is a `Value`, else nothing. An entity exists iff some cell under it shows a
value. The app can also read `cand` itself — one candidate per author — which
is Automerge's `getConflicts` for records.

**Deletion.** `delete(E)` by `A` = `Tomb` at `(E)` with a fresh HLC. It
prunes `A`'s older records under `E` (bytes freed wherever it arrives) and
hides other authors' older records under `E` in the view. Their bytes are
freed by a maintenance rule: when a replica holding key `B` sees its own
`Value` shadowed by another author's newer `Tomb`, it writes its own `Tomb`
at `(E)`. A writer that never returns leaves ≤ one stale value per cell until
revoked.

**Against the lessons table.** No counter has semantics at its maximum
(`0` and `2^64−1` are ordinary `ts` values). Same-author same-`ts` records
are ordered by hash (T-EQUIV closed). Existence is a view, so there is no
`{0,0}` and nothing derived four ways. Digest and fingerprint share one
element set (§5). Revocation is an element, not a gate.

## 4. Clock and identity

**Minting.** Each device runs the HLC of Kulkarni et al.: `l := max(l, pt)`,
`c` increments on ties and resets otherwise; `receive` takes the max with
any *valid* stored record's `ts`, clamped to the device's own `not_after`.
`ts = l·2^16 + c` (Ditto's layout) is a `u64` with no reserved value. If `pt`
is behind `not_before`, the device mints `not_before`.

**Identity.** Author = device Ed25519 key, one subspace per collection; the
collection root key only issues `Cap`/`Rev`/`Clamp`/`Seal` and never writes
data. Unforgeability is needed for T-9, not for T-3.

**H8 analysis.** Let `K` be a writer with window `[a, b]` and `H = b − now`
(the horizon, ≤ 2^44 µs ≈ 200 days by bound).

- *Wrong clock, fast.* `K` mints `ts` up to `b`. In the view, cells `K`
  touches show `K`'s values until honest clocks pass that `ts` or the owner
  writes `Clamp(K, t)` (one record). Damage: ≤ cells in `K`'s area, ≤ `H` in
  time, zero bytes outside `K`'s subspace; other writers' stores are
  untouched.
- *Wrong clock, slow.* `receive` pulls `l` forward; `K`'s writes beat
  anything it has seen (HLC Theorem 1). Unsynced writes lose in the view
  until it syncs; the app shows "edit not current".
- *Backup restore.* Re-emitted old records are pruned wherever `K`'s later
  records or tombstones survive. If a tombstone has expired (`T_gc`), an old
  value resurrects in `K`'s cells only; re-deleting fixes it. The restored
  HLC is `max(old l, pt)`, so new writes beat anything restored.
- *Cloned key.* Two devices write one subspace; `(ts, h)` is total, so
  replicas still agree (T-3); users see the clones overwriting each other in
  `K`'s cells. The owner revokes `K` and issues two keys; `Rev(K)` prunes
  both clones' records.
- *Malicious.* All of the above deliberately, plus flooding its subspace
  (bounded by its area and a per-subspace quota) and lying during
  reconciliation (withholds data only from itself; T-7 is per honest pair).
  `Rev(K)` deletes its subspace from every store and view; the epoch rotates
  (§6). No record it can produce bricks the collection: nothing prunes across
  authors, and the root's writes are not data.

Equivocation (two records at one `(path, ts)`) is ordered by hash, the
BFT-CRDT prescription; version vectors are never exchanged.

## 5. Reconciliation and digest

**Element order.** Per collection, elements are `(ts, h)` of every record in
`store` that is not an expired tombstone (§7), ordered lexicographically:
the Negentropy order, which makes "recent edits" a contiguous range.

**Fingerprint.** Meyer requires a monoid lift `f: U → M`; we use
`M = (Z/2^256, +)`, `f_k(x) = BLAKE2b-256(k ‖ h_x)` with `k` a per-session
key derived from the Noise handshake, and send `(Σ f_k ‖ count)` truncated
to 16 B. An injecting adversary must choose records before any honest
session key exists, so k-sum attacks on the additive group (the LtHash
weakness) reduce to guessing PRF outputs; a cheating *party* harms only
itself. This closes Kome's additive-fingerprint limitation without new
primitives. A range-summarizable order-statistics tree (Meyer §4;
[arXiv 2603.19820](https://arxiv.org/abs/2603.19820)) gives any range's
fingerprint in `O(log n)`.

**Protocol.** Initiator sends `(range, fingerprint)` for the collection;
on mismatch the responder splits into `b = 16` subranges or, holding ≤
`t = 32` items, sends them; matching ranges are skipped. Rounds
`≤ 2 + 2⌈log_16 n⌉` (Meyer §3.3), bytes `O(n_Δ · log n)`. Frames are
self-delimiting, ≤ 4 KiB by default (BLE-friendly, negotiable to 64 KiB);
when a frame fills, remaining ranges coalesce into one deferred fingerprint
range as in Negentropy. No peer state survives the session (H4). Items are
the ciphertext records; the receiver validates and applies `store`, and both
sides end with the union of their valid records (T-7).

**Digest.** `digest(store) = BLAKE2b-256` over the sorted `h` list of the
same element set the fingerprint ranges over — a function of the store only
(T-5), from which `exists`, snapshot and load all derive.

**Privacy.** Peers first run private interest overlap: each sends
`BLAKE2b(salt ‖ collection_id)` under a per-session salt; only intersections
are named. A stranger learns nothing; a relay sees Noise ciphertext of
fixed-size frames. Dial-by-key with hole-punch-then-relay follows Iroh.

## 6. Authorization, encryption, revocation

**Write capabilities.** `Cap` chains are rooted at the collection root key.
Each link names `(subject pk, area = (subspace = subject, path prefix),
[not_before, not_after], may_delegate)` and is a subset of its parent in
every dimension (meadowcap narrowing); depth ≤ 4, window ≤ 2^44 µs. Every
writer, including the owner's devices, holds a windowed capability; renewal
is a new `Cap`. Expired capabilities stay (records minted under them remain
valid), bounded by `W × renewals`.

**Revocation.** `Rev(K)` is a root-signed record; it prunes `K`'s data (§3)
and is never pruned. Where it has not arrived, `K`'s records are accepted and
later pruned; where it has, they are pruned on arrival. Either way, two
replicas with the same set of records have the same store — the
"revocation seen on one side only" incident is unreachable by construction
(T-11). `Clamp(K, t)` is the partial form: it leaves `K` a writer but caps
the `ts` the view honours, for repairing a mis-clocked device without
re-provisioning it.

**Read control.** A root-signed `Seal` names `(epoch_id = h, parents,
members)` and carries the epoch key `k_e` boxed to each member's X25519 key
with ChaCha20-Poly1305 (≤ 64 boxes of 48 B). Every `Value` body is
encrypted under its named epoch. Writers use the newest epoch they can
decrypt, by `(ts, h)` among epochs whose parent chain they hold; concurrent
seals from two root devices form a DAG whose later seals name both parents.

**Removal** = `Rev(K)` + a `Seal` without `K`. The removed device keeps what
it already decrypted (inherent; Jazz documents the same), cannot decrypt any
later epoch (fresh key never sent to it — T-12), cannot get records accepted
(pruned), and cannot see membership changes (members live inside the sealed
collection, Signal-style). It still sees traffic shape, as any stranger does.
This is Sender-Keys-grade post-compromise security at O(n) per removal,
chosen because MLS leaves conflicting commits to "an established way to
resolve" and BeeKEM is unaudited.

**Root loss** is a re-founding, as today; social recovery is out of scope.

## 7. Storage and GC

**Storage.** Append-only log of ciphertext records with Bitcask compaction
(Kome today; BEC's append-only `M`). Per collection: a B-tree on `(ts, h)`
whose internal nodes carry fingerprint sums (the monoid tree), and a B-tree
on `(author, path)` for pruning and the view. Entries are fixed-size; all
bounds are compile-time constants (SPARK).

**Exact GC rule.** A replica may physically drop a record `r` at local time
`now` iff one of:

- (G1) `∃ r' ∈ store. r' ≻ r` — immediately, on arrival of `r'`;
- (G2) `kind(r) = Tomb ∧ now ≥ ts_r + T_gc` — and such a record is excluded
  from the reconciled element set, so peers do not re-send it;
- (G3) `¬valid(r)` after its pending-buffer timeout.

Nothing else is ever dropped. `T_gc` is a collection constant (default 90
days, ≥ any writer's horizon). G1 preserves the store by definition. G2 only
forgets a tombstone; its sole observable effect is that a same-author record
older than it may be re-admitted from a replica offline longer than `T_gc` —
the Earthstar bound, confined to one author's cells. Per-replica state is
`Σ_authors |live records| + |unexpired tombstones| + |Cap, Rev, Clamp,
Seal|`, each term explicitly bounded; per cell ≤ `W = 64` candidates.

## 8. Assumptions

1. Ed25519 signatures are existentially unforgeable; BLAKE2b-256 is
   collision-resistant (identity of records) and a PRF under a secret key
   (fingerprints); X25519 + ChaCha20-Poly1305 give IND-CCA sealing.
2. Every honest replica eventually reconciles, directly or transitively,
   with every other honest replica (eventual delivery; the BFT-CRDT
   "unavoidable" assumption).
3. Honest devices' clocks agree within `T_gc` (for G2 only; convergence
   never depends on clocks).
4. Capability windows are bounded by `2^44 µs` and the root issues them;
   the root key is honest (a malicious owner is out of scope, as today).
5. At most `W = 64` writers hold capabilities in a collection at once;
   bounded record, path, chain and frame sizes as stated.

## 9. Known weaknesses

- **Per-cell metadata is O(authors)** on contested cells; stale values of
  absent writers persist until they return or are revoked.
- **Far-future pinning is bounded, not eliminated**: up to the horizon or
  until a human issues `Clamp`/`Rev`.
- **Resurrection window** after `T_gc` for a writer's own old data.
- **Auth records are kept forever** (small, but grow with member churn).
- **O(n) re-seal per removal**; the root must be online to remove; the
  two-parent epoch DAG must be modelled.
- **Fingerprint security is a PRF argument**, not ECMH's collision bound.
- **Pending-buffer drops** delay (never prevent) delivery; a malicious peer
  can waste bounded buffer space.
- Cross-author add-vs-delete is last-action-wins; add-wins would be a view
  change only.

## 10. Proof obligations

Let `R` be the set of well-formed records, `valid: R → Bool` a function of a
record's bytes, `≻ ⊆ R × R` as in §3, `store(S)` the `≻`-maximal valid
subset of a finite `S ⊆ R`, and `view` as in §3.

- **T-1 (≻ is a strict partial order).** `≻` is irreflexive and
  transitive on `R`.
- **T-2 (store is a semilattice).** For finite `A, B, C ⊆ R`:
  `store(store(A) ∪ B) = store(A ∪ B)`; hence `join(A,B) := store(A ∪ B)` is
  commutative, associative and idempotent on stores.
- **T-3 (CONV).** For any two finite sequences of records with the same
  underlying set, applied in any order with any duplication from the same
  start, the resulting stores are equal. (Corollary of T-2.)
- **T-4 (VIEW).** `view` is a function of `store` alone; in particular
  `cand(E,f)` has at most one record per author.
- **T-5 (DIGEST).** `digest` is a function of the reconciled element set
  `elems(store, now)`; two stores with equal element sets have equal
  digests, and `elems` is monotone in `store` for fixed `now`.
- **T-6 (FP-SOUND).** For a session key `k` unknown to the chooser of the
  record sets, `fp_k(X) = fp_k(Y) ⇒ X = Y` except with probability
  ≤ `q²/2^128 + Adv_PRF`, where `q` is the number of records.
- **T-7 (RBSR).** Between two honest replicas, reconciliation of a
  collection terminates within `2 + 2⌈log_b n_min⌉ − ⌊log_b t⌋` rounds
  (unbounded frames) and transmits `O(n_Δ · log n)` bits, after which both
  hold `store(A ∪ B)`; with frame limit `F` the round bound is multiplied by
  at most `⌈msg/F⌉`.
- **T-8 (BOUND).** Every record, index entry, frame and pending buffer is
  within its stated constant; the number of candidates per cell is ≤ `W`;
  the HLC never mints outside `[not_before, not_after]`.
- **T-9 (BLAST).** For a writer `K` with window `[a,b]` and area `Π`, every
  record `r` with `valid(r)` and `author(r)=K` has `path(r) ∈ Π` and
  `ts_r ≤ b`; `r` prunes nothing outside `K`'s subspace; and if `Rev(K) ∈
  S` then no record authored by `K` is in `store(S)` or affects `view`.
- **T-10 (GC).** G1 leaves `store` unchanged. G2 at time `now` leaves
  `view` unchanged on every replica whose store contains no record `r'` with
  `author(r') = author(r)`, `path(r) ⊑ path(r')`, `ts_{r'} < ts_r`; i.e. the
  only effect of expiry is possible re-admission of such `r'`.
- **T-11 (REV-MONOTONE).** `store` is a function of the record set; adding
  `Rev(K)` to a set never makes two replicas' stores differ when their sets
  are equal; and `Rev(K) ∈ S ⇒ Rev(K) ∈ store(S)` for all supersets.
- **T-12 (EPOCH).** A key `K` absent from `Seal e'` and every descendant of
  `e'` cannot decrypt any `Value` naming an epoch in that subtree, under
  IND-CCA of the seal and freshness of `k_{e'}`.
- **T-13 (HLC).** `tick` is strictly increasing within a window and
  `receive` never moves the clock backwards nor beyond `not_after`;
  `e hb f ⇒ ts_e < ts_f` for events of one honest device.

T-1..T-5 and T-9..T-11 are short Lean inductions over finite sets; T-7 is
the substantial one (induction over the range split, as `MATH_MODEL.md` §4
anticipates); T-6 and T-12 are cryptographic reductions proved on paper.

## 11. Self-score

- **C1 — 5.** T-3 assumes only that `valid` is a function of the record
  and `≻` a strict partial order; no clock, signature or hash assumption.
- **C2 — 4.** A bad writer touches only its subspace, for at most the
  horizon; one `Rev`/`Clamp` record undoes it everywhere.
- **C3 — 3.** `O(authors)` per contested cell; tombstones expire; auth
  records persist; no membership oracle.
- **C4 — 5.** `O(log n)` rounds, `O(n_Δ log n)` bytes, 4 KiB frames, no
  per-peer state; relays and strangers see ciphertext and salted hashes.
- **C5 — 4.** Removed members lose future reads, writes and membership
  visibility; they keep past plaintext and traffic shape.
- **C6 — 5.** Core = one partial order, one max-set lattice, one pure view,
  one monoid; finite, bounded, pointer-free.
- **C7 — 4.** Monocypher only; new costs are a keyed sum, an
  order-statistics B-tree and ≤ 64 boxes per epoch.
- **C8 — 4.** Conflicts are one value per author; deletes vanish;
  resurrection is the only surprise.
- **C9 — 5.** Existence is a view, kinds are a sum type, every integer is a
  plain bounded number, digest and fingerprint share one element set.
