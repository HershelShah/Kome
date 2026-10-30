# Candidate C: signed logs, not cells

Angle: *"Logs, not cells."* Every writer key owns a hash-chained, signed,
append-only log (Hypercore / SSB / Earthstar family). The replicated set is
the set of entries; state is a deterministic fold over the union of all logs.
Cells exist only as the fold's result, never as the thing replicated or signed.

## 1. Summary

- Unit of replication: a signed **entry** `(writer, seq, prev, height, link,
  epoch, ciphertext)`; id = BLAKE2b-256 of the signed body. Logs are chains by
  `prev`; a cloned key makes a **tree**, and the fold accepts every branch.
- Order: `key(e) = (height, writer, seq, id)`, a strict total order. `height`
  is a **verified Lamport height** (`h(prev)+1 ≤ h ≤ 1+max(h(prev), h(link))`),
  checked against entries the reader holds; no wall clock anywhere.
- Fold: per `(entity, field)` keep the max-key `SET`; per entity keep the
  max-key `DROP`; a cell is live iff its key beats the entity's drop. This is
  a semilattice join, so the fold is order-independent and incremental.
- Space: each writer periodically emits a **checkpoint** (its own compacted
  cells + a frontier). Entries below a writer's checkpoint are *void* by a
  fold rule, so truncating them is invisible. Tombstones leave when every
  member's checkpoint frontier has passed the drop.
- Authorization and revocation are ops in the owner's log (`GRANT`,
  `EXCLUDE(writer, from_seq)`), folded like data: monotone, never a gate.
- Encryption: per-collection epoch keys sealed to members in the owner's log;
  payloads under XChaCha20-Poly1305 with random nonces.
- Sync: range reconciliation over `(writer, seq, id)` with a per-session
  salted fingerprint; relays carry Noise ciphertext only.
- Weakest point: an entry folds only once its `prev` and `link` are held or
  covered, and a cloned key's sibling checkpoint can void up to one
  checkpoint-interval of the other clone's writes (rebase recovers).

## 2. Data model

### 2.1 Entry layout

Signed body (little-endian, fixed offsets; `cid` is prepended to the signed
bytes but not transmitted, as domain separation):

```
off len field
 0   1  ver     = 1
 1   1  kind    ∈ {0 = OPS, 1 = CKPT}       (any other byte: malformed)
 2  32  writer  Ed25519 public key
34   8  seq     1 ≤ seq ≤ 2^62
42  32  prev    id of (writer, seq−1) on this branch; for seq = 1: cid
74   8  height  1 ≤ height ≤ 2^62
82   1  nlink   ∈ {0, 1}
83  40  link    (writer 32, seq 8)  — present iff nlink = 1
     4  epoch   u32
    24  nonce   random, XChaCha20-Poly1305
     4  clen    ≤ 65536
  clen  ciphertext || 16-byte tag
```
followed by `sig` (64 bytes, Ed25519 over `cid || body`). `id = BLAKE2b-256(cid
|| body)`; `cid = BLAKE2b-256(genesis)`, where genesis is a signed descriptor
`(owner key, 32 random bytes)`, not an entry, so the owner key is part of the
collection id and every log's `seq = 1` has `prev = cid`. Overhead per
entry: 195 bytes (no link) or 235 (link), plus a 32-byte derived id in the
index. No reserved values: an absent link is a count of zero; `seq = 1`'s
`prev` is a real hash; `2^62` is a refusal bound on append, not a state.

Plaintext of an `OPS` payload: `nops: u8 ≤ 64`, then ops. Op tags:
`SET(entity, field, value)`, `UNSET(entity, field)`, `DROP(entity)`,
`GRANT(key, role, from_seq, sealed_keys[])`, `EXCLUDE(key, from_seq)`,
`EPOCH(n, sealed_keys[])`. Bounds: entity ≤ 64 B, field ≤ 32 B, value ≤ 16 KiB,
role ∈ {owner, writer, reader}, ≤ 64 members, ≤ 16 GRANT/EXCLUDE per key.

### 2.2 Chains, forks, trees

A **log** is a writer's entry set; it is a chain when every seq appears once.
Two held entries with equal `(writer, seq)` and different ids are a **fork
proof** (clone or backup restore). The fold does not reject forks: the log is
then a tree and every branch folds. Forks are reported to the app and trigger
the writer-side **rebase** (§3).

### 2.3 Height

`h(cid) := 0`. An `OPS`/`CKPT` entry `e` is **well-heighted** iff
`h(prev)+1 ≤ h(e) ≤ 1 + max(h(prev), h(link))` (with `h(link)` omitted when
`nlink = 0`). A writer sets `h = 1 + max(h(prev), h(link))` with `link` the
highest entry it has folded, so a write made after seeing `x` outranks `x`
(T-HLC-3 without a clock). An entry whose `prev` or `link` is neither held nor
covered (§6) is **pending**: kept, replicated, not folded. Heights are
honest-work-bounded: `h(e) ≤` the size of `e`'s verified causal past.

### 2.4 The fold

Let `E` be the held entries and `F = effective(E)` (§6: valid, authorized,
not void, not pending, decryptable). State:

```
cell(ent, f)   = argmax_key { e ∈ F, SET(ent,f,v) ∈ e }          (or ⊥)
drop(ent)      = max_key    { e ∈ F, DROP(ent) ∈ e }              (or ⊥)
live(ent, f)   = cell(ent,f) ≠ ⊥ ∧ key(cell) > key(drop(ent))
exists(ent)    = ∃ f. live(ent, f)
```
`UNSET` is a `SET` carrying an *absent* marker (a tagged union, not an empty
string). Ops within an entry are keyed `(key(e), op_index)`: one atomic batch.
Checkpoint cells keep their original `(height, seq)`, so compaction never
re-orders anything.

Example. A: seq1 `SET(n, name, "x")` h=1; B: seq1 `SET(n, name, "y")` h=1
(concurrent). `(1,A,1,·)` < `(1,B,1,·)` → "y". A folds B's entry and writes
seq2 `DROP(n)`, link `(B,1)`, h=2: `(2,A,2,·)` beats both cells → `n` gone.
B, offline, writes seq2 `SET(n, name, "z")` h=2, no link: `(2,B,2,·)` >
`(2,A,2,·)` → `n` exists with "z". The current engine's LWW outcome, with the
writer key as tie-break instead of a clock.

Deletion: `DROP` erases every field whose key is below it; values are
physically dropped at the next checkpoint (§6); the tombstone is the
`(entity, height, seq)` triple, 80 bytes max.

## 3. Clock and identity (H8)

There is no clock in the model. Cases:

- **Wrong clock.** No effect; the only timestamps are app-level values.
- **Buggy writer.** Malformed entries fail static validation and never enter
  `E`. A wrong `height` makes the entry pending forever and stalls only that
  writer's own chain. A runaway writer appending a million entries inflates
  heights by a million: honest writers fold them and continue at `+1`; nobody
  is pinned. The cost is storage, bounded by the owner's `EXCLUDE` (§6).
- **Backup restore.** The device is back at seq `n`; the world holds its
  `n+1..m`. Its next append forks at `n+1`. Both branches fold; nothing is
  lost *unless* the other branch holds a checkpoint at `s > n`, which voids
  the restored branch's entries with `seq ≤ s`. Bound: the ops written between
  restore and first sync. Recovery is local: on seeing its own key ahead of
  itself the device **rebases** — sets `seq := max_seen + 1` and re-emits, as
  fresh entries, the ops of its own voided entries. Re-emitted ops get new,
  higher keys ("last to sync wins"), which is the accepted concurrency rule.
- **Cloned key.** A permanent fork: two devices extend two branches. Both
  fold; the app is told. Damage: (i) each clone's checkpoint voids the other's
  entries below it, bounded per checkpoint interval and repaired by rebase;
  (ii) a clone's checkpoint that never folded another writer's `DROP` can
  carry cells below that drop after the tombstone was collected, resurrecting
  the entity (§6); repaired by dropping again. Recovery: owner `EXCLUDE(W, s)`
  and new keys per device.
- **Malicious writer.** Can: write any value anywhere (inherent to write
  access); fork itself; link-bomb (pending forever, hurting only itself); lie
  in its own checkpoint (omit own cells = delete own data; claim an unfolded
  frontier = resurrect entities it wrote); reuse a nonce (exposes only its own
  plaintext XOR to epoch-key holders). Cannot: forge others, claim height
  beyond verifiable work, stop any honest writer from appending a winning
  entry, disguise a fork as a chain. Damage is confined to entities it
  touched and reversed by `EXCLUDE(W, from_seq)` plus rewrites; writes before
  `from_seq` survive.
- **Malicious owner.** Out of scope: the owner is the root of the collection,
  as today (SECURITY.md "root recovery not yet").

## 4. Reconciliation and digest

The replicated set is `effective(E)` ordered by `(writer, seq, id)` (72-byte
sort key; forks are adjacent). Range-based set reconciliation as in M3 (16
buckets, FP/LEAF/HAVE), with two changes:

1. **Per-session salt.** Each side draws a 32-byte salt; a range fingerprint is
   `(count, Σ BLAKE2b-256(salt || id))` mod 2^256. The sets are fixed before
   the salt exists, so a chosen-entry collision would have to hold for all
   salts, i.e. be equality. This removes the additive-fingerprint residual for
   O(n) 64-byte hashes per session (10^5 entries ≈ 10 ms).
2. **Head pre-exchange.** The first message carries the sender's max
   checkpoint seq per writer (≤ 64 × 40 B); each side omits entries the peer's
   checkpoints already void, so a checkpoint is never answered with the
   garbage it replaced. Current data, not a memory of a past session (H4).

Sessions snapshot `effective(E)` at begin. `digest(E) := fingerprint with salt
= 0^32 over effective(E)`: the digest *is* the sync fingerprint (lesson:
"digest defined separately from the sync fingerprint"). Transport: any byte
stream or datagram; descriptors are self-contained. Relays see Noise XX
ciphertext and a routing key, as today; entry headers (writer, seq, link) are
visible only inside the channel, i.e. to members.

## 5. Authorization, encryption, revocation

**Membership is state, not a gate.** `GRANT(X, role, a)` and `EXCLUDE(X, b)`
are ops in an owner-role log. Entry `e` of `X` is **authorized** iff the
grant/exclude op of greatest `from_seq ≤ seq(e)` in `effective(E)` is a
`GRANT`. An `EXCLUDE` is permanent for that key (re-admission uses a new
key), so a replica that has seen it holds a *subset* of the other's effective
set, never a different one (lesson row 7). The genesis descriptor names the first `owner`;
rotation is `GRANT(new, owner)` + `EXCLUDE(old)`.

**Epochs.** `EPOCH(n, [(member, X25519-box(k_n))…])` in the owner's log,
`n` increasing by one. Payloads are sealed under `k_epoch` with a random
24-byte nonce (not `(writer, seq)`-derived: a fork reuses `(writer, seq)`).
On `EXCLUDE` the owner emits a new epoch to the remaining members. A `GRANT`
seals every epoch key still referenced by `effective(E)` (≤ 64; checkpoints
retire older ones). An entry whose epoch key the reader lacks is held and
replicated, not folded.

**A removed member** keeps everything up to its exclusion epoch (inherent),
receives new ciphertext only from peers that have not folded the `EXCLUDE`
(read-scoping is against the peer's folded member set: eventually consistent
cut-off, as today), learns from headers who wrote how much and who-had-seen-
what until peers stop serving it, and can sign entries forever, which are void
wherever the `EXCLUDE` is held.

## 6. Storage and GC

**Checkpoint.** `CKPT` series of writer `W`: `n ≤ 4096` consecutive entries
`seq = s..s+n−1`, kind 1, payload `(n, i, frontier?, cells[], tombs[])`.
Part 0 carries `frontier: [(writer, seq)] ≤ 64`, the heads `W` had folded.
Cells are `(entity, field, value, height, seq)`; tombs `(entity, height,
seq)`. A checkpoint is **valid** iff it is well-heighted with `link` = its
max-height frontier entry (so `h(ckpt) > h(x)` for all frontier `x`); it
contains every cell/tomb of `W` with `seq < s` not dominated by an entry at or
below its frontier (omission of a dominated cell is mandatory and checkable
by any holder of the dominator); and its frontier is pointwise ≥ the previous
checkpoint's.

**Void predicate** (a fold rule, evaluated on `E`): entry `e` of `W` is void
iff

```
V1  kind(e)=OPS  ∧ ∃ CKPT series c of W in E, complete, with seq(e) ≤ last(c)
V2  kind(e)=CKPT ∧ ∃ CKPT series c' of W in E, complete, key(c') > key(e)
V3  ∃ EXCLUDE(W, b) ∈ effective(E), b ≤ seq(e)
```
`effective(E)` = entries that are valid, authorized, not void, decryptable,
and whose `prev`/`link` are **covered**: held in `E`, or void under V1/V2 by a
checkpoint `c` of the same writer, in which case the unknown height is
bounded by `h(c)` in the well-heighted check. Pending entries and their chain
descendants are outside `effective(E)`. Every clause reads only `E`, so two
replicas with equal `E` agree, and two replicas with equal `effective(E)`
agree on state.

**Truncation rule (exact).** A replica may delete `e` iff `e` is void
(V1–V3). Void is monotone in `E` (checkpoints and excludes are grow-only; V1
says *any* checkpoint, V2 compares against a growing maximum), so deletion
never changes `effective(E)` now or later. A reader holding only entries above
a checkpoint has `W`'s full state (the checkpoint *is* the compacted prefix)
and bounds later heights by `h(c)`; it cannot verify the chain below `s` and
need not.

**Tombstone collection** (writer policy, not a fold rule). `W` may omit
tomb `(ent, k)` from its next checkpoint iff for every authorized member `X`
(and every excluded member whose last checkpoint is effective) `W` holds a
checkpoint `c_X` with `c_X.frontier[W] ≥ seq(k)`. Then `X`'s cells of `ent`
below `k` are omitted from `c_X` (validity), its later entries have
`h > h(c_X) > h(k)`, and its earlier entries are void: nothing below `k`
reappears except from a sibling (fork) checkpoint that never folded the drop.
A member that never checkpoints holds tombstones hostage until excluded.
`EXCLUDE` carries a `purge` bit voiding all of `X`'s entries (the owner
re-emits cells it wants to keep under its own key first).

**Bounds per replica.** `≤ 64` writers × (one checkpoint + entries since) ×
`≤ 2^62` seq; checkpoint ≤ 4096 × 64 KiB. Pending set bounded by a per-writer
cap (e.g. 1024 entries), beyond which later entries of that writer are not
stored.

## 7. Assumptions

A1. Ed25519 is unforgeable. A2. BLAKE2b-256 is collision-free on ids and on
`salt || id`. A3. XChaCha20-Poly1305 is a secure AEAD; random nonces do not
repeat under one key (2^-96 per pair). A4. The owner key is honest and not
lost. A5. Liveness only: every effective entry eventually reaches every
member, and active members checkpoint eventually. A6. Entries per writer
< 2^62. Nothing about clocks, timing, or message order.

## 8. Known weaknesses

- **Overhead.** 195–235 B per entry plus 80 B per checkpoint cell; one op per
  entry is ~2× the current cell cost. Apps must batch (64 ops/entry).
- **Pending semantics.** An entry waits for its `link`, and a pending link
  delays it further. Below a checkpoint height is only bounded (`h ≤ h(c)`),
  so an entry may be pending at a truncated replica and folded elsewhere:
  sets differ, convergence holds, visibility lags.
- **Forks × checkpoints.** A sibling checkpoint voids the other branch's
  prefix (bounded, rebase-recoverable) and can resurrect a collected
  tombstone. A key on two devices is the one case the model handles by
  damage control rather than prevention.
- **Membership in the GC predicate.** Tombstone collection needs every
  member's checkpoint; a dormant member holds tombstones hostage until
  excluded. The member set is fold state, not an oracle, but it is there.
- **Concurrency tie-break is the writer key**, not time; a truly concurrent
  pair resolves arbitrarily (deterministically). The app may ship an
  advisory wall time inside values for display only.
- **Owner single point.** Owner key loss = re-found the collection.
- **Heights are honest-work-bounded**, not small: a long griefer chain raises
  everyone's heights (harmless) and storage (until excluded).

## 9. Proof obligations

- **T-ENTRY.** Under A2, `id` is injective on signed bodies; `prev` and
  `link` denote at most one entry.
- **T-ORDER.** `(height, writer, seq, id)` with lexicographic comparison is a
  strict total order on entries (T-ENTRY for the last component).
- **T-FOLD.** For any set `F`, `cell`, `drop`, `live` are well-defined
  (argmax over a total order) and `fold(F)` equals the LWW semilattice join
  over `F` with keys `(key(e), op_index)`: commutative, associative,
  idempotent (reuse `LWW.merge_*`).
- **T-EFF.** `effective` is a function of `E` alone; `void` is monotone:
  `E ⊆ E' ⇒ void(E) ⊆ void(E')`; and `effective(E) ⊆ E \ void(E)`.
- **T-CONV.** `effective(E_A) = effective(E_B) ⇒ fold(E_A) = fold(E_B)` and
  `digest(E_A) = digest(E_B)`. (Stronger than the current T-CONV: held sets
  may differ by garbage.)
- **T-GC.** `effective(E \ void(E)) = effective(E)`; hence truncation
  preserves state and digest.
- **T-CKPT.** If `c` is a valid checkpoint of `W` and `E` contains every
  entry of `W` with `seq < s` that `c` covers, plus every dominator `c`
  relied on, then `fold(E ∪ c) = fold(E)`.
- **T-HEIGHT.** For every `e ∈ effective(E)`, `h(e) ≤ |past(e)|`, the
  transitive `prev`/`link` closure in `E` (checkpoints count their covered
  range); and for any `E` with `max h < 2^62` an honest writer can append an
  `e` in `effective(E ∪ {e})` greater than every entry of `E` (no bricking).
- **T-FORK.** Two entries in `E` with equal `(writer, seq)` and distinct ids
  exist iff the writer's log is not a chain; both are in `effective` when
  individually valid.
- **T-TOMB.** If `W` omits tomb `(ent, k)` under §6's predicate and every
  checkpoint in `E'` ⊇ `E` is valid and on the branch `W` observed, then no
  `e' ∈ effective(E')` carries a cell of `ent` with key < `k`.
- **T-AUTH.** Authorization is a function of `effective(E)`; adding an
  `EXCLUDE` to `E` removes effective entries and adds none.
- **T-RBSR / T-RBSR-WIRE.** Over `effective(E)` sorted by `(writer, seq,
  id)`, the split protocol terminates in O(log₁₆ n) rounds and both sides
  hold the union; salted fingerprint equality on a range ⇔ set equality on
  that range (A2), for sets fixed before the salt is drawn.
- **T-DIGEST.** `digest` is a function of `effective(E)` only; equals the
  zero-salt fingerprint of the full range.
- **T-ENC.** Every op is readable only by holders of its epoch key; an
  excluded member's keys cover no epoch created after its exclusion.

## 10. Self-score

- **C1 = 4.** Assumptions are A1–A3 only; no clock, no order, no membership
  oracle. One off for the size of `effective`, which the theorem quantifies
  over.
- **C2 = 4.** No permanent pin exists (Lamport `+1`); blast radius is the
  entities a writer touched; `EXCLUDE(from_seq)` recovers and keeps earlier
  writes. One off for fork × checkpoint loss.
- **C3 = 3.** 195–235 B/entry needs batching; checkpoints give exact
  truncation; tombstones need member cooperation.
- **C4 = 4.** Same RBSR shape, salted fingerprints close the collision
  residual, head pre-exchange avoids garbage traffic; relays as blind as
  today.
- **C5 = 4.** Epoch keys cut a removed member off cryptographically; it keeps
  what it had and sees header metadata until peers fold the exclude.
- **C6 = 3.** Trusted core = fold (a join) + `effective` (three void clauses,
  height check, auth lookup). All bounded arrays, SPARK-friendly; `effective`
  monotonicity is the one non-trivial Lean lemma.
- **C7 = 4.** Same four primitives; flat fixed-offset entries; no new
  dependency.
- **C8 = 4.** One rule ("last key wins", drop beats older fields); forks and
  rebases are explicit app events; no presence register to keep consistent
  with fields.
- **C9 = 4.** No sentinels (optional link is a count, `prev` of seq 1 is a
  real hash, bounds are refusals); one off because `exists(ent)` is derived
  from live cells, which is a definition rather than a stored fact.
