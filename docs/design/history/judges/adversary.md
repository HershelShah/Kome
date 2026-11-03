# Adversarial judge: attacks against the four candidates

Stance: every design lets an authorized-but-misbehaving writer, a removed
member, a relay, or a stranger do more than it admits. For each candidate I
ran the eight attack classes from the brief, with concrete records/messages and
the resulting state per replica. Notation: `M` = malicious authorized writer,
`X` = member removed at time `T`, `L` = a lagging honest replica that has not
yet received the revocation, `U` = an up-to-date honest replica, `O` = owner /
root. "Admitted" means the candidate's own §8/§9 already states the finding.

Common ground (not re-scored per candidate): in all four, an authorized
writer can overwrite or delete any cell it can see, and a thief holding a
device key can do so until the owner notices. All four physically free deleted
values on every replica, so a thief's deletes are irreversible everywhere
(A: `dom` clause; B: removal is lattice top; C: next checkpoint; D: G1 +
self-Tomb). All four leak sizes/timing/who-talks-to-whom to a relay. I only
score what each design does *beyond* this baseline, and whether it says so.

---

## Candidate A: hardened LWW

### Attacks that work

**A-1. Pin at the ceiling is a guaranteed win, not a "tie" (attack class a, d).**
`v = (t, author, seq, h)` compared lexicographically; at `t = ceil` the order
falls to `author` as a 256-bit integer. Ed25519 public keys are cheap to grind:
`M` generates keys until `pk_M > pk` of every roster member (a handful of
tries). Trace: `M` emits `PUT(E, name, "x") v=(ceil, pk_M, 1, h)`. Honest `U`
writes `name`: `floor.t = ceil` → `t_emit = ceil` (clamped) → `v_emit = (ceil,
pk_U, k, h')`, `pk_U < pk_M` → `status = SHADOWED` on every replica, forever
until a ROSTER with a higher ceiling is held. The doc frames this as "block
another writer except by tie at ceil" as if the tie were symmetric; it is
attacker-chosen. T9 holds (refresh unshadows) but `M` re-pins at the new ceil
in one record, so the real bound is "until revocation", and every honest cell
`M` touched is Lamport-ized forever (admitted). `DEL(E) v=(ceil, pk_M, …)`
makes `E` un-recreatable the same way until revocation.

**A-2. Garbage survives revocation; cleanup tombstones live ~horizon + TTL (d, g).**
`void` is a view, not a drop (§5, and the design is right that it must be).
Consequence it does not state: after `revoked(M, from_t)`, `M`'s records stay
in `F` and keep dominating. Trace: `M` writes `PUT(ent_i, f, 64 KiB) v=(ceil,
pk_M, i, ·)` for `i = 1..N` on fresh random `ent_i`. Revocation: all `N` are
void but still in `F` on every replica (N × ~65 KB each, replicated). The only
removal path is `O` writing `DEL(ent_i)` per entity: `O`'s DEL chases to
`old_ceil + 1` (possible only because the revocation ROSTER raised the
ceiling), dominates, frees the value — and then the DEL itself sits until
`now ≥ old_ceil + 1 + del_ttl`, i.e. ≈ 400 days + `del_ttl`, as ~180 B × N of
tombstones. §8 says floods are "bounded only by revocation and the owner's
DELs"; revocation bounds nothing here, and the DEL cost is a year of
tombstones. Resulting state: `U` holds N void PUTs until `O` acts, then N
DELs for a year.

**A-3. Removed member injects into up-to-date replicas via previous-epoch bundles (e).**
§5: "a BUNDLE is readable iff the replica holds its epoch key (current or
previous)". `X` was a member of epoch `e`; after the revocation ROSTER (epoch
`e+1`), every `U` still opens epoch-`e` bundles. Trace: `X` posts to a mailbox
relay `BUNDLE = ns ‖ e ‖ nonce ‖ AEAD_{k_e}(PUT(c, f, "junk") v=(from_t − 1,
pk_X, s, ·))` for every cell `c` whose floor `t < from_t − 1` (most cells:
honest `t` ≈ wall time at last write). `U` fetches, decrypts under its
retained `k_e`, applies: records are well-formed, admissible (`t ≤ ceil`), not
void (`t < from_t`), and dominate. Likewise `DEL(E) v=(from_t − 1, …)` drops
every value under `E` on every `U`. This lasts until epoch `e+2` (a second
rotation), with no laggard required. §5 admits only "to any lagging member
until the new ROSTER reaches it"; the previous-epoch rule makes every member a
laggard for one extra generation. Back-dating also makes `void` a no-op
against a deliberate attacker (admitted implicitly).

**A-4. Concurrent ROSTERs from two root devices silently drop a revocation (e).**
`dom(ROSTER)` is by `(gen, h)`. Owner devices `R1`, `R2` both hold gen 4. `R2`
issues gen 5 revoking `X`; `R1` concurrently issues gen 5 refreshing the
ceiling. Whichever has the larger `h` wins; if `R1`'s does, `X` is still in
`members` with the epoch key wrapped to it, and `R2`'s revocation is
dominated and GC'd. `R2`'s UI said "removed". Not malicious, but `X` only
needs to wait. `revoked[]` is per-ROSTER, not grow-only, so the design relies
on root devices never racing. Not admitted.

**A-5. Bundle header leaks collection id and rotation events to the relay (f).**
`BUNDLE = ns ‖ epoch ‖ nonce ‖ …` in the clear. A mailbox relay learns which
`ns` each key posts/fetches, bundle counts and sizes per collection, and every
epoch increment (= a membership change). Noise sessions hide this; the
non-interactive path does not. Not admitted; the summary says relays see
"ciphertext and a routing key".

**A-6. Inadmissible-record retransmission (g, minor).** `M` signs `K` records
with `t = 2^48 − 1`. Every replica skips them, none stores them, so every
session with `M` rediscovers the same `K`-element symmetric difference and
ships them again: `O(K log N)` descriptors + `K` elements per session with
`M`, forever. Bounded by `M`'s storage and membership; still a per-session
tax the design treats as a proof-statement nuisance only.

### Attacks the design defeats
- Far-future clock on honest writers: chase is cell-local; no engine clock to
  poison (the SECURITY.md incident is genuinely gone). Far-past clock: loses,
  then chases. (a) defeated except at `ceil`.
- Backup restore / cloned key: same-`(author, seq)` ordered by `h`; `F`
  identical on every replica; flagged; seq jumped. Loss confined to the
  restorer's own pre-sync writes and expired-tombstone resurrection
  (admitted). (b, c) defeated.
- Kill another writer's future writes: impossible except at the ceiling tie
  (A-1). Brick the collection: impossible; ROSTER refresh is root-only and
  monotone. (d) mostly defeated.
- Fingerprint forgery: 4096-bit accumulator with `|R|` in the hash; Wagner
  k-sum ≈ 2^128 with an infeasible number of inserted elements. (h) defeated.
- Unbounded metadata: ROSTER ≤ 64 members / 1024 revocations; no vectors; per
  cell 44 B. (g) bounded except A-2.

### Honesty
Best of the four. §8 states the LWW overwrite power, pre-revocation damage,
Lamport-ization, TTL resurrection, garbage floods, root-liveness. It omits the
pk-grind making the tie a sure win, the post-revocation permanence of garbage
and the year-long cleanup tombstones, the previous-epoch bundle window, the
ROSTER race, and the bundle header leak.

### Scores
- **C2 = 3.** Every attack is attributable (signed), ends at revocation +
  one ceiling refresh, and the owner can always write above the attacker; but
  pins are sure wins until then, and garbage cleanup is O(N) owner DELs living a
  year.
- **C5 = 2.** Cut-off is epoch rotation with no re-encryption (cheap), but the
  previous-epoch bundle rule gives `X` a full extra generation of
  back-dated write/delete into up-to-date replicas, the ROSTER race can
  silently re-admit, and mailbox headers tell the relay `ns` and every
  rotation.

---

## Candidate B: causal ORSWOT

### Attacks that work

**B-1. One unsigned HELLO wipes the collection; unattributable; lattice-irreversible (d, e).**
Removal is "dot seen in context, absent from live", honoured from any `RW`
peer. `seen(ctx_M, (s,k))` needs only `k ≤ ctx_M[s].n`, and `n` is legitimately
backed by evidence of `W`'s *latest* dot — `M` never needs to have held the
dots it removes. Trace: `M` (RW) opens a session with `U`, sends `HELLO`
with its true context (every slot's current `n`, all with valid evidence) and
an empty live set. RBSR: every dot `d` of every writer is in `U∖M`. Finalize
at `U`: `seen(ctx_M, d) ∧ M is RW` → drop `d`. `U.live = ∅`, bytes freed
immediately. `U` is RW, so every peer `U` later meets drops the same dots
(removed is top). No signature was made, no record names `M`; the owner sees
an empty collection and no culprit. Recovery is the per-replica "quarantine
ring" (local, bounded, non-replicated), so a wipe larger than the ring is
gone. The same trace from `X` (removed at `T`) against a laggard `L` that
still holds `X` as RW works with `X`'s *old* context — no new evidence
needed — and `L` then carries the wipe to every `U`. §8.1 ("removal has no
author") is framed as a propagation nuisance; §3(a) says `M` can remove dots
"it has seen". Neither says one message removes everything written before
`M`'s snapshot, forever.

**B-2. A lost datagram inside a session is a deletion (g, honest version of B-1).**
Finalize: add received dots, buffer out-of-order seqs, *then* `ctx_A := ctx_A
⊔ ctx_B`. Trace: `B` holds `W`'s dots `(s,6..10)` live, `ctx_B[s].n = 10`;
session to `A` loses `(s,7)` in transit (A5 assumes no reliability). After
finalize `A` has 6,8,9,10 live and `n = 10`; `(s,7)` is now seen-not-live =
removed at `A`. Next session `A ↔ B`: `(s,7) ∈ B∖A`, `seen(ctx_A, ·)`, `A` is
RW → `B` drops it. An honest write is destroyed by packet loss. The same
happens when the 4096-element pending buffer overflows ("overflow drops them
and a later sync refetches" — it cannot, the context already says seen). The
protocol must refuse the context join until the transfer is provably complete;
the text does not say so, and a malicious peer withholding one element is B-1.

**B-3. Backup restore loses all pre-sync writes, not "about half" (b).**
`W` restored at `n_b`; its originals `(s, n_b+1..n)` were typically superseded
by `W`'s own later writes, i.e. are *removed* at everyone. `W` writes before
syncing: `(s, n_b+1) ↦ e'`. On join, `seen(ctx_U, (s, n_b+1))` and the dot is
not live at `U` → `e'` is dropped as removed regardless of hash; same for
every subsequent dot up to `n`. §8.4 says "about half"; it is 100% of the
post-restore pre-sync writes whose dots were ever superseded. `W` can re-issue
only if it still holds the plaintext (its own ring).

**B-4. Undecryptable elements cannot be superseded by anyone but the owner (d, g).**
The write rule drops "every dot of the same `(rid, fld)` visible to `s`";
`rid`/`fld` live inside `ct`. `M` emits elements with `epoch = 65535` (or
any epoch nobody holds) and random `ct`: valid signature, valid dot, opaque
payload. No writer can identify a `(rid, fld)` to supersede, no `Delete rid`
can find them, so they stay live (≤ 65 KiB each, unbounded count) until the
owner fences `M`. Admitted only as generic "fill storage".

**B-5. Equivocation winner is attacker-steerable (c, minor).** `live(e₁) ⊔
live(e₂) = argmin H`, `H = BLAKE2b(nonce ‖ ct)` with a writer-chosen nonce. A
clone grinds its nonce and always wins. Deterministic, but not "deterministic
and fair".

**B-6. Fingerprint collision at ≈ 2^32 (h).** `Σ h(e) mod 2^256` with `h` over
`(slot, seq, epoch, H)` and `H` free via the nonce: Wagner with 2^16 lists
costs ≈ 2^31 work and ~65 k inserted elements (~6.5 MB). `M` ships set `S1` to
`A`, `S2` to `B` with `Σ S2 = h(d) + Σ S1`, same count; the range holding
honest `d` fingerprints equal on both sides and is never split; `B` never
receives `d`. Admitted (§8.5) with a hand-waved per-transport lattice hash.

### Attacks the design defeats
- Far-future / forged time: no clock anywhere; `app-stamp` only among true
  concurrents. (a) defeated.
- Forged seq: `(s, 2^63)` burns only `M`'s own slot; T-EVID/T-NOKILL hold —
  nobody can advance another writer's `n`, so no honest future dot is dead on
  arrival. (a, d-kill) defeated by theorem — the strongest result among the
  four on this axis.
- Pin / brick: no order to pin; every new write is a fresh dot. (d-pin)
  defeated.
- Context size: 256 × 128 B fixed, never pruned. (g-metadata) defeated.
- Relay: only Noise frames; no clear-text header. (f) defeated, with the
  caveat that no non-interactive bundle format exists at all.
- Forward secrecy on removal: hash chain, one box per new member, no
  re-encryption. (e-read) defeated cleanly.

### Honesty
Structurally honest (10 listed weaknesses), but the three that matter are
understated: unauthenticated removal is a one-message, irreversible,
unattributable wipe (B-1), the restore loss is total not half (B-3), and
in-session loss/overflow becomes deletion (B-2). B-4 is not mentioned.

### Scores
- **C2 = 2.** T-NOKILL and no-pin are real and proven; but any RW member (or
  a removed one via a laggard) deletes everything in one unsigned message,
  with no culprit and no replicated recovery.
- **C5 = 3.** Cleanest cryptographic cut-off (hash-chained epochs, no
  re-encryption, no clear headers); `X` cannot mint; but `X` needs no new
  signature to execute B-1 through one laggard, and keeps the dot structure.

---

## Candidate C: signed logs

### Attacks that work

**C-1. A self-covering checkpoint forges any height; the bound becomes a brick (a, d).**
§6: `effective(E)` requires `prev`/`link` "covered: held in `E`, or void under
V1/V2 by a checkpoint `c` of the same writer, in which case the unknown height
is bounded by `h(c)`". For a `CKPT` series `c` at `seq = s`, its own `prev`
`(W, s−1)` is void under V1 *by `c` itself* (`seq ≤ last(c)`), so `h(prev)`
is "unknown, ≤ h(c)" and the well-heighted check `h(prev)+1 ≤ h(c)` is
vacuous. Trace: `M` emits one entry `CKPT seq = 10^9, height = 2^62, prev =
random, link = none, cells = []`. Every replica: valid, authorized, covered,
effective. Honest `U` folds it and must append at `h = 1 + max(h(prev),
h(link)) = 2^62 + 1 > 2^62` → refuses (T-HEIGHT's precondition `max h < 2^62`
is violated by the attacker, not reached by work). `U` can still write at
`h = 2^62` exactly (upper bound is a `≤`), after which every entry in the
collection has equal height and `key = (2^62, writer_pk, seq, id)` resolves by
writer key — `M` grinds `pk_M = 0xFF…` and wins every cell it touches until
`EXCLUDE`; honest writers are pk-ordered forever (the causal-length
saturation lesson, re-created). Even without going to the bound, "heights are
honest-work-bounded" (§2.3, T-HEIGHT) is false: one 195-byte entry buys any
height. Not admitted; the text claims the opposite.

**C-2. `EXCLUDE(X, from_seq)` is evaded by forking below `from_seq` (e).**
Authorization is "the grant/exclude op of greatest `from_seq ≤ seq(e)`", V3 is
`b ≤ seq(e)`, and §2.2 says the fold "does not reject forks: every branch
folds". Trace: owner emits `EXCLUDE(X, b)` with `b = X`'s head seq at `T`. `X`
then emits `(X, b−1)' : prev = id(X, b−2), link = (latest honest entry),
height = h(link)+1, epoch = e_old, ops = [DROP(ent) ∀ ent, SET(…)]`. `seq = b−1
< b`: the governing op is the GRANT → authorized; not void (V3 needs `b ≤
seq`); `prev` is held (or void-covered by `X`'s own old checkpoint). It is
effective at every replica that ever receives it (via any `L`, or any peer
whose ingestion is by record validity), and its height is the newest, so it
wins every cell. `X` can repeat at `b−1` with a new `id` indefinitely (each is
a new branch). The only cure is `EXCLUDE … purge` (void everything of `X`),
after which the owner must re-emit all of `X`'s surviving cells under its own
key — O(`X`'s data). §5 says "can sign entries forever, which are void
wherever the EXCLUDE is held"; false for `seq < b`. Not admitted.

**C-3. Tombstone GC needs every member's checkpoint; a member can hold it hostage silently (d, g).**
`W` may omit tomb `k` only if every member's checkpoint frontier passed it. `M`
checkpoints regularly with a frontier that never advances (validity only
demands pointwise ≥ previous). Every tombstone in the collection is
uncollectable while `M` is a member; a dormant honest tablet does the same.
H7 asked for no membership oracle; §6's predicate iterates "every authorized
member". Admitted (§8.4), but it is a hard-constraint miss, not a weakness.

**C-4. O(n) hashing per session per side (g).** Salted fingerprints must be
recomputed for every session (`Σ BLAKE2b(salt ‖ id)` over all `n` effective
entries). A member opening sessions in a loop costs the victim `n` hashes per
session regardless of `Δ`; the design's 10 ms is for 10^5 entries on a laptop,
not a BLE device with 10^6. Admitted as a cost, not as a lever.

**C-5. Million-entry griefing is replicated storage until EXCLUDE (g).** `M`
appends 10^6 entries of 195 B (195 MB) with `link` to nothing; they are
effective and must be stored by every replica until `EXCLUDE`. Pending-set
caps do not help: the entries are not pending. Admitted (§3 "cost is storage,
bounded by EXCLUDE").

**C-6. Zero-salt digest is collidable (h, minor).** `digest = fingerprint with
salt = 0^32`, an unkeyed 256-bit sum: ≈ 2^32 Wagner by a content-choosing
writer. Sync is safe (per-session salt), but the thing exposed to "storage
checks and the app" as the digest can be made equal for different effective
sets.

### Attacks the design defeats
- Wrong clock: none exists. (a-time) defeated.
- Backup restore / clone: forks are accepted, both branches fold, replicas
  agree; loss bounded to one checkpoint interval and repaired by rebase.
  (b, c) defeated at the convergence level (damage admitted).
- Kill another writer: only `EXCLUDE` (owner) can; forged `link` hurts only
  the forger (pending). Defeated.
- Chosen-set fingerprint collision in sync: per-session salt, sets fixed
  before the salt. (h) defeated for reconciliation.
- Pre-exclusion thief writes: `EXCLUDE(X, b)` with `b` = seq at theft voids
  the thief's writes retroactively — the only candidate whose revocation can
  undo a thief's deletes (if the dominated cells were not yet omitted by an
  honest checkpoint). Genuine strength.
- Relay: Noise only; headers (writer, seq, link) visible to members only.
  (f) defeated.

### Honesty
Weakest where it matters. §8 lists overhead, pending lag, fork × checkpoint,
membership in GC, owner single point, griefer heights "harmless" — and the
last is contradicted by C-1, while §5's revocation claim is contradicted by
C-2. Both are claimed as theorems (T-HEIGHT, T-AUTH) that the stated rules do
not deliver.

### Scores
- **C2 = 1.** As written, one checkpoint entry forges height to the bound and
  pins cells / degrades the whole collection to pk-order until EXCLUDE; a
  million-entry flood is replicated until EXCLUDE; recovery from a thief is
  good (retroactive void) but the ongoing-writer case is the worst of the four.
- **C5 = 1.** A removed member keeps full write/delete power through
  fork-below-`from_seq` unless purged (O(data) re-emission by the owner);
  members see full causal structure in headers; epoch cut-off itself is fine.

---

## Candidate D: prior art

### Attacks that work

**D-1. A far-future `Tomb` makes every honest writer irreversibly destroy its own data (a, d, e).**
§3 "Deletion": when a replica holding key `B` sees its own `Value` shadowed by
another author's newer `Tomb`, it writes its own `Tomb` at `(E)` — which
prunes `B`'s own records under `E` (same author, prefix, newer) and frees
their bytes on every replica. Trace: thief/`M` with key `K` (window
`[a, b]`) emits `Tomb(E_i) ts = b` for every entity `E_i` it can see (one
record each, ≤ 2^44 µs ≈ 200 days ahead). Each honest `B`, on applying, finds
its values under `E_i` shadowed → signs `Tomb_B(E_i) ts = HLC_B` → `B`'s values
under `E_i` are pruned (G1) at every replica, bytes gone. Owner then issues
`Rev(K)`: `K`'s tombs are pruned — but `Tomb_B` records are honest, signed by
`B`, remain, and `B`'s values are already freed everywhere. Nothing comes
back. The same happens via a laggard `L` after `Rev(K)`: `L` applies `K`'s
tomb, self-tombs, propagates its own signed tomb. This converts the "bounded,
view-only pin" (§9) into unbounded, permanent, cross-author data loss triggered
automatically. Not admitted.

**D-2. `Rev(K)` deletes every record `K` ever wrote — including the owner's own lost phone (c, e).**
Prune rule: `kind(a) = Rev ∧ subject(a) = author(b)` prunes all `Value`/`Tomb`
of `K`, in every store, forever. Each *device* is an author with its own
subspace, so the standard H8 remedy — revoke a lost/cloned phone — erases
everything that phone authored (likely most of the owner's data) from all
replicas. To keep it, the owner must first re-author every record under
another key (O(data), new `ts` on every cell). `Clamp(K, t)` is the only
non-destructive option, and it leaves a thief able to write back-dated
records `ts ≤ t` that still beat anything older in the view (`cand` honours
`ts_r ≤ clamp`). §9 lists only "O(n) re-seal per removal". Not admitted.

**D-3. Device-global HLC adoption re-imports clock poisoning; the 16-bit counter exhausts at the ceiling (a).**
§4: `receive` takes the max with *any* valid stored record's `ts`, clamped to
the device's own `not_after`. Trace: `K` writes one record at `ts = b_K` in
shared collection `X`. Every device `D` storing it sets `l_D = min(b_K,
not_after_D)` — for the whole device, so `D`'s writes in private collection
`Y` (where `K` has no capability) now carry `ts ≈ not_after_D` and beat
every other `Y`-writer's honest edits until their clocks pass it. Then
`ts = l·2^16 + c`: with `l` pinned, every local tick increments `c`; after
65 536 events `c` cannot grow, `l` cannot exceed `not_after_D`, and T-13's
"strictly increasing within a window" is unsatisfiable — the device either
wraps (H6), refuses (honest writer stalls until the root renews its Cap), or
mints outside its window (invalid). The candidate says `receive` is "never for
acceptance" and T-9 says "zero bytes outside `K`'s subspace"; timestamps are
not bytes, and they leak across collections through the device clock. Not
admitted.

**D-4. Per-session-keyed fingerprints cost O(n) per session and cannot use the claimed O(log n) tree (g).**
`f_k(x) = BLAKE2b(k ‖ h_x)` with `k` from the Noise handshake means every leaf
value changes per session; an order-statistics B-tree with precomputed sums
is useless, so each session recomputes `n` PRF calls per side. Same lever as
C-4 for a session-churning member, and an internal contradiction in §5/§7.
Not admitted (§9 only says the security is "a PRF argument").

**D-5. New members cannot read history, or Seals grow without bound (e, g).**
A `Seal` boxes `k_e` for the new epoch only; `Value` bodies stay under the
epoch they were written in. A member added after rotation `e'` has no `k_e`
for `e < e'`. Either every rotation re-encrypts all records (O(data) rewrite,
with new `(ts, h)` churn on every cell) or Seals carry all prior keys (growth
with rotations × members, on top of the admitted "auth records kept
forever"). The text picks neither. Not admitted.

**D-6. Expired-tombstone re-send between skewed clocks (g, minor).** `elems`
excludes tombs with `now ≥ ts + T_gc`; a slow-clocked replica still includes
them and ships them every session to a fast one, which drops them on arrival
(G2). O(#expired tombs) per session pair.

### Attacks the design defeats
- Far-future clock: `valid(r)` rejects `ts` outside the capability window;
  `Clamp(K, t)` is one record; HLC receive makes honest post-observation
  writes beat `K`'s (a chase) as long as the honest window ends later. (a)
  partly defeated — the residue is D-3.
- Backup restore / clone: `(ts, h)` total within a subspace; replicas agree;
  resurrection confined to `K`'s own cells after `T_gc`. (b, c) defeated at
  convergence level.
- Kill another writer / brick the collection: nothing prunes across authors,
  root writes no data, per-cell candidates ≤ 64. (d-kill, d-brick) defeated
  cleanly — strongest isolation of the four.
- Removed member's writes, including back-dated: `Rev(K)` prunes every `K`
  record regardless of `ts`, wherever it lands. (e-write) defeated — the only
  candidate where back-dating buys nothing (modulo D-1 side effects at a
  laggard).
- Fingerprint forgery: session key unknown to the chooser; digest is a hash
  of the sorted id list, not a sum. (h) defeated.
- Relay/stranger: PIO hides collection ids, fixed-size frames, membership
  sealed inside the collection. (f) best of the four.
- Flood cleanup: `Rev(K)` removes `K`'s garbage in one record. (g) best of
  the four — at the price of D-2.

### Honesty
Medium. §9 admits bounded pinning, resurrection, O(authors) cells, auth
growth, re-seal cost, pending drops, last-action-wins. It omits the two
largest: the self-Tomb cascade (D-1) and that revocation is data destruction
(D-2), plus the device-global HLC (D-3), the O(n)-per-session keyed
fingerprint (D-4), and new-member key history (D-5).

### Scores
- **C2 = 2.** Subspace isolation and one-record `Rev` are the best
  containment story here; but a stolen key's far-future tombs make honest
  writers delete their own data permanently, the clock leaks across
  collections, and recovering from a lost device means losing its records.
- **C5 = 4.** `Rev` neutralizes all of `X`'s writes regardless of `ts`,
  epochs cut reads, PIO and padding blind relays and strangers; deductions
  for D-1 via laggards, the unspecified history-key story, and plaintext
  retention (inherent).

---

## Ranking

1. **A (hardened LWW)** — C2 3 / C5 2. Every surviving attack is signed,
   attributable, and ends at revocation plus one ceiling refresh; the owner
   can always write above the attacker; garbage and tombstone costs are
   large but bounded and visible. Its weakness list is the most candid. The
   fixes it needs are small and local: drop previous-epoch bundle acceptance,
   make `revoked[]` grow-only across ROSTERs, encrypt the bundle header, and
   admit the pk-grind.
2. **D (prior art)** — C2 2 / C5 4. The best containment (nothing crosses a
   subspace, one `Rev` cleans everything, back-dating is useless, relays learn
   least). Loses to A because two un-admitted rules turn the stolen-device
   case into permanent loss: the self-Tomb maintenance rule (D-1) and
   `Rev`-prunes-everything (D-2), plus a device-global HLC that re-imports the
   clock-poisoning incident. All three are removable without touching the
   lattice, which is why it is second, not fourth.
3. **B (causal ORSWOT)** — C2 2 / C5 3. The strongest theorems against pins
   and future-write kills, and the cleanest key rotation. Ranked below D
   because its worst attack is intrinsic to its core mechanism: removal by
   context is one unsigned message, unattributable, lattice-irreversible,
   usable by any RW member or any removed member through one laggard, and the
   same mechanism turns packet loss into deletion. Fixing it means signed
   removals, i.e. the tombstones the design was built to avoid.
4. **C (signed logs)** — C2 1 / C5 1. Two load-bearing claims are false as
   written: heights are not honest-work-bounded (a self-covering checkpoint
   forges 2^62 in one entry and recreates the saturation incident), and
   `EXCLUDE(from_seq)` does not revoke (fork below `from_seq`). Add the
   membership-oracle GC, O(n) hashing per session, and replicated griefing
   storage. The retroactive-void of a thief's writes is a real idea worth
   stealing; the rest needs a rewrite of §2.3/§6 before it can be scored
   higher.
