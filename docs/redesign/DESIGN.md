# Kome, redesigned: the frontier store

**Decision.** Build Kome on a single lattice: the *frontier* of a set of
signed records under one strict total order, with every policy question
(authorization, far-future clocks, revocation) moved out of the merge and into
either a monotone admission rule or a pure view. This is candidate A's core
with candidate D's hygiene, corrected for every counterexample the three
judges produced. The judges' reports are in `judges/`; the candidates in
`candidates/`. The reasoning is in §1, the design in §2–§8, the theorems in
§9, and what is still open in §10.

A second round (§1.1) searched four further designs and two modules against
this one. The core survived unchanged; the round contributed three repairs
(§4, §7, §9), one protocol module (§8), one authorization module (§6), and
one specified extension (§4, candidate F) that is not on the critical path.

## 1. Why this and not the others

Four designs were produced independently and judged by three adversarial
reviewers (mathematics, attacker, implementer). The combined verdict:

| Candidate | Math | Attacker | Implementer | Decisive finding |
|---|---|---|---|---|
| A hardened LWW | 2nd | 1st | 1st | Core lattice sound; two stated theorems false (ceiling gate non-monotone; TTL refuse-on-arrival diverges under clock skew) |
| B causal ORSWOT | 3rd | 3rd | 2nd | Cleanest lattice; but removal is an unsigned, unattributable, irreversible message, and a buffer overflow during catch-up turns undelivered writes into deletions |
| C signed logs | 4th | 4th | 4th | Height check differs between a trimmed and an untrimmed replica, so they never agree; a self-covering checkpoint forges a maximal height in one entry |
| D prior art | 1st | 2nd | 3rd | Store lattice has the only monotone admission gate; but cross-author deletion is view-only and expires, so deleted data returns on every replica; and the self-tombstone rule lets a stolen key make honest devices destroy their own data |

B and C are rejected on structural grounds: their worst failures are
intrinsic to the mechanism each was built around (removal-by-absence, and
height verification against truncatable history). A and D fail on fixable
specification errors, and the fixes make them the same design:

- A with its ceiling demoted from an arrival gate to a *monotone* admission
  rule, and its tombstone expiry changed from refuse-on-arrival to
  apply-then-expire; or
- D with cross-author tombstones that dominate in the store (so deletion is
  durable and membership-free), its self-tombstone rule removed, its
  device-global clock adoption removed, and its revocation given a `from_t`.

What follows is that design. Candidate B's hash-chained epoch keys are
adopted for read control. Nothing from C survives except its observation that
a thief's post-theft writes should be voidable retroactively, which A already
had.

### 1.1 Round two: the search for a better design

Four more candidates were written against this design as the baseline (S)
and judged by the same three reviewers (`judges/round2-*.md`):

| Candidate | Idea | Math | Attacker | Implementer | Verdict |
|---|---|---|---|---|---|
| E height versions | order by a chasing `height`, keep `t` honest for expiry | 2nd | 2nd | 1st | **Rejected.** Fixes two real baseline warts (cleanup tombstones live `δ + del_ttl`; sub-ceiling pins Lamport-ize a cell) but opens a new one: expiry is by writer-chosen `t` while domination is by `height`, so a `DEL` with `t = 0` and a higher `height` dominates the owner's tombstone and expires at once, leaving no tombstone and letting old signed `PUT`s resurrect the entity. Deleter-chosen tombstone lifetime is a new attacker primitive S does not have. Also incompatible with H. |
| F typed fields | per-`(cell, author)` records joined per type (counter, set, multi-value) | 3rd | **1st** | 2nd | **Adopted as a specified extension, phase 2.** Composes with S (same-author domination by the full `v` keeps T2'/T3); needs the `W` register (§4) or per-cell state is unbounded. Gives up nothing S has; changes `get` and the index to `(cell, author)`. Built when an application needs engine-side counters or sets. |
| G causal multi-value | per-author store, parent hashes resolved in the view, no clock in the order | 4th | 3rd | 3rd | **Rejected.** The strongest anti-pin statement of both rounds (no `PUT` can be shadowed), but resolved siblings are retained not freed, "last modified" leaves the engine, and a forged height after each roster can exhaust the ceiling space on the attacker's schedule. Its `W` register is kept (§4). Stays as the answer if a multi-person-list application wants visible conflicts. |
| H snapshot GC | root-signed per-entity kill levels replace `del_ttl` | 5th | 4th | 4th | **Rejected.** The lattice is sound and "no resurrection ever" is the cleanest theorem of the round, but the liveness assumption it removes from the drop rule reappears as a completeness obligation on the root with *destruction* of synced data as the failure mode (a restored root's chunk kills a re-created entity everywhere); a stolen root key becomes an unrevocable one-record wipe; snapshot traffic scales with live entities, not deletions; and its `t`-keyed kill set is not a down-set of any height order, so it cannot be combined with E or G. |
| I one-round sketch | IBLT round 0 before the range split | accept | accept | accept | **Adopted** (§8), capped so the sketch fits one message. |
| J multi-root | several root keys, rotation, per-field writer sets | accept with fix | accept | half | **Adopted without field rules** (§6): root loss becomes recoverable; `roots_ever` must be joined in the handshake and root additions gated by the founding key. Field rules cut (labels only). |

The three judges disagreed on E (the implementer wanted it, the other two
did not) and on how soon F belongs on the critical path; they agreed that
H and G lose, that I is free, and that the baseline's lattice could not be
broken. What the round did find in the baseline were two prose faults, both
repaired below and neither touching a checked theorem: `maxceil` is replica
state the sync protocol never joined, so a latecomer could refuse a record
every other replica admits until a root refresh (fixed by joining the
grow-only registers in the session handshake, §4); and assumption A4 was
too weak as stated (restated in §7).

The governing rule the math judge extracted, which decides every future
proposal: **the frontier lattice is sound iff every kill predicate is a
down-set of the record order on its key.** Every rejected combination in
this round fails exactly that test.

## 2. Objects

**Identifiers.** A collection `ns` is 16 bytes, self-certifying:
`ns = BLAKE2b-256(root_pk ‖ salt)[0:16]`. An entity `ent` is 16 bytes. A field
name is 1–32 bytes. A value is 0–65 535 bytes (blob chunks of 32 KiB fit;
larger payloads are chunked above the engine). An empty value is a value.

**Version.** `v = (t : u48, author : [32]u8, seq : u48, h : [32]u8)`, compared
lexicographically with `author` and `h` as unsigned 256-bit integers. `h` is
the record's own content hash, so distinct records never compare equal and the
order is total by construction. `t = 0` and `seq = 0` are ordinary values.

**Records.** Canonical content is hashed and signed; `h = BLAKE2b-256(tag ‖
content)`, `sig = Ed25519(h)`.

```
PUT     ns[16] ent[16] flen:u8 field[flen] t:u48 seq:u48 author[32] vlen:u16 value[vlen]
DEL     ns[16] ent[16]                     t:u48 seq:u48 author[32]
ROSTER  ns[16] root_pk[32] salt[16] gen:u48 ceiling_t:u48 del_ttl:u48 epoch:u16
        n_members:u8 (≤64) members[n] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
REVOKE  ns[16] root_pk[32] salt[16] sign_pk[32] from_t:u48 rev_seq:u48
```

`PUT`/`DEL` are signed by `author`; `ROSTER`/`REVOKE` by `root_pk`, and are
well-formed only if `ns` matches `(root_pk, salt)`. A record is **well-formed**
iff its bounds hold and its signature verifies: a function of its bytes alone.

**Why these four kinds.** `PUT` and `DEL` are the data. `ROSTER` carries
membership, the epoch key, and two replicated parameters (`ceiling_t`,
`del_ttl`). `REVOKE` is separate from `ROSTER` because it must be grow-only:
a revocation can never be undone by a later roster (the attacker judge's
finding against A, where a restored root's roster could drop a revocation).

## 3. The lattice

For `H` a set of well-formed records, **domination** is:

```
dom(p, H) for PUT p   := ∃ q ∈ H : PUT, cell(q) = cell(p), q.v > p.v
                       ∨ ∃ d ∈ H : DEL, entity(d) = entity(p), d.v > p.v
dom(d, H) for DEL d   := ∃ d' ∈ H : DEL, entity(d') = entity(d), d'.v > d.v
dom(r, H) for ROSTER  := ∃ r' ∈ H : ROSTER, same ns, (r'.gen, r'.h) > (r.gen, r.h)
dom(x, H) for REVOKE  := false
F(H) := { x ∈ H | ¬ dom(x, H) }
```

`F(H)` is the **frontier**, and it is the state. `dom` is monotone in `H`
(T2) and *upward-closed*: a dominator of a dominator of `x` dominates `x`
(T2'). The mathematics judge identified T2' as the lemma A's proof needed and
did not state; it holds for every kind above, which is why `REVOKE` is not
allowed to dominate (a revocation dominating a writer's `PUT` would not
dominate what that `PUT` had already dominated; see §6). From T2 and T2':

```
F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))        (T3)
```

so a replica may drop a dominated record the moment it is dominated, on any
subset of replicas, at any time, and no future frontier changes. That one
equation is the whole GC story for values: a deleted entity's values are freed
everywhere a `DEL` arrives, with no membership knowledge and no clock.

**Views** are pure functions of `F`:

```
deleted_at(ns, ent) := max { d.v | d ∈ F, DEL on (ns, ent) }        -- Option
cell(ns, ent, f)    := the unique PUT in F on (ns, ent, f)           -- Option
exists(ns, ent)     := ∃ f. cell(ns, ent, f) ≠ None
void(p)             := ∃ REVOKE(p.author, from_t) ∈ F : p.t ≥ from_t
far(p)              := p.t > now_local + slack      -- advisory flag only
```

There is no presence bit and no sentinel: an entity exists iff it has a live
field; a deleted entity is a `DEL` and nothing else.

## 4. Admission

Every well-formed record is admitted **except** a `PUT`/`DEL` with
`t > maxceil` or `author ∉ W`, where `maxceil` is a per-collection
max-register updated from `ceiling_t` of every `ROSTER` ever applied
(including rosters dominated on arrival), and `W` is a per-collection
grow-only set of every `sign_pk` that any applied `ROSTER` has ever listed
(candidate G's register, adopted in round two). Both are stored, not
derived, and only grow. `W` bounds who can occupy the store: without it a
member could relay records under unrostered ground keys and make a cell's
state unbounded (the math judge's finding against F), and typed cells (§4,
F) would have no per-cell bound at all. Removal from `W` does not exist;
removal of a writer is `REVOKE` (§6).

This replaces A's gate ("inadmissible under the currently maximal roster"),
which the mathematics judge broke with two rosters of equal generation. The
new rule is **monotone in the held history**: once a record is admissible at
a replica it stays admissible, and a record inadmissible at one replica
becomes admissible there as soon as the roster that made it admissible
elsewhere arrives. Inadmissible records are not held; they are re-offered by
whichever peer holds them on the next reconciliation (T4 is stated in exchange
form for exactly this reason). The ceiling keeps the top of the version order
unreachable: no admissible record can pin a cell beyond `maxceil`, and every
roster refresh moves `maxceil` up.

The state of a replica is therefore the triple `(F, maxceil, W)`; its join
is `(F(F₁ ∪ F₂), max(c₁, c₂), W₁ ∪ W₂)`.

**The registers are reconciled, not only the records (round-two repair).**
`maxceil`, `W` and `roots_ever` (§6) are replica state, and §8 reconciles
only the records of `F`. A roster that raised `maxceil` on some replicas
and was then dominated everywhere never reaches a replica that joins later,
and the design's own "root restored from backup" row produces exactly that:
an equal-generation roster with a lower ceiling that wins by `h` leaves a
record admissible at one replica and refused at another after every
exchange until some root issues a higher ceiling. So every session's HELLO
carries `(maxceil, W, roots_ever)` and each side joins them componentwise
`(max, ∪, ∪)` before any element is offered. Admission stays monotone, no
theorem changes, and the exchange clause of T4 becomes true. A replica is
never worse off for joining: the registers only ever widen what is
admissible.

**Typed fields (extension, candidate F).** When an application needs
counters, grow-only sets or multi-value registers in the engine, a `PUT`
may carry `ftype : u8 ∈ {LWW, GSET, PNCOUNTER, MVREG, MAXREG}` as part of
the cell key, the author's full state for that field as its value, and the
`PUT`-over-`PUT` clause of `dom` gains the condition `(ftype = LWW ∨ same
author)`. The frontier then holds at most one record per `(cell, author)`,
bounded by `|W|`, and the cell's value is a join over the surviving,
non-void per-author records. LWW cells are unchanged. The specification is
`candidates/F-typed-fields.md`, as repaired by the round-two judges (`W`
required; the fold saturates; view output read through a cursor). It is
not on the critical path: an application can get the same semantics today
with one LWW sub-cell per device.

## 5. Clocks and writing

There is no engine clock, no `tick`, no `receive`, nothing adopted from a
peer. The attacker judge's finding against D (device-global adoption carried
one collection's far-future record into every other collection on the device)
cannot occur because no timestamp is ever adopted.

```
floor(cell)  := max(cell(ns,ent,f).v, deleted_at(ns,ent))     -- for DEL: max over all fields and deleted_at
t_emit       := max(now_ms, floor.t + 1 if floor exists); if t_emit > maxceil then t_emit := maxceil
seq_emit     := seq_self + 1;  at 2^48 − 1 the write fails SEQ_EXHAUSTED, no record is produced
v_emit       := (t_emit, self_pk, seq_emit, h)
status       := SHADOWED if floor exists ∧ v_emit < floor   (only when t_emit = maxceil) else OK
```

A write *chases* the cell's floor, so read-your-writes holds (T8) unless the
cell is pinned at the ceiling. A device with no real-time clock works: all its
writes chase. `seq_self` is the only persisted clock state.

**What a misbehaving writer can do (H8).**

| Case | Effect | Bound |
|---|---|---|
| Clock ahead by δ | Wins concurrent conflicts on cells it writes for δ; those cells then resolve by chase (arrival order) rather than wall time | δ ≤ maxceil − now; only cells it touched; automatic |
| Clock behind | Loses concurrent conflicts; its own cells still chase | its cells only; a fixed clock takes effect at once |
| Backup restore | Re-emits old `seq` values: equivocation, ordered by `h`, flagged; old records re-offered and dominated unless the `DEL` has expired (§7) | self-detected (own record with `seq ≥ seq_self + 1`); `seq` jumps; status `CLONE_SUSPECTED` |
| Cloned key | Continuous equivocation; replicas still agree | flagged; owner issues `REVOKE(old, from_t)` and a roster with fresh keys |
| Malicious | Overwrite or delete any cell (that is what write access means); pin cells to `maxceil`; flood entities; grind a public key that wins ties at the ceiling | no forging; no exceeding `maxceil`; pins end at the next roster refresh; floods end at `REVOKE` plus owner `DEL`s |
| Root restored from backup | Issues a roster with an old `gen`; dominated or dominating by `(gen, h)`, but `maxceil` never decreases and `REVOKE`s are never lost | convergent either way |

The honest statement of the residual: **LWW cannot un-ring a wall clock**. A
cell whose floor was pushed far ahead resolves by chase until wall time passes
it. The ceiling bounds how far; it does not prevent it. A thief's overwrites
before revocation stand, flagged `void`; the bytes they replaced are gone. The
attacker judge ranked this acceptable because every such act is signed,
attributable, bounded, and ends at revocation plus one refresh.

## 6. Authorization, encryption, revocation

**Membership is key possession.** The `ROSTER` wraps the current epoch key to
each member's `dh_pk`. Epoch keys form a hash chain `k_e = BLAKE2b-256(k_{e+1}
‖ "prev")` (from candidate B): a member holding `k_e` derives every older key,
so a new member needs one box and can read all history, and a removed member
holding `k_e` cannot derive `k_{e+1}`. The root precomputes the chain from a
random top; 2^16 epochs suffice for any collection's life.

**Two gates on transport, none on records.** A peer is admitted to a session
for `ns` iff its device key is in `ROSTER_max.members`. A sealed bundle
(mailbox, broadcast, BLE) is readable iff the replica holds its epoch key;
bundles are accepted **only under the current epoch** (the attacker judge's
finding against A: accepting the previous epoch let a removed member write
into up-to-date replicas for a whole epoch). Both gates decide who you talk
to, never what a record means.

**Several roots (module J, adopted in round two).** A `ROSTER` lists
`n_roots ≤ 4` root keys and `prev_h`, the hash of the roster it extends.
`ROSTER`, `REVOKE` and the epoch key may be issued by any listed root; a
root may be revoked like a member. A root is *added* only by a roster signed
by the founding key (the one `ns` is derived from), so a stolen secondary
root cannot mint an unbounded chain of successors; a root is removed by any
root. `roots_ever` is a grow-only register of every root any applied roster
has listed, joined in the HELLO with `maxceil` and `W`; `ROSTER`/`REVOKE`
admission is `signer ∈ roots_ever`. Roster domination is per signer
(`same signer ∧ (gen, h)` greater), and the effective roster is the view
`ROSTER_eff := max_(gen,h)` over frontier rosters whose signer is not
`root_void`. Two roots racing equal generations resolve by `h` as before;
`REVOKE`s are grow-only so nothing a race can do loses one. The payoff is
that losing the root device is recoverable whenever `n_roots ≥ 2`. Per-field
writer sets were part of module J and are cut: enforced at admission they
are non-monotone (the math judge's D counterexample), and as a view flag
they are a label that cannot stop an unauthorized write from freeing an
authorized value's bytes.

**Revocation** is `REVOKE(X, from_t)`: grow-only, never dominated, root-signed.
Its effect is the view flag `void` on `X`'s records with `t ≥ from_t`, plus
the roster that follows it (fresh epoch, `X` removed). It is deliberately
*not* a prune. The mathematics judge's analysis of A explains why and it is
worth restating: if a revocation dropped `X`'s records from `F`, a record `p'`
of `X` that had already dominated (and freed) an honest `p` would vanish on
one replica and leave the cell empty, while a replica that saw the revocation
first would still hold `p`. Same records, different frontiers. Retroactive
removal needs history; a frontier has none. So `void` hides and flags, and an
honest writer's next write chases above the voided record. The cost: a
revoked writer's garbage stays in `F` as void records until the owner `DEL`s
those entities (an app-level "purge revoked writer" routine issues the
`DEL`s; the tombstones then expire).

`from_t` gives the owner the choice D lacked: revoke a lost phone from the
moment it was lost, keeping everything it wrote before.

## 7. Storage and tombstone expiry

Append-only log of `content ‖ sig` frames, sealed at rest under the device
key; in-memory index `cell → (offset, v)`; compaction rewrites exactly `F`.
Per cell, version metadata is 6 + 6 + 32 bytes plus a cached 32-byte `h`.

**Drop rule.** A frame is dropped iff

```
dom(x, F)                                                  -- deterministic, membership-free (T3)
∨ (x is DEL ∧ now_local ≥ x.t + ROSTER_max.del_ttl)        -- tombstone expiry
```

The second clause is **apply-then-expire**, not A's refuse-on-arrival: an
arriving `DEL` is always applied (it dominates and frees the entity's values)
and only then, if already past `del_ttl` by the local clock, dropped. The
mathematics judge showed that refusing an expired `DEL` on arrival lets two
replicas with a two-millisecond skew diverge and then resurrect the entity on
both. With apply-then-expire, a skewed pair converges on the next exchange
(the replica still holding the `DEL` re-sends it; the other re-applies and
re-expires it; the cost is one frame per session until both expire it) and
the only residual is the documented one: a straggler that never saw the `DEL`
and reconnects after `del_ttl` resurrects the entity with its stale fields,
which the user re-deletes. That requires a device offline for longer than
`del_ttl` (default 180 days); it is a liveness assumption (A4), stated as such,
not hidden in a safety theorem.

**A4, restated (round-two repair).** "Every member syncs with some member
once per `del_ttl`" is not enough: the math judge gave a four-member
schedule satisfying it in which the `DEL` reaches two members, both expire
it, and a third member that never saw it re-seeds the entity everywhere.
The assumption expiry needs is **A4′: every `DEL` reaches every member
within `del_ttl` of `d.t`**, that is, sync-graph diameter times sync period
is below `del_ttl`. Its failure mode is resurrection of deleted data, never
destruction of live data, which is why this clause was kept over candidate
H's snapshots.

**Chased tombstones (residual found by candidate E).** A `DEL` that
dominates a far-future `PUT` must chase to `t > p.t`, so its tombstone lives
`δ + del_ttl` where `δ` is how far ahead the pinning clock was, bounded by
`maxceil − now`. Candidate E removed this by ordering on a separate counter
and was rejected because a writer-chosen expiry clock is worse than an
inflated one (§1.1). The residual is storage of one tombstone frame per
pinned entity for at most one horizon beyond `del_ttl`. Compute
`x.t + del_ttl` in 64 bits; at `x.t = 2^48 − 1` a 48-bit sum wraps and
would turn an immortal tombstone into an instant one.

**Bounds.** `|F(ns)| ≤ live cells + DELs younger than del_ttl + 1 roster +
revocations (≤ 1024, then the collection is re-founded)`. No vectors, no
per-peer state, no shells, no pending buffers.

## 8. Reconciliation and digest

Elements are the records of `F` for one `ns`, keyed
`kind:u8 ‖ ent[16] ‖ field[32] ‖ h[32]` with `ROSTER = 0, REVOKE = 1, DEL = 2,
PUT = 3`, so authorization records sort first and usually arrive first; under
reordering nothing breaks, because admission is monotone (§4).

**Fingerprint = digest.**

```
acc(e)     := BLAKE2b-256("kome/acc" ‖ h(e) ‖ i) for i in 0..15, concatenated, as an integer mod 2^4096
ACC(R)     := Σ acc(e) mod 2^4096
fp(R)      := BLAKE2b-256("kome/fp" ‖ |R| ‖ ACC(R))
digest(ns) := fp(F|ns)
```

`ACC` is homomorphic over disjoint union, so block prefix sums (one 512-byte
sum per 64 elements, 8 bytes amortized per element) answer any sub-range in at
most 64 big-integer additions, and the snapshot cache the current engine's
performance work depends on survives. The implementer judge preferred this to
the per-session keyed sum of C and D, which forces O(n) hashing per session;
the attacker judge accepted its security: a k-sum attack on a 4096-bit modulus
costs about 2^128 and needs 2^64 inserted records. The current 256-bit sum is
breakable in about 2^32 by a member, which is why the size changes.

**Round 0: one-round set difference (module I, adopted in round two).**
After the HELLO (which also joins the registers, §4) each side sends an
invertible Bloom lookup table over the 32-byte element hashes of `F`,
sized from the two sides' `|F|` and clamped so one sketch fits in one
message (at most 1 000 cells of 44 bytes). Subtracting the two tables and
peeling yields the exact symmetric difference in one round when it is small,
which is the common case; peeling failure and a false decode are both
detected (every recovered hash must verify against a held or received
record) before any state is written, and the session falls through to the
range protocol below. The sketch is homomorphic, so it is cached per
collection and updated per record. It adds nothing to the trusted core:
every element it names is still delivered and checked as a record.

**Protocol.** Range-based set reconciliation as today: both sides snapshot
`F`, exchange `(lo, hi, fp)`, split 16-way on mismatch, ship elements for
ranges of at most 4, finish with a HAVE round. Descriptors are self-contained;
loss, duplication and reordering cost rounds, not correctness. A session with
no loss takes at most `⌈log₁₆ N⌉ + 2` rounds; under loss it terminates given
fairness (some descriptor eventually gets through), which T7 states
explicitly. Transports: Noise XX bound to the device key for interactive sync;
sealed bundles (`ns ‖ epoch ‖ nonce ‖ AEAD(elements)`, header encrypted) for
store-and-forward. Relays see ciphertext and a routing key.

## 9. Proof obligations

Stated so that each is a finite, first-order fact about sets of records.
Core-Lean-provable ones are marked ✓; the two hard ones are marked ✗.

- **T1 ✓ Total order.** On well-formed records with `h` injective, `v` is a
  strict total order.
- **T2 ✓ Monotone domination.** `H ⊆ H' ⇒ dom(x, H) ⇒ dom(x, H')`.
- **T2' ✓ Upward closure.** `y dom x ∧ z dom y ⇒ z dom x`, for every kind.
- **T3 ✓ Frontier homomorphism.** `F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))` and
  `F(F(H)) = F(H)`. Hence dropping dominated records anywhere, at any time,
  changes no future frontier.
- **T4 ✓ Convergence.** With state `(F, maxceil)` and `apply(S, r)` admitting
  `r` iff `r.t ≤ maxceil` (for data records): two replicas that applied the
  same set of records in any order with any duplication hold the same `F`
  and `maxceil`; and, given that the session HELLO joins the registers
  (§4), after a complete reconciliation two replicas hold `F(H_A ∪ H_B)`
  and `max(c_A, c_B)`, including records that were inadmissible at one side
  when first offered. (Without the HELLO join the exchange clause is false:
  round-two math judge, counterexample 1 against S.)
- **T4' ✓ Monotone admission.** `adm(r, c, W) ∧ c ≤ c' ∧ W ⊆ W' ⇒
  adm(r, c', W')`, and neither `maxceil` nor `W` nor `roots_ever` ever
  shrinks under any sequence of rosters, including rosters of lower
  generation. (`W` is not yet in the Lean model; §10.)
- **T5 ✓ View determinism.** `deleted_at`, `cell`, `exists`, `void` are
  functions of `F` alone.
- **T6 ✓ Digest.** `digest(ns) = fp(F|ns)`; `ACC(R₁ ⊎ R₂) = ACC(R₁) +
  ACC(R₂)`; under k-sum hardness, `fp(R₁) = fp(R₂) ⇒ R₁ = R₂`.
- **T7 ✗ Reconciliation.** From `F_A, F_B` over `N` elements, the protocol
  terminates in `≤ ⌈log₁₆ N⌉ + 2` rounds without loss, and in finitely many
  rounds under loss, duplication and reordering given fairness; both sides
  then hold `F(F_A ∪ F_B)`. (An induction over the recursive split; the
  substantial Lean project.)
- **T8 ✓ Chase.** If `floor.t < maxceil` then `v_emit > floor`; always
  `v_emit.t ≤ maxceil` and `v_emit.seq` exceeds every `seq` this device
  emitted.
- **T9 ✓ Bounded pin.** No admitted data record has `t > maxceil`; once a
  roster with a higher ceiling is applied, every honest write to any cell
  is unshadowed.
- **T10 ✓ Equivocation.** Two distinct records with equal `(author, seq)`
  are ordered identically everywhere; `F` is unaffected by arrival order.
- **T11 (liveness) Tombstone expiry.** Under A4′, after every replica has
  expired `d`, no replica holds a record `d` dominated; and apply-then-expire
  guarantees that two replicas differing only in whether `d` has expired
  agree again after one exchange.
- **T12 ✓ Revocation locality.** Applying a `REVOKE` or a `ROSTER` changes
  `F` only at that record; it never adds or removes a `PUT` or `DEL`; `void`
  is monotone in `F`.
- **T13 ✓ Bounds.** Every emitted record satisfies the §2 layout; `seq`, `t`,
  `gen`, `rev_seq` never wrap; at a bound, emission fails with no side effect.
- **T14 ✗ Epoch secrecy.** A key absent from roster `e` and all later rosters
  cannot derive `k_e'` for any `e' ≥ e` (hash-chain one-wayness plus the
  AEAD). A paper reduction, not a Lean theorem.

**Assumptions.** A1 Ed25519 unforgeable; the root key is honest. A2 BLAKE2b
collision-resistant; the 4096-bit sum is k-sum hard. A3 Some root device
refreshes the roster within each horizon (writes degrade to ceiling ties
otherwise; convergence unaffected). A4′ For tombstone expiry only: every
`DEL` reaches every member within `del_ttl` of `d.t`. A5 Writers persist
`seq_self` (violations are detected). A6 Every session joins the grow-only
registers `(maxceil, W, roots_ever)` in its HELLO (a protocol obligation,
checkable per session). **No clock assumption for convergence.**

## 10. What is open

1. **Lean model of this design.** Written: `formal/lean/Kome/Frontier.lean`
   states and proves T1, T2, T2', T3, T4 (with GC and admission), T4', T5,
   T8, T9, T12 and part of T13 over finite lists, with `maxceil` as a stored
   max-register. T3 is derived from a general "sandwich" lemma (a subset that
   still contains the frontier has the same frontier), which also yields the
   GC-under-admission half of T4. **Machine-checked** under Lean 4.35.0
   (`formal/lean/build.sh`), no `sorry`, standard axioms only. T7 remains.
   Round-two deltas not yet in the model: the `W` register as a second
   component of `State` (same shape as `ceil`); per-signer roster
   domination and `roots_ever` (module J); and one alignment, noted by the
   math judge: the model *holds* inadmissible records and filters them out
   of the view, while this document discards them and relies on re-offer.
   Both converge; the model should discard, since holding them is unbounded.
2. **Toolchain.** Lean comes from nixpkgs (`nix shell nixpkgs#lean4`), since
   `elan` could not be downloaded in the authoring environment; `lean-toolchain`
   names 4.35.0 for anyone using `elan`.
3. **The accumulator.** monocypher has no BLAKE2b XOF; `acc(e)` is sixteen
   independent BLAKE2b-256 calls with a counter, and 4096-bit addition is a
   64-limb loop. Both trivial in SPARK; the prefix-sum index needs its own
   bounded structure.
4. **Session ordering.** Rosters should be shipped before data in a session
   (they sort first) so that a stale-ceiling peer admits as much as possible
   in one pass; correctness does not depend on it.
5. **Conflict visibility.** This design keeps one value per cell and frees
   losers' bytes. Round two wrote the alternative out in full as candidate G
   (per-author store, parents resolved in the view) and rejected it for
   records (§1.1); its sibling view is F's `MVREG` type plus parent hashes,
   so an application that wants visible conflicts gets them through the F
   extension rather than a different lattice.
6. **Quotas.** Floods by an authorized writer are bounded only by revocation
   and owner `DEL`s. A per-author byte quota in the roster is a view-level
   addition that would not touch the lattice.
7. **The C ABI.** The implementer judge estimates about 70% of the current
   `sync_engine.h` keeps its shape (`set/get/delete/exists/scan/session_*`);
   `grant/revoke/capability_*` become roster and revoke operations;
   `sync_engine_digest` keeps its contract and gains the "digest equals
   fingerprint" guarantee.
8. **Phase 2: typed fields.** Candidate F is specified and composes; build
   it after `W` is in the model and T7 is proved, when an application asks
   for engine-side counters or sets. Estimated at about 7.5 person-weeks over
   the core by the implementer judge.
9. **Module I sizing.** The sketch cap (1 000 cells) is set by the current
   maximum message length; raising the message bound raises the cap. Below
   the cap the common sync is two round trips; above it the range protocol
   runs as before.

Effort, per the implementer judge's estimates across both rounds: roughly
24 person-weeks for the Lean theorems plus the SPARK core, about 3.5 more
for module I outside the trusted core, about 3 for module J, and about 7.5
for the F extension when it is built; T7 is the long pole throughout.
