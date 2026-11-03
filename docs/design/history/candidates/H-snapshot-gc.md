# Candidate H: root-signed snapshots replace tombstone expiry (+ I: one-round set difference, + J: trust-axis hardening)

Angle: *"Delete the clock from the drop rule."* DESIGN.md's only non-pure
clause is tombstone expiry (`now_local ≥ d.t + del_ttl`), which needs the
liveness assumption A4 and leaves the straggler-resurrection residual. H
replaces it with a root-signed, chunked, self-contained `SNAP` record that
*dominates* old tombstones and dead values inside the lattice, so GC is
`dom(x, F)` and nothing else. I and J are orthogonal modules on the same
store. Everything not restated below is **unchanged from DESIGN.md**.

## 1. Summary

- **H.** The root periodically signs `SNAP(ns, range [ent_lo, ent_hi], w,
  lvl[])`: a per-entity *kill level* in `t`. Every `PUT`/`DEL` on an entity
  in the range with `t < lvl` is dominated by the SNAP. Unlisted entities get
  level `w` (the watermark); listed ones carry an explicit level (22 bytes
  each, ≤ 2 900 per 64 KiB chunk). Each chunk is self-contained.
- SNAP-over-SNAP domination is **kill-set inclusion** (`s' ⊒ s`, a merge-walk
  over two sorted lists), not `(gen_s, h)`. Upward closure (T2') is then a
  theorem, not an obligation on the root; a backup-restored root is harmless
  by construction (§3).
- The drop rule becomes `dom(x, F)` alone. `del_ttl`, `now_local` and A4
  disappear. **No resurrection, ever** (T11'): a straggler's stale `PUT`
  below an absorbed `DEL` is dominated on arrival at every replica holding
  the SNAP, whether or not that replica ever held the `DEL`.
- The price: a straggler's *own* unsynced writes below the watermark on
  entities nobody else kept are dominated too; they are reported
  (`SNAP_DOMINATED`), not silently applied. The root must be live to free
  tombstones (A3, already assumed). A root key becomes a one-record wipe.
- **I.** The first reconciliation round is an IBLT set-difference sketch
  over element hashes: bytes ∝ difference, one round trip in the common
  case, 16-way split on decode failure. Hashing and XOR only; adds nothing
  to the trusted core.
- **J.** Up to four root keys; rosters chain by `prev_h`; any root signs
  rosters, `REVOKE`s and `SNAP`s; a root is revoked by another root; roster
  domination is per signer; the effective roster is a view. Per-field
  writer sets live in the roster and are enforced in the *view* (`unauth`),
  so admission stays monotone. `maxceil` and a grow-only `roots_ever` set are
  the only non-frontier state.

## 2. Data model

**Identifiers, versions, PUT, DEL, well-formedness:** unchanged from
DESIGN.md §2.

**New record (H).**

```
SNAP    ns[16] signer[32] salt[16] gen_s:u48 ent_lo[16] ent_hi[16] w:u48
        n_lvl:u16 (≤ 2 900) lvl[n] { ent[16] floor:u48 }
```

Signed by `signer`. Well-formed iff bounds hold, the signature verifies,
`ent_lo ≤ ent_hi`, and `lvl[]` is strictly increasing in `ent` with every
`ent ∈ [ent_lo, ent_hi]`. A function of the bytes alone. `floor = 0` and
`w = 0` are ordinary values (a level of 0 kills nothing). Size: 112 B header
+ 22 B per entry; 2 900 entries = 63 912 B < 64 KiB. Without J, `signer` is
`root_pk` and `ns = BLAKE2b-256(signer ‖ salt)[0:16]` is checked as for
`ROSTER`; with J see §5.

**Kill level.** For `ent ∈ [s.ent_lo, s.ent_hi]`:

```
lvl_s(ent) := floor   if (ent, floor) ∈ s.lvl
            := s.w    otherwise
```

A SNAP asserts, per entity in its range, "every record with `t < lvl_s(ent)`
is dead". Entities the root knows nothing about get `w`; live entities get a
level at or below their oldest live cell; recently deleted entities whose
previous level exceeded `w` keep it explicitly (§6 gives the construction).
The task's `live[]` of 16-byte ids is this list without `floor`; §9 (T2')
shows why the floor is necessary.

**Changed records (J).** `del_ttl` is removed; `root_pk` becomes `signer`;
rosters gain a root set, a chain hash and field rules; `REVOKE` gains
`from_gen`:

```
ROSTER  ns[16] signer[32] salt[16] prev_h[32] gen:u48 ceiling_t:u48 epoch:u16
        n_roots:u8 (≤4)   roots[n]   { root_pk[32] }
        n_members:u8 (≤64) members[n] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
        n_rules:u8 (≤32)  rules[n]   { plen:u8 prefix[plen ≤ 32] writers:u64 }
REVOKE  ns[16] signer[32] salt[16] subject[32] from_t:u48 from_gen:u48 rev_seq:u48
```

`writers` is a bitmap over the *same record's* `members[]`, so a rule is
self-contained. A roster's well-formedness is still a function of its bytes
(signature under `signer`); whether `signer` is a root is an *admission*
question (§5), monotone like the ceiling.

**Domination.** The two PUT clauses, the DEL clause and `REVOKE` are
unchanged from DESIGN.md §3; the following are added or replaced:

```
dom(p, H) for PUT p   += ∃ s ∈ H : SNAP, s.ns = p.ns, ent(p) ∈ range(s), p.t < lvl_s(ent(p))
dom(d, H) for DEL d   += ∃ s ∈ H : SNAP, s.ns = d.ns, ent(d) ∈ range(s), d.t < lvl_s(ent(d))
dom(s, H) for SNAP s  := ∃ s' ∈ H : SNAP, s'.ns = s.ns, range(s') ⊇ range(s), s' ⊒ s,
                         ¬(s ⊒ s') ∨ (s'.gen_s, s'.h) > (s.gen_s, s.h)
dom(r, H) for ROSTER  := ∃ r' ∈ H : ROSTER, same ns, r'.signer = r.signer, (r'.gen, r'.h) > (r.gen, r.h)   -- (J)

s' ⊒ s  ("s' covers s")  :=  range(s') ⊇ range(s) ∧ s'.w ≥ s.w ∧ ∀ ent ∈ range(s) : lvl_s'(ent) ≥ lvl_s(ent)
```

`⊒` is decided by one merge-walk over the two sorted `lvl[]` lists: for each
`ent` listed in either, compare the two levels (an unlisted side contributes
its `w`); for all other entities the check is `s'.w ≥ s.w`. O(n + n'), no
range enumeration. Note that `t` alone decides SNAP domination (never
`author`, `seq`, `h`): the kill set is a `t`-prefix per entity, and whatever
a `t`-prefix cannot express stays as an explicit `DEL` in `F` (§6).

`F(H)`, views `cell`, `exists`, `void`: unchanged. Two views change (T5):

```
deleted_t(ns, ent)  := max( deleted_at(ns, ent).t, snap_floor(ns, ent) )          -- Option
snap_floor(ns, ent) := max { lvl_s(ent) | s ∈ F : SNAP, ent ∈ range(s) }            -- 0 if none
unauth(p)           := ¬ permitted(p, ROSTER_eff)                                    -- (J), §5
```

**Example** (`v` written `(t, author, seq)`; one chunk covering all of `ns`).

```
PUT(E, name, "Ada")  v=(1000, A, 7)
DEL(E)               v=(2000, B, 3)         -> F = {DEL@2000}
SNAP  w=5000, lvl=[]                        -> DEL dominated (2000 < 5000). F = {SNAP}
PUT(E, name, "Ada")  v=(1000, A, 7)         -> straggler re-offers it: 1000 < 5000, dominated. F = {SNAP}
PUT(E, name, "Ada2") v=(6000, A, 9)         -> 6000 ≥ 5000: F = {SNAP, PUT@6000}; E exists again (re-creation)
SNAP' w=9000, lvl=[(E, 5000)]               -> SNAP' ⊒ SNAP (5000 ≥ 5000 on E, 9000 ≥ 5000 elsewhere); SNAP dropped.
                                               PUT@6000 survives (6000 ≥ 5000).  F = {SNAP', PUT@6000}
```

Any permutation with duplicates yields the same `F`; a replica that never
held the `DEL` reaches it from the `SNAP` alone.

## 3. Clock and identity

**Emission** gains one term so a writer never emits under a level it holds:

```
t_emit := max( now_ms, floor.t + 1 if floor exists, snap_floor(ns, ent) );  if t_emit > maxceil then t_emit := maxceil
```

Everything else in DESIGN.md §5 is unchanged. Since the root sets
`w = now_root − snap_lag` (default 180 days), a clock-bearing writer never
chases a SNAP; a device with `now = 0` chases to the level, which is the
intended Lamport behaviour.

**H8 under H.** Rows for clock skew, cloned key and malicious member are
unchanged. Two rows change:

| Case | Effect | Bound |
|---|---|---|
| Backup restore / straggler (member offline > `snap_lag` with unsynced writes) | Its held records below the arriving SNAP's level are dominated. Others' records: correct (they were deleted or superseded). Its *own* `PUT`s on entities the root did not list: dominated and reported as `SNAP_DOMINATED(ent, field, value)` | the straggler's own sub-watermark writes; the app may re-`PUT`, which chases above the level (an explicit, attributed re-creation) |
| Root restored from backup (holds an old SNAP or none) | Issues `s_r` with levels computed from its own `F`. If some held `s` covers `s_r`, `s_r` is dominated on arrival; if neither covers the other, both stay in `F` and both kill. Kill sets only grow, so no record wrongly returns | at most one extra chunk per range until the next root SNAP covers both; convergence unaffected (T3 needs no root obligation) |

Why covering instead of `(gen_s, h)` matters here: under `(gen_s, h)`, a
restored root's lower-level SNAP with a winning `h` would *drop* a higher
SNAP, and records the latter had already killed on some replicas would be
live on others: the math judge's A-counterexample 1 in SNAP form. Under
`⊒`, a SNAP is dropped only by one that kills at least as much.

**New root power (honest statement).** `SNAP(range = all, w = 2^48−1, lvl =
[])` kills every data record in the collection, on every replica, with
bytes freed on arrival. DESIGN.md's root could do the same only through a
roster change plus a member device issuing `DEL`s; H makes it one record.
The root is honest by A1; a *stolen* root key is now a wipe, and §8 says
what that costs.

## 4. Reconciliation and digest (module I)

Elements, keys, accumulator, `fp`, `digest`, transports: unchanged from
DESIGN.md §8, except `kind` order becomes `ROSTER = 0, REVOKE = 1, SNAP = 2,
DEL = 3, PUT = 4`, so SNAPs ship before the data they dominate and a receiver
can drop dominated incoming data before verifying it (verify-on-win). A
SNAP's key is `kind ‖ ent_lo ‖ ent_hi (as field) ‖ h`.

**One-round set difference.** Round 0 is replaced:

```
A → B : HELLO  |F_A|, fp(F_A)
B → A : SKETCH c, IBLT_c(F_B)                        if fp differs; c = cap(|F_A|, |F_B|)
A     : D := IBLT_c(F_B) − IBLT_c(F_A); decode(D) → (only_B, only_A)  or FAIL
A → B : WANT only_B ; ELEMS only_A                   on success → B replies ELEMS, then the HAVE round as today
A → B : SPLIT [lo, hi]×16                            on FAIL  → DESIGN.md §8 protocol from round 1
```

The sketch element is `h(e)` (32 bytes, unique per record). One BLAKE2b-256
per element, `BLAKE2b-256("kome/iblt" ‖ h)`, yields three 32-bit index seeds
and a 64-bit `check`; cached per element (20 bytes). A cell is `(count:i32,
key_xor[32], check_xor[8])` = 44 bytes; `cap(a, b) := clamp(2·|a − b| + 32,
32, 4 096)` cells, so a sketch is 1.4–180 KiB and decodes any difference up to
about `cap/1.3` with failure probability under 1 % (k = 3, standard IBLT
behaviour). IBLTs are homomorphic, so each side keeps `IBLT_{32}`, `IBLT_{512}`
and `IBLT_{4096}` incrementally (≈ 200 KiB) and sketches in O(1) per
session; DESIGN.md's snapshot cache survives.

**Bound.** Common case: two round trips before the HAVE round, `44·cap +
Δ` bytes; the fallback preserves T7's `⌈log₁₆ N⌉ + 2` worst case plus one
round. The difference estimate is only a hint: an underestimate is a decode
failure, caught by the `check_xor` with error probability 2^-64 per cell, and
*any* decoded id that no side holds (or a final `fp` mismatch) also falls
back. The sketch therefore changes no state and is outside the trusted core:
T7's correctness clause ("both hold `F(F_A ∪ F_B)`") rests on the HAVE round
and the fallback, exactly as today. A malicious peer can force a 180 KiB
sketch and a fallback per session: bounded cost, no state effect.

**Minisketch (BCH) as the alternative.** `8·c` bytes for capacity `c` (ten
times smaller), certain decode up to `c`, but it sketches 64-bit ids (a
truncation of `h`, 10^-10 collision mass at 10^5 elements, also caught by the
fallback) and needs GF(2^64) multiplication, Berlekamp–Massey and root
finding: ≈ 1 500 lines of bounded-loop SPARK with no proof content beyond
array bounds, and O(c²) field operations per decode. IBLT needs hashing and
XOR only, so it fits monocypher-only and is the default; Minisketch is a
drop-in for transports where bytes matter more than code size (BLE).

## 5. Authorization, encryption, revocation (module J)

Epoch keys, the hash chain, transport gates, bundles, `void` and `from_t`:
unchanged from DESIGN.md §6.

**Roots.** State gains a per-collection grow-only set `roots_ever` (≤ 256
keys; beyond that the collection is re-founded), initialised to the founding
key: the one `pk` with `BLAKE2b-256(pk ‖ salt)[0:16] = ns`. A `ROSTER`,
`REVOKE` or `SNAP` is **admitted** iff `signer ∈ roots_ever ∨ signer
self-certifies ns`; applying an admitted `ROSTER` does `roots_ever ∪=
r.roots`. This is monotone in the held history exactly as `maxceil` is
(T4'): once admissible, always admissible; an inadmissible record is not
held and is re-offered by the peer that holds it. Replica state is
`(F, maxceil, roots_ever)`; join is `(F(F₁ ∪ F₂), max(c₁, c₂), R₁ ∪ R₂)`.

**Why per-signer roster domination.** Each root key has its own chain:
`F` holds the latest roster of every root that ever issued one (≤ 256, in
practice ≤ 4). The effective roster is a view:

```
root_void(r)  := ∃ REVOKE(subject = r.signer, from_gen) ∈ F : r.gen ≥ from_gen
ROSTER_eff    := argmax (gen, h) { r ∈ F : ROSTER, ¬ root_void(r) }
```

If roster domination stayed global `(gen, h)`, a revoked root's roster at
`gen = 2^48 − 1` would dominate and *drop* every honest roster forever, and
voiding it afterwards would leave replicas that saw it first with no roster
and the others with the honest one: the §6 argument against dropping on
revocation, in roster form. Per-signer chains keep the honest roster in `F`;
the view ignores the revoked chain from `from_gen` on. A revoked root's
rosters before `from_gen` stand (they may be `ROSTER_eff` until an honest
root issues the next generation). `prev_h` is the chain: a root device that
finds `ROSTER_eff.h ≠ prev_h` of the roster it is about to issue knows it
raced and re-issues at `gen + 1` on top of `ROSTER_eff`.

**Two roots, equal gen.** Both rosters are in `F` (different signers);
`ROSTER_eff` picks by `(gen, h)`, the baseline rule. The loser's additions
are not lost: its device re-issues them at `gen + 1`; its removals are
`REVOKE`s, grow-only, so the attacker judge's A-4 cannot recur. Two gen-`g`
rosters wrap two epoch-`g` keys; holders of the loser cannot open bundles
sealed under the winner until the next roster: a delay, not a divergence.

**Rotation and loss.** Losing a root device is recoverable iff `n_roots ≥ 2`
beforehand (the second key may be an offline paper key): a surviving root
issues `REVOKE(lost, from_gen = gen + 1, from_t)` and a roster with
`roots' = roots \ {lost} ∪ {new}`. With one root key, loss still means
re-founding, as in DESIGN.md.

**Ceiling with multiple roots.** `maxceil := max ceiling_t` over every
*admitted* roster, any signer, dominated or not: commutative, so concurrent
raises and backup-restored roots are harmless (T4'). The cost is in §8: a
revoked root's raise is permanent.

**Per-field writer sets, in the view.**

```
permitted(p, r) := p.author ∈ r.members ∧ ∀ rule ∈ r.rules : prefix(rule) ≤ p.field ⇒ writers(rule)[idx_r(p.author)] = 1
unauth(p)       := ¬ permitted(p, ROSTER_eff)
```

A field no rule matches is writable by every member (that is the
definition, not a default-by-absence). `unauth` is a flag like `void`: the
PUT stays in `F`, keeps dominating, reads as "cleared, flagged: unauthorised
field write by X"; an honest writer's next write chases above it.

**Why not at admission.** Suppose unauthorised PUTs were refused on arrival.
Replica A holds roster gen 5 (W may write `f`), admits `p = PUT(E, f)` by W,
which dominates and frees honest `q`. Replica B holds gen 6 (W may not),
refuses `p`, keeps `q`. After both hold gen 6, A has `{p}` on the cell, B has
`{q}`; B refuses `p` on every exchange; A cannot un-free `q`. Same records,
different frontiers, repaired by nothing. This is the math judge's
counterexample 2 against D (`valid` depending on held caps) with the roster
in the role of the cap, and lesson row 7 of REQUIREMENTS.md. Grants and
revocations of a field move in both directions, so no max-register makes
this admission monotone; the view is the only monotone place.

## 6. Storage and GC

Layout, index, compaction: unchanged from DESIGN.md §7.

**Drop rule.** A frame is dropped iff `dom(x, F)`. Nothing else. No clock
reading anywhere in the state machine.

**Root SNAP construction** (policy on root devices; T15 proves it sound).
The root keeps a binary trie of ranges over the 128-bit entity space,
starting from one range. For a range `R` due for a snapshot, from its own
frontier `F_R` and the SNAP `s₀` it holds on `R` (levels `lvl₀`, or 0 if
none):

```
w       := max( s₀.w, now_root − snap_lag )
for ent ∈ R with exists(ent) ∨ lvl₀(ent) > w ∨ (∃ DEL d ∈ F_R on ent ∧ d.t ≥ w):
    base := if ∃ d = deleted_at(ent) ∧ exists(ent) then min(d.t + 1, min { q.t | q ∈ F_R, PUT on ent })
            else if ¬ exists(ent) then w  else 0
    emit (ent, max(base, lvl₀(ent)))
```

Every other entity gets `w` implicitly. The `min(d.t + 1, …)` term absorbs
the tombstone of a re-created entity unless a live cell ties it at the same
millisecond, in which case the `DEL` stays in `F` until the tie is broken
(one 141 B frame per such entity, at most one per live entity). The
`lvl₀` term makes the new SNAP cover the old one (T16), so the old one is
dropped on every replica. A range is split (two children, each half) when its
entry count would exceed 2 900; the parent SNAP is then covered by neither
child and persists: orphans are the internal nodes of the trie, fewer than
the leaves, and each is a correct, harmless kill set. Ranges with no
absorbable `DEL` since their last SNAP are not re-issued, so SNAP traffic
is proportional to deletion churn per range, not to the collection.

**A replica lacking a chunk** holds the baseline state for that range:
tombstones and dead values stay until the chunk arrives, then are dropped by
`dom`. Nothing diverges; nothing waits.

**Bounds.** `|F(ns)| ≤ live cells + DELs on entities with no covering SNAP
level above them (≤ 1 per entity deleted since its range's last SNAP, plus
≤ 1 per re-created entity with a same-millisecond tie) + SNAP frames (< 2 ×
leaf ranges, each ≤ 64 KiB) + rosters (≤ 1 per root key ever) + revocations
(≤ 1 024)`. SNAP traffic per generation of a range: 112 B + 22 B per listed
entity; 10^5 live entities fully re-snapshotted = 2.2 MiB, against 141 B per
tombstone otherwise carried for `del_ttl`.

## 7. Assumptions

- A1 Ed25519 unforgeable; **every key in `roots_ever` is honest** (a stolen
  root key is the owner, and §8 says what it can do).
- A2 BLAKE2b collision-resistant; the 4 096-bit sum is k-sum hard.
- A3 Some root device refreshes rosters and snapshots ranges within each
  horizon. Without it, writes degrade to ceiling ties and tombstones
  accumulate (bounded by the number of deletions); convergence unaffected.
- A5 Writers persist `seq_self` (violations detected).
- **A4 is removed.** No clock enters any safety theorem; `snap_lag` affects
  only which straggler writes are reported rather than applied.
- A6 (I) IBLT decoding is a hint; correctness never rests on it.

## 8. Known weaknesses

- **A root key is a one-record wipe.** `SNAP(all, 2^48 − 1, [])` frees every
  value on every replica on arrival, and SNAP domination cannot be voided
  (the §6 argument). DESIGN.md's root could only wipe through a member
  device. Mitigation outside this document: require `⌈n_roots/2⌉`
  countersignatures on a SNAP when `n_roots ≥ 2` (checkable from bytes).
- **A revoked root's SNAPs keep killing** and its ceiling raises are
  permanent (`maxceil` is a max-register over admitted rosters). A stolen
  root key that raised `maxceil` to `2^48 − 1` removes the ceiling's
  protection for the collection's life; the remedy is re-founding.
- **Stragglers lose instead of resurrecting.** A member offline longer than
  `snap_lag` finds its unsynced writes below the watermark dominated when the
  entity was not listed; the engine reports them and the app must re-write.
  This is the mirror image of DESIGN.md's zombie, chosen because the
  reporting device is the one that holds the data.
- **SNAP traffic is proportional to live entities**, not to deletions, for
  any range that is re-issued; a collection that deletes rarely pays more
  than it did with `del_ttl`. Orphan chunks after splits persist forever.
- **Per-field rules are flags, not walls.** An unauthorised member write
  still dominates and frees the honest value; protection against a member
  is social, as it is for `void`.
- **The SNAP is 64 KiB** and needs the same fragmentation path the 48 KiB
  roster already needs on BLE/UDP; the `⊒` check is O(n + n') per pair.
- **Entities the root never saw** below `w` die when their range is
  snapshotted; a writer whose creations never reached the root within
  `snap_lag` is the straggler case above.

## 9. Proof obligations

Unchanged and already machine-checked in `Frontier.lean`: **T1**, **T2**,
**T3** (via `F_sandwich`, which needs only T2' and irreflexivity), **T4**
(`applyAllA_view`, with `adm` generalised to the pair `(maxceil,
roots_ever)` — same `adm_mono` shape), **T4'**, **T9**, **T10**, **T13**
(emission arithmetic). T6, T14 unchanged on paper.

Restated:

- **T2' (upward closure), restated.** `dominates` gains the SNAP cases. The
  cases to check, all finite: (i) `s dom d`, `d dom p` ⇒ `p.v < d.v` ⇒ `p.t
  ≤ d.t < lvl_s` ⇒ `s dom p`. (ii) `s dom p`, `p dom p'` ⇒ `p'.t ≤ p.t` ⇒
  `s dom p'`. (iii) `s' dom s`, `s dom x` ⇒ `x.t < lvl_s ≤ lvl_s'` ⇒ `s' dom
  x`. (iv) `s'' dom s' dom s`: `⊒` is transitive; if `s ⊒ s''` then all three
  ranges coincide and cover mutually, so the `(gen_s, h)` tie-breaks chain.
  Nothing dominates a `REVOKE`; a data record never dominates a SNAP.
  **Counterexample to the 16-byte variant** (why `floor` exists): `d =
  DEL(E)@2`, `p₂ = PUT(E)@20` re-creates `E`; `s` (`w = 10`, `E` dead) kills
  `d`; `s'` (`w = 30`, `E` listed live without a level) must not kill `p₂`,
  so it cannot kill `d` either, yet `s' dom s dom d`: T2' fails, and a
  replica that dropped `d` under `s` and one that never saw `s` end with
  different `F`. With `floor(E) = 10` in `s'`, `d` (2 < 10) is killed and
  `p₂` (20 ≥ 10) survives.
- **T5, restated.** `deleted_t`, `snap_floor`, `ROSTER_eff`, `root_void`,
  `unauth` are functions of `F` alone.
- **T8, restated.** If `max(floor.t, snap_floor − 1) < maxceil` then
  `v_emit > floor` and `v_emit.t ≥ snap_floor`; always `v_emit.t ≤ maxceil`.
- **T11' (no resurrection), replaces T11.** If `s ∈ F_X` and `x` is a data
  record on `ent ∈ range(s)` with `x.t < lvl_s(ent)`, then `x ∉ F_X`, and for
  every state `X'` reachable from `X` by applying any records, `x ∉ F_{X'}`
  (a SNAP leaves `F` only for one that covers it; T2 + T2'). Corollary: for
  a `DEL d` with `d.t < lvl_s(ent)`, every `PUT p` with `p.v < d.v` is absent
  from every replica holding `s` or a successor, held or not held `d`. No
  liveness, no clock. Core-Lean, ≈ 1 week on top of the restated T2'.
- **T12, restated.** Applying a `ROSTER`, `REVOKE` or `SNAP` never adds a
  `PUT` or `DEL`; a `SNAP` removes only records in its range with `t < lvl`;
  `void`, `root_void`, `unauth` are monotone in `F` for fixed `ROSTER_eff`
  (`unauth` is *not* monotone across roster generations: that is why it is a
  view).
- **T13, extended.** SNAP and roster layouts; `gen_s`, `from_gen` never wrap.

New:

- **T15 (SNAP soundness).** For `s` built by §6 from `F_R`: every `PUT p ∈
  F_R` on `ent ∈ range(s)` has `p.t ≥ lvl_s(ent)`, so the root never kills a
  cell it shows. (Live: `base ≤ min live t`, and `lvl₀ ≤ p.t` because `p` is
  not dominated by `s₀ ∈ F_R`. Dead: vacuous.)
- **T16 (SNAP covering).** The §6 construction yields `s ⊒ s₀` whenever `s₀`
  is held, so the previous SNAP of the range is dropped everywhere.
- **T17 (admission with roots).** `adm(r, c, R)` is monotone in `(c, R)`;
  `roots_ever` and `maxceil` only grow under any sequence of records,
  including rosters from revoked or restored roots.
- **T18 (effective roster).** `ROSTER_eff` is well-defined (total order on
  `(gen, h)`), ignores exactly the rosters `root_void` names, and is in `F`
  (per-signer domination keeps every signer's maximum).
- **T7, restated (I).** The sketch phase terminates in ≤ 2 rounds and either
  yields `only_A, only_B` whose exchange gives `F(F_A ∪ F_B)` under A2, or
  falls back; the fallback is DESIGN.md's T7. Still the long pole (✗).

Lean status: T1, T2, T3, T4, T4', T9, T10 survive verbatim as list theorems
(the `Record` type gains `snap` and `dominates` gains four arms; `F_sandwich`
and `exists_max_dominator` are unchanged once `dominates_trans` is
re-proved); T2' must be re-proved with `lvl` modelled as a finite
association list and `⊒` as its decidable merge-walk, plus a lemma that the
walk decides the pointwise statement; T5, T8, T11', T12, T15–T18 are new
statements over the same finite lists. T7 is unchanged in difficulty.

## 10. Self-score

- **C1 = 5.** Convergence rests on A1, A2 and nothing else: no clock, no
  liveness, no membership in any safety theorem; A4 is gone and T11' is a
  finite statement about held records.
- **C2 = 3.** Member blast radius unchanged (pins end at refresh,
  overwrites stand flagged); a stolen root key is now a one-record wipe and
  a permanent ceiling raise, recoverable only by re-founding.
- **C3 = 4.** 76 B per cell unchanged; tombstones become 22 B levels or
  nothing; GC is `dom` alone; SNAP traffic ∝ live entities per re-issued
  range and orphan chunks persist.
- **C4 = 4.** Two round trips and bytes ∝ difference in the common case
  with a cacheable homomorphic sketch; fallback keeps the log bound; 64 KiB
  SNAP elements need fragmentation; relays unchanged (blind).
- **C5 = 3.** Unchanged from DESIGN.md (epoch cut-off, current-epoch bundles,
  `from_t`); root loss recoverable with a second key; per-field rules do not
  restrict a member cryptographically.
- **C6 = 4.** Trusted core: `<`, `dom` (now five arms and a merge-walk), `F`,
  `fp`, emission, two max-registers, four view predicates; the clock clause
  is gone; I adds nothing; the restated T2' is the one heavier Lean proof.
- **C7 = 4.** IBLT is hashing and XOR; the SNAP builder runs only on root
  devices; rosters grow by ≤ 1.3 KiB; 200 KiB of resident sketches is the
  one new footprint item.
- **C8 = 3.** As DESIGN.md plus two statuses (`SNAP_DOMINATED`, `unauth`);
  the app must handle "your old offline writes were not applied"; field
  rules are expressible without a new write path.
- **C9 = 4.** No `now_local` in state; `floor = 0`, `w = 0` ordinary;
  unlisted entities map to `w` by definition; bounds are decode refusals;
  the residual derivations are `exists`, `ROSTER_eff` and "unlisted ⇒ w",
  all views.
