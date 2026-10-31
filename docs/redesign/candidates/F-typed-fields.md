# Candidate F: typed lattice fields over the frontier store

## 1. Summary

- Keep DESIGN.md's frontier store whole: one strict total order on records, `F(H)` as the state, monotone ceiling admission, `void` as a view, apply-then-expire tombstones, the 4096-bit accumulator. Nothing in §4–§8 of DESIGN.md changes except where this document says so.
- Every `PUT` carries a **type tag** `ftype : u8 ∈ {0 LWW, 1 GSET, 2 PNCOUNTER, 3 MVREG, 4 MAXREG}`. The tag is part of the **cell key**: `cell(p) = (ns, ent, field, ftype)`. A type can never be "changed"; a different tag is a different cell.
- A `PUT` on a typed cell carries the **author's full state** for that cell (its own `(inc, dec)` totals, its own added elements, its current value), signed under its own `seq`.
- Domination becomes **per `(cell, author)`** for the four non-LWW types: a `PUT` dominates an earlier `PUT` of the *same author* on the *same cell* by the full version `v`; a `DEL` of the entity dominates every `PUT` on it, all authors, all types. LWW cells keep cross-author domination, so DESIGN.md is literally the `ftype = 0` special case.
- The cell's value is a **view**: a fold of a commutative monoid over the surviving, non-void per-author records (max by `v`, union, sum, set, max). The lattice never looks inside a value; the view never changes `F`.
- `F` holds at most one record per `(cell, author)`: ≤ 64 live-member records per typed cell, plus void records of revoked authors until the owner `DEL`s the entity.
- T1–T4, T4', T6, T7, T9, T11, T14 survive verbatim; T2', T5, T8, T10, T12, T13 are restated. The Lean file's generic core (`F_sandwich`, `frontier_hom`, `convergence`) is untouched; only `Record`, `dominates`, its two lemmas and `cell_unique` change.
- The full version `v` for same-author domination is **forced**, not chosen: any same-author order that is not a sub-order of `v` breaks T2' against `DEL` (§2, counterexample).
- A writer's `PUT` never dominates another author's typed record, so a far-future or malicious writer cannot pin a typed cell; `SHADOWED` on typed cells survives only against a `DEL` at the ceiling.
- Where it gives ground: monotonicity of GSET/PNCOUNTER/MAXREG is an honest-writer property, not a lattice property; a `DEL` resets counters, and a resurrecting writer that never saw the `DEL` carries its whole historic total; typed cells cost O(authors) records instead of one.

## 2. Data model

**Identifiers, versions, hashing, signing.** Unchanged from DESIGN.md §2. `v = (t, author, seq, h)`, lexicographic, total by `h`.

**Records.** `DEL`, `ROSTER`, `REVOKE` unchanged from DESIGN.md §2. `PUT` gains one byte:

```
PUT  ns[16] ent[16] flen:u8 field[flen] ftype:u8 t:u48 seq:u48 author[32] vlen:u16 value[vlen]
```

**Well-formedness** is still a function of the bytes alone. It now also requires `ftype ≤ 4` (a bounded enumeration, no reserved value) and a value layout that matches the tag:

| `ftype` | value layout | bound | author's state means |
|---|---|---|---|
| 0 LWW | any bytes | `vlen ≤ 65 535` | the value |
| 1 GSET | `n:u16 ‖ n × (len:u8 ‖ elem[len])`, elements distinct and sorted bytewise | `vlen ≤ 65 535`, `len ≤ 255` | the set of elements this author has added |
| 2 PNCOUNTER | `inc:u48le ‖ dec:u48le` | `vlen = 12` | this author's lifetime increments and decrements |
| 3 MVREG | any bytes | `vlen ≤ 65 535` | this author's current value |
| 4 MAXREG | `m:u64le` | `vlen = 8` | the largest value this author has written |

GSET canonicality (sorted, distinct) exists so that equal sets hash equally; an unsorted encoding is ill-formed, not a different set. `inc = dec = 0` is an ordinary state, not a sentinel: "this author has added nothing".

**Cells.** `cell(p) := (ns, ent, field, ftype)` for a `PUT`; `(ns, ent)` for a `DEL`; `ns` for a `ROSTER`. Two `PUT`s on one field name with different tags are on **different cells**: they never dominate each other and never share a view. That is the deterministic rule for "conflicting types": no conflict in the lattice, possibly two cells under one name, which the views expose rather than resolve. The alternative, LWW over tags with cross-type domination by `v`, was rejected because one schema-drifted writer could then erase every other author's counter state with a single `PUT`.

**Domination.** The only definition in the lattice that changes:

```
dom(p, H) for PUT p  :=  ∃ q ∈ H : PUT, cell(q) = cell(p), q.v > p.v,
                              (p.ftype = LWW  ∨  q.author = p.author)          -- (D1)
                       ∨ ∃ d ∈ H : DEL, entity(d) = entity(p), d.v > p.v         -- (D2)
dom(d, H) for DEL, dom(r, H) for ROSTER, dom(x, H) for REVOKE :  unchanged from DESIGN.md §3
F(H) := { x ∈ H | ¬ dom(x, H) }
```

For `ftype = 0` this is DESIGN.md §3 verbatim. For the other four, a `PUT` is dominated only by its own author's later `PUT` on the same cell or by a `DEL` of the entity. Since `author` is a component of `v` and equal in (D1), same-author comparison reduces to `(t, seq, h)`.

**Why the full version and not `(seq, h)`.** An author's `seq` is monotone, so `(seq, h)` looks like the natural same-author order and would free the chase from `t`. It breaks T2'. Take author `A` with a clock that went backwards and a `DEL` by `B`:

```
x : PUT  (E, f, PNCOUNTER)  v = (t=100, A, seq=1)
y : PUT  (E, f, PNCOUNTER)  v = (t=50,  A, seq=2)
z : DEL   E                 v = (t=70,  B, seq=1)
```

Under `(seq, h)`: `y dom x`; under `v`: `z dom y` (70 > 50) but `¬ z dom x` (70 < 100). Replica `P` applies `x, y, z`: `x` dropped by `y`, `y` dropped by `z`, `F_P = {z}`; `y` is gone and never sent again. Replica `Q` applies `x, z`: `F_Q = {x, z}`. Reconciliation: `Q` offers `x`, nothing at `P` dominates it, `F_P = {x, z}`. Both hold `{x, z}` although `F({x, y, z}) = {z}`: GC changed a future frontier, the upward-closure failure the mathematics judge identified as A's unstated lemma. Any same-author order that disagrees with `v` on some pair admits this trace, because `DEL` must compare by `v`. The same argument rules out MAXREG domination by value order `(m, v)` across authors. So: one order, `v`, everywhere; per-author state is a restriction of `dom`, not a new order.

**T2' for the new `dom`** (`y dom x`, `z dom y` ⇒ `z dom x`): (1) `x, y, z` PUT by (D1): same cell throughout, and either `x.ftype = LWW` or `z.author = y.author = x.author`; `z.v > y.v > x.v`. (2) `x, y` PUT by (D1), `z` DEL by (D2): same entity, `z.v > y.v > x.v`. (3) `x` PUT, `y, z` DEL: same entity, transitive; a PUT never dominates a DEL. (4) `x` DEL or ROSTER: unchanged. (5) `x` REVOKE: never dominated. Author equality is an equivalence and `>` on `v` is transitive, so the conjunction composes. T2 is immediate: (D1)/(D2) are existentials over `H`.

**Views** are pure functions of `F`:

```
deleted_at(ns, ent)      := unchanged from DESIGN.md §3
recs(c)                  := { p ∈ F | PUT, cell(p) = c, ¬ void(p) }        -- ≤ 1 per author (T5)
cell(c) for c.ftype =
   LWW        : value of the unique p ∈ recs(c)                          -- Option
   GSET       : ⋃ { elems(p) | p ∈ recs(c) }
   PNCOUNTER  : Σ p.inc − Σ p.dec  over recs(c)                            -- i64; |·| < 2^55
   MVREG      : { (p.author, p.value) | p ∈ recs(c) }
   MAXREG     : max { p.m | p ∈ recs(c) }                                  -- Option
exists(ns, ent)          := ∃ c on ent. recs(c) ≠ ∅   (LWW: cell(c) ≠ None)
void(p), far(p)          := unchanged from DESIGN.md §3
types(ns, ent, field)    := { c.ftype | c on (ns, ent, field), recs(c) ≠ ∅ }
```

Each join is a fold of a commutative, associative operation over a set, so it is a function of the set (T15). `void` records are excluded from every join: **a revoked author's contribution disappears from the sum, the union, the set and the max** the moment the `REVOKE` is held, deterministically everywhere (`void` is a function of `F`). The void record itself stays in `F`; §5 shows DESIGN.md §6's reason still applies. Sums are bounded by type: ≤ `64 + 1024` authors ever, each `< 2^48`, so `|Σ| < 2^59` fits `i64` with no read-time overflow check.

**Example.** Authors `A`, `B`; cell `c = (E, likes, PNCOUNTER)`; `v` written `(t, author, seq)`.

```
PUT c (inc=1, dec=0)  v=(1000, A, 7)     -> recs(c) = {A:(1,0)}            cell(c) = 1
PUT c (inc=1, dec=0)  v=(1001, B, 2)     -> {A:(1,0), B:(1,0)}             cell(c) = 2
PUT c (inc=3, dec=1)  v=(1500, A, 8)     -> A's old record dominated, dropped; {A:(3,1), B:(1,0)}  = 3
DEL E                 v=(2000, B, 3)     -> both PUTs dominated, dropped.   F|E = {DEL@2000}
PUT c (inc=1, dec=0)  v=(2500, A, 9)     -> A observed the DEL: base is zero. {A:(1,0)}            = 1
```

Any permutation with duplicates yields the same `F` (T3, T4). Compare the LWW example in A §2: the shape is identical, with one record per author instead of one per cell.

## 3. Clock and identity

**Timestamp, ceiling, `seq`, identity, cloning detection.** Unchanged from DESIGN.md §5 and §4.

**Emission on a typed cell** (`ftype ≠ LWW`). The author chases **its own previous record only**:

```
own(c)      := the PUT in F on c with author = self_pk                    -- Option, ≤ 1 by T5
floor_T(c)  := max(own(c).v, deleted_at(ns, ent))                          -- Option
base        := own(c).state if own(c) ≠ None else zero(ftype)
state_new   := PNCOUNTER: (base.inc + n, base.dec + m)   fail COUNTER_EXHAUSTED if either ≥ 2^48
               GSET:      base ∪ elems                   fail GSET_FULL if encoding > 65 535 B, INVALID if an elem > 255 B
               MVREG:     arg
               MAXREG:    max(base, arg)
t_emit, seq_emit, v_emit : as DESIGN.md §5 with floor := floor_T
status      := SHADOWED if floor_T ≠ None ∧ v_emit < floor_T  else OK
```

`own(c) ∈ F` already implies `own(c).v > deleted_at` (else (D2) would have dropped it), so "did I observe the delete" is answered by the frontier: after a `DEL` the author's base is `zero(ftype)`. That is the **re-add rule**: a `DEL` dominates every author's state; an author whose later `PUT` exceeds the `DEL` starts the cell fresh *for that author*. A counter reset on delete is the intended semantics ("delete the entity" means everything about it); carrying totals across a delete would need history.

**No self-shadowing.** Because `author` is equal in (D1), `v_emit` versus `own(c)` reduces to `(t, seq, h)`; `t_emit ≥ own.t` (chase or clamp, and `own.t ≤ maxceil` by T9) and `seq_emit > own.seq` (A5), so `v_emit > own(c).v` always, even at the ceiling. `SHADOWED` on a typed cell arises only from `floor_T = deleted_at` at `t = maxceil` with `pk_self < pk_deleter`: the baseline's ceiling pin, confined to `DEL`s. LWW cells keep DESIGN.md §5 unchanged.

**Equivocation.** Two distinct records with equal `(author, seq)` have distinct `h`, so they are strictly ordered by `v`. On the **same cell** one dominates the other by (D1) and only the maximum is held; on different cells both are held. Every replica holding both flags the author (`CLONE_SUSPECTED`). For a counter, a cloned key's parallel increments are **neither double-counted nor merged**: the record greater by `(t, seq, h)` is the author's state. Determinism over accuracy; the lost delta is bounded by the clone's own writes and visible through the flag.

**H8 for typed cells.** The table in DESIGN.md §5 stands for LWW cells and for `DEL`. On typed cells:

| Case | Effect | Bound |
|---|---|---|
| Clock ahead or behind | None on other authors: its record dominates only its own; a backwards clock is caught by the own-record chase. | none |
| Backup restore | Pre-sync writes start from the restored stale state with a fresh `t`, so they **dominate the author's newer records**: its counter regresses, its set shrinks. Detected on first sync (`seq ≥ seq_self + 1` or equivocation); `seq` jumps. | own contribution since the backup |
| Cloned key | Same-author equivocation; max by `v` per cell; flagged. | own contribution |
| Malicious | Inflate its own counter to `±(2^48 − 1)`, add 65 535 B to a set, `DEL` any entity; pin nothing, dominate nothing of others. After `REVOKE(X, from_t)` every record with `t ≥ from_t` leaves every join. | per-author; ends at `REVOKE` with no owner `DEL` |

The last row is the gain over the baseline for C2: a thief's pre-revocation `PUT`s on typed cells do **not** stand after revocation. Only its `DEL`s stand.

## 4. Reconciliation and digest

**Element key.** `kind:u8 ‖ ent[16] ‖ field[32] ‖ ftype:u8 ‖ author[32] ‖ h[32]` (114 bytes; `ftype`, `author` zero for non-PUT kinds). The 33 extra bytes keep one cell's records contiguous in range order, so a contested cell ships in one leaf. Everything else (`kind` order, `acc`, `ACC`, `fp`, `digest`, 16-way split, leaf bound 4, HAVE round, Noise XX, sealed bundles, relay blindness): **unchanged from DESIGN.md §8**. Verify-on-win still holds: a record rejected by (D1) or (D2) reaches no state. `N` grows by at most `authors − 1` per contested typed cell; rounds stay `⌈log₁₆ N⌉ + 2`.

## 5. Authorization, encryption, revocation

Membership, the epoch hash chain, the two transport gates, current-epoch-only bundles, grow-only `REVOKE(X, from_t)`: **unchanged from DESIGN.md §6**.

**Why `void` is still a view and not a prune, even per-author.** Per-author domination tempts a stronger rule: let `REVOKE(X, from_t)` dominate `X`'s typed records with `t ≥ from_t`, since they dominate nothing of anyone else. It fails T2' inside one author: `x = PUT_X(t=40)`, `y = PUT_X(t=60)` same cell, `REVOKE(X, from_t = 50)`. `y dom x`, `REVOKE dom y`, `¬ REVOKE dom x`. Replica `P` (`x, y, REVOKE`) ends with nothing of `X` on the cell; replica `Q` (`x, REVOKE, y`) ends with `x`, non-void, counted. Divergent. The only prune that keeps T2' is "`REVOKE` dominates *all* of `X`'s typed records regardless of `t`", which is D's `Rev`-deletes-everything (adversary judge D-2) and discards `from_t`. So `REVOKE` hides and flags; the view drops the voided contribution; the record sits in `F` until the owner `DEL`s the entity (cost in §6). The semantics are better than the baseline's, where the voided value still *shows* as a flagged cell.

## 6. Storage and GC

Log, sealing at rest, compaction to `F`, the drop rule (`dom(x, F)` or tombstone expiry), apply-then-expire, A4, the straggler residual: **unchanged from DESIGN.md §7**.

**Index.** `(cell, author) → (offset, v)` instead of `cell → (offset, v)`; a read of a typed cell folds over ≤ `authors` entries (≤ 64 for live members). Per record 76 bytes of version plus the 33-byte wider key.

**Bounds.**

```
|F(ns)| ≤ #LWW cells with a live value
        + Σ_typed cells  #authors that ever wrote the cell and were not since dominated by a DEL
        + #DELs younger than del_ttl + 1 roster + revocations (≤ 1024)
```

Per typed cell: ≤ 64 records of current members, plus ≤ 1024 void records of revoked authors, plus records of departed-but-not-revoked members (a lost device's increments are, correctly, still counted). Hard bound 1088 per cell by the roster and revocation bounds; the practical bound is "authors who touched it". One `DEL` frees the whole cell everywhere, void records included: the owner's purge path for a revoked writer's typed garbage costs one record per entity, as for LWW cells.

## 7. Assumptions

A1–A5 unchanged from DESIGN.md §9; **no clock assumption for convergence**. Two more are explicit because the typed joins depend on them for *meaning*, never for convergence:

- A6. An honest author's own state is monotone (counters never decrease, sets never shrink, max never falls) because it is computed from its own surviving record. A restored backup violates this for one author and is detected, not prevented.
- A7. Applications agree on a field's type out of band; the engine reports, and does not resolve, a name with two live typed cells.

## 8. Known weaknesses

- **Monotonicity is not a lattice property.** GSET, PNCOUNTER and MAXREG are grow-only *per honest author*: the lattice keeps the author's latest record, whatever it says. A buggy, restored or malicious author can shrink its own set or regress its own counter in one write (a restore does so silently until first sync; `(seq, h)` would prevent that and breaks T2', §2). Convergence is unaffected; the damage is confined to that author's contribution and is attributable.
- **Delete resets, and the reset is clock-raced.** A `DEL` zeroes every author's state. An author that *observed* the `DEL` restarts at zero; an author whose concurrent write lands above the `DEL` by `t` carries its **entire historic total** into the resurrected entity. The resurrected counter is "sum of full totals of whoever wrote after the delete", not a clean restart: the LWW delete-vs-edit race with more visible consequences.
- **Per-cell state is O(authors-ever).** Void records of revoked authors and stale records of departed authors remain until the entity is deleted; a long-lived MVREG cell accumulates one value per author who ever touched it. LWW cells still hold one record.
- **MVREG is a per-author register map, not an observed-remove MV-register.** No author can retire another's stale value; the only purge is `DEL`. This is D's candidate view, with D's cost.
- **Equivocating clones lose increments.** Two devices with one key both incrementing a counter converge on one of their states, not the sum; a clone is by definition not distinguishable as a second author.
- **Larger keys and index.** 114-byte element keys and a `(cell, author)` index cost ~33 bytes per record and up to 64 entries per read.
- **Everything the baseline gives up** (LWW un-ring on LWW cells, a thief's `DEL`s stand, `DEL` pins at the ceiling, TTL straggler resurrection, root liveness for the ceiling) is inherited unchanged.

## 9. Proof obligations

Numbering follows DESIGN.md §9; "✓" means already machine-checked in `formal/lean/Kome/Frontier.lean` and surviving without change, "restate" means the statement changes and the existing proof must be redone, "new" means a new theorem.

- **T1 ✓ unchanged.** `Version` and its order are untouched.
- **T2 ✓ unchanged.** `Dom_mono` is generic in `dominates`.
- **T2' restate.** `dominates_trans` for the new `dominates`, whose `put/put` case is `e = e' ∧ f = f' ∧ ty = ty' ∧ (ty = 0 ∨ v.author = v'.author) ∧ Version.lt v v'`. The five cases of §2; the `omega` proof survives since author equality is a linear constraint.
- **T2'-neg (new, negative).** With `put/put` domination by `(seq, h)` and `del/put` by `v`, `dominates_trans` is false: the §2 three-record trace, checked by `decide`. This documents why the full version is required.
- **T3 ✓ unchanged.** `F_sandwich`, `F_prefix`, `F_suffix`, `frontier_hom`, `F_idem` use only `dominates_irrefl` and `dominates_trans`.
- **T4 ✓, T4' ✓ unchanged.** `applyAllA_view`, `convergence`, `adm_mono` are generic over `Record` given the two lemmas; `adm` ignores `ftype`.
- **T5 restate.** `cell_author_unique`: two frontier PUTs on one cell with `ty ≠ 0` and equal author are the same record; for `ty = 0`, `cell_unique` as today. Plus: `types`, `recs` and each typed `cell(c)` are functions of `F` alone.
- **T6 ✓, T7 ✗ unchanged.** Larger element set, same algebra and protocol.
- **T8 restate.** Own-floor chase: if `floor_T.t < maxceil` then `v_emit > floor_T`; and **T8' (new)**: for `ty ≠ 0`, `v_emit > own(c).v` unconditionally (equal author, `t_emit ≥ own.t`, `seq_emit > own.seq`), so `SHADOWED` on a typed cell implies `floor_T = deleted_at` with `t = maxceil`.
- **T9 ✓ unchanged.**
- **T10 restate.** Two distinct records with equal `(author, seq)` are ordered identically everywhere; on one cell exactly the greater is in `F`; `F` is unaffected by arrival order (a corollary of T3).
- **T11 unchanged** (liveness, under A4).
- **T12 restate.** Applying a `REVOKE`/`ROSTER` changes `F` only at that record; `void` is monotone in `F`; and the typed joins are monotone-decreasing in the `REVOKE` set (a voided contribution leaves every join). Plus **T12-neg (new, negative)**: `REVOKE` dominating `X`'s typed records with `t ≥ from_t` violates T2' (§5 trace).
- **T13 restate.** Add: `ftype ≤ 4` and the per-type value layout are decode refusals; `inc, dec < 2^48`, GSET encoding ≤ 65 535 B, elements ≤ 255 B; `COUNTER_EXHAUSTED`/`GSET_FULL` produce no record; the PNCOUNTER view fits `i64` for ≤ 1088 authors.
- **T14 unchanged** (paper reduction).
- **T15 (new) Join determinism.** For each `ftype`, `cell(c)` is the fold of a commutative, associative operation over the finite set `recs(c)`, hence independent of enumeration order and equal on replicas with equal `F` (Lean: `foldl` invariant under permutation, for `Nat` sum, `max`, and union up to membership).
- **T16 (new) Per-cell bound.** `|{ p ∈ F | cell(p) = c }| ≤ |{ p.author | p ∈ F, cell(p) = c }|`, from T5; with the roster/revocation bounds, ≤ 1088.
- **T17 (new, under A5 and no restore) Own monotonicity.** An honest author's successive surviving records on a GSET/PNCOUNTER/MAXREG cell between two `DEL`s are monotone in its state order. A statement about the emission rule, not the lattice.

The hard theorem remains T7. The Lean delta is one constructor field, one `decide` clause, two negative examples and three short folds: about one person-week on top of DESIGN.md's budget.

## 10. Self-score

- **C1 = 4.** Same assumptions as the baseline, nothing added for convergence; T3/T4 reused verbatim. Not 5 because T4 is still in exchange form (ceiling) and T11 is liveness.
- **C2 = 4.** On typed cells a misbehaving writer can neither pin nor overwrite others, and its contribution leaves every view at `REVOKE` without owner cleanup; a restore or clone regresses only its own contribution. Thief `DEL`s and `DEL` pins at the ceiling still stand.
- **C3 = 3.** LWW cells cost as before; typed cells cost one record per author ever (void ones until `DEL`), 33 B wider keys and a fold per read. Still no vectors, no per-peer state, membership-free GC.
- **C4 = 4.** Unchanged RBSR, cacheable fingerprint, blind relays; slightly larger `N` and descriptors.
- **C5 = 3.** Unchanged from the baseline; typed cells make post-`from_t` writes vanish from views rather than merely flag, but a removed member still keeps plaintext and back-dates during propagation.
- **C6 = 4.** The trusted core grows by one `dominates` clause, five commutative folds and a typed decoder; the generic frontier proofs are reused unchanged, and the two tempting shortcuts (`(seq, h)`, `REVOKE`-as-prune) are refuted as theorems rather than left as folklore.
- **C7 = 4.** No new primitives; wider index key; joins are loops over ≤ 64 fixed-size entries; counters are `u48` arithmetic with refusal.
- **C8 = 4.** Counters, grow-only sets, max-registers and visible per-author conflicts without app-level encoding tricks; `TYPE_CONFLICT`, delete-resets and the clock-raced resurrection are what the app must understand.
- **C9 = 4.** `ftype` is a bounded enumeration with no reserved value, value layouts are decode-time refusals, `(0,0)` is an ordinary state, exhaustion refuses; the residuals are `exists` as a view (as in the baseline) and the per-cell bound being by roster, not by type.
