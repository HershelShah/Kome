# Candidate G: multi-value cells with explicit causal parents

## 1. Summary

- No clock enters the order. A PUT carries a causal `height` and the hashes of the foreign cell versions it supersedes (`parents`). Two PUTs on one cell by different authors never dominate each other in the store: they are **siblings**, kept and shown.
- The store is DESIGN.md's frontier with **one clause changed**: PUT-vs-PUT domination requires the same author. T2, T2', T3 and T4 survive with that clause; the Lean model changes in one constructor case of `dominates`.
- Sibling resolution is a **view**, not a store rule: a sibling is hidden iff another sibling on the cell names its hash as a parent. `get` returns the live siblings (at most one per author); `set` names what the app saw. Naming-as-domination was tried and rejected in §2 because it is not upward-closed.
- A write that saw a record always hides it, whatever height that record claims. A forged height can pin only a DEL (blocking re-creation of one entity) and only until the next roster refresh; it can never hide an honest value or shadow an honest PUT.
- DELs keep a strict total order `(height, author, seq, h)`, because freeing other authors' bytes needs one. Concurrent delete-vs-edit resolves by height, where DESIGN.md resolves by time.
- Admission stays monotone: a data record is admitted iff `height ≤ maxh ∧ author ∈ W`, two grow-only registers fed by every ROSTER and REVOKE ever applied. `W` bounds siblings per cell by authors ever rostered and closes a gap DESIGN.md leaves open (a member relaying records signed by unrostered keys).
- The price: a resolved sibling stays in `F` with its value until its author rewrites the cell or the entity is deleted; a PUT may carry up to 63 parent hashes; no wall time exists except for tombstone expiry.
- On the far-future-clock problem: the far-future regime, the ceiling tie that shadows honest PUTs and the "Lamport-ized forever" cell are gone. Lost: true concurrency presents as a conflict instead of resolving by wall time, and "last modified" becomes the app's business.

## 2. Data model

Identifiers, `ns`, `ent`, `field`, values: unchanged from DESIGN.md §2.

**Version.** `v = (height : u48, author : [32]u8, seq : u48, h : [32]u8)`, compared lexicographically exactly as DESIGN.md §2 compares `(t, author, seq, h)`; `t` is replaced by `height`, nothing else moves. `height = 0` is an ordinary value (a first write on a never-deleted entity). T1 is unchanged.

**Records.**

```
PUT     ns[16] ent[16] flen:u8 field[flen] height:u48 seq:u48 author[32]
        n_parents:u8 (≤63) parents[n][32] vlen:u16 value[vlen]
DEL     ns[16] ent[16] issued_t:u48 height:u48 seq:u48 author[32]
ROSTER  ns[16] root_pk[32] salt[16] gen:u48 ceiling_h:u48 del_ttl:u48 epoch:u16
        n_members:u8 (≤64) members[n] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
REVOKE  ns[16] root_pk[32] salt[16] sign_pk[32] rev_seq:u48 void:u8 ∈ {0,1} [from_seq:u48 iff void = 1]
```

Changes from DESIGN.md §2: PUT loses `t`, gains `height`, `n_parents`, `parents`. DEL loses `t`, gains `height` and `issued_t` (read by tombstone expiry in §6 and by nothing else; it is never compared). ROSTER's `ceiling_t` becomes `ceiling_h`. REVOKE's `from_t` becomes an explicit `Option` of `from_seq` (`void = 0`: removed, nothing voided). Hashing, signing, well-formedness: unchanged; `parents` are opaque 32-byte strings and well-formedness never asks whether they are held. `n_parents = 0` is ordinary.

**Domination.**

```
dom(p, H) for PUT p   := ∃ q ∈ H : PUT, cell(q) = cell(p), q.author = p.author, q.v > p.v   -- CHANGED
                       ∨ ∃ d ∈ H : DEL, entity(d) = entity(p), d.v > p.v                     -- unchanged
dom(d, H) for DEL d   := unchanged from DESIGN.md §3
dom for ROSTER/REVOKE := unchanged from DESIGN.md §3
F(H) := { x ∈ H | ¬ dom(x, H) }
```

Within one author, `(height, seq, h)` is a strict total order, so the changed clause is transitive; a DEL above a PUT is above everything that PUT dominates; T2' holds for every pair of kinds by the same case analysis as before.

*Why a PUT does not dominate its parents.* The obvious rule, `q dom p iff p.h ∈ q.parents`, is not upward-closed. Take `p`, then `q` naming `p`, then `r` naming `q` (three authors). `F({p, q, r}) = {r}`, but a replica that applied `q, r` first holds `{r}` and then admits `p`: `F({r} ∪ {p}) = {p, r}`, because `r` does not name `p` and `q`, the only witness, was dropped. T3 fails; apply-with-GC is order-dependent. The writer cannot repair it by naming transitively, since `p` was already gone from its frontier when `r` was written. Dropped intermediates make ancestry invisible, so naming can only ever be a view over held records.

*Why not order PUTs by height across authors.* That is DESIGN.md with `t := height`: the same silent LWW, ceiling ties and shadows, minus wall-time meaning.

**Views** (pure functions of `F`).

```
sibs(c)      := { p ∈ F | p is a PUT on cell c }                     -- at most one per author (T5)
named(p)     := ∃ q ∈ sibs(cell(p)) : p.h ∈ q.parents
live(c)      := { p ∈ sibs(c) | ¬ named(p) }                          -- what the app sees
pick(c)      := max_v live(c)                                         -- Option; a deterministic default
deleted_at   := unchanged from DESIGN.md §3
exists(ent)  := ∃ f. live(ent, f) ≠ ∅
void(p)      := ∃ REVOKE(p.author, void = 1, from_seq) ∈ F : p.seq ≥ from_seq
```

`far` is gone; there is nothing to compare a clock against. `named` is acyclic because a record's hash covers its parent list, so a cycle is a hash fixed point (A2); hence `live(c)` is non-empty whenever `sibs(c)` is (T-G1), and `exists` needs no second derivation.

**Example.** Authors A, B, C; `v` written `(height, author, seq)`; parents in braces.

```
a1 = PUT(E, phone, "555")      v=(0, A, 7)  {}
b1 = PUT(E, phone, "556")      v=(1, B, 3)  {a1}        B saw a1 and resolves it
a2 = PUT(E, phone, "557")      v=(1, A, 8)  {}          A was offline; did not see b1
```

`F = {a2, b1}` (`a1` is dominated by `a2`); `live = {a2, b1}`: a genuine conflict, both shown with their authors. C resolves it: `c1 = PUT(E, phone, "555 / 557") v=(2, C, 1) {a2, b1}` gives `live = {c1}`. B then rewrites: `b2 v=(3, B, 4) {a2, c1}` names the **whole foreign frontier**, not just what it sees as live, so `a2` stays hidden after `b1` is dropped. Any arrival order gives the same `F` (T3) and the same `live` (T5).

**What the app sees (C8).** This is the design's point, so the API is part of the data model:

```
sync_get(ns, ent, field, out sib[≤ n], &n)
    sib := { author[32], height, seq, h[32], value, flags: VOID | HEIGHT_SUSPECT }   -- live(c), one per author
sync_pick(ns, ent, field)         → the max_v live sibling, or NOTFOUND            -- for apps that want one value
sync_set(ns, ent, field, value, seen[] | NULL)
    → OK | SHADOWED | CONFLICT_UNSEEN | SEQ_EXHAUSTED | NOMEM
sync_delete(ns, ent)              → OK | SHADOWED | SEQ_EXHAUSTED
sync_scan(ns)                     → entities with ≥ 1 live sibling, each with a CONFLICTED bit
```

`seen` is the hash list the app got from `get`. `set` fails with `CONFLICT_UNSEEN` if a live foreign sibling arrived since (a compare-and-set: a value the user never saw is never silently superseded); `seen = NULL` means "resolve whatever is there". Either way the engine names every foreign record in `sibs(c)`, resolved ones included, which keeps resolution cumulative (§3).

## 3. Height, parents and identity

Replaces DESIGN.md §5 ("Clocks and writing"). There is still no engine clock, no `tick`, no `receive`, nothing adopted from a peer; now there is no wall clock in any record order either.

**Emission.**

```
S        := sibs(c) \ {own}                                            -- foreign frontier, ≤ |W| − 1
if seen ≠ NULL ∧ ∃ p ∈ live(c) \ {own} : p.h ∉ seen → CONFLICT_UNSEEN, no record
parents  := { r.h | r ∈ S }; if |S| > 63, the 63 largest by v
height   := 1 + max({r.height | r ∈ S} ∪ {own.height} ∪ {deleted_at(ent).height} ∪ {0})
            if height > maxh then height := maxh
seq      := seq_self + 1; SEQ_EXHAUSTED at 2^48 − 1, no record
v_emit   := (height, self_pk, seq, h)
status   := SHADOWED if deleted_at(ent) exists ∧ v_emit < deleted_at(ent).v   (only when height = maxh) else OK
```

For a DEL: `height := 1 + max` over every sibling of every field of `ent` and `deleted_at(ent)`, clamped; `issued_t := now_ms` (or 0 on a device without a clock; it affects only when the tombstone expires). `seq_self` remains the only persisted clock state.

Three consequences. (1) **Read-your-writes is unconditional for PUTs**: `own` dominates the writer's previous record by `seq` even at the ceiling and names every foreign record held, so `live(c) = {own}` at the writer at once (T8 loses its `floor.t < maxceil` hypothesis). (2) **Cumulativity**: `parents` is the full foreign frontier, not the live set, so an author's next write carries forward every resolution its previous write made, which T3 is about to drop. With only 4 parents a fifth author's resolved value would re-surface on the writer's next write; hence 63, matching 64 members. (3) **Height is on trust.** A replica holding a named parent can check `height > parent.height` and flag `HEIGHT_SUSPECT`; it must not refuse, because a replica lacking the parent cannot run the check and the two would diverge (the math judge's counterexample 1 against C). Heights are bounded only by `maxh`.

**Ceiling.** `maxh` is the per-collection max-register of `ceiling_h` over every ROSTER ever applied, exactly as `maxceil` in DESIGN.md §4; `ceiling_h` is a count, not a time. Honest heights grow by one per causally dependent write, so a root sets `ceiling_h := max height held + 2^32` and refreshes when any held height exceeds `ceiling_h − 2^31`; a refresh is needed only after a pin, and 2^16 refreshes fit in u48.

**Identity, `seq`, equivocation**: unchanged from DESIGN.md §5, plus one fact: `F` keeps at most one record per `(cell, author)`, so two clones of a key contribute one sibling between them, ordered by `(height, seq, h)`.

**Versus `(t, author, seq, h)`.** In DESIGN.md a write that *saw* a far-future record already wins, by chasing; the damage there is to writes that did not see it (resolved silently in the bad clock's favour), to the cell afterwards (Lamport-ized until wall time catches up), and at the ceiling (an attacker-chosen key wins the tie and shadows every honest PUT, the adversary judge's A-1). Here: a write that saw `m` names it and hides it everywhere, whatever `m.height`; a write that did not see `m` appears beside it, attributed, with both values intact; nothing is Lamport-ized because there was no wall time to depart from; and no PUT can be shadowed, since the store never lets a foreign PUT dominate. Only a DEL at `maxh` from a larger key can still pin, and only entity re-creation. So on the far-future-clock problem this design strictly dominates the frontier store.

The cost is the other side of the coin. Two phones that edit a contact's number offline produce a conflict the app must present or merge; DESIGN.md picks the later clock, usually the edit made last, which is what users expect. For settings (`theme = dark` vs `light`) a sibling pair is a nuisance; `pick` breaks it by causal depth then key, deterministic and meaningless, and an app wanting "latest wins" must store a timestamp in the value and choose itself, the app-stamp leak the implementer judge disliked in B. In favour: LWW loses the edit on the device the user is not looking at, with no trace; here that loss is impossible and merging a contact with two new numbers is one `set`. Against: on one person's own devices, concurrent edits of one field are rare, so the common case gains nothing and pays O(authors) per contested cell. Honest summary: better for shared lists and contacts edited by several people; a wash or slightly worse for a single user's settings.

**H8, case by case.**

| Case | Effect | Bound |
|---|---|---|
| Clock wrong (either way) | None; no record carries a compared clock. `issued_t` wrong only shifts when that DEL's tombstone expires | — |
| Forged height on a PUT | Wins `pick` on cells it touches until named; never hides a value; clamps honest heights on those cells to `maxh` | ends when any honest write names it; `HEIGHT_SUSPECT` where parents are held |
| Forged height on a DEL at `maxh` with a larger key | Entity cannot be re-created by smaller keys (`SHADOWED`) | until the next roster refresh, as DESIGN.md T9 |
| Backup restore | Re-emits low `seq`; ordered by `(height, seq, h)`, flagged `CLONE_SUSPECTED`; a resolution made by the lost record may re-surface as a sibling (never a lost value) | self-detected; `seq` jumps |
| Cloned key | One sibling per cell between the clones; resolutions by the losing clone can re-surface | flagged; owner issues `REVOKE` + roster |
| Malicious | Overwrite own slot of any cell, DEL any entity (write access); keep any cell permanently in conflict with one sibling of its own; name honest values to hide them (attributable: its record carries the hash); DEL-pin at `maxh` | one sibling per cell per key in `W`; no forging; hiding is reversible by a re-`set`; ends at `REVOKE` + one owner DEL per flooded entity |
| Root restored from backup | As DESIGN.md §5; `maxh` and `W` never decrease | convergent either way |

## 4. Reconciliation and digest

Unchanged from DESIGN.md §8: same element keys `kind ‖ ent[16] ‖ field[32] ‖ h[32]`, same 4096-bit accumulator, same protocol, same transports and bundles. Notes: a contested cell's siblings share the `ent ‖ field` prefix and so fall in one leaf range; the in-memory index is keyed `(cell, author) → (offset, v)` so verify-on-win (skip the Ed25519 verify of a record the held same-author record already dominates) stays sound; a PUT can be up to 2 016 bytes larger than before when 63 parents are named, which the 64 KiB leaf and bundle bounds absorb.

## 5. Authorization, encryption, revocation

Unchanged from DESIGN.md §6 with three edits.

**Admission** (replaces DESIGN.md §4 for data records): a PUT or DEL is admitted iff `height ≤ maxh ∧ author ∈ W`, where `W` is a grow-only set of signing keys updated from `members` of every ROSTER ever applied (including rosters dominated on arrival) and from `sign_pk` of every REVOKE. Both registers are stored, not derived, and only grow, so admission is monotone in the held history as DESIGN.md §4 requires; the replica state is `(F, maxh, W)` with join `(F(F₁ ∪ F₂), max, ∪)`. `|W| ≤ 2 048` by capacity; beyond that a collection is re-founded. Without `W`, a malicious member could relay records under 10⁶ ground keys and give one cell 10⁶ siblings; with it, each rostered key contributes at most one. The root engine removes a member only by a REVOKE (`void = 0` if nothing is to be hidden) followed by a roster, because of the caveat `maxceil` already has: a replica that joins after a roster was dominated never applies it, so a key listed only there must reach it through the never-dominated REVOKE.

**Revocation** is `REVOKE(X, rev_seq, void, from_seq)`: grow-only, never dominated, root-signed; `void` flags `X`'s records with `seq ≥ from_seq`. The owner reads `from_seq` off the last record of `X` it holds. A deliberate thief can equivocate at lower `seq` values, exactly as it could back-date `t` under DESIGN.md (adversary A-3); `void` is for lost devices, `REVOKE` plus owner DELs is for thieves. Unchanged in strength, not in mechanism.

**Session and bundle gates, epoch chain**: unchanged from DESIGN.md §6.

## 6. Storage and GC

Log, sealing, compaction: unchanged from DESIGN.md §7. The index is `(cell, author) → (offset, v)`; per sibling 6 + 6 + 32 + 32 bytes of version plus 8 bytes of offset; a per-cell `named` bitmap (≤ 64 bits) is recomputed from the siblings' parent lists, read from the log, whenever a sibling of that cell changes.

**Drop rule.**

```
dom(x, F)                                                        -- T3, deterministic, membership-free
∨ (x is DEL ∧ now_local ≥ x.issued_t + del_ttl)                    -- apply-then-expire, unchanged
```

**What frees bytes.** A same-author rewrite frees the previous value everywhere on arrival; a DEL frees every sibling of every field of the entity; tombstones expire as before. A **resolved sibling is not freed**: it remains its author's frontier record and must, because resolution is a view. Suppose it were dropped: `H₁ = {a1, b1 names a1}` gives `{b1}`; `H₂ = {b2}` (B's later write, made on a clone that never held `a1`, so it names nothing) gives `{b2}`. Then `F(H₁ ∪ H₂) = {a1, b2}` with `a1` live, because `b2` dominates the only witness `b1` and does not name `a1`; but the two pruned states join to `{b2}`. Same records, different views. So a contested cell retains one full value per author that wrote it until that author writes the cell again or the entity is deleted. A writer whose value lost can clear its own slot by rewriting the cell with the winning value and `seen = NULL`, which costs one record and produces no new conflict; an app-level "accept resolution" routine can do it automatically for the local author.

**Bounds.** `|F(ns)| ≤ Σ_cells |authors on cell| + DELs younger than del_ttl + 1 roster + revocations`; `|sibs(c)| ≤ |W| ≤ 2 048`, in practice ≤ 64; `n_parents ≤ 63`; the far-future `issued_t` of a malicious DEL keeps a 141-byte tombstone until an owner DEL above it dominates it (at the next refresh if it sits at `maxh`).

## 7. Assumptions

- A1, A2, A5: unchanged from DESIGN.md §9. A2 additionally gives acyclicity of `named` (a record cannot name its own hash transitively).
- A3 (root liveness) is weaker: a refresh is needed only after a height pin, not on a calendar.
- A4 (tombstone expiry only): unchanged; the single clock in the system.
- A6 (cumulativity, for the view only): an honest writer names the whole foreign frontier it holds. A violation (restore, clone, or a cell with > 64 authors-ever) can re-surface an already-resolved sibling; it cannot hide a value or affect `F`.
- No clock assumption, and no height assumption, for convergence.

## 8. Known weaknesses

- **Resolved siblings are retained.** A contested cell costs one full value per author that ever wrote it, until that author rewrites or the entity is deleted. This is D's O(authors) per contested cell, accepted knowingly; DESIGN.md §10 item 5 declined exactly this cost.
- **No time.** `pick` orders true concurrents by causal depth and then by public key: deterministic and meaningless. "Last modified" must be a field; apps wanting wall-clock LWW implement it over siblings and inherit the app-stamp leak.
- **DELs still use a total order.** Concurrent delete-vs-edit resolves by height, partial resurrection included, as in DESIGN.md; a DEL forged to `maxh` by a larger key blocks re-creation of that entity until a refresh (A-1, narrowed to DELs).
- **Parent lists.** Up to 63 × 32 bytes per PUT; a cell with more than 64 authors-ever cannot be collapsed by one record and must be deleted and re-created.
- **Cumulativity is a writer discipline (A6)**, not a store property. Restores and clones can re-surface resolved conflicts.
- **`W` grows for the life of a collection** and, like `maxceil`, is a stored register that a latecomer can only reconstruct from rosters it applied; removal must go through REVOKE.
- **Tombstone expiry is unchanged**, with its clock, its skew cost and its straggler resurrection.
- **Height verification is advisory.** A forged height is detected only where the named parents are held, and detection changes nothing but a flag.

## 9. Proof obligations

- **T1 ✓ Total order.** Unchanged; `Version.t` is renamed `height`. The Lean theorem survives verbatim.
- **T2 ✓, T2' ✓, T3 ✓.** `dominates (put e' f' a' v' _) (put e f a v _) := e = e' ∧ f = f' ∧ a = a' ∧ v < v'`; `dominates_trans` is re-proved by the same `cases … <;> omega`, with the author equality threaded through the put/put/put and put/put/del cases. `F_sandwich`, `frontier_hom`, `F_idem` survive unchanged.
- **T4 ✓ Convergence.** State `(F, maxh, W)`; `adm (c, W) r := r.height ≤ c ∧ r.author ∈ W` for data records. `applyAllA_view` and `convergence` restate with the pair register; `adm_mono` becomes monotone in the product order `(≤, ⊆)`.
- **T4' ✓ Monotone admission.** As DESIGN.md, plus `W` never shrinks.
- **T5 ✓ View determinism.** `cell_unique` is restated as `cell_author_unique`: two frontier PUTs on one cell by one author are the same record. New: `sibs`, `named`, `live`, `pick`, `exists`, `void` are functions of `F`.
- **T-G1 ✓ Live non-empty.** If `named` is acyclic on `sibs(c)` (hypothesis, discharged by A2 on paper), `sibs(c) ≠ ∅ ⇒ live(c) ≠ ∅`. Finite acyclic relation has a maximal element.
- **T-G2 ✓ Sibling bound.** `|sibs(c)| ≤ |{ author(p) | p ∈ F }| ≤ |W|` for any `F` of admitted records.
- **T-G3 ✓ Saw-it-wins.** If `q ∈ F` and `p.h ∈ q.parents` and `cell(p) = cell(q)` then `p ∉ live(cell)` at every replica holding `q`, for any `p.height`.
- **T-G4 (paper) Cumulativity.** If an honest writer emits `q'` after `q` on one cell at a replica holding `p ≠ own` in `sibs`, then `p.h ∈ q'.parents` whenever `|S| ≤ 63`; hence a resolution survives the drop of `q`.
- **T6 ✓ Digest.** Unchanged.
- **T7 ✗ Reconciliation.** Unchanged; still the long pole.
- **T8 ✓ Chase.** Strengthened: for a PUT, `live(c) = {own}` at the writer after `set`, with no ceiling hypothesis (`own` beats the previous own record by `seq`; `own` names all of `S`). The DEL clause keeps DESIGN.md's form with `height`.
- **T9 ✓ Bounded pin.** No admitted record has `height > maxh`; after a roster with a higher `ceiling_h`, every honest DEL and PUT is unshadowed. Only DELs can shadow.
- **T10 ✓ Equivocation.** Unchanged, plus: two records with equal `(author, cell)` never both lie in `F`.
- **T11 Tombstone expiry.** Unchanged (liveness, A4), with `issued_t` in place of `t`.
- **T12 ✓ Revocation locality.** Unchanged.
- **T13 ✓ Bounds.** Adds `n_parents ≤ 63`, `|W| ≤ 2 048`; `height` clamps, never wraps.
- **T14 ✗ Epoch secrecy.** Unchanged.

Of `Frontier.lean`: the `Version` section, `F_sandwich`, `frontier_hom`, `F_idem`, `applyAllF_mem`, `convergence_F` and the ceiling lemmas survive unchanged; `dominates`, `dominates_trans`, `cell_unique`, `adm`, `adm_mono`, `State`, `applyA` and `convergence` are restated; `chase` loses its hypothesis. About 1–2 person-weeks of Lean and 3 of SPARK (parent lists, `(cell, author)` index, `named` bitmap, `W`) on top of DESIGN.md's estimate.

## 10. Self-score

- **C1 = 4.** Same frontier lattice and theorems as DESIGN.md, with no clock in any order; two grow-only registers in the state instead of one; tombstone expiry still carries the only clock.
- **C2 = 4.** A misbehaving writer can never hide or shadow an honest value and contributes at most one sibling per cell; residuals are DEL-pins at `maxh` until refresh and retained void garbage until owner DELs.
- **C3 = 3.** One retained value per author per contested cell, up to 2 KiB of parents per PUT, a `W` register; deletes still free everything at once and tombstones still expire.
- **C4 = 4.** Reconciliation, accumulator, relays and bundles unchanged; records are larger when contested.
- **C5 = 3.** Unchanged from DESIGN.md: epoch cut-off is clean, `void` is a flag, a deliberate thief needs `REVOKE` plus DELs; `from_seq` is neither better nor worse than `from_t`.
- **C6 = 4.** The trusted core is DESIGN.md's plus one author-equality clause and one acyclicity hypothesis; most of `Frontier.lean` survives; the view is a few lines over `F`.
- **C7 = 4.** No clock required for anything but tombstones; same primitives; parent storage and a bitmap per contested cell are the only additions.
- **C8 = 4.** Conflicts are visible, attributed, compare-and-set protected and resolved by one call; one short of 5 because delete-vs-edit is still silent and `pick` is arbitrary.
- **C9 = 4.** No sentinels (`height = 0`, `n_parents = 0`, `void = 0` all ordinary), explicit `Option`s, exhaustion refuses; the residual is the `height = maxh` regime, as in DESIGN.md.
