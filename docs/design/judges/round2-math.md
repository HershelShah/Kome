# Math judge, round two: S, E, F, G, H, I, J

Stance as in round one: every convergence, upward-closure, GC-invisibility
and admission-monotonicity claim was treated as false until I failed to break
it. I took `dom`, `F`, admission and the drop rule (`x` dropped iff `dom(x,
F)` against the *current* frontier, DESIGN.md §7) literally and tried to
build two replicas offered the same records ending with different `F`, a
chain `y dom x, z dom y, ¬ z dom x`, a GC step that changes a later frontier,
a non-monotone admission, and an H5/H6 violation. Notation: `v = (t, author,
seq)` with `h` omitted unless it decides; `F_X` is replica X's frontier after
applying the listed records in order, with GC after each.

One result governs most of what follows and I state it once: **the frontier
lattice is sound for exactly those `dom` relations in which every kill
predicate is a down-set of the record order on the same key.** S, E, F, G, J
and H each satisfy this on their own; two of the compositions do not (§8).

---

## 1. Candidate S (the frontier store, DESIGN.md)

### What survives

T1, T2, T2', T3, T4 (applied-set form), T4', T5, T8, T9, T12 are
machine-checked in `Frontier.lean` and I re-read the statements against the
prose: `dominates` matches §3, `adm` matches §4, `applyA` is apply-with-GC
with the ceiling as a max-register, and `convergence` quantifies over
arbitrary order and duplication. The sandwich lemma is the right proof and
`exists_max_dominator` is exactly the T2' use. I could not break the lattice.
Two things in the prose are not what is checked.

### Counterexample 1 — T4's exchange clause is false: `maxceil` is not a record and is never reconciled

`maxceil` is updated "from every ROSTER ever applied, including rosters
dominated on arrival", but §8 reconciles the records of `F` only. A roster
that raised `maxceil` on some replicas and was then dominated everywhere
cannot reach a replica that joined later. The design's own H8 row ("root
restored from backup … dominated *or dominating* by `(gen, h)`") produces it.

```
R_hi : ROSTER gen=3 ceiling_t=5000 h=0x01…      real root
R_lo : ROSTER gen=3 ceiling_t=4000 h=0xF0…      root restored from a backup older than the horizon; wins by h
p    : PUT (E,f) v=(4500, W, 1)                  honest W, emitted under R_hi (now = 4500)
q    : PUT (E,f) v=(3500, W, 0)                  W's earlier value

Replica A applies R_hi, q, p, R_lo:   maxceil=5000; p dominates q (q freed); R_lo drops R_hi.   F_A={R_lo, p}, c_A=5000
Replica B joins later, receives from A:  F_A contains R_lo only, so B applies R_lo, then q from a third replica.
                                       maxceil_B=4000; p (t=4500) inadmissible.                  F_B={R_lo, q}, c_B=4000
```

Complete reconciliation A ↔ B: A offers `p`, B refuses (not held, "re-offered
next time"); B offers `q`, A drops it (dominated). `F_A ≠ F_B` and `c_B ≠
max(c_A, c_B)` after every exchange until some root issues a ceiling ≥ 4500.
The Lean theorem is not contradicted (it assumes both replicas applied
`R_hi`); the prose clause "after a complete reconciliation both hold `F(H_A ∪
H_B)` and `max(c_A, c_B)`" is. The register is replica state that the sync
protocol does not join. Fix: carry `maxceil` in the session HELLO and join by
`max` (one line, no theorem changes). The same fault recurs, worse, in G's `W`
and J's `roots_ever` (§4, §7).

### Counterexample 2 — A4 as stated does not prevent resurrection on every replica

A4 says "every member syncs with some member at least once per `del_ttl`".
That is satisfied by a schedule in which the `DEL` never reaches two members
before everyone who held it has expired it. `del_ttl = 100`, four members:

```
t=0     X: p = PUT(E,f) v=(0,X,1);  p reaches Y, Z, W
t=1000  X: d = DEL(E) v=(1000,X,2)
t=1050  X↔Y  (Y gets d, drops p)         Z↔W  (neither has d)
t=1100  X and Y expire d (now ≥ 1100): both hold nothing on E
t=1120  Y↔Z: Z offers p, nothing dominates it, Y admits.   F_Y={p}
t=1150  X↔Y: Y offers p, X admits.   W↔Z.                   every replica: F={p}
```

Every member synced within every 100-unit window; `E` is back everywhere,
with no clock skew. The assumption convergence-with-expiry needs is "every
`DEL` reaches every member within `del_ttl` of `d.t`", i.e. sync-graph
diameter × sync period < `del_ttl`. State it that way.

### Model/prose mismatch (C6)

`Frontier.lean` *holds* inadmissible records (`keep` only drops what an
admitted record dominates) and filters them out of `view`; the prose discards
them. Both converge, but the machine-checked system is not the shipped one.

### Obligations rejected

- **T4, exchange clause**: false (CE 1) until the register is reconciled.
- **T11**: true as a liveness statement but its hypothesis A4 is too weak (CE 2).

### H5/H6

`t = maxceil` regime; `now_local` in the drop rule; the digest of two
converged replicas differs while they disagree on a tombstone's expiry. All
three were noted in round one and are unchanged.

### Hardest theorem

T7, unchanged. Everything else is checked.

### Scores

C1 4 (lattice checked; exchange clause false by an unreconciled register; A4
understated) · C2 4 (bounded, attributable, ends at refresh) · C3 4 · C4 4 ·
C5 3 · C6 4 (checked core; model holds inadmissibles, prose does not) · C7 4 ·
C8 3 · C9 4.

---

## 2. Candidate E (height-first versions)

### What survives

The claim that T2'/T3 survive is correct and trivially so: `dominates` never
inspects the components of `v`, only `Version.lt`, and `(height, t, author,
seq, h)` is a strict total order under hash injectivity. Admission on `height
≤ maxceil` is the same max-register argument. T8 (chase on height) and T8''
(chain dominance) are one-liners. I could not construct a convergence or GC
failure for E alone, and the sub-ceiling-pin improvement over S is real:
after one chase the cell is back to honest behaviour.

### Counterexample 1 — a clockless deleter's `DEL` cannot stay applied: the system flaps

S supports devices with no clock ("all its writes chase"). In E the `DEL`'s
`t` never chases, so a clockless device emits `t = 0` and its tombstone
expires at once on every replica with a clock, while the deleter (whose
`now_local = 0`) never expires it.

```
p : PUT (E,f) v=(h=0, t=1000, A, 1)         held by A, B, C
d : DEL  E    v=(h=1, t=0,    D, 1)         D is clockless;  del_ttl = 100

B applies d:  p dominated, freed;  now_B=2000 ≥ 0+100, d expired.     F_B = {}
C (not yet synced with D) still holds p.
B↔C: C offers p; nothing in F_B dominates it; B admits.                F_B = {p}
D↔B: D offers d; B applies (p freed), expires d.                        F_B = {}
A↔B: A offers p …                                                       F_B = {p}
```

Every pairwise exchange ends in agreement, but the global state never
settles while any holder of `p` exists and `D` keeps re-offering `d`; no A4
violation is involved. E lists "tombstone durability depends on the deleter's
clock" as a weakness, but the consequence is that a supported device class
cannot delete. S avoided this by accident (`t_emit ≥ floor.t + 1` gave the
tombstone the entity's own age). The fix is to let the `DEL`'s `t` chase
`floor.t` while leaving `PUT`'s `t` honest, which costs E's T11' only on
entities whose last write was pinned.

### Note — ceiling pins never end by themselves

`m = PUT(E,f) v=(maxceil, 2^48−1, M, …)` beats every clamped honest `DEL`
until a refresh, and `M` re-pins after each, forcing one refresh per hour
and burning `2^28` of `2^48` each time. Bounded and attributable, but E's A3
is event-driven: an offline root leaves pinned cells shadowed indefinitely,
where S's wall clock eventually passed the pin.

### Obligations rejected

None false. T11' ("every replica drops `d` at `d.t + del_ttl`") is true and is
exactly what CE 1 exploits.

### H5/H6

`height = maxceil` regime; height is a consumable with a meaningful
exhaustion (`CEIL_EXHAUSTED` → re-found); otherwise S's hygiene.

### Hardest theorem

T7. The Lean delta is as small as E says (one field, one `adm` clause).

### Scores

C1 4 · C2 4 · C3 3 (immortal attacker tombstones; clockless deletes free
bytes but cannot keep them freed) · C4 4 · C5 3 · C6 4 · C7 4 · C8 3 (chains
beat clocks; apps must know) · C9 4.

---

## 3. Candidate F (typed lattice fields)

### What survives

I verified the claim that `(D1) ∨ (D2)` is upward-closed. The put/put/put case
needs `cell` equality throughout (so `ftype` agrees) and either `ftype = LWW`
or `z.author = y.author = x.author`; author equality is an equivalence
relation and `>` on `v` is transitive, so it composes. The put/put/del case
is `z.v > y.v > x.v` on one entity. The `(seq, h)` refutation in §2 is
correct and is the general principle above (a same-author order that is not
a sub-order of `v` is not a down-set of the `DEL`'s order).

The equivocation rule is a function of the held set: two records with equal
`(cell, author)` are ordered by `v`, the smaller is dominated by (D1), and
that is `dom` over `H`, nothing else. The `CLONE_SUSPECTED` flag is a side
effect, not state.

"LWW over types correctly rejected": F rejects it on blast-radius grounds,
which is right, but it is also rejected mathematically. The only
upward-closed cross-type rule is full cross-author domination by `v` on
`(ent, field)` for every type (that is S). Any mixed rule fails:

```
x : PUT (E,f,PNCOUNTER) v=(10, A, 1)
y : PUT (E,f,LWW)       v=(20, B, 1)      "LWW wins over typed": y dom x
z : PUT (E,f,PNCOUNTER) v=(30, C, 1)      z dom y (z is newer than the LWW record)
¬ z dom x: typed, different authors.     T2' fails; F({x,y,z}) depends on order.
```

### Counterexample 1 — T16 is false and the PNCOUNTER view overflows: per-cell state is unbounded

Per-author domination means nothing ever dominates a typed record except its
own author's later record or a `DEL`. S admits any well-formed record signed
by any key (G notes the gap). So one member relaying records under `N`
ground keys gives one typed cell `N` frontier records, none dominated.

```
cell c = (E, likes, PNCOUNTER)
p_i : PUT c (inc = 2^48−1, dec = 0) v=(1000, K_i, 1)   for i = 1 … 2^20, K_i freshly ground keys
```

`|{p ∈ F : cell(p) = c}| = 2^20`, against T16's bound 1088; the view `Σ inc` is
`2^68`, against T13's "`|Σ| < 2^59` fits `i64` with no read-time overflow
check". The same holds with no malice: a roster that rotates 64 members per
generation without `REVOKE` has authors-ever `64 × gens`. Under S the same
flood costs one surviving record per cell (cross-author domination); F
converted a bounded cell into an unbounded one. The fix is G's `W`
(admission `author ∈ W`, grow-only), which bounds a cell by `|W|`, and an
`i64` saturating fold or a smaller `inc` width; with `W` the design is sound.

The delete-reset race F documents (`x: inc=100 @100 by A`, `d: DEL @200 by
B`, `z: inc=101 @250 by A` who never saw `d`; `F = {d, z}`, counter reads
101) is confirmed deterministic and confirmed ugly; the app must be told.

### Obligations rejected

- **T16**: false (CE 1). **T13**'s overflow clause: false (CE 1).
- Everything else stands; T2', T15 are correct.

### H5/H6

`ftype ≤ 4` on a `u8` is a runtime check, as `n_members` is; `(0,0)` is an
ordinary state (good); the per-cell bound is derived from the roster and is
false without `W`.

### Hardest theorem

T7; T15 is a day in Lean (permutation-invariant fold for `Nat` sum/max and
list union).

### Scores

C1 4 · C2 3 (per-cell flood by relayed keys; overflowing view) · C3 2
(O(authors-ever) per typed cell, unbounded without `W`) · C4 4 · C5 3 · C6 4
· C7 4 · C8 4 · C9 3 (T16/T13 false; bound by roster, not by type).

---

## 4. Candidate G (multi-value cells with causal parents)

### What survives

The one-clause change (`q.author = p.author` on put/put) is a sub-relation of
S's `dom` whose restriction to one author is a sub-order of `v`, so T2' and T3
hold; I checked the mixed cases (same-author chain under a `DEL`). The
rejection of naming-as-domination is correct and is the clearest statement in
the round of why views must not prune.

`live(c)` is deterministic. When `parents` name records a replica never
held, `named(p)` quantifies over `sibs(c) ⊆ F`, so a hash naming nothing
hides nothing, and if the named record arrives later it is hidden then. The
view is a function of `F` in every case (T5).

### Counterexample 1 — a forged-height `PUT` at `maxh` from a larger key cannot be deleted

G's H8 table says a forged height "can pin only a DEL" and "only entity
re-creation". A `PUT` at the ceiling pins against every `DEL`:

```
m : PUT (E,f,"junk") v=(maxh, M, 1) {}         pk_M > pk_O
d : DEL  E           v=(maxh, O, 5)             clamped; d < m, so ¬ d dom m
F = {m, d};  live(E,f) = {m};  exists(E) = true
```

`O` can hide `m` by writing `(maxh, O, 6) {m}` (then `live = {o}`), but
cannot free `m`'s bytes or delete `E` until a roster refresh, and `M`
re-pins after each. The bound is S's; the claim is wrong. `sync_delete`
returns `OK` here (status is checked against `deleted_at` only), so the
app is told the entity is deleted when it is not: a status hole.

### Counterexample 2 — `W` makes convergence depend on root policy and is not reconciled

`W` is "updated from `members` of every ROSTER ever applied"; a latecomer
reconstructs it from the rosters it applies, and dominated rosters are not
re-sent. G requires the root to remove a member only by `REVOKE` + roster so
that the key reaches latecomers through the never-dominated `REVOKE`. That is
policy, not construction: a root device running a roster edit that omits the
`REVOKE` (or a restored root) produces a permanent split.

```
R3 : ROSTER gen=3 members={O, X}       R4 : ROSTER gen=4 members={O}   (no REVOKE for X)
d  : DEL E v=(h=5, X, 9)               p : PUT (E,f) v=(h=2, O, 1)

A applies R3, p, d, R4:  X ∈ W_A; d dominates p (freed).                F_A = {R4, d}
B joins after R3 is dropped everywhere; applies R4, p:  X ∉ W_B.        F_B = {R4, p}
A↔B: A offers d, B refuses (author ∉ W);  B offers p, A drops it.      divergent; nothing a later roster does re-adds X
```

Same fault class as S CE 1 but with no root-liveness repair short of an
explicit `REVOKE(X)`. Fix: join `W` in HELLO (`∪`), or make root additions
and member additions never-dominated records.

### Obligations rejected

- The H8 table's "forged height pins only a DEL" (CE 1).
- **T4** in exchange form, for the same reason as S, with `W` added (CE 2).

### H5/H6

`|W| ≤ 2048` is reached by honest use (32 full rotations of 64 members) and
its attainment means re-founding; `height = maxh` regime; the `named` bitmap
is derived per cell but recomputed, not stored, so it is a cache, not an
invariant. `n_parents = 0`, `void = 0` ordinary: good.

### Hardest theorem

T7; T-G1 needs a finite-acyclic-relation-has-a-maximum lemma, a day.

### Scores

C1 4 · C2 4 · C3 3 · C4 4 · C5 3 · C6 3 (two unreconciled registers, one
policy-dependent; an acyclicity hypothesis discharged on paper) · C7 4 · C8 4
(the compare-and-set is the best conflict surface in the round) · C9 3.

---

## 5. Candidate H (root-signed snapshots)

### What survives

T2' for the five-arm `dom` holds, and I checked it harder than H did. The
data cases are down-sets: `p' < p ⇒ p'.t ≤ p.t`, so `s dom p ⇒ s dom p'`;
`p < d ⇒ p.t ≤ d.t`. The SNAP chain is transitive because `⊒` is pointwise
`≥` on a `⊇` range and the `(gen_s, h)` tie-break is used only when the kill
functions are equal, where it is a total order. A backup-restored root's
chunk either is covered (dropped) or is not (both stay, kill sets union):
no divergence. Two chunks with overlapping, non-nested ranges both stay and
both kill; the kill predicate of `F` is the union, monotone, convergent. The
16-byte-variant refutation is correct. Convergence of `(F, maxceil,
roots_ever)` holds exactly as for S, with the same unreconciled-register
caveat (now three registers).

T11' is true as stated: once `s ∈ F_X`, every `x` with `x.t < lvl_s` is absent
from every reachable state. It is a safety theorem with no clock in it. The
question is what it is a theorem *about*.

### Counterexample 1 — an honest restored root kills a live, re-created, fully synced entity

T15 ("the root never kills a cell it shows") is relative to the root's own
`F_R`. A root restored from backup has a stale `F_R`, and the design's row
for it says only that "no record wrongly returns". Records wrongly die:

```
backup of root at time 2000:  F_R = { d = DEL E v=(1000, B, 1) }          (E deleted)
later, everywhere:            p = PUT (E,f) v=(3000, X, 1)                 (E re-created)
current root's chunk:         s  : w=5000  lvl=[(E, 1001)]                 (absorbs d, keeps p; T15 holds for s)
restored root (clock correct, now=lag+4000) snapshots before syncing:
                              s_r: w=4000  lvl=[]                          (E ¬exists in F_R ⇒ level w)

s ⊒ s_r ?  lvl_s(E)=1001 ≥ lvl_sr(E)=4000 fails.   s_r ⊒ s ? w 4000 ≥ 5000 fails.   Both stay in F.
p.t = 3000 < lvl_sr(E) = 4000  ⇒  p dominated on every replica, bytes freed.
```

Honest `X` was never offline; every replica agreed on `p`; a root key that
A1 calls honest destroyed it, and no later SNAP can undo it (`⊒` only
grows). `X` sees `SNAP_DOMINATED` only while it still holds `p`; if `X`'s
device is gone, so is the data. The unstated assumption is "a root snapshots
a range only from a frontier containing every record any replica holds on
that range": the gossip-completeness assumption S needed for A4, moved from
the drop rule into the root, with the failure mode changed from resurrection
(user re-deletes) to destruction (user re-types, if anyone can). **"A4 is
removed" is a relocation, not a removal**, and C1 = 5 is not earned.

### Counterexample 2 — the straggler window for a clockless or slow-clocked writer is one SNAP period, not `snap_lag`

The task asked whether honest new data can be silently killed. Yes, and not
only after 180 days. A device holding the latest SNAP `s` (watermark `w`)
with `now_local < w` (clockless: `now = 0`) chases to `t = w` exactly. The
root's next chunk has `w' > w`. If the write reached the root, the root
lists the entity with `level = max(0, lvl₀) = w` and it survives (T15). If
it did not, the entity is unlisted and gets `w'`:

```
device D (clockless) holds s (w=5000); creates E_new:  t_emit = max(0, snap_floor=5000) = 5000
D syncs with Y (not the root).  Root re-snapshots the range (any deletion in it suffices):  s' w=6000, E_new unlisted
s' reaches Y:  5000 < 6000 ⇒ E_new's cells freed at Y.   D re-PUTs at t = 6000 on next sync … 
```

A clockless device that reaches the root less often than the root snapshots
the range **can never create a durable entity**; each re-`PUT` lands on the
previous watermark and the next chunk passes it. A clock slow by `δ ≥
snap_lag` is the same case; for small `δ` the window is S's 180 days. H's
"chases to the level, the intended Lamport behaviour" is exactly what makes
clockless devices lose.

### Counterexample 3 — a write that is dead on arrival is reported `OK`

If `snap_floor(ent) > maxceil` (a root listed `(ent, L)` with `L > maxceil`,
legal, and also how a root could kill a ceiling pin), `t_emit` chases to `L`
and clamps to `maxceil < L`: the record is dominated by the SNAP the writer
already holds, and `status = OK` because `SHADOWED` is checked against
`floor` only. An H8 fault (an entity unwritable until a roster raises the
ceiling, with no signal), not a convergence fault.

### Obligations rejected

- **C1 = 5 / "A4 removed"**: rejected (CE 1, CE 2); the assumption moved.
- **T15** as a safety claim: true only relative to a complete `F_R`; false for
  a restored or partitioned root (CE 1). The H8 row for a restored root is
  incomplete.
- **T8 restated**: the `snap_floor − 1 < maxceil` hypothesis excludes CE 3
  rather than bounding it; the emission rule needs a `SNAP_SHADOWED` status.
- **T11'**: accepted as stated.

### H5/H6

Best in the round for the drop rule: no `now_local` in state, `w = 0` and
`floor = 0` ordinary. Residuals: three unreconciled registers; `n_lvl ≤
2 900` on a `u16` is a runtime check; "unlisted ⇒ `w`" is a definition, as
claimed, but `exists` and `ROSTER_eff` remain derived views; the SNAP
construction (a policy with a clock) is inside the trusted core because
T15/T16 quantify over it.

### Hardest theorem

T2' with `lvl` as an association list and `⊒` as a merge-walk that must be
proved to decide the pointwise statement: a week, as H estimates. T7
unchanged.

### Scores

C1 3 (lattice sound; the headline assumption removal is a relocation whose
failure destroys synced data) · C2 2 (root is a one-record wipe; a revoked
root keeps killing; clockless writers livelock; dead-on-arrival writes read
`OK`) · C3 4 · C4 4 · C5 3 · C6 3 (five-arm `dom`, merge-walk, and a clocked
root policy inside the trusted core) · C7 4 · C8 2 · C9 4.

---

## 6. Module I (IBLT first round)

Decode failure is detectable: a cell with `count = ±1` is accepted only if
`check_xor = check(key_xor)`, so a false peel passes with probability
`2^-64` per cell; a falsely decoded id is then looked up by the side that
supposedly holds it, which does not, and the final `fp` comparison catches
the rest. No state is written on the sketch path; the HAVE round and the
16-way fallback carry T7's correctness as before. A malicious peer can force
the largest sketch and a fallback every session: bytes, not state. `|F_A| −
|F_B|` is a poor estimator of the symmetric difference, so the fallback will
be common under symmetric divergence; cost only. Accept. Scores (where
meaningful): C4 5 · C6 4 · C7 4 (200 KiB resident) · C9 4.

---

## 7. Module J (multi-root, per-signer rosters)

### What survives

Per-signer roster domination is a restriction of a total order within a
signer, so T2' holds (same argument as F's per-author clause). The
"`unauth` must be a view" argument is correct and is the D-CE-2 lesson
applied properly. `ROSTER_eff` is a function of `F` (T18).

### Counterexample 1 — `roots_ever` splits a latecomer from everyone, permanently

`roots_ever` is a stored register fed by *applied* rosters; a roster that
added a root and was then dominated (per-signer, by the same signer's later
roster that removed it) never reaches a latecomer.

```
R1 (founder) : ROSTER gen=5 roots={R1, R2}          R2 ∈ roots_ever on A
R2           : REVOKE(subject=X, from_t=…)          admitted on A (R2 ∈ roots_ever); never dominated; void(X) on A
R1           : ROSTER gen=6 roots={R1}              dominates gen 5 (same signer) everywhere

B joins after gen 5 is dropped:  roots_ever_B = {R1};  R2's REVOKE inadmissible at B, re-offered forever.
F_A ∋ REVOKE(X),  F_B ∌ REVOKE(X).   No honest action re-adds R2 to roots_ever_B except re-listing R2 as a root.
```

`REVOKE`s are never dominated precisely so that they are never lost; J's
admission loses them anyway. Same fault as S CE 1 and G CE 2, but with no
A3 repair. Fix: join `roots_ever` in HELLO, or make root additions a
never-dominated record kind.

### Counterexample 2 — a revoked root keeps minting admissible roots

Admission is `signer ∈ roots_ever`, grow-only; `root_void` is a view. A
revoked (stolen) root `R2` issues `ROSTER roots={R2, E1, E2, E3}`: admitted,
`roots_ever ∪= {E1, E2, E3}`; `E1` (not revoked) issues `gen = 2^48−1`, which
is `ROSTER_eff` until revoked; each `REVOKE` costs the honest root one record
and the attacker mints the next. Bounded by `|roots_ever| ≤ 256`, after
which the collection is re-founded, which is what H already concedes for a
stolen root, but the design says nothing about the chain. A bytes-checkable
monotone fix exists: root *additions* are admissible only under the founding
key's signature (or a fixed-at-founding quorum), member rosters under any
root.

### Scores

C1 3 (CE 1 is a permanent split from an honest sequence) · C2 3 · C5 4 (root
loss is recoverable) · C6 3 · C9 4.

---

## 8. Composition

**The rule.** Composing two modules is safe iff every kill predicate of the
composed `dom` is still a down-set of the composed record order on its key.
This decides every pair below.

**E + H (or G + H): not convergent.** H kills by `t`; E orders by `height`
first. A `t`-prefix is not a down-set of `(height, t, …)`:

```
p' : PUT (E,f) v=(height=1, t=9000, A, 1)      A's clock ahead
p  : PUT (E,f) v=(height=2, t=1000, B, 1)      B saw p' and chained above it; honest clock
s  : SNAP  E ∈ range, lvl(E)=5000

p dom p' (height);  s dom p (1000 < 5000);  ¬ s dom p' (9000 ≥ 5000).   T2' fails.

Replica X applies p', p, s:   {p'} → {p} → {s}
Replica Z applies p, s, p':   {p} → {s} → {p', s}        same records, F_X ≠ F_Z
```

`F({p', p, s}) = {s}` but there is no maximal dominator of `p'` in it, so
the sandwich lemma fails and apply-with-GC is order-dependent; a replica
that holds `{p', s}` re-seeds `p'` into every replica that had dropped it.
H can only be composed with a height order if the SNAP kills by height, and
then the watermark has no time meaning: a straggler's new entity has
`height = 0` and dies at the next chunk, so the 180-day grace is gone and a
chunk must list every live entity. H is coupled to the wall-clock order.

**F + H: composes.** Per-author domination is a sub-relation of S's, so
`s dom p, p dom p'` (same author) gives `p'.t ≤ p.t < lvl`. The root's level
construction must take `min t` over *all* authors' live records on the
entity (T15 adapts).

**F + E: composes.** F's "one order, `v`, everywhere" is satisfied by E's `v`;
the own-chase moves to `height`.

**F + G: coherent.** G's siblings are F's MVREG plus parents; for the other
four types G's per-author clause *is* F's (D1), and G's `W` is the fix F
needs (§3 CE 1).

**J, I with anything: orthogonal.** J touches only the authorization kinds;
I touches no state. J's `roots_ever` fault, S's `maxceil` fault and G's `W`
fault share one fix: the session HELLO carries every grow-only register and
the join is componentwise `(max, ∪, ∪)`.

**Recommended composition (mathematically strongest).** **S′ + I + J′**,
with **F+W** as the typed-field extension where applications need counters
or sets, and **neither E nor H**:

- S′ = S with (i) `maxceil` joined in HELLO, which makes T4's exchange
  clause true; (ii) A4 restated as "every `DEL` reaches every member within
  `del_ttl` of `d.t`"; (iii) G's `W` register, joined in HELLO, as the
  data-record admission bound, which closes the unrostered-key relay gap
  even without typed cells.
- J′ = J with `roots_ever` joined in HELLO (or root additions as
  never-dominated records) and root additions admissible only under the
  founding key.
- F+W = F with `author ∈ W` admission and a saturating `i64` fold.

Assumption list for convergence: A1 (Ed25519 unforgeable; founding key
honest), A2 (BLAKE2b collision-resistant; 4096-bit sum k-sum hard), and the
protocol obligation that every session joins the registers. For the ceiling:
A3 (some root refreshes within each horizon). For tombstone freeing: A4′ as
restated, with resurrection (not destruction) as its failure mode. A5
(writers persist `seq`; violations detected). No clock assumption anywhere in
the lattice. The Lean delta over `Frontier.lean` is the `W` component of
`State` (same shape as `ceil`), F's `dominates` clause with `cell_author_unique`,
and J's per-signer roster arm; T7 remains the long pole.

---

## 9. Ranking

| Rank | Design | C1 | C2 | C6 | C9 | Most damaging counterexample |
|---|---|---|---|---|---|---|
| 1 | **S** frontier store | 4 | 4 | 4 | 4 | `maxceil` is never reconciled: a restored root's equal-`gen` roster that wins by `h` leaves `p@4500` admissible at A and refused at B after every exchange; fixed by one HELLO field |
| 2 | **E** height-first | 4 | 4 | 4 | 4 | A clockless deleter's `DEL` (`t=0`) expires on arrival everywhere and is re-offered forever: the entity flaps between deleted and present with no A4 violation |
| 3 | **F** typed fields | 4 | 3 | 4 | 3 | `2^20` relayed ground keys give one PNCOUNTER cell `2^20` undominated records and a `2^68` sum; T16 and T13's overflow clause are false; fixed by G's `W` |
| 4 | **G** causal multivalue | 4 | 4 | 3 | 3 | A member removed by roster without `REVOKE` is in `W` at old replicas and not at latecomers: its `DEL` is held on one side and refused on the other, with no root-liveness repair |
| 5 | **H** snapshot GC | 3 | 2 | 3 | 4 | An honest restored root's chunk (`w=4000`, `E` unlisted) kills a re-created, fully synced `PUT@3000` on every replica, irreversibly; "A4 removed" is A4 moved into the root with destruction as its failure mode |
| mod | **I** IBLT round | — | — | 4 | 4 | None; decode failure and false decode are both caught before any state is written |
| mod | **J** multi-root | 3 | 3 | 3 | 4 | A root added at gen 5 and removed at gen 6 is absent from a latecomer's `roots_ever`; its never-dominated `REVOKE` is refused there permanently |

**Verdict.** The single most optimal design is the baseline S, repaired in
two lines and extended by the modules that add no new kill predicate: carry
the grow-only registers in the session handshake (which makes T4's exchange
clause true and is the same fix for G's `W` and J's `roots_ever`), restate A4
as a propagation bound, adopt G's `W` as the admission bound for data records,
adopt I unchanged, and adopt J with root additions gated by the founding
key. F's typed cells compose with that core and should be taken when an
application needs them, after `W` is in place. E is not wrong, but it buys
sub-ceiling pin hygiene with a tombstone clause a supported device class
cannot satisfy, and it cannot be composed with H. H's lattice is sound, but
its central promise does not hold: the liveness assumption it removes from
the drop rule reappears as a completeness assumption on the root, its
failure erases synced data instead of resurrecting deleted data, clockless
writers livelock against the watermark, and its `t`-keyed kill predicate is
incompatible with every height-ordered variant. A GC rule should be a
down-set of the order it lives under, and a root should only be able to free
what every replica already agrees is dead; H's SNAP satisfies the first
condition and not the second.
