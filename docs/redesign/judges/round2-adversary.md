# Adversarial judge, round two: attacks against E, F, G and H (+I, +J)

Stance as in round one: find what a misbehaving or malicious party can do,
with a concrete trace and the resulting state per replica. Notation: `M` =
malicious authorized writer, `X` = member removed at `T`, `L` = lagging honest
replica, `U` = up-to-date honest replica, `O` = owner / root, `S` = the
baseline frontier store of DESIGN.md. "Admitted" means the candidate's own
text already states the finding.

**Common ground, scored once.** All four keep S's lattice and inherit its
residuals, which are the bar: a writer overwrites or deletes any cell it
can see; a thief's pre-revocation `DEL`s are irreversible; a ceiling pin by
a ground key (round-one A-1) is a sure win until the next refresh and
re-pinnable until `REVOKE`; a revoked writer's records stay in `F` as
`void` until the owner `DEL`s each entity (A-2); inadmissible records are
re-shipped every session (A-6); a straggler offline longer than `del_ttl`
resurrects stale fields; a stolen root key is the owner. S fixed A-3, A-4,
A-5, so S scores C2 3 / C5 3 here. Adversaries (a)–(h) were run against
each design; I report where a design differs from S and say "as S"
otherwise.

---

## Candidate E: height versions

### Attacks that work

**E-1. The un-delete gadget: a zero-`t` `DEL` erases a tombstone and leaves no
trace (a, d, h).** Expiry is `now_local ≥ d.t + del_ttl` with `d.t` writer-
chosen and unbounded by admission, while domination is by `height`. So a
`DEL` can be *higher* than the owner's tombstone and *expire instantly*.

```
O : DEL(E)            v=(h=7,  t=now,  O, 41)      -> E's fields freed, tombstone lives del_ttl
M : DEL(E)            v=(h=8,  t=0,    M, 12)      -> dominates O's DEL (8 > 7); O's DEL dropped everywhere
                                                      apply-then-expire: now ≥ 0 + del_ttl -> M's DEL dropped at once
                                                      F|E = {}  on every replica that received it
M : re-offer PUT(E, name, "Ada")  v=(h=3, t=…, A, 7)   (honest A's original signed record, which M kept)
                                                    -> nothing on E dominates it: admitted. E is back, signed by A.
```

The owner's deletion is reversed on every replica with the original honest
signatures, and the record that did it is in no replica's `F` (attribution
survives only in logs that compaction rewrites). S cannot do this: a
dominating `DEL` must chase to `t > d_O.t`, so its expiry is never earlier
than the one it replaced. Any straggler or relay replaying old `PUT`s
completes the attack once `M`'s `DEL` has expired. Bounded (one entity per
record), reversible (owner re-`DEL`s), unattributable after the fact,
repeatable until `REVOKE`. §6 admits the honest-clock version and does not
notice that the deleter chooses it. Implementation hazard in the same
clause: `x.t + del_ttl` with `x.t = 2^48 − 1` wraps a u48 and turns an
immortal tombstone into an instant one; compute it in u64.

**E-2. Immortal attacker tombstones come back after the owner's cure expires
(d, g, h).** `DEL(E) v=(h, 2^48−1, M, …)` never expires (admitted). The cure
is `DEL(E) v=(h+1, now, O, …)`, which dominates it and expires at `now +
del_ttl`. After that, any replica still holding `M`'s `DEL` (a straggler, or
`M` itself before revocation) re-offers it and it is re-admitted: nothing
dominates it any more. So the immortal tombstone is not removable, only
re-shadowed every `del_ttl` by another owner `DEL`, forever. Harm is storage
(147 B per entity) and the pin on re-creation if it sits at the ceiling;
bounded by `M`'s record count.

**E-3. Alarm-driven refresh is an attacker-paced root duty (d).**
`near_ceiling` fires above `maxceil − 2^27`; the root refreshes at most
hourly. Roster at `T`; at `T + 1 s` `M` writes `PUT(c_i) v=(maxceil, 2^48−1,
M, …)` for `K` cells; honest writes to `c_i` are `SHADOWED` (emitted, lost)
until `T + 1 h`; `M` re-pins at `T + 1 h + 1 s`. The cells are unwritable
99.97% of the time until `REVOKE`, and the attacker, not the schedule, sets
the root's work rate; a root offline at night leaves pins standing with no
clock to heal anything. S's pin is the same with a calendar refresh, so not
worse. Height exhaustion by this route: `2^20` hourly refreshes is 120 years
(30 with J's four roots). Bounded.

**E-4. Chains beat clocks is the attacker's default (d).** `height = floor +
2^20` on every cell `M` rewrites: no alarm, no after-effect, and every
concurrent honest edit during propagation is silently lost. Equal in power
to S's far-future `t`, better in after-effects; §8 describes it as an
honest-user oddity.

### Attacks the design defeats
- Far-future `t` on a `PUT`: no chase on `t`, no Lamport-ization, `far`
  flags exactly the attacker's records, cleanup tombstones live `del_ttl`
  not `δ + del_ttl` (A-2's year-long cost is gone). (a, d) better than S.
- Far-behind clock: loses equal-height ties only. (a) defeated except E-1.
- Backup restore / clone: as S. (b, c) defeated.
- Forged height: a pin bounded by the ceiling, never a validity failure;
  no semantics at the maximum; `CEIL_EXHAUSTED` refuses. Causal-length
  saturation does not recur. (d) defeated.
- Removed member: as S; via a laggard, one pin window plus E-2. `from_t` is
  accurate for honest-clock thieves. (e) as S.
- Stolen root: `ceiling_h = 2^48 − 1` makes pins permanent; re-found. (f)
  as S. Relay: as S. (g)
- Straggler: resurrects after `del_ttl` as S; its own offline edits now lose
  to any two-write chain. (h) slightly worse for the straggler's own data.

### Honesty
Good. §8 states chains-beat-clocks, no natural end to ceiling pins, the
consumable height space, clock-dependent tombstone durability and immortal
tombstones. It misses that the deleter *chooses* its tombstone's lifetime
(E-1), that the cure for an immortal tombstone expires while the disease does
not (E-2), and the u48 overflow in the expiry clause.

### Scores
C1 4 (same theorem, no clock assumption; T11 still liveness). **C2 3**
(sub-ceiling pins and cleanup tombstones are genuinely better than S; the
un-delete gadget and un-removable immortal tombstones are new and the
former is unattributable after expiry). C3 4 (+6 B per cell; tombstone term
bounded by honest time). C4 4 (unchanged). **C5 3** (as S; `from_t`
accuracy improves, back-dating still escapes). C6 4 (Lean delta is small
and the file text confirms it). C7 4. C8 3 (apps must learn that chain
length, not time, decides). C9 3 (the `height = maxceil` regime plus the
expiry clause's overflow hazard on an unbounded `t`).

---

## Candidate F: typed lattice fields

### Attacks that work

**F-1. A typed cell cannot be repaired by anyone but the author or the
owner's `DEL` (d).** Per-author domination (D1) means an honest writer
cannot overwrite `M`'s contribution. Trace:

```
M : PUT(E, tags, GSET)  {65 535 B of junk elements}   v=(t, M, 5)
U : PUT(E, tags, GSET)  {"work"}                      v=(t', U, 9)   -> both in F; view = junk ∪ {"work"}
U : (no record of U's can remove M's elements)
O : DEL(E)                                            -> every author's state zeroed, honest ones included
```

Same for `MAXREG`: `m = 2^64 − 1` pins the max for everyone until `REVOKE`;
for `PNCOUNTER`: `(0, 2^48 − 1)` drags a shared count to `−2.8 × 10^14`.
All attributable, all ending at `REVOKE` with no owner `DEL` (the design's
real gain); but the only in-band cure before revocation is deleting the
entity, which resets the honest authors too, and the only cure for a
*buggy* honest device is to revoke it. In S the owner could overwrite the
junk in place. Admitted in part ("no author can retire another's stale
value").

**F-2. Back-dated typed records survive `from_t`; the cure is `from_t = 0`
(e).** `void` is `t ≥ from_t` and same-author domination is by full `v`,
so `M` writes every record at a constant low `t` with increasing `seq`:
each dominates its predecessor by `seq`, none is voided by any `from_t`
above it, and `M`'s `(0, 2^48 − 1)` stays in the sum after `REVOKE(M,
from_t = T)`. The owner's answer is `from_t = 0`, which voids everything
honest `M` ever contributed: "lost phone from the moment it was lost" does
not exist against a deliberate thief. S's back-dating residual, except that
in F the owner cannot overwrite the record either (F-1). Not admitted.

**F-3. Type conflict as keepalive and amplifier (d).** `exists(ent)` is
true if any typed cell has a non-void record. `M` writes `PUT(E, f, ftype)`
for `ftype ∈ {1..4}` on every field: four extra cells per field, each
≤ 64 KiB, retained until `DEL` or `REVOKE`, keeping `E` in `scan` after
honest writers emptied the LWW cells. The owner's `DEL` dominates all (D2):
S's re-create tug of war with 5× the storage per field. Not mentioned.

**F-4. Reset-on-delete is not an inflation lever but a resurrection one (b,
h).** `M` gains nothing by writing after a `DEL` (its state is arbitrary up
to `2^48` anyway). A straggler's pre-`DEL` counter record arriving after the
tombstone expired adds its lifetime total to the restarted cell; a relay
withholding one `DEL` from one member produces the same. Admitted (§8).

### Attacks the design defeats
- Clock ahead or behind on a typed cell: no effect on other authors. (a)
  defeated on typed cells; as S on LWW cells and `DEL`.
- Pins: a `PUT` never dominates another author's typed record; round-one
  A-1 survives only on `DEL`. (d) better than S.
- Backup restore / clone: regresses only its own contribution, detected at
  first sync; a clone loses increments, never double-counts. (b, c) defeated.
- Removed member: post-`from_t` typed contributions leave every view at
  `REVOKE` with no owner cleanup; bytes stay until `DEL`; F-2 is the limit.
  (e) better than S for views.
- Stolen root, root restore, relay, fingerprint: as S. (f, g, h)
- Bounds: `ftype ≤ 4`, `inc, dec < 2^48`, GSET ≤ 65 535 B are decode
  refusals; the sum fits i64 for 1 088 authors. (g-metadata) bounded.

### Honesty
Best of the four. §8 lists non-lattice monotonicity, delete-reset races,
O(authors) per cell, the register-map limitation, clone loss and the
inherited S residuals, and refutes its own two tempting shortcuts as
theorems. It omits the back-dating interaction with `from_t` (F-2), the
exists-keepalive amplification (F-3), and that "repair" of a typed cell is
`DEL` or `REVOKE` and nothing else.

### Scores
C1 4 (S's theorem, generic core reused; T2' re-proved with author equality).
**C2 4** (on typed cells a writer cannot pin or overwrite anyone and its
contribution leaves every view at `REVOKE`; minus: repair is destructive,
storage retained until `DEL`). C3 3 (one record per author ever per typed
cell, 114 B keys). C4 4. **C5 3** (view purge at `REVOKE` is better than S;
back-dating forces `from_t = 0`; bytes retained). C6 4. C7 4. C8 4 (counters
and sets without app tricks; the app must understand reset-on-delete and
`TYPE_CONFLICT`). C9 4.

---

## Candidate G: causal multi-value cells

### Attacks that work

**G-1. Ceiling exhaustion in weeks, not centuries (d).** The root "sets
`ceiling_h := max height held + 2^32` and refreshes when any held height
exceeds `ceiling_h − 2^31`"; "2^16 refreshes fit in u48". No rate limit is
stated. Trace: after every roster, `M` writes one `PUT(c) height = maxh`;
the root refreshes; `M` repeats. With a root that refreshes within a minute
of noticing, `2^16` refreshes take 45 days and the collection is re-founded
(`CEIL_EXHAUSTED`); with E's hourly limit, 7.5 years. Each refresh is a full
roster to every replica. E's `2^28` step with a stated limit gives 120
years; G's `2^32` step with none gives weeks. Not admitted.

**G-2. Sticky siblings: an honest writer cannot free an attacker's bytes
(d, g).** A resolved sibling is retained (§6, correctly, for T3). So:

```
M : PUT(E, notes, 65 535 B)  v=(0, M, 1) {}
U : PUT(E, notes, "ok")      v=(1, U, 4) {M.h}      -> live = {U}; M's 64 KiB stays in F on every replica
U : (any number of rewrites)                        -> M's record is still U-named, still 64 KiB, still in F
O : DEL(E)                                          -> the only thing that frees it; U's "ok" goes too
```

Repeat over `N` cells: `N × 64` KiB replicated and immune to honest
overwrite. S frees the loser's bytes on arrival. Admitted as a cost of
contested cells; not stated as an attacker's storage lever that only `DEL`
or `REVOKE` plus `DEL` ends.

**G-3. A revoked writer's record keeps hiding honest values (e).** `named(p)
:= ∃ q ∈ sibs(c) : p.h ∈ q.parents`, and `sibs` includes `void` records.
Trace: `M` writes `q` naming every honest sibling on `c`; `O` issues
`REVOKE(M, void = 1, from_seq ≤ q.seq)`. `q` is flagged `VOID`, but
`live(c) = {q}` still: every honest value on `c` is hidden until its author
rewrites the cell; for an author who has left, forever. `M` does this on
every cell in one pass before revocation. The design's remedy ("reversible
by a re-`set`") assumes the hidden author is still around. The fix (`named`
over non-void siblings) is one word and is not in the text.

**G-4. The un-delete gadget, in `issued_t` form (a, d, h).** DEL order is
`(height, author, seq, h)`; expiry reads `issued_t`, which is never compared
and never admitted against anything. E-1's trace works verbatim with
`issued_t = 0`: `M`'s `DEL` above the owner's dominates it, expires at once
everywhere, and the entity's original signed `PUT`s are re-admitted from any
holder. Not admitted; §6 only notes the far-future `issued_t` case.

**G-5. Forged parents and heights (d).** Naming non-existent hashes is
harmless. Naming every honest sibling hides all of them in one record
(G-3's pre-revocation form); the honest reply is a rewrite, a tug of war
with a visible trail. `HEIGHT_SUSPECT` is raised only where a named parent
is held, so a `PUT` that names nothing and claims `height = maxh − 1` is
unflagged everywhere, wins `pick`, and forces every honest write on the
cell to `maxh` (G-1's alarm). Admitted in substance.

**W register.** Only root-signed records feed `W`, so a member cannot
exhaust it. A stolen root can (32 rosters of 64 fresh keys, or 2 048
`REVOKE`s), but forces re-founding in S anyway; a restored root lists real
members and adds nothing. Honest key churn over a collection's life is the
real bound.

### Attacks the design defeats
- Any clock: nothing compared. (a) defeated except G-4.
- Shadowing a `PUT`: impossible; A-1 survives only on `DEL`s at `maxh` from
  a larger key, until refresh. (d-pin) best of the four.
- Hiding an honest value silently: impossible; the hider's record carries
  the hash it hides. (d-hide) defeated with attribution, modulo G-3.
- Backup restore / clone: one sibling per key per cell; resolutions
  re-surface, never values. (b, c) defeated.
- Removed member: as S; via a laggard, one `DEL` pin window plus G-3. (e)
- Stolen root: `maxh = 2^48 − 1` pins only `DEL`s; `W` exhaustion;
  re-found. (f) slightly better than S.
- Relay, straggler: as S; a straggler's offline edits appear as attributed
  siblings instead of losing silently. (g, h)

### Honesty
Good on its own mechanism (retention, no time, DEL pins, parent lists,
cumulativity as discipline, `W` growth, advisory heights). It omits the
refresh-rate exhaustion (G-1), that retention is an attacker's storage lever
(G-2), that `void` records still hide (G-3), and the `issued_t` gadget (G-4).

### Scores
C1 4. **C2 3** (no PUT shadowing and no silent hiding are real; against
them, bytes that only `DEL` frees, void namers that keep hiding, a ceiling
burnable in weeks, and the un-delete gadget). C3 3. C4 4. **C5 3** (as S;
G-3 gives a removed member a lasting, if reversible, effect S lacks). C6 4.
C7 4. C8 4. C9 4.

---

## Candidate H: root-signed snapshots (+ I, + J)

### Attacks that work

**H-1. A root key is a one-record wipe *and* brick, and revocation does not
stop it (f).** Admitted as a wipe; the brick is not. Trace, root key `R`
stolen:

```
R : SNAP(ns, range = all, w = 2^48−1, lvl = [])
    -> every PUT and DEL in ns has t < 2^48−1: dominated, bytes freed on arrival at every replica
U : PUT(E, name, "x")   t_emit = max(now, snap_floor = 2^48−1) = 2^48−1 > maxceil -> clamped to maxceil
    -> maxceil < lvl: dominated by the held SNAP on arrival, at the writer and everywhere. Nothing is ever live again.
```

The only state in which a write can survive is `maxceil = 2^48 − 1`, where
every write ties at the ceiling by ground key. Under J, a second root issues
`REVOKE(R, from_gen)`, which voids `R`'s rosters; but SNAP admission is
`signer ∈ roots_ever`, grow-only, with no `root_void` clause, and there can
be none: refusing a SNAP another replica already applied is the
non-monotone trap of §5. So `R`'s SNAPs are admitted forever, through any
laggard or relaying member; a thief who issues the wipe a day after being
revoked succeeds. `R`'s `ceiling_t = 2^48 − 1` is likewise permanent.
Recovery is re-founding; the countersignature rule of §8 is the only
bytes-only check that could help and is outside the design. Against H8
("no single record may permanently brick a collection") this is a single
record; the defence is A1 (roots honest), which J weakens by making root
keys plural and revocable without making SNAPs revocable.

**H-2. `roots_ever` is a grow-only set a thief fills in one pass (f, J).**
Any admitted roster does `roots_ever ∪= r.roots`, dominated or void or not.
`R` issues a roster with 4 fresh root keys, then rosters signed by those, 4
per roster: 64 rosters reach 256 and the collection is re-founded, and
every minted key can sign SNAPs (H-1) and raise `maxceil`. Revoking them
costs one `REVOKE` each and does not stop their SNAPs. J's "recoverable iff
`n_roots ≥ 2`" holds only against a thief who does nothing. Not admitted.

**H-3. The root's clock drives the watermark (a, root).** `w = now_root −
snap_lag`. A root 2 years ahead sets `w ≈ now + 1.5 y`: live entities it
holds are listed with `floor = 0` and survive; every record it has *not*
seen (in flight, created since its last sync) has `t < w` and is dominated
on arrival everywhere; every new write chases `snap_floor = w` into the far
future, or, if `w > maxceil`, clamps below `w` and is dead on arrival. S's
root clock error affects only `ceiling_t`, harmlessly. Not malice, but the
largest clock blast radius in two rounds; `w ≤ max t held − margin` would
cap it and is not stated.

**H-4. The honest slow-clock device loses creations repeatedly (a, h).** A
device behind by more than `snap_lag` writes new entities at `t =
max(now_dev, w_old)`. The next SNAP has `w' > w_old`; unless the root synced
that entity in between it is unlisted, gets `w'`, and the write is
`SNAP_DOMINATED` at the device; the app re-writes; the cycle repeats.
Reported, not silent, as the design argues, but the report is the only
path and an app without the callback loses the data; other replicas drop
the `PUT` with no report, so the only copy is on the device that must act.
Acceptable for a 180-day straggler; a recurring tax for an always-on device
with a bad clock, not mentioned.

**H-5. SNAP amplification and orphans (d, g).** A range is re-issued when
it holds an absorbable `DEL`, listing every live entity. `M` creates and
deletes one entity per range per root cycle: every leaf range is re-issued
(≤ 64 KiB each, 2.2 MiB for 10^5 live entities) to every replica; one 141 B
`DEL` buys 64 KiB of root-signed traffic per replica. And a range splits at
2 900 entries with the parent chunk persisting: `M` creates 3 000 entities,
waits for the split, deletes them; the 64 KiB orphan stays in every `F`
forever, ~22 B of permanent replicated storage per entity ever created.
Both bounded by root cadence and attributable; admitted as costs, not as
member-controlled triggers.

**H-7 (J). The epoch chain with four roots is unspecified, and the natural
reading is a C5 hole (e).** `k_e = H(k_{e+1} ‖ "prev")` from a random top
held by "the root". Either the roots share the top, so a revoked root
derives every future epoch key and `REVOKE(root)` buys no read cut-off
until re-founding; or each root has its own chain and a member boxed under
one cannot derive history under another. The text says neither; "two
gen-`g` rosters wrap two epoch-`g` keys" is only "a delay" if both wrap the
same chain.

**H-8 (J). Per-field writer sets are labels (d).** An unauthorized member's
`PUT` dominates and frees the authorized value; `unauth` flags it; the
honest writer re-writes from memory. The design says so and its divergence
trace in §5 is correct. Acceptable, provided no UI reads `rules[]` as a
security boundary: against any member key the rules buy nothing.

**Module I.** The sketch is entirely the sender's bytes, so a malicious `B`
can make any cell "pure" with any key and check; `A` then `WANT`s ids `B`
must back with well-formed signed records, or ships elements `B` claims to
lack. Neither changes `A`'s state wrongly: a bogus id is "held by no side"
and falls back; a hidden honest element is caught by the final `fp`, or `B`
lies about `fp` too and is simply withholding, which any peer can do. A
member can grind `h` to land three honest-colliding positions in ~`2^20`
tries (decode failure, fallback, bounded DoS); a false pure cell with a
consistent check costs ~`2^64`. I accept that I is outside the trusted
core. Residual: 180 KiB plus a 4 096-cell decode per session is a tax a
session-churning member can impose (round-one C-4's shape, no state effect).

### Attacks the design defeats
- Resurrection: none, ever, at any replica holding the SNAP, with no
  liveness assumption; a relay withholding a `DEL` for a year achieves
  nothing once a SNAP exists. (g-withhold, h) best of any design in two
  rounds.
- E-1/G-4's un-delete gadget: impossible; there is no expiry to race. (d)
- Attacker tombstones with far-future `t`: absorbed by a listed level; the
  root never needs an owner `DEL` above the attacker, and can kill a ceiling
  pin without out-writing the pinning key. (d) better than S, E.
- Root restored from backup: `⊒` covering makes a lower SNAP harmless by
  construction. (f-restore) defeated by theorem, not policy.
- Two roots racing rosters (J): both in `F`, removals are grow-only;
  round-one A-4 cannot recur. (f) better than S.
- Member blast radius: as S; cleanup `DEL`s no longer live `δ + del_ttl`
  but wait for a SNAP. Fingerprint, relay: as S. (h)

### Honesty
Candid on the wipe, the revoked root's SNAPs, permanent ceiling raises,
stragglers losing, SNAP traffic, orphan chunks and labels-not-walls. It
omits that the wipe is also a brick (writes can never re-enter below the
level), that `roots_ever` is thief-fillable, that `w` depends on the root's
clock, the slow-clock recurring loss, and the epoch chain under several
roots.

### Scores
C1 5 (A1, A2 only; no clock, no liveness in any safety theorem; T11' is a
finite statement). **C2 2** (member radius as S; the root radius is a single
unrevocable record that wipes and bricks, plus a thief-fillable root set and
a permanent ceiling raise; H8's "no single record" is met only by assuming
roots honest while J makes root compromise a designed-for case). C3 4. C4 4
(I is a real gain; 64 KiB elements need fragmentation). **C5 3** (root
loss recoverable with a second key is new and good; the revoked root's SNAPs
and the unspecified chain top take it back; member-level as S). C6 4
(`dom` has five arms and a merge-walk; T2' is the heavy proof). C7 4
(200 KiB of sketches, root-only builder). C8 3 (`SNAP_DOMINATED` is an
app obligation). C9 4.

---

## Composition

**S + E.** Strengthens the owner against sub-ceiling clock pins (no
Lamport-ization, `del_ttl`-bounded cleanup tombstones) and weakens deletion
durability: E-1 gives any writer a tombstone-erasing, self-expiring `DEL`,
and E-2 makes immortal tombstones un-removable. The ceiling pin's end moves
from a calendar to the root's reaction time; S's calendar refresh was also
root liveness, so that is a wash. Net for the attacker: a trade, not a gain,
with E-1 the one new primitive.

**S + H.** Removes `del_ttl`: straggler resurrection, the withheld-`DEL`
attack and the `δ + del_ttl` cleanup cost disappear, and attacker
tombstones at any `t ≤ maxceil` are absorbable. Does any mechanism still
end an attacker's effect without root action? No, and S had only wall time
passing a sub-ceiling pin: in S+H a pin ends at refresh (root), tombstones
at a SNAP (root), garbage at `REVOKE` plus `DEL`. The root is on the
critical path for GC as well as pins, and the root key is H-1. Net: members
weaker, root key catastrophic.

**S + E + H.** Does not compose as written. H's kill set is a `t`-prefix per
entity; E's `DEL`-over-`PUT` domination is by `height`. T2' needs
`s dom d ∧ d dom p ⇒ s dom p`:

```
p : PUT(E, f)  v=(height=3, t=2^48−1, M, …)      -- admissible in E: height ≤ maxceil, t unbounded
d : DEL(E)     v=(height=4, t=now,    O, …)      -- d dom p by height
s : SNAP       lvl(E) = now + 1                  -- s dom d (d.t < lvl); ¬ s dom p (p.t ≥ lvl)
Replica P applies p, d, s : p dropped by d, d dropped by s, F_P = {s}
Replica Q applies p, s    : F_Q = {s, p}
Reconcile : Q offers p; nothing at P dominates it; F_P = {s, p}.  F({p, d, s}) = {s}.
```

GC changed a future frontier (the round-one lesson against A, now between
two candidates): a record with `t = 2^48 − 1` is immune to every SNAP and
resurrects deterministically once the tombstone that killed it is absorbed.
A time prefix is not downward-closed in a height-first order, and a height
watermark kills every new entity (honest heights start at 0). So E (and G)
and H are mutually exclusive unless H's levels become full versions and the
root lists every entity, a different design. The naive composition gives
the attacker a convergence failure on demand.

**S + F.** Composes cleanly (F's same-author domination is by the full `v`,
which is what makes it compose with `DEL`). Strengthens the owner on every
typed cell (no pin, no overwrite, view purge at `REVOKE`) and leaves LWW
cells and `DEL` exactly at S. New attacker primitives: none beyond F-1's
"repair is `DEL`" and F-3's amplification. The best single addition.

**S + E + F + H + I + J.** Broken by E + H (above). Without E, S + F + H +
I + J composes: typed records are killed by SNAP levels like any `PUT` (the
root's `base = min live t` ranges over all authors), J's `unauth` must join
the typed-join exclusion list (unstated), I is orthogonal. Members are
confined (F), tombstones absorbed (H), roots plural and recoverable (J),
and the root key is H-1/H-2: J makes it *more* reachable (four keys, one on
paper) while H makes any one of them a permanent, unrevocable wipe. H + J
strengthens the attacker.

**Best C2 and C5: S + F + J, without H's SNAP (keep `del_ttl`), with I as a
protocol module.** C2 4, C5 3–4. Honest residual list: (1) LWW cells and
`DEL`s keep S's ceiling pin until refresh, re-pinnable until `REVOKE`; (2)
a thief's `DEL`s stand; (3) cleanup `DEL`s live `δ + del_ttl` and a
straggler past `del_ttl` resurrects, typed cells with full historic totals;
(4) typed-cell garbage is bytes until the owner `DEL`s the entity, which
also zeroes honest contributions; (5) back-dated typed records need
`from_t = 0`; (6) a stolen root fills `roots_ever` and raises `maxceil`
permanently (re-founding), but a *lost* root device is recoverable; (7) J
must specify the epoch chain under several roots or `REVOKE(root)` gives no
read cut-off; (8) per-field rules are labels; (9) inadmissible records cost
a per-session re-ship.

---

## Ranking

| Rank | Candidate | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 | C9 | Decisive finding |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | F typed fields | 4 | **4** | 3 | 4 | **3** | 4 | 4 | 4 | 4 | No new attacker primitive; pins and overwrites gone on typed cells; repair is `DEL` (F-1) |
| 2 | E height versions | 4 | **3** | 4 | 4 | **3** | 4 | 4 | 3 | 3 | Sub-ceiling pins neutered; un-delete gadget (E-1) and un-removable immortal tombstones (E-2) |
| 3 | G causal multi-value | 4 | **3** | 3 | 4 | **3** | 4 | 4 | 4 | 4 | No PUT can be shadowed or silently hidden; ceiling burnable in weeks (G-1), sticky siblings (G-2), void namers hide (G-3), `issued_t` gadget (G-4) |
| 4 | H snapshots + I + J | 5 | **2** | 4 | 4 | **3** | 4 | 4 | 3 | 4 | Strongest convergence and no resurrection; one unrevocable root record wipes and bricks (H-1), root set thief-fillable (H-2), root clock drives the watermark (H-3) |

F over E: E's gains are on clock pins, which S already bounded; its losses
are on deletion durability, which S had right; F gives up nothing S had. E
over G: G's no-shadow theorem is the strongest anti-pin statement in two
rounds, but G adds three un-admitted levers to E's one, and G-1 is a
re-founding on the attacker's schedule. H last on C2 despite the best C1:
every end-of-effect moves to the root, and the root key becomes a single
irreversible record.

**Verdict.** From the attacker's side the most optimal design is the
baseline frontier store with F's typed cells and J's multi-root roster
(`S + F + J`), with I as a protocol-only module and *without* H's SNAP and
*without* E or G: it is the only combination in this round in which every
attack I found is signed, attributable, bounded by one author's own records,
and ended by `REVOKE` plus at most one owner `DEL` per entity, with no
record that any party can write to brick or wipe a collection, and with a
lost root device recoverable. Its price is the baseline's: LWW cells and
`DEL`s keep the ceiling pin until refresh, cleanup tombstones live
`δ + del_ttl`, and a straggler past `del_ttl` can resurrect. H's
no-resurrection theorem is the one thing worth wanting from the rest, and
it is only acceptable if SNAPs become `k`-of-`n` countersigned (checkable
from bytes, admission still monotone) and `w` is bounded by held state
rather than by the root's clock; E and G must not be combined with it at
all.
