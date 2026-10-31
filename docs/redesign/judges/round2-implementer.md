# Implementer's verdict on the round-two candidates (E, F, G, H + I, J)

Lens as in round one: "I have to build this in SPARK behind `sync_engine.h`,
prove it in Lean, and ship it to phones, WASM and a device with 256 KiB of
RAM." Inputs: REQUIREMENTS.md, DESIGN.md (the frontier store, "S" below),
`formal/lean/Kome/Frontier.lean` (T1–T5, T8, T9, T12, part of T13
machine-checked), `formal/spark/CONVENTIONS.md` (no access types, bounded
loops, `Formal_Ordered_Maps` with a capacity, no tasking),
`include/sync_engine.h` (ABI v4), and round one's PERF numbers (Ed25519
verify 130 µs, sign 44 µs).

Baseline S, for reference: PUT wire = 144 + flen + vlen bytes, DEL = 141 B,
ROSTER ≤ 47.8 KiB; version `v` = 76 B; index entry per cell ≈ 64 B key + 76 B
`v` + 8 B offset + 16 B map node ≈ **164 B** (16.4 MB at 100k cells); eight
trusted-core mechanisms (`<`, `dom`/`F`, emission, roster/wrap, `void`, TTL
clause, accumulator/`fp`, RBSR); ≈ 24 person-weeks (pw), of which ≈ 4 pw of
Lean are banked. All four candidates keep S's RBSR, accumulator, roster chain
and log; I score what each adds or breaks.

---

## Candidate E — height-ordered versions

### Data structures and bounds

| Structure | Bound | Change vs S |
|---|---|---|
| Version `v` | 82 B (height 6, t 6, seq 6, author 32, h 32) | +6 B |
| PUT / DEL wire | 150 + flen + vlen / 147 B | +6 B each |
| Index entry | ≈ 170 B | +6 B; 17.0 MB at 100k |
| `maxceil` (over `ceiling_h`) | u48 max-register | same shape, different unit |
| `max_height_held` (for `near_ceiling`) | u48 max-register, root devices only | new, policy state |
| Height budget | 2^48 / 2^28 = 2^20 refreshes | type-bounded; `CEIL_EXHAUSTED` refuses |

Pointer-free and bounded exactly as S; the only new state is one more u48.

### Hot paths

- **PUT emission.** `floor` is the cell's index entry; `height_emit =
  min(floor.height + 1, maxceil)` is O(1) once the cell is found (O(log N)).
  Same as S's `t` chase; the index already carries the full `v`, so no new
  lookup.
- **DEL emission.** `height = 1 + max` over every live field of the entity
  and `deleted_at`: a range scan over the entity's index entries, O(fields).
  S does the same scan for `t`.
- **Apply.** Admission compares `height ≤ maxceil`: O(1). `near_ceiling`
  detection is one compare per applied record against `maxceil − 2^27`,
  updating `max_height_held`. Zero extra verifies; verify-on-win is unchanged.
- **The alarm.** The engine cannot set alarms. It can answer
  `sync_engine_roster_due(e, ns)` (new call, O(1)) after a session, and the
  root app refreshes at the end of the session in which the pin arrived: **no
  new wake-up**, the device was awake to sync. Compute per refresh is one sign
  + 64 × (X25519 + AEAD) ≈ 5 ms plus one 48 KiB roster to every member; the
  1/hour rate limit caps an attacker at 24 rosters/day = 1.15 MB/day per
  member and ≈ 120 ms/day of root CPU. Not a battery item. It *is* a liveness
  duty on the root app, and on iOS "after the next session" means "next time
  the owner opens the app"; pinned cells stay shadowed until then, where the
  baseline's sub-ceiling pins heal by wall time without the root.

### SPARK expressibility

Trivial: a five-field compare, one clamp, one more max register.

### Lean delta

`Version` gains a field; `Version.lt` has five levels; `lt_irrefl`,
`lt_trans`, `lt_trichotomy` remain `omega` (five Nat atoms per side, fine).
`dominates_trans` is still `cases ×3 <;> omega` over 64 cases. `adm` reads
`height`; `adm_mono`, `adm_put_le` unchanged in shape. `emitT`/`chase`/
`emitT_le` are replaced by `emitH floorH c := min (floorH + 1) c` and three
one-line lemmas (T8, T8', T8''). T13's `CEIL_EXHAUSTED` is one more
refusal lemma. **0.5 pw**, including re-running the build. The doc's "two
days" is right.

### C ABI impact

`sync_change` gains `height`; one new status (`SYNC_STATUS_NEAR_CEILING` or
the `roster_due` query); `set/get/delete/scan/session_*` keep their shape.
Smallest ABI delta of the four.

### Footprint

+6 B per record and per cell; no new code paths but the clamp. Clock optional
for PUTs, as in S. **Not for DELs**: a device with `now = 0` (the small-device
target without an RTC) emits `DEL` with `t = 0`, which every replica applies
and then expires *immediately*. The values are freed, no tombstone exists
anywhere, and any laggard's stale PUT resurrects a field with no A4
violation. S's chase gave such a DEL `t = floor.t + 1`. In E a clockless
device must be refused `DEL` (`NO_CLOCK`) or given a coarse clock by the app:
a real embedded regression the document understates.

### Ergonomics

```c
/* Conflict: same as S, resolved in the store; nothing to do but read. */
sync_engine_get(e, ns, 16, ent, 16, "phone", 5, &v, &n);   /* winner by (height, t, author) */
/* Delete: one call; partial-record resurrection as in S if an edit raced. */
sync_engine_delete(e, ns, 16, ent, 16);                     /* status may be SHADOWED at the ceiling */
```

One value, one rule, as in S. What changes for the user: among concurrent
edits from the same floor, a device that edited twice offline beats one that
edited once, later. For a single person's phone/laptop pair that is the
common conflict, and E resolves it against the later edit. `far` becoming
accurate is the one C8 gain.

### Scores

- **C1 = 4** same theorems, same assumptions; `t` out of the causal order.
- **C2 = 4** sub-ceiling pins have no after-effect; attacker tombstones at `t = 2^48−1` are immortal until owner-dominated; height budget is burnable.
- **C3 = 4** 82 B per cell; cleanup tombstones live exactly `del_ttl`, not `δ + del_ttl`.
- **C4 = 4** unchanged.
- **C5 = 3** unchanged; `from_t` is now accurate for honest-clock thieves.
- **C6 = 4** same eight mechanisms; Lean delta half a week.
- **C7 = 4** +6 B; clockless DEL leaves no tombstone (would be 3 without a `NO_CLOCK` refusal).
- **C8 = 3** one rule, but chains beat clocks on the most common conflict a single user has.
- **C9 = 4** `height = 0` ordinary; `height = maxceil` regime and `now_local` clause remain.

---

## Candidate F — typed lattice fields

### Data structures and bounds

| Structure | Bound | How |
|---|---|---|
| PUT wire | 145 + flen + vlen | +1 B `ftype` |
| Element key | 114 B (+33) | descriptors ≈ 227 B vs 194 |
| Index `(cell, author) → (offset, v)` | key 97 B + 76 + 8 + 16 ≈ **197 B** per record | 19.7 MB at 100k records; by capacity |
| Records per typed cell | ≤ 64 live + ≤ 1 024 void = 1 088 | by roster/revocation bounds |
| Typed cell in RAM | 1 088 × 197 B = 214 KB worst | fixed per cell; number of cells by capacity |
| Typed cell in log | 1 088 × 65 535 B = **68 MiB** worst (GSET/MVREG) | fixed per cell, and huge |
| PNCOUNTER view | i64, |Σ| < 2^59 | type-bounded |
| **GSET / MVREG view output** | up to 1 088 × 65 535 B | **not bounded by any type in the document** |

The last row is the H5 problem. `cell(c)` for GSET is the union of ≤ 1 088
sets of ≤ 64 KiB; for MVREG, ≤ 1 088 values. In SPARK the output buffer needs
a declared maximum, and the only honest one is `Max_Value_Len × authors`
(4 MiB for 64 live members, 68 MiB with void records). Either the typed read
becomes a cursor (`get_elems(cell, start_after, limit)`, the right answer) or
the engine declares a `Max_View_Len` and refuses above it. The document has
neither.

### Hot paths

- **`get` on a typed cell**: lower-bound in the ordered map O(log N), a
  forward scan of ≤ k entries sharing the cell prefix, one log read per entry
  (12 B for PNCOUNTER, up to 64 KiB for GSET), then the fold. PNCOUNTER at
  k = 64: 64 random log reads, tens of µs from RAM, ms from flash. GSET at
  k = 64 with 64 KiB sets: 4 MiB of reads and a 64-way merge per `get`.
- **"Increment by 3."** `sync_engine_set` cannot express it (a PUT carries the
  author's *full* state). The ABI needs `sync_engine_counter_add(e, ns, ent,
  field, int64 delta)`, `set_add`, `max_set` and a typed `get`. The engine
  does read-modify-write: `own(c)` lookup O(log N), decode, add with refusal
  at 2^48, sign (44 µs), emit. **Safe under concurrent app threads?** The ABI
  has no thread-safety contract; every call already mutates `seq_self`, so
  apps serialize calls per handle. Given that, the engine-side RMW is atomic
  per call, which is *better* than the app doing `get` + `set`: between those
  two calls a sync-applied `DEL` can reset `own(c)`, and the app's `set` then
  carries the stale total into a resurrected entity. So the typed calls must
  exist and the RMW must live in the engine.
- **Apply.** `dom` for a typed PUT looks up `(cell, author)`: same O(log N).
  Verify-on-win weakens: a foreign PUT on a typed cell is never dominated by
  another author's record, so every author's record is verified once.

### SPARK expressibility

Five value decoders (GSET canonicality: sorted, distinct, O(vlen)), five folds
over a bounded map range, `u48` arithmetic with refusal, and the output-bound
question above. ≈ 1 200 lines, no recursion.

### Lean delta

`Record.put` gains `ty`; `dominates` put/put becomes `e = e' ∧ f = f' ∧ ty =
ty' ∧ (ty = 0 ∨ a = a') ∧ lt v v'`; `dominates_trans` still closes by `omega`
(author equality is linear). `cell_unique` splits into `cell_unique` (ty = 0)
and `cell_author_unique`. T2'-neg and T12-neg by `decide` over three-record
lists: cheap and valuable. T15 (fold is permutation-invariant) is the real
work: this project uses core Lean, not Mathlib, so `List.Perm → foldl sum
equal` for Nat sum, max and union-up-to-membership must be written: ≈ 3
days. **1.5 pw.**

### C ABI impact

Four new write calls, a typed/cursor read, `ftype` in `sync_change`, a
`TYPE_CONFLICT` report in `scan`. ≈ 1 pw. `set/get/delete` keep shape for
LWW cells.

### Footprint

+33 B per index entry **for every record, LWW included** (a fixed-width SPARK
key carries `author` and `ftype` for all kinds): 20% more RAM at 100k for a
feature most cells do not use. In WASM the folds are small; the view buffer
is the problem.

### Ergonomics, honestly

```c
/* Inventory quantity: two devices sell stock offline. */
sync_engine_counter_add(e, ns, 16, item, 16, "qty", 3, -3);   /* own state: dec += 3 */
sync_engine_counter_get(e, ns, 16, item, 16, "qty", 3, &total); /* Σ inc − Σ dec over authors */
/* Delete resets everyone: an author that never saw the DEL carries its
   whole historic total into the resurrected item. */
sync_engine_delete(e, ns, 16, item, 16);
/* Shared list: NOT a GSET (no removal). One entity per item, LWW fields, DEL to remove. */
```

For the stated applications: contacts, notes, settings are LWW; shared lists
are entities, because GSET cannot remove; MAXREG is a nicety. **PNCOUNTER is
the one type with a real use** (inventory quantities), and an app can build
it on S today with per-device sub-cells `(item, "qty/<device-id>")` summed in
the app: same O(authors) cost, no engine change, no 33 B on every key. F's
real advantages over that are engine-defined delete-reset and `void` removing
a revoked author's contribution automatically. MVREG is D's per-author
candidate view with D's cost and no observed-remove.

### Scores

- **C1 = 4** generic frontier proofs reused; `v` forced as the same-author order (the T2' counterexample is correct and important).
- **C2 = 4** typed cells cannot be pinned or overwritten by others; restore regresses own state silently until first sync.
- **C3 = 3** O(authors-ever) per typed cell, 33 B wider keys on every record, 68 MiB worst case per cell in the log.
- **C4 = 4** unchanged protocol; 227 B descriptors.
- **C5 = 3** unchanged.
- **C6 = 3** +2 mechanisms (typed decoders, five folds) and an unbounded view output the proof must bound somewhere.
- **C7 = 3** +20% index RAM for all cells; view buffer or cursor API needed.
- **C8 = 3** counters are real; GSET without remove and MVREG without retire are not what the listed apps need; four new write calls.
- **C9 = 4** `ftype ≤ 4` is a decode refusal; `(0,0)` ordinary; the view bound is the gap.

---

## Candidate G — multi-value cells with causal parents

### Data structures and bounds

| Structure | Bound | How |
|---|---|---|
| PUT wire | 145 + 32·n_parents + flen + vlen; **2 161 + flen + vlen** at 63 parents | fixed by type |
| DEL wire | 147 B (`issued_t` + `height`) | fixed |
| Index `(cell, author)` | ≈ 197 B per sibling | by capacity |
| Siblings per cell | ≤ |W| ≤ 2 048; ≤ 64 in practice | by `W` |
| `W` (authors ever rostered) | 2 048 × 32 B = 64 KiB per collection, persisted | fixed by type |
| `named` bitmap per contested cell | 64 bits, or 2 048 bits worst | derived cache |
| Retained resolved siblings | one full value per author-ever per contested cell | until rewrite or DEL |

### Hot paths

- **`set` with `seen[]`.** Range-scan the cell's siblings (≤ k), compute
  `live`, check `seen ⊇ live \ own` (k × 32 B compares), copy the whole
  foreign frontier into `parents` (≤ 63 × 32 B), height = 1 + max, sign.
  O(k); the record is up to 2 KiB larger than S's, 32 B larger in the
  uncontested case.
- **`named` recompute.** When a sibling of cell `c` changes, `live(c)` needs
  every sibling's parent list: k log reads of up to 2 KiB and k × 63 hash
  compares: 128 KiB of I/O and 4 032 memcmps (~50 µs) on a 64-author cell. A
  persistent 64-bit `named` bitmap avoids the reads but is a derived
  invariant compaction must recompute (acceptable as a cache with a checked
  rebuild).
- **DEL emission.** `1 + max` over every sibling of every field: O(fields ×
  authors).
- **Apply.** Same `(cell, author)` lookup as F; **admission** adds `author ∈
  W`, O(log 2 048). Verify-on-win: only same-author older records are
  skippable; every foreign sibling is verified.

### SPARK expressibility

Parent lists are a bounded 63 × 32 B array in the codec; `W` is a
`Formal_Ordered_Sets` with capacity 2 048; the bitmap is `mod 2**64`.
Acyclicity of `named` is not checked at runtime, so `live` is a plain filter:
no fixpoint, no recursion. ≈ 1 500 lines.

### Lean delta

put/put gains `a = a'`: `omega` survives. `State` becomes `(held, ceil, W)`
with `adm (c, W) r := r.height ≤ c ∧ r.author ∈ W`; `adm_mono` over the
product `(≤, ⊆)` and `applyAllA_view` with a second register: ≈ 3 days.
**T-G1** (finite acyclic `named` has a maximal element) is the non-trivial
piece in core Lean: acyclicity must be supplied as a rank function (`rank p <
rank q` whenever `p.h ∈ q.parents`, which hash commitment gives), then
induction on the sibling list: ≈ 3 days. **2 pw.**

### C ABI impact

The largest of E/F/G. `sync_engine_get` either becomes `pick` (hiding
conflicts, which defeats the design) or gains a sibling array; `set` gains
`seen[]` and `CONFLICT_UNSEEN`; `sync_scan_entry` gains a `CONFLICTED` bit;
`sync_change` loses `hlc`, gains `height` and `parents`. ≈ 1.5 pw, every
binding changes.

### Footprint

+33 B per index entry (as F), +64 KiB `W` per collection (log-resident with a
small cache on a 256 KiB device), parent lists in the log, retained sibling
values. No clock except `issued_t`.

### Ergonomics

```c
sync_sibling sib[64]; size_t n = 64;
sync_engine_get_siblings(e, ns, 16, ent, 16, "phone", 5, sib, &n);
if (n > 1) {                                   /* show both, attributed */
    uint8_t seen[64][32]; for (i = 0; i < n; i++) memcpy(seen[i], sib[i].h, 32);
    rc = sync_engine_set_cas(e, ns, 16, ent, 16, "phone", 5, merged, mlen, seen, n);
    if (rc == SYNC_STATUS_CONFLICT_UNSEEN) { /* re-read and retry */ }
}
/* Delete: total order by height; edit-vs-delete race gives a partial record, as in S. */
sync_engine_delete(e, ns, 16, ent, 16);
/* The loser's device must rewrite the cell to free its retained value: */
sync_engine_set_cas(e, ns, 16, ent, 16, "phone", 5, winner, wlen, NULL, 0);
```

The conflict surface is genuinely good for a list shared by several people:
attributed, compare-and-set protected, one call to resolve. The costs: a
resolved sibling's bytes stay until *its author* rewrites the cell (an
"accept resolution" write the app did not ask for, the thing I held against
D); a settings-style app gets a `theme` sibling pair resolved by `pick` =
causal depth then public key, and if it wants "latest wins" it stores a
timestamp in the value and picks itself: B's app-stamp leak. For one
person's devices, where concurrent edits are rare and "the one I made last"
is the expected winner, G regresses the common case to fix the rare one.

### Scores

- **C1 = 4** no clock in any order; two grow-only registers; `named` needs the acyclicity hypothesis.
- **C2 = 4** no PUT can shadow or hide an honest value; DEL pins at `maxh` remain.
- **C3 = 3** retained siblings, 2 KiB parent lists, `W`, 33 B wider keys.
- **C4 = 4** unchanged protocol; contested PUTs are large.
- **C5 = 3** unchanged.
- **C6 = 3** `live`/`named` view, `W`, CAS, T-G1's hypothesis; most of `Frontier.lean` survives.
- **C7 = 3** parents in the log, bitmap recompute, 64 KiB `W` per collection.
- **C8 = 3** excellent for multi-person lists, worse for a single user's settings; engine-driven "accept" writes; `get` changes meaning.
- **C9 = 4** `n_parents = 0`, `height = 0`, `void = 0` ordinary; the bitmap is a derived cache.

---

## Candidate H — root-signed snapshots (with modules I and J)

### H: data structures and bounds

| Structure | Bound | How |
|---|---|---|
| SNAP record | 112 B + 22 B × n_lvl, n_lvl ≤ 2 900 → ≤ 63 912 B | fixed by type |
| SNAP frames held per collection | leaves + orphans < 2 × leaves; leaves ≈ ⌈live entities / 2 900⌉ | by capacity |
| Kill-level lookup state | 22 B per **live** entity (every live entity is listed by the §6 builder) + 112 B per chunk | by capacity; 2.2 MB at 10^5 entities, 220 KB at 10^4 |
| Covering chunks per entity | ≤ trie depth (≤ 128, ≈ 8 in practice) | fixed |
| Root-side trie + per-range dirty flags | ≤ 2 × leaves entries | root policy state |
| `SNAP_DOMINATED` report queue | must be a bounded ring of (ent, field, value ≤ 64 KiB) | new; needs a capacity |

### H: hot paths

- **Kill-level lookup on every applied PUT/DEL** (and in `t_emit`). Find the
  chunks covering `ent` (a range index keyed by `ent_lo`, ≤ depth hits),
  binary-search each sorted `lvl[]` (≤ 12 compares), take the max: ≈ 100
  compares per record. SPARK without pointers means a resident copy of the
  chunks: 22 B per live entity, bounded by the live-entity capacity, not by a
  type. At 10^4 entities that is 220 KB: fine on a phone, a stretch on a
  256 KiB device.
- **SNAP arrival.** `⊒` against each held chunk whose range intersects: a
  merge-walk of ≤ 5 800 steps per pair, ≤ depth + children pairs; then drop
  every record in `[ent_lo, ent_hi]` with `t < lvl`, a range scan of the cell
  index. Milliseconds.
- **SNAP construction on the root.** Not O(entities log entities): with the
  ordered cell index it is a linear range scan, O(cells in range + n_lvl₀).
  The cost is *how often* and *how big*. The builder lists every live entity
  in the range, so a re-issue costs 22 B × live entities whatever it absorbs;
  and with `w = now − snap_lag`, today's DEL is absorbed 180 days from now,
  so under steady deletion every range is dirty every period and the whole
  collection is re-snapshotted every period: 10^5 live entities → 35 leaves →
  2.2 MiB per period to every member. Tombstones cost 141 B per deletion,
  once. Break-even per range is ≈ 450 deletions per period (15% churn);
  below that tombstones are cheaper, by 15× at 1 000 deletions/day on a daily
  period. H is net-negative on C3 for low-churn collections unless the root
  adds a churn threshold, and then tombstones linger until churn accumulates,
  since nothing else expires them.
- **Orphans.** Each trie split leaves the parent SNAP uncovered forever (no
  single later SNAP has its range and ≤ 2 900 entries). 10^5 entities → 34
  orphans ≈ 2.1 MiB of dead chunks every replica holds and every new member
  downloads; 10^6 → 21 MiB. A "jointly covered by a set of SNAPs" rule would
  fix it but makes `dom`'s witness a set, which breaks the per-element
  `dominates` shape every proof in `Frontier.lean` rests on.
- **Straggler reporting.** On SNAP arrival the engine must notice its *own*
  records are about to be dominated, copy their values into a bounded event
  ring before dropping them, and expose `sync_engine_poll_events`. The ring
  needs a capacity and an overflow policy, both absent.

### H: SPARK expressibility

SNAP codec with the strictly-increasing check, merge-walk, range index, range
drop, event ring, and the root builder with its trie (policy, ≈ 400 lines,
root only). All loops bounded by 2 900 or by capacity, no recursion. ≈ 1 800
lines core + 400 policy.

### H: Lean delta

This is where it costs. `dominates` gains four arms that are not
`omega`-shaped: `lvl_s(ent)` is an association-list lookup and `⊒` is a
pointwise `∀ ent ∈ [lo, hi]`. `dominates` is `Bool` via `decide` today; the
SNAP arm needs a decidable instance over the bounded range (slow but valid)
or a `Prop`-valued `Dom` plus a lemma that the merge-walk decides it.
`dominates_trans` becomes a real proof with lookup lemmas (cases i–iv), ≈ 1.5
pw; merge-walk soundness ≈ 0.5; T11' ≈ 1; T15/T16 ≈ 0.5; `adm` over
`(maxceil, roots_ever)` ≈ 0.3. **≈ 4 pw** (J's T17/T18 another 0.5). The
restated T2' is the heaviest Lean item in round two.

### H: C ABI impact

`SNAP` kind in `sync_change`; `poll_events` with `SNAP_DOMINATED`; a root-side
`sync_engine_snapshot(e, ns)`; `del_ttl` leaves the roster API. ≈ 1 pw.

### H: ergonomics

```c
/* Delete: unchanged call; tombstone leaves when the root snapshots the range. */
sync_engine_delete(e, ns, 16, ent, 16);
/* After a long offline period, drain what the SNAP discarded: */
while (sync_engine_poll_events(e, &ev) == SYNC_OK)
    if (ev.kind == SYNC_EVENT_SNAP_DOMINATED)      /* your write from 7 months ago */
        ask_user_to_reapply(ev.ent, ev.field, ev.value, ev.len);   /* re-PUT chases above the level */
```

"Your offline edits were discarded, here they are" is a worse conversation
than "a deleted item came back" for most apps, and it needs UI the baseline
does not. The positive: it is attributable and the data is in hand.

### H: scores

- **C1 = 5** no clock, no liveness, no membership in any safety theorem.
- **C2 = 3** stolen root key = one-record wipe; revoked root's ceiling raise is permanent.
- **C3 = 3** 22 B per live entity resident, SNAP traffic ∝ live entities per period, permanent orphans; GC is `dom` alone.
- **C4 = 4** (with I: 5 in the common case); 64 KiB chunks need fragmentation.
- **C5 = 3** unchanged.
- **C6 = 3** the SNAP `dom` arm and merge-walk are the heaviest proof in round two; builder soundness is a policy theorem.
- **C7 = 3** resident levels, chunk fragmentation, event ring; builder on roots only.
- **C8 = 2** `SNAP_DOMINATED` is a data-loss dialog; everything else as S.
- **C9 = 4** no `now_local` in state; `w = 0`, `floor = 0` ordinary.

### Module I — IBLT first round

Cell = 44 B; `cap ≤ 4 096` → **176 KiB per sketch on the wire**, 3.7×
`Max_Message_Len` (48 KiB): the sketch needs fragmentation or `cap ≤ 1 000`
(≈ 770 differences in one round; above that, split). Resident: three sketches
(32 + 512 + 4 096 cells) = 204 KB per collection + 20 B per element (2 MB at
100k); update is one BLAKE2b then 9 cell XORs; decode is a peel over ≤ 4 096
cells, < 1 ms in WASM. Hash seeds are fixed constants (both sides sketch
independently), so a member can grind three-way collisions (≈ 2^36 BLAKE2b
per forced decode failure): bounded cost, fallback, no state effect. SPARK:
arrays and XOR, ≈ 400 lines, outside the trusted core. **Minisketch in
SPARK**: GF(2^64) carry-less multiply as 64 shift-xor steps is ≈ 30
pointer-free lines; Berlekamp–Massey is O(c²) field multiplies: at c = 4 096,
1.7 × 10^7 multiplies × 64 steps ≈ 10^9 ops, seconds on a phone, worse in
WASM; usable only for c ≤ 256 (BLE-sized diffs). ≈ 1 500 lines with no proof
content. IBLT is the right default. **3.5 pw; adopt independently of H.**

### Module J — multiple roots, per-signer rosters, field rules

`roots_ever`: 256 × 32 B = 8 KiB, grow-only, persisted; admission O(log 256).
Per-signer roster domination: the index gains `(ns, signer) → roster`; `F`
holds ≤ 256 rosters of ≤ 49.3 KiB (`prev_h`, roots, 1.3 KiB of rules) = 12.6
MiB worst, ≤ 200 KiB in practice. `ROSTER_eff` and `root_void` are views,
cached and recomputed on every roster/REVOKE apply. **`unauth` on every
read**: member index (cached, O(log 64)) + ≤ 32 rules × ≤ 32 B prefix compare
+ one bit test ≈ 1 µs per `get`; `scan` over 10^4 entities pays 10 ms unless
the bit is cached per index entry and recomputed on roster change (≈ 100 ms
at 100k). Unanswered: does an `unauth` PUT count for `exists`? It must be
decided before T5 is restated. Rules are flags, not walls: a UI hint that
costs a view predicate on every read. Lean: T17, T18, T12 restated with
`unauth` non-monotone across generations ≈ 1.5 pw; SPARK ≈ 3; ABI ≈ 1
(roster API with root sets and rules, `REVOKE` with `from_gen`). **6.5 pw.**
The valuable half is `roots_ever` + per-signer domination (root loss becomes
recoverable); the field rules I would cut.

---

## Composition

Effort is incremental over S (≈ 24 pw: SPARK 15, Lean 5 remaining, ABI 2,
tests 2); +15% integration when three or more modules touch `dom` or the
index key.

| Composition | SPARK | Lean | C ABI | Tests | **Total pw** | Core mechanisms | PUT overhead (B over value) | Index entry | One head? |
|---|---|---|---|---|---|---|---|---|---|
| S | 15 | 5 | 2 | 2 | **24** | 8 | 144 + flen | 164 B | yes |
| S+E | 16 | 5.5 | 2.5 | 2.5 | **26.5** | 8 | 150 + flen | 170 B | yes |
| S+H | 20 | 9 | 3 | 3.5 | **35.5** | 9 (TTL out, SNAP in) + root builder | 144 + flen; +22 B/live entity resident | 164 B + levels | barely: trie, orphans, event ring |
| S+E+H | — | — | — | — | **not buildable as specified** (below) | | | | no |
| S+F | 19 | 6.5 | 3 | 3 | **31.5** | 10 | 145 + flen | 197 B | yes |
| S+E+F+H+I+J | 33 | 13 | 6 | 7 | **≈ 59 → 68 with integration** | 15; `dom` has 8 arms; `Record` 5 kinds | 151 + flen; SNAP + 49 KiB rosters per root | 203 B + levels + sketches | no |

**S+E+H does not compose.** H's kill set must be a prefix of the version
order per entity, or T2' case (ii) fails. Under E the order is `(height, t,
…)`, so a kill level in `t` is not a prefix: take `p'` at `(height 0, t =
2^47)` from a fast clock and honest `p` at `(1, now)` on the same cell; `p`
dominates `p'`; a SNAP with `lvl = now + 1` dominates `p` but not `p'`. A
replica that held `p'`, then `p`, then the SNAP ends with `{SNAP}`; one that
received the SNAP first and then `p'` ends with `{SNAP, p'}`, `p'` live. Same
records, different frontiers. Expressing levels in E's order instead
((height, t) pairs, 28 B per entry) destroys the watermark: heights are
per-cell Lamport counters with no cross-entity meaning, so "unlisted entities
die below `w`" either kills every entity the root has not seen (an
offline-created entity dies at the next SNAP however recent) or kills
nothing, in which case every entity ever deleted stays listed in every later
SNAP forever (28 B per deleted entity, never freed: H7 by another name). E
and H are mutually exclusive; the six-module row inherits this and is listed
only for its cost.

**S+F+H+I+J (the six-module row without E)** is buildable: F's same-author
domination is a sub-order of `v`, so a `t`-prefix kill set is upward-closed
across it. But 15 mechanisms, an eight-arm `dom`, two index key layouts, 204
KB of sketches and 22 B per live entity resident, 49 KiB rosters per root
key, and a Lean file where `dominates_trans` is no longer `cases <;> omega`:
one engineer cannot hold it, and two will disagree about what `exists`
returns for an `unauth`, `void`, typed cell under a SNAP level.

**Best C3/C6/C7/C8 balance: S+E, plus I as a transport module.** S+E keeps
the eight-mechanism core and the half-week Lean delta, fixes the tombstone
inflation (`δ + del_ttl` → `del_ttl`) and the sub-ceiling Lamport-ization the
adversary judge disliked most in S, and costs 6 B per record. I adds one
round trip in the common case for 3.5 pw outside the trusted core, with
`cap` clamped to 1 000 cells so the sketch fits today's message bound. Two
conditions on E: refuse `DEL` on a device with `now = 0` (`NO_CLOCK`) rather
than emit an instantly-expiring tombstone, and ship `sync_engine_roster_due`
with the rule "refresh at the end of the session that raised it", the only
form of alarm an engine without a scheduler can offer.

**What I would cut.** H: the clock leaves the state, the cleanest theorem of
the round, but it arrives with per-period re-snapshots of every live entity,
permanent orphans, a straggler-loses dialog, a one-record root wipe and the
heaviest Lean delta; the TTL clause it removes is one line with a stated
assumption. F: apps can build PNCOUNTER on S with per-device sub-cells today;
revisit when one demands engine-side counters. G: the best conflict surface
of the round for multi-person lists, but it changes what `get` means, retains
losers and regresses a single user's settings; keep it as the answer to
DESIGN.md §10 item 5 if such an app appears. J: adopt `roots_ever` and
per-signer roster domination later as a 3 pw increment if root loss is a real
complaint; cut the field rules.

---

## Ranking

| Rank | Candidate | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 | C9 | Σ | Δ effort over S |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | **E** height versions | 4 | 4 | 4 | 4 | 3 | 4 | 4 | 3 | 4 | 34 | +2.5 pw |
| 2 | **F** typed fields | 4 | 4 | 3 | 4 | 3 | 3 | 3 | 3 | 4 | 31 | +7.5 pw |
| 3 | **G** causal multi-value | 4 | 4 | 3 | 4 | 3 | 3 | 3 | 3 | 4 | 31 | +8.5 pw |
| 4 | **H** snapshot GC | 5 | 3 | 3 | 4 | 3 | 3 | 3 | 2 | 4 | 30 | +11.5 pw (+3.5 I, +6.5 J) |
| module | **I** IBLT round | — | — | — | 5 | — | 4 | 3 | — | — | adopt | +3.5 pw |
| module | **J** roots + rules | — | 4 | 3 | — | 3 | 3 | 3 | 3 | 4 | half | +6.5 pw |

F over G on a tie because F keeps `get`'s shape and wall-clock LWW for the
cells apps actually use, and its H5 gap (the view output bound) has a known
fix (a cursor), whereas G's costs are semantic. H last despite the best C1:
the implementer pays in resident levels, chunk traffic that scales with live
entities rather than deletions, permanent orphans, an event ring, and the
only Lean item in the round that is not an `omega` script.

**Verdict.** Build **S+E with I**: the frontier store with `(height, t,
author, seq, h)` versions, ceiling in heights, the alarm as a post-session
`roster_due` query, `NO_CLOCK` refusal for clockless deletes, and an IBLT
round 0 capped at 1 000 cells. It is ≈ 30 pw against S's 24, keeps the
eight-mechanism trusted core and the existing `Frontier.lean` proofs with a
half-week delta, adds 6 B per record and 204 KB per collection of untrusted
sketch state, keeps 70% of `sync_engine.h` call sites, and removes the two
baseline behaviours the attacker judge found worst (tombstone inflation by a
fast clock, Lamport-ized cells for up to 400 days) at the price of one
honestly stated ergonomic change: among truly concurrent edits, a longer
chain beats a later clock. Everything else in this round either changes what
`get` means (F, G) or trades a one-line clock clause for a snapshot subsystem
that is more code, more bytes and more proof than the problem it solves (H),
and I would not let any of them onto the critical path before T7 is proved.
