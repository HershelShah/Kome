# Candidate E: ordering counter separated from wall time

## 1. Summary

- DESIGN.md's frontier store, kept exactly, with one substitution: `v = (height : u48, t : u48, author, seq : u48, h)`, lexicographic. `height` is a bounded per-cell Lamport counter that chases the cell's floor; `t` is the writer's honest wall clock and **never chases**.
- Causal order ("I had seen your write") is decided by `height`; true concurrency (same floor) by `t`. Read-your-writes needs no clock; "later edit wins" holds among concurrent writes even on cells an attacker has pushed.
- The roster ceiling bounds `height` (`ceiling_h`), `maxceil` is a max-register over it, and admission `height ≤ maxceil` is the same monotone rule as DESIGN.md §4. Nothing bounds `t`.
- `t` has three uses only: tie-break at equal height, the `far` flag, tombstone expiry. A `DEL` over a far-future `PUT` keeps `t = now`, so its tombstone expires `del_ttl` after it was written; the baseline keeps such tombstones alive for as long as the attacker's clock was ahead.
- A malicious writer can still pin a cell with `height = maxceil, t = 2^48−1`; it shadows honest writers until a roster refresh, as in the baseline, but no wall-clock passage ever ends it, so refresh must be alarm-driven as well as scheduled.
- `height` is bounded by type, by admission and by an emission clamp with an explicit `SHADOWED` status; it has no semantics at its maximum, and no replica verifies a height against history. Neither the causal-length saturation incident nor candidate C's truncation failure can recur.
- Everything else is unchanged; the Lean model changes in `Version`, `adm` and the emission lemmas only.
- Where it breaks: a chain of concurrent edits beats a single later edit regardless of wall time (a most-ops-wins residue); a ceiling pin ends only by root action; tombstone durability is only as good as the deleter's clock; the height space is a consumable that forced refreshes burn.

## 2. Data model

**Identifiers, values, well-formedness.** Unchanged from DESIGN.md §2.

**Version.** `v = (height : u48, t : u48, author : [32]u8, seq : u48, h : [32]u8)`, compared lexicographically with `author` and `h` as unsigned 256-bit integers. `h` is the record's content hash (which now covers `height`), so distinct records never compare equal (T1). `height = 0`, `t = 0`, `seq = 0` are ordinary values.

**Records.** `PUT` and `DEL` gain a `height` field; `ROSTER` carries `ceiling_h` in place of `ceiling_t`. `REVOKE` is unchanged.

```
PUT     ns[16] ent[16] flen:u8 field[flen] height:u48 t:u48 seq:u48 author[32] vlen:u16 value[vlen]
DEL     ns[16] ent[16]                     height:u48 t:u48 seq:u48 author[32]
ROSTER  ns[16] root_pk[32] salt[16] gen:u48 ceiling_h:u48 del_ttl:u48 epoch:u16
        n_members:u8 (≤64) members[n] { sign_pk[32] dh_pk[32] nonce[24] box[48] }
REVOKE  ns[16] root_pk[32] salt[16] sign_pk[32] from_t:u48 rev_seq:u48
```

Signing, hashing and well-formedness are unchanged from DESIGN.md §2. `height` is writer-chosen, as `t` was; well-formedness does not check it against anything.

**Lattice.** `dom`, `F`, upward closure and the frontier homomorphism are unchanged from DESIGN.md §3, read with the new `>`. The proofs of T2, T2', T3 never inspect the components of `v`, only that `<` is a strict total order (§9).

**Views.** `deleted_at`, `cell`, `exists`, `void`, `far` are unchanged from DESIGN.md §3. One advisory view is added:

```
near_ceiling(x)  := x.height > maxceil − H_STEP/2       -- advisory; honest writes never get here (§3)
```

Because `t` no longer chases, `far(p)` flags exactly the records whose writer's clock was ahead, not honest writes that inherited a far floor.

**Example.** Devices A (clock behind by 500 ms) and B; `v` written `(height, t, author, seq)`.

```
PUT(E, name,  "Ada")    v=(0, 1000, A, 7)
PUT(E, phone, "555")    v=(0, 1000, A, 8)
DEL(E)                  v=(1, 2000, B, 3)   -> height = max over E + 1 = 1; both PUTs dominated. F = {DEL@1}
PUT(E, name, "Ada L.")  v=(1, 1500, A, 9)   -> A had not seen the DEL: floor = name@0, height 1, concurrent
                                               with the DEL; equal height, 1500 < 2000: dominated, dropped.
PUT(E, name, "Ada L.")  v=(2, 1600, A, 10)  -> A has now seen the DEL: floor = deleted_at, height 2 > 1:
                                               wins although A's clock still reads below B's. F = {DEL@1, name@2}
```

Any permutation with duplicates yields the same `F` (T3). The baseline resolves the last line by chasing `t` to 2001; E resolves it by height and leaves `t` truthful.

## 3. Clock and identity

**Emission.** This is the only definition that changes materially.

```
floor(cell)  := max(cell(ns,ent,f).v, deleted_at(ns,ent))     -- for DEL: max over all live fields of ent and deleted_at
height_emit  := 0 if no floor; else floor.height + 1; if height_emit > maxceil then height_emit := maxceil
t_emit       := now_ms                                         -- honest; 0 on a device without a clock; never clamped
seq_emit     := seq_self + 1;  at 2^48 − 1 the write fails SEQ_EXHAUSTED, no record is produced
v_emit       := (height_emit, t_emit, self_pk, seq_emit, h)
status       := SHADOWED if floor exists ∧ v_emit < floor   (only when floor.height = maxceil ∧ floor.t ≥ now_ms) else OK
```

`floor` is DESIGN.md §5's function under the new order. The chase moves to `height`: whenever `floor.height < maxceil`, `v_emit > floor` on the first component alone (T8). At the ceiling the tie falls to `t`, so an honest writer still beats a ceiling-height record whose `t` is in the past; it is shadowed only by a record that is both at the ceiling and `far`. `seq_self` remains the only persisted clock state; nothing is adopted from a peer.

**Ceiling.** `maxceil` is the max-register over `ceiling_h` of every `ROSTER` ever applied, stored, never decreasing (DESIGN.md §4 with `ceiling_h` for `ceiling_t`). An honest root issues `ceiling_h = maxceil + H_STEP`, `H_STEP = 2^28`, (a) on the baseline's wall-clock schedule, (b) when it holds any `near_ceiling` record, rate-limited to one alarm-driven refresh per hour. If `maxceil + H_STEP > 2^48 − 1` the roster emission fails `CEIL_EXHAUSTED` and the collection is re-founded. Honest heights grow by one per causally chained write, so 2^28 is 15 sustained writes per second to one entity for 200 days; honest use never trips the alarm. Admission: `height > maxceil` is inadmissible, not held, re-offered by whoever holds it (DESIGN.md §4, T4').

**Identity, `seq`, equivocation.** Unchanged from DESIGN.md §5: equal `(author, seq)` on distinct records is an equivocation ordered by `(height, t, h)`; a self-received `seq ≥ seq_self + 1` raises `CLONE_SUSPECTED` and jumps `seq_self`. `seq` remains the equivocation witness and the fourth tie-break.

**Analysis.**

*Equal-height concurrent writes.* Two writers that saw the same floor emit the same height; the order is then `t`, so the later wall-clock edit wins and a clock behind loses, as in the baseline. Equal `t` falls to `author`: deterministic, pk-grindable only at millisecond coincidence. This is the one place wall time decides, and the place it should.

*The ceiling pin, honestly compared.* `M` emits `PUT(c) v=(maxceil, 2^48−1, M, …)`. Honest `U` writing `c` clamps to `maxceil`, has `t < 2^48−1`, is `SHADOWED` everywhere until a roster raises `maxceil`; then `U` chases to `old maxceil + 1` and wins. `DEL(E)` at the ceiling likewise makes `E` un-recreatable until refresh. The baseline's ceiling pin is identical (clamp, tie by ground pk, refresh ends it), and in both designs `M` re-pins in one record until revoked. The difference is below the ceiling. In the baseline a pin at `t_far < maxceil` is a *Lamport-ization*: later honest writes chase to `t_far + k`, concurrent honest writes tie by `author` rather than wall time, until wall time passes `t_far`, up to 400 days. In E a sub-ceiling pin costs nothing after the first chase: honest writes land at `H + 1` and concurrent ones still tie by honest `t`. Conversely, nothing in E ever "passes" a ceiling pin: the baseline's schedule-driven refresh arrives within a horizon by A3, whereas E's alarm needs a root online *after* the pin. Same liveness assumption, event-driven instead of calendar-driven.

*Does `height` re-create causal-length saturation?* The incident was an unbounded `u64` counter, max-merged, with presence in its parity, where a peer-supplied `UINT64_MAX` made the honest `+= 1` wrap and lose forever. Here: (1) `height ≤ maxceil ≪ 2^48` by admission, so a record carrying `2^48 − 1` is held nowhere; (2) at the ceiling, emission clamps and reports `SHADOWED`; nothing wraps (T13); (3) the maximum means nothing: presence is the view `exists`, a record at the ceiling is an ordinary record that ties; (4) `maxceil` only grows (T4'); (5) height is the first component of a total order ending in `h`, not a merged register. The residue is the baseline's: `height = maxceil` is a regime with distinct behaviour, the H6 blemish the mathematics judge noted for `t = ceil`.

*Not candidate C.* No replica checks `height = floor.height + 1`; a lying height is a pin bounded by the ceiling, not a validity failure, so trimmed and untrimmed replicas cannot disagree about any record's standing.

*`DEL` at `h` and a `PUT` at `h + 1` that never saw it.* `d = DEL(E) v=(h, t_d, …)` means `E`'s floor was `h − 1` at emission. A `PUT p` on `(E, f)` at height `h + 1` from a writer that never held `d` must have chased a `PUT p'` at height `h` on the same cell, itself concurrent with `d`. Then `p > d` on height alone: `p` is live, `p'` and every other field below `d` are dominated, and `E` exists with the one field `f`, the baseline's partial-record outcome. What differs is the deciding quantity: the baseline decides `p` vs `d` by wall time; E by chain length first (two writes beat one), wall time only at equal length. `d` is not dominated by `p` (a `PUT` never dominates a `DEL`), stays in `F` as `deleted_at`, and expires at `t_d + del_ttl` by the honest `t_d`.

*Decoupling `t` from the order without breaking convergence.* The frontier is a function of the held set (T3); expiry is a per-replica removal of a held `DEL`, apply-then-expire, so T11's argument is textually the baseline's: a replica still holding `d` re-sends it, the other re-applies (re-dominating anything it resurrected) and re-expires, one frame per session until both expire. Expiry depends on `d.t` and `now_local` only; it must, because any local-first-seen variant lets two replicas with staggered expiry re-seed each other forever. What expiry gains is that `d.t` is the deleter's real time (§6).

*Backup restore.* A restored device re-emits old `seq` values (equivocation, flagged, `seq` jumped) and writes from stale floors: to a cell others have since written once it lands at equal height and wins by `t`; to a cell written twice or more it loses by height. The baseline's restored device wins every such conflict (`t = now`). Re-offered backup records are dominated unless their `DEL` expired, as before. *Cloned key.* Clones chase the same floors, tie by `t`, converge, and are flagged by the `seq` collision. Unchanged.

**H8, what changes.**

| Case | Effect in E | Bound |
|---|---|---|
| Clock ahead by δ | Wins *equal-height* conflicts; cannot shadow below the ceiling; `far` flags exactly its records; its tombstones live δ longer | its own records; no chase propagates δ |
| Clock behind | Loses equal-height conflicts; read-your-writes holds by height; its tombstones expire early (§8) | its cells and tombstones |
| Backup restore | Stale-floor writes lose to any chain of length ≥ 2 | self-detected; flagged |
| Malicious | Overwrite or delete any cell; pin at `maxceil` with far `t`; force refreshes; flood; immortal own tombstones (`t = 2^48−1`) | `height ≤ maxceil`; pins end at refresh; refreshes rate-limited, attributable; floods and immortal tombstones end at `REVOKE` plus owner `DEL`s, which live `del_ttl` |
| Root restored | Lower `ceiling_h`: `maxceil` never decreases, `REVOKE`s never lost | unchanged |

## 4. Reconciliation and digest

Unchanged from DESIGN.md §8: element key `kind ‖ ent ‖ field ‖ h`, the 4096-bit accumulator, `digest = fp(F|ns)`, 16-way RBSR with HAVE round, Noise XX sessions, current-epoch-only bundles. `h` commits to `height`, so a record and its re-heighted twin are distinct elements. Inadmissible elements (`height > maxceil`) are skipped and re-offered, with the baseline's per-session tax.

## 5. Authorization, encryption, revocation

Unchanged from DESIGN.md §6: membership is key possession, epoch keys are a hash chain, bundles are accepted under the current epoch only, `REVOKE(X, from_t)` is grow-only and sets the `void` view flag on `X`'s records with `t ≥ from_t`, never a prune (the mathematics judge's divergence argument applies verbatim).

One consequence improves. In the baseline an honest record written before a theft but chased above a far floor carries `t ≥ from_t` and is wrongly voided; in E `t` is the real time of writing, so `from_t` voids exactly what an honest-clocked thief wrote after `from_t`. A back-dating thief escapes `void` in both designs; the answer remains the owner's `DEL`s.

## 6. Storage and GC

**Layout.** Unchanged from DESIGN.md §7 except per-cell version metadata: 6 + 6 + 6 + 32 bytes plus the cached 32-byte `h`, six bytes more per cell than the baseline.

**Drop rule.** Textually the baseline's:

```
dom(x, F)                                                  -- deterministic, membership-free (T3)
∨ (x is DEL ∧ now_local ≥ x.t + ROSTER_max.del_ttl)        -- apply-then-expire, local
```

but `x.t` is now what the deleter's clock read. **The motivation, quantified.** Baseline: `M` pins entity `E` with `PUT v=(t_far, …)`, `t_far = now + δ`, `δ ≤ 400` days. The owner's `DEL` must chase to `d.t = t_far + 1`, so every replica keeps it until `t_far + 1 + del_ttl`: the tombstone lives `δ + del_ttl`, up to 580 days with the default 180; every later `DEL` on `E` also chases above `t_far`; a flood of `N` pinned entities costs `N` such tombstones after the owner cleans up (the attacker judge's A-2). E: `d = (pin.height + 1, now, O, …)` dominates the pin at once, frees its bytes, and expires at `now + del_ttl`. The attacker's clock lead buys nothing; the `N` cleanup tombstones live exactly `del_ttl`.

**What the expiry clause can do wrong.** The baseline's straggler (a holder of a dominated `PUT` reconnecting after every replica expired `d`) resurrects one field under the same A4. Two E-specific cases. A `DEL` by a device with a clock far behind (or none, `t = 0`) is applied, frees the entity's values, then expires at once everywhere, leaving no tombstone; any stale lower-height `PUT` arriving later resurrects a field with no A4 violation. The baseline has this only when the entity's last write was already older than `del_ttl`. And an attacker's `DEL` with `t = 2^48 − 1` never expires by itself; the owner removes it with one `DEL` above it (after a refresh if pinned at the ceiling), whose tombstone expires normally.

**Bounds.** `|F(ns)| ≤ live cells + DELs younger than del_ttl by their own t + 1 roster + revocations (≤ 1024)`, unchanged in form; the tombstone term is now bounded by honest `t` rather than by `maxceil_t + del_ttl`.

## 7. Assumptions

- A1, A2, A4, A5 unchanged from DESIGN.md §9.
- A3 (restated). Some root device refreshes the roster within each horizon *and* within a bounded delay of any `near_ceiling` record it holds. Without it, writes at the ceiling degrade to `t`-then-author ties; convergence is unaffected.
- A6 (new, tombstone durability only). A deleting device's clock is not behind real time by more than `del_ttl`. Not needed for convergence.
- No clock assumption for convergence; wall-clock quality decides equal-height conflicts and tombstone lifetime, nothing else.

## 8. Known weaknesses

- **Chains beat clocks.** Among concurrent writes E is not wall-clock LWW: a device that edited a cell twice while offline beats one that edited it once, later, from the same floor. A laptop's Tuesday edit loses to a phone's two Monday edits. Deterministic and bounded, but it is the "most-ops-wins" residue of causal length, and the baseline would have kept the later edit.
- **A ceiling pin has no natural end.** Both designs end ceiling pins only at a refresh, but E has no regime where time heals anything, and only the alarm nudges a root to act. An offline root leaves every pinned cell shadowed indefinitely; a malicious writer re-pins after each refresh until revoked.
- **Height space is a consumable.** Each refresh adds `2^28`; `2^20` refreshes exhaust `u48`. A writer that pins after every refresh forces at most one refresh per hour, so exhaustion by attack takes 120 years, but it is a resource the wall-clock ceiling did not expose, and it ends in a re-founding.
- **Tombstone durability depends on the deleter's clock.** A clockless or badly behind device's deletes free bytes and leave no tombstone, so stale fields from any laggard resurrect; a clock far ahead leaves tombstones that live too long. The baseline's chase accidentally protected clockless deleters of recently written entities.
- **Immortal attacker tombstones.** `t` is unbounded by admission, so an attacker's `DEL` with `t = 2^48 − 1` expires only when the owner dominates it with its own `DEL`, one per entity, after a refresh if pinned.
- **Inherited from the baseline.** A thief's pre-revocation overwrites stand (flagged); back-dated `t` escapes `void`; floods need `REVOKE` plus owner `DEL`s; inadmissible records cost a per-session retransmission; the `height = maxceil` regime has special semantics.
- **Six more bytes per record and per cell**, and `h` commits to `height`, so a migration cannot reuse any existing signature.

## 9. Proof obligations

Status against `formal/lean/Kome/Frontier.lean`: **U** survives with no change to its text, **R** needs restating (same proof shape), **N** is new, **✗** is paper-only or the long pole.

- **T1 (R) Total order.** `Version` gains `height`; `Version.lt` has five components; `lt_irrefl`, `lt_trans`, `lt_trichotomy` are the same `omega` scripts over five fields.
- **T2 (U) Monotone domination**, **T2' (R) Upward closure.** `dominates`, `Dom_mono`, `dominates_trans` are unchanged in text; `dominates_trans` and `dominates_irrefl` unfold `Version.lt` and re-elaborate.
- **T3 (U) Frontier homomorphism.** `exists_max_dominator`, `F_sandwich`, `F_prefix`, `F_suffix`, `frontier_hom`, `F_idem` never inspect a version.
- **T4 (R) Convergence.** `applyAllF_mem`, `convergence_F`, `applyAllA_view`, `convergence` are unchanged; only `adm` changes: `adm c (put _ _ v _) = decide (v.height ≤ c)`, likewise `del`. Statement as DESIGN.md: same records in any order with duplication give the same `(F, maxceil)`; after a complete exchange both hold `F(H_A ∪ H_B)`.
- **T4' (R) Monotone admission.** `adm_mono` with `height`; `maxceil` never decreases (`le_ceilAll`, `maxCeil_*` unchanged).
- **T5 (U) View determinism.** `cell_unique` and the view definitions are unchanged.
- **T6 (U) Digest.** Unchanged (paper: accumulator algebra over element hashes).
- **T7 (✗) Reconciliation.** Unchanged statement, still the long pole.
- **T8 (N) Chase.** `emitH floorH c := min (floorH + 1) c`; `floorH < c → floorH < emitH floorH c`; always `emitH ≤ c`; `seq_emit` exceeds every `seq` this device emitted. Replaces `emitT`, `chase`, `emitT_le`.
- **T8' (N) Concurrency by wall time.** `a.height = b.height → (Version.lt a b ↔ (a.t, a.author, a.seq, a.h) <_lex (b.t, b.author, b.seq, b.h))`. Trivial from the definition; it is the theorem that `t` decides exactly the concurrent case.
- **T8'' (N) Chain dominance.** `a.height < b.height → Version.lt a b`, whatever `a.t, b.t`. The honest statement of weakness 1.
- **T9 (R) Bounded pin.** `adm_put_le` with `height`: no admitted data record has `height > maxceil`; after a roster with a higher `ceiling_h` is applied, every honest write to any cell has `height > ` every previously held record's and is unshadowed.
- **T10 (U) Equivocation.** Equal `(author, seq)` records are ordered by `(height, t, h)` identically everywhere.
- **T11 (liveness, U) Tombstone expiry.** Under A4, after every replica has expired `d`, no replica holds a record `d` dominated; apply-then-expire makes two replicas differing only in `d`'s expiry agree after one exchange. The proof does not mention how `d.t` was chosen.
- **T11' (N, paper) Pin-independent tombstone lifetime.** For every honestly emitted `DEL`, `d.t = now_ms` at emission, so every replica drops `d` at `d.t + del_ttl` regardless of the heights or `t`s of the records it dominated. One line from the emission rule; the theorem the baseline cannot state.
- **T12 (U) Revocation locality.** Unchanged.
- **T13 (R) Bounds.** Every emitted record satisfies the §2 layout; `height`, `seq`, `t`, `gen`, `rev_seq` never wrap; `height_emit ≤ maxceil ≤ 2^48 − 1`; roster emission fails `CEIL_EXHAUSTED` with no side effect at the bound.
- **T14 (✗) Epoch secrecy.** Unchanged, paper reduction.

Lean delta: one structure field, one `adm` clause, three replaced lemmas, three new one-liners; the file is otherwise untouched. Two days, not weeks.

## 10. Self-score

- **C1 = 4.** Same theorem, same assumptions (A1, A2, nothing about clocks), same exchange form forced by the ceiling; T11 now has a one-line pin-independence corollary.
- **C2 = 4.** Everything the baseline bounds, plus: sub-ceiling pins have no after-effect, cleanup tombstones live `del_ttl` not `δ + del_ttl`, no false-positive `void`; minus a burnable height budget and attacker tombstones that outlive the owner's inaction.
- **C3 = 4.** 82 bytes of version per cell (+6), one record per entity, values freed on `DEL`; the tombstone term of `|F|` is bounded by honest time rather than `maxceil_t + del_ttl`.
- **C4 = 4.** Unchanged from the baseline: cacheable homomorphic fingerprint, log-round RBSR, blind relays, current-epoch bundles.
- **C5 = 3.** Unchanged: removed member keeps what it saw, back-dating escapes `void`, bundles need the current epoch; `from_t` is now accurate for honest-clock thieves.
- **C6 = 4.** Same trusted core (`<`, `dom`, `F`, `fp`, emission); the Lean model changes in `Version`, `adm` and three emission lemmas; the expiry clause is the only impure one.
- **C7 = 4.** Unchanged: same primitives, no HLC, clock optional for emission; six more bytes per record.
- **C8 = 3.** One rule still; concurrent edits resolve by wall time only at equal chain length, which an app must be told; `far` and `near_ceiling` are meaningful flags; partial records on delete-versus-edit remain.
- **C9 = 4.** No sentinels, `height = 0` ordinary, exhaustion refuses; the `height = maxceil` regime and the `now_local` clause are the same two blemishes the baseline carries.
