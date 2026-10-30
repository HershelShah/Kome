# Implementer's verdict on the four redesign candidates

Lens: adversarial, "I have to build this in SPARK behind the C ABI and prove it
in Lean". Inputs: REQUIREMENTS.md (H1–H8, C1–C9), formal/spark/CONVENTIONS.md
(bounded, pointer-free, Formal_* containers, no recursion without a variant,
no tasking), PERF.md §1–§2 (Ed25519 verify = 130 µs and dominates; sign =
44 µs; everything else is rounding error), include/sync_engine.h (ABI v4).

Scored here: C3 (metadata/GC), C4 (sync/transport), C6 (trusted core), C7
(footprint), C8 (ergonomics). Convergence strength, blast radius, privacy and
hygiene (C1/C2/C5/C9) are other judges' business; I mention them only where
they change what has to be built.

Shared facts that apply to every candidate, so they do not move the ranking:

- Every candidate's main state is a map keyed by cell/dot/entry whose size is
  "number of records". SPARK bounds that with a `Formal_Ordered_Maps` capacity
  constant and a refusal (`Err_Nomem`). "Bounded by capacity" below means
  exactly this; it is acceptable under H5 but it is not "bounded by the type".
- Every candidate uses the M3 range-based set reconciliation (RBSR) shape. The
  session's working set (outstanding range descriptors, leaf buffers) needs
  the same capacity bound the current engine's `sync_session` has.
- Every candidate needs one Ed25519 verify per genuinely new record. 100k
  records of first sync = 13 s of verify on one core (PERF ch.4 parallelism is
  compiled out under WASM). Where a candidate can skip verifying records that
  would not change state (PERF ch.2) I say so; where it cannot, that is a
  real regression.
- The C shim allocates (`sync_free`, `sync_changes_free`); that is outside the
  SPARK core for every candidate and is not counted against anyone.
- Elements up to 64 KiB in a ≤4-element LEAF exceed a UDP datagram for all
  four; this is today's limitation and stays.

---

## Candidate A — hardened LWW (`A-hardened-lww.md`)

### 1. H5 boundedness

| Structure | Bound | How |
|---|---|---|
| PUT record | 80 + flen + vlen ≤ 65 647 B + 64 sig | fixed by type (ns 16, ent 16, field ≤32, value ≤65 535) |
| DEL record | 77 B + 64 sig | fixed by type |
| ROSTER record | ≤ 1 + 16 + 32 + 16 + 6·4 + 4 + 1 + 64·137 + 2 + 1024·38 ≈ **47.8 KiB** | fixed by type (members ≤64, revoked ≤1024) |
| Version `v` | 76 B (t 6, seq 6, author 32, h 32) | fixed |
| Frontier `F` (cell → offset, v) | #live cells + #DELs < del_ttl + 1 | **by capacity**; DEL count is time-bounded (A4), not type-bounded |
| Per-author seq table | ≤ 64 × 38 B | fixed (replicated roster parameter n_members) |
| Accumulator block prefix | ⌈N/64⌉ × 512 B (8 B/elem amortized) | by capacity, derived from F |
| Equivocation detection (author, seq → h) | ≤ |F| | by capacity; only among held records |
| Session state | RBSR descriptors | by capacity |

Dynamic allocation / recursion: none required. `dom` is a lookup of one cell
and one entity's `deleted_at`; `F` is maintained incrementally. 4096-bit
addition is a 64-limb loop. **Missing primitive**: monocypher has no
BLAKE2b-XOF; the 512-byte `acc(e)` must be built as 8 × BLAKE2b-512(h ‖ i),
which is a construction the Lean side must then treat as a PRF — fine, but it
is not "BLAKE2b-XOF" and the doc should say so. Removing an element from the
block-prefix array is O(N/64) 512-byte subtractions (~1.5k limb-ops × 64 at
100k) ≈ 50 µs, comparable to a sign; a Fenwick layout fixes it if it matters.

H6: no sentinels; `t = 0`, `seq = 0` are ordinary; `Option` floors are explicit
tags. Exists is a view (one derivation). Good.

### 2. Overhead and sync cost

- Wire: PUT ≈ 144 + flen B over the value; DEL = 141 B; a new entity costs
  **one** signed record (today: two — PERF backlog item 5 is solved by
  construction).
- RAM per cell: 76 B version + 64 B key (ns, ent, padded field) + 8 B offset +
  map node ≈ 150–170 B; signature stays in the log. A deleted entity with k
  fields costs one 141 B DEL frame.
- Per replica: ≤ 48 KiB roster, 2.4 KiB seq table, 8 B/element accumulator
  blocks. No vectors, no per-peer state.
- Sync, n records, d differences: ⌈log₁₆ n⌉ + 2 rounds (7 at 100k), O(d·log₁₆ n)
  descriptors of ≈194 B (keys are 81 B) plus d elements. Fingerprint is a
  homomorphic sum, so the per-element `acc` and the block prefixes are
  **cacheable across sessions** — PERF ch.3's O(1) gossip path survives.
- Verifies per synced record: **1**, and only for records that `dom` does not
  reject first (verify-on-win is sound here because a dominated record reaches
  no state). ROSTER: 1 verify + 1 X25519 + 1 AEAD open per member.

### 3. Trusted core

Mechanisms to implement and prove: (1) total order `<` on versions, (2)
`dom`/`F` — which is simultaneously merge, GC and the digest's element set,
(3) emission rule (chase + ceiling clamp + seq), (4) ROSTER: membership, epoch
key wrap, revocation list, ceiling, `del_ttl`, (5) `void` view, (6) TTL
tombstone clause, (7) 4096-bit accumulator + fp, (8) RBSR. **8**, and (2)
is the only one with real content; (3), (5), (6) are small pure functions of
`F` and one clock reading. No checkpoints, no fences, no epochs beyond a key
wrap, no fold. The smallest core of the four.

Adversarial notes: the session must deliver a newer ROSTER before elements
above the receiver's stale ceiling, or those elements are skipped and the
session ends unconverged ("the roster is in the first range" is a sort-order
fact, not a delivery-order guarantee — rounds are per range, in parallel). T4
is therefore honestly stated in exchange form, but the implementer must
re-run the session after a roster bump. The 48 KiB ROSTER in a 4-element LEAF
does not fit a BLE or UDP message; it needs its own fragmentation path.

### 4. Ergonomics

- `set(ns, ent, f, v)` → emit PUT, status OK | SHADOWED | SEQ_EXHAUSTED.
- `get` → `cell(ns,ent,f)`, NOTFOUND if absent, flagged if `void`.
- `delete(ns, ent)` → emit DEL; `list(ns)` → entities with ≥1 live field.
- Concurrent conflict: **silent LWW** by `(t, author, seq, h)`; the loser is
  gone; nothing is surfaced. Same as today.
- Concurrent delete vs. edit: resolved by `t`; a resurrected entity carries
  only the fields newer than the DEL (partial record). A straggler older than
  `del_ttl` resurrects one field (zombie); user re-deletes.
- No field removal exists: `PUT ""` is a legal value, not an unset (same gap
  as `sync_engine_erase_field` today).
- Leaks to the app: SHADOWED (read-your-writes failed at the ceiling),
  CLONE_SUSPECTED, void flags; **16-byte `ent`** means human-readable entity
  ids must be hashed and the original name stored as a field — `scan` can no
  longer return the app's own keys. No read-time policy knobs.

### 5. WASM / embedded

- RAM at 100k cells: ≈15–17 MB index + 0.8 MB accumulator + 48 KiB roster;
  values stay in the log. At 10k: ≈1.7 MB.
- Code: today's engine minus HLC and capability graph, plus 64-limb addition
  and the XOF construction. Smallest delta.
- Clock: optional for emission (`now = 0` works, cells go Lamport); required
  only for TTL GC and, on root devices, roster refresh. No threads, no OS
  beyond a byte log.

### 6. Migration

- Data: importable by re-signing every live cell under the importing device
  (100k × 44 µs ≈ 4.4 s). `t = hlc.physical` fits u48. **Authorship is lost**.
  Entities >16 B (the blob layer's `'c'0x00‖32-byte hash` = 34 B) must be
  re-keyed; blob chunk values (32 KiB) fit.
- ABI: `set/get/delete/exists/scan/session_begin/step/end/digest/open/flush/
  compact/batch_*` keep their shapes; `sync_change` changes (no HLC struct, no
  `causal_length`, kind set PUT/DEL/ROSTER); `sync_capability_*`,
  `grant/revoke/is_revoked` are replaced by a roster API; `sync_session_begin_
  scoped` becomes implicit (membership is the only mode). ABI version bump,
  ~70 % of call sites unchanged.

### 7. Proof effort

Lean: T1 (1 pw), T2/T3 frontier homomorphism with cross-kind DEL domination
(2), T6 accumulator algebra (0.5), T7 RBSR (3), T8/T9 chase arithmetic (1),
T10/T12/T13 (1), T11 TTL as a stated-assumption lemma (0.5): **≈ 9 pw**.
SPARK: codec, `F` map + apply, emission, roster/wrap, accumulator + prefixes,
RBSR session, log/compaction, GC: **≈ 14–16 pw**. Total **≈ 24 pw**.

### Scores

- **C3 = 4** — 76 B/cell, one record per entity, DEL frees values at once; TTL tombstones and a 48 KiB roster element are the costs.
- **C4 = 4** — plain set-union RBSR with a cacheable homomorphic fingerprint; roster-before-elements ordering and inadmissible skips can cost a second session.
- **C6 = 4** — `dom`/`F` is merge, GC and digest in one; ceiling, chase, TTL and void are four small satellites; T11 needs a timing assumption.
- **C7 = 4** — smallest code delta, clock optional; 4096-bit sums and an XOF construction monocypher lacks.
- **C8 = 3** — silent LWW, partial records on delete/edit races, SHADOWED/void flags, and 16-byte entity ids break app-readable keys.

---

## Candidate B — causal ORSWOT with evidence (`B-causal-orswot.md`)

### 1. H5 boundedness

| Structure | Bound | How |
|---|---|---|
| Element | 119 B header + pt ≤ 65 682 B | fixed by type |
| Context `ctx` | 256 × ≤128 B = **32 KiB** | **fixed by type** (slot is u8) |
| `live : dot ⇀ elem` | #live field writes | by capacity |
| (rid, fld) → dots index | ≤256 dots per field (one per slot) | per-field bound fixed; number of fields by capacity |
| Pending buffer | ≤4 096 elements — **× 65 KiB = 268 MB worst case** | count-bounded, **not byte-bounded**: must be fixed |
| Roster (enrollments) | ≤256 × ~130 B | fixed |
| Fences | ≤256 | fixed |
| Keybox | members × 72 B, latest only | fixed |
| Hash chain | 2^16 epochs; derive older keys by hashing | fixed; up to 65 536 BLAKE2b per derivation (≈80 ms) |
| Equivocation proofs | 212 B each; needs a bounded ring | add a constant |

Dynamic allocation / recursion: none. `Entry` is a discriminated record, the
context a 256-array of it — the most SPARK-native state of the four. `seq ≤
2^63` is a decode refusal, not a wrap.

### 2. Overhead and sync cost

- Wire per field write: 119 B over the plaintext (dot 9, epoch 2, nonce 24,
  len 4, tag 16, sig 64) + 2 B pt header. k concurrent values keep k copies.
- RAM per live dot: 9 + 32 (H) + 8 (offset) + the (rid ≤64, fld ≤64) index
  key ≈ 110–180 B depending on key packing. Per replica: 32 KiB ctx + ≤33 KiB
  roster + keybox. **A delete costs zero replicated bytes**: it travels as a
  context entry (≤128 B per slot per session), not as a tombstone.
- Sync: HELLO (ctx hash + differing entries, ≤32 KiB worst, ~0.6 KiB for 5
  devices) + ⌈log₁₆ n⌉ rounds + finalize ⇒ 8 rounds at 100k. Descriptors are
  the cheapest of the four (keys are 9 B). Fingerprint is an unkeyed 256-bit
  sum: cacheable, but admittedly weak against a member (§8.5).
- Verifies per synced record: **1** per new element (cannot be skipped: a new
  dot always changes state) + 1 per differing context entry per session
  (evidence) + 1 per fence. AEAD open + one BLAKE2b per element to index it.

**The implementation trap.** Invariant `d ∈ dom live ⇒ seen(ctx, d)` plus
`Seen{n}` meaning "all of 1..n seen" forces per-writer contiguity: `(s, 9)`
cannot be committed while `(s, 5..8)` are unresolved, and `ctx` can only be
joined at **finalize** (joining it earlier and then losing the session would
make A believe B's un-received live dots are removals and later drop them
from a third peer — silent data loss). So every element received in a
session sits in the pending buffer until the session completes. RBSR delivers
leaves in arbitrary range order across rounds, so an initial 100k-element
sync needs a 100k-element pending set, or overflows the 4 096 cap and
"refetches later" — up to N/4 096 ≈ 25 sessions, each O(N log N), to finish
a first sync. The fix (per-slot live counts in HELLO so `ctx[s]` can be
adopted once that slot's live dots are all in) is a protocol change the
document does not contain, and it is the piece T-RBSR must then cover.

### 3. Trusted core

(1) Entry lattice, (2) per-dot status lattice, (3) state join including the
fence subtraction, (4) local write = observed-remove, (5) enrollment/slots,
(6) fences, (7) epoch hash chain + keybox, (8) RBSR + **finalize** (removal
inferred from absence + context — the protocol is semantically load-bearing,
not a transport), (9) pending/contiguity buffer, (10) read policies ×4.
**10**, but (1)–(4) are textbook lattice algebra and GC is literally "drop
what is not live". The hard part is (8)/(9): T-RBSR here proves that a
protocol with message loss computes `S_A ⊔ S_B` with pre-session contexts;
the other candidates' RBSR only has to prove "both hold the union".

### 4. Ergonomics

- `set(rid, fld, v)` → mint dot, drop observed dots of that field.
- `get(rid, fld, π)` → `π(live set)`; `π = all` returns the conflict set.
  **The current `get` signature needs a policy argument or a `get_all`.**
- `delete(rid)` → drop every visible dot; `list` → rids with ≥1 live dot
  (needs a rid → count index).
- Concurrent conflict: **both values visible**, policy picks; honest and
  resolvable. `max-dot` is arbitrary, `app-stamp` pushes a timestamp into the
  app's value encoding — a leak the app author must understand.
- Concurrent delete vs. edit: add-wins partial record (only the edited
  field). No TTL zombies at all — the cleanest delete story.
- Cliff: **256 enrollments per collection, ever**; a reinstall burns a slot;
  re-founding re-mints and re-signs every dot (100k × 44 µs = 4.4 s, plus
  every peer wipes and resyncs). This is an app-visible event.

### 5. WASM / embedded

- RAM at 100k: ≈12–25 MB (key packing decides) + 32 KiB + pending (must be
  capped in bytes, e.g. 1 MiB, which makes the first-sync problem above
  worse). At 10k: ≈1.5–2.5 MB.
- Code: lattice join, RBSR + finalize, hash chain. Moderate.
- **No clock anywhere** — the only candidate with a truly clockless core. No
  threads, no OS.

### 6. Migration

- Data: importing device takes slot 0 and re-mints every live cell as a fresh
  dot (N signs, N encrypts). Authorship and HLCs lost (HLC can be embedded as
  an `app-stamp`). Entity ≤64 B and value ≤65 536 B cover the blob layer.
- ABI: `set/delete/exists/scan/session_*/open/flush/compact/batch_*` keep
  shape; `get` changes (policy); `sync_change` → element | ctx entry | fence
  (apply must accept three kinds); capability API → enroll/fence; digest
  changes. ~55 % preserved.

### 7. Proof effort

Lean: T-ENTRY/T-DOT/T-JOIN product lattice with the fence clause and the
`n ⇒ evidence` dependency (3 pw), T-EVID/T-NOKILL (1), T-GATE (1),
**T-RBSR with finalize semantics under loss (4)**, T-FP/T-GC/T-READ (1):
**≈ 10 pw**. SPARK: ctx array, live map + field index, join, write/delete,
codec, AEAD/sign, hash chain + keybox, enroll/fence, RBSR + finalize +
pending, storage: **≈ 17–20 pw**. Total **≈ 28 pw**.

### Scores

- **C3 = 4** — 119 B per write, 32 KiB fixed, deletes travel as context entries, GC immediate and membership-free; k conflict copies and slot exhaustion.
- **C4 = 3** — cheapest descriptors, but finalize is load-bearing, contiguity forces session-atomic pending, first sync of a large set is multi-session as written, 256-bit sum is member-breakable.
- **C6 = 4** — the state is a SPARK record type and the join is lattice algebra; one point off because T-RBSR must prove a protocol, not a union.
- **C7 = 4** — no clock, small state; pending buffer must be re-bounded in bytes and the first-sync behaviour costs RAM or sessions.
- **C8 = 4** — visible conflicts, clean deletes, replaceable policy; `get` changes shape, `app-stamp` leaks, 256-slot re-founding is a cliff.

---

## Candidate C — signed logs (`C-signed-logs.md`)

### 1. H5 boundedness

| Structure | Bound | How |
|---|---|---|
| Entry | 195/235 B + payload ≤ 65 552 B | fixed by type |
| Ops per entry | ≤64; entity ≤64, field ≤32, value ≤16 KiB | fixed |
| Per-writer log since checkpoint | seq ≤ 2^62 | **by capacity only** — all superseded versions are retained until the writer checkpoints |
| CKPT series | ≤4 096 parts × 64 KiB = **256 MiB per writer** | fixed by type, but huge |
| Pending set | ≤1 024 per writer × 64 writers × 64 KiB = **4 GiB worst** | count-bounded, not byte-bounded |
| id → entry index (for `prev`/`link`) | one per held entry | by capacity |
| Fold index (entity, field) → (key, ref) | by capacity | |
| writer → cells index (for EXCLUDE recompute) | by capacity | |
| Grant/Exclude per key | ≤16 | fixed |
| Epoch keys referenced by effective(E) | ≤64 | fixed |

Recursion: resolving pending entries when a `prev`/`link` arrives is a
fixpoint over "chain descendants"; implementable as a loop with a variant
bounded by the pending cap, but it needs a reverse (waiting-on) index.
`effective(E)` has a covering clause that references other entries' void
status — the one predicate here that is not a per-element check.

### 2. Overhead and sync cost

- Wire: 195–235 B per entry; 3–4 B per op amortized at 64 ops/entry,
  **195 B per op unbatched**. Checkpoint cells 80 B each.
- RAM per cell ≈150 B + ≈50 B per held entry for the chain index; 100k cells
  ≈ 20 MB plus pending.
- **Checkpoints re-ship state.** A checkpoint is a full snapshot of the
  writer's live cells, signed as new entries. Every peer downloads it, verifies
  up to 4 096 signatures (≈0.5 s) and stores it before V1 lets it drop the old
  entries. For a 100k-cell writer that is ≈10 MB+ of transfer per checkpoint
  per peer. Between checkpoints every superseded version is kept. H4's
  "transfer proportional to the difference" holds only if you count a
  snapshot as a difference. Tombstone collection additionally needs **every
  member's** checkpoint frontier past the drop — the membership oracle H7
  forbids, admitted in §8.
- Per-session salted fingerprints: O(n) BLAKE2b per session, **no snapshot
  cache** (PERF ch.3 regresses from O(1) to ≈50 ms at 100k on a desktop,
  worse on a phone). Reconciling over `effective(E)` rather than `E` means a
  pending entry is re-fetched every session until its dependency arrives.
- Rounds ⌈log₁₆ n⌉ + 2 + head pre-exchange; descriptors ≈180 B (72 B keys).
- Verifies per synced record: **1 per entry** = 1/64 per op when batched —
  the only candidate that amortizes signatures — but never skippable (chain
  integrity), and checkpoint parts add 1 per 64 KiB of state.

### 3. Trusted core

(1) entry validation, (2) chain/tree with forks, (3) height check with
covering, (4) LWW fold with `(key, op_index)`, (5) `effective` (valid ∧
authorized ∧ ¬void(V1–V3) ∧ decryptable ∧ covered — a fixpoint), (6)
checkpoints: build, validity, series completeness, (7) tombstone-collection
predicate over member frontiers, (8) GRANT/EXCLUDE fold with `from_seq`, (9)
epochs sealed in the owner log, GRANT reseals ≤64, (10) writer-side rebase,
(11) RBSR + salt + head pre-exchange, (12) pending/covering resolution.
**12**, and (5)–(7) interact: an EXCLUDE arriving late un-folds cells whose
winners were that writer's, so the fold is not monotone in `E` and every
cell the writer touched must be recomputed from retained losers. Largest
core of the four.

### 4. Ergonomics

- `set` → append an OPS entry (the API must expose batching or pay 195 B
  per field); `get` → fold cell; `delete` → DROP; `list` → entities with live
  fields.
- Concurrent conflict: silent LWW by `(height, writer, seq, id)`; among true
  concurrents the **writer key** decides — deterministic, meaningless.
- Concurrent delete vs. edit: partial record (edit with height > DROP). Fork
  × checkpoint can resurrect a collected tombstone.
- Leaks: fork and rebase events; **pending visibility** (bytes arrived, not
  shown until `link` resolves — "edit from your laptop is on the phone but
  invisible"); the need to batch; checkpoint scheduling.

### 5. WASM / embedded

- RAM at 100k ≈ 20 MB + chain index + pending; building a checkpoint streams
  but validating a received one needs all parts held.
- Code: largest — chain/tree, covering, checkpoints, rebase.
- No clock, no threads, no OS. 16 KiB value bound breaks the 32 KiB blob
  chunks (`SYNC_BLOB_CHUNK_MAX`).

### 6. Migration

- Data: fold cells into 64-op entries (1 563 entries, 70 ms of signing).
  Authorship and HLC lost; blob layer must re-chunk.
- ABI: `set/get/delete/scan` keep shape; `sync_change`/`apply`/`export`
  change unit to entries; capabilities → GRANT/EXCLUDE ops; new surface for
  checkpoint trigger, fork events, rebase; digest changes. ~45 % preserved —
  the most change.

### 7. Proof effort

Lean: T-ORDER (0.5), T-FOLD reuse (1), **T-EFF monotone void + covering
fixpoint (4)**, T-CKPT (3), T-HEIGHT (2), T-TOMB as a writer-policy argument
over member frontiers (3), T-AUTH (1), T-RBSR + salt (3): **≈ 17 pw**.
SPARK: codec, chain index, pending/covering, fold with recompute, checkpoint
build/validate, truncation, auth, epochs, RBSR + head exchange, storage:
**≈ 26–30 pw**. Total **≈ 45 pw**.

### Scores

- **C3 = 2** — 195 B/entry, history retained until checkpoint, checkpoints re-ship the writer's state, tombstones need every member.
- **C4 = 3** — same RBSR, but salted fingerprints kill the snapshot cache and checkpoint traffic is O(state).
- **C6 = 2** — twelve interacting mechanisms; `effective` is a fixpoint and the fold is not monotone under EXCLUDE.
- **C7 = 3** — clockless, but the largest code and index footprint; 16 KiB values break the blob layer.
- **C8 = 3** — silent LWW by writer key, pending-visibility lag, forks/rebases and batching are app-visible.

---

## Candidate D — prior art assembly (`D-prior-art.md`)

### 1. H5 boundedness

| Structure | Bound | How |
|---|---|---|
| Record | 32 coll + 1 kind + 32 author + path ≤98 + 8 ts + 32 cap_ref + 32 epoch + body ≤16 KiB + 64 sig ≈ **203 B + path** overhead | fixed by type |
| Store (≻-maximal valid records) | ≤ #cells × W (64) candidates | by capacity; per-cell bound fixed |
| Index (author, path) | by capacity | |
| Index (ts, h) with fingerprint sums ("order-statistics B-tree") | by capacity | pointer-free B-tree with monoid annotations in SPARK is a project; a sorted array + prefix sums (today's shape) substitutes |
| Pending buffer | ≤256 records × 16 KiB = 4 MiB | fixed |
| Cap chains | depth ≤4, window ≤2^44 µs | fixed |
| Auth records (Cap, Rev, Clamp, Seal) | "kept forever", W × renewals | **unbounded over time** by the type; a capacity constant plus refusal is needed, and an old Cap cannot be dropped without a reference count (a derived invariant, H6-adjacent) |
| Seal | ≤64 boxes × 48 B; two-parent epoch DAG | fixed per seal; DAG by capacity |
| HLC | `ts = l·2^16 + c`, u64 | fixed; `c` overflow is a plain +1 |

Recursion: cap chain validation is a ≤4 loop. Epoch DAG "writers use the
newest epoch by (ts,h) among epochs whose parent chain they hold" is a
bounded walk. No dynamic allocation.

**Spec defect that moves the proof:** §3 says `valid(r)` is a function of
`r` alone, and T-1/T-2 are stated that way; but validity requires the cap
chain, which is other records in `S`. `valid` is `valid(r, S)`, monotone in
`S`. T-2 must be re-stated over (record, held caps) and the pending-buffer
drop/refetch rule must be in the theorem. Not fatal, but it is the first
thing the Lean work will hit.

### 2. Overhead and sync cost

- Wire ≈203 B + path per record — the heaviest per-record header (the 32 B
  collection id and 32 B `cap_ref`/`epoch` are repeated in every record; A
  spends 16 + 0 + 4 for the same information).
- RAM per record ≈250 B with two indexes; **a contested cell holds one
  record per author** (≤64) and a stale value of an absent writer persists
  until that writer returns or is revoked. 100k records ≈ 25 MB.
- Deletion is same-author only; other authors' bytes under a Tomb are freed
  only by the **maintenance rule** (each shadowed author writes its own Tomb:
  k extra signs, k extra TTL tombstones) or by `Rev`. A lost device's values
  stay forever unless the root revokes it — H7 "without a membership oracle"
  is met only by proxy of the root.
- Fingerprint is keyed per session: `f_k` must be recomputed for all n
  records every session — **O(n) BLAKE2b per session, no cache** (same ch.3
  regression as C), and the annotated tree must be rebuilt per key.
- Rounds: Meyer's 2 + 2⌈log₁₆ n⌉ (12 at 100k, or 7 with the current engine's
  variant); 16 B fingerprints and 40 B keys make descriptors ≈100 B; 4 KiB
  frames with coalescing (but a 16 KiB record cannot fit a 4 KiB frame —
  frames must negotiate up).
- Verifies per synced record: **1**, skippable when a held same-author
  record already prunes it (sound: pruned records reach no state); plus ≤4
  once per new cap chain.

### 3. Trusted core

(1) `≻` (prefix + hash + Rev clause), (2) max-set `store`, (3) view with
revoked/clamp filters and per-author candidates, (4) HLC tick/receive/clamp
to window, (5) `valid`: cap chain narrowing, depth, windows, (6) Rev/Clamp,
(7) Seal + two-parent epoch DAG + ≤64 boxes, (8) tombstone TTL + maintenance
rule, (9) keyed fingerprint monoid + range tree, (10) RBSR with frame
coalescing, (11) PIO handshake, (12) pending buffer. **12**; (1)–(3) are
short, (4)–(8) each carry their own small theorem and their own failure
modes (window expiry, DAG forks, dead writers).

### 4. Ergonomics

- `set` → mint Value with HLC under the device's Cap; **fails or clamps when
  the cap window has expired** (≤200 days; the root must renew every writer
  periodically) — an app-visible failure mode no other candidate has.
- `get` → `win` of `cand`; `cand` is exposed (one candidate per author,
  Automerge-style `getConflicts`). `delete` → Tomb at `(E)`. `list` → entities
  with a showing cell (needs an index).
- Concurrent conflict: LWW by `(ts, h)` for the shown value, losers visible —
  the best conflict presentation of the four, with no policy knob to leak.
- Concurrent delete vs. edit: last-action-wins by ts (partial record);
  resurrection of a same-author value after `T_gc`.
- **`Rev(K)` prunes everything K ever wrote** (no `from_ts`; `Clamp` is the
  only partial). Revoking a lost primary phone deletes its contributions on
  every replica unless the owner re-writes them under another key first — a
  race against the thief. A, B and C all keep pre-revocation writes.
- The engine writes records on its own (maintenance Tombs): signing cost and
  log growth the app did not ask for.

### 5. WASM / embedded

- RAM at 100k ≈ 25 MB (+ per-author candidates) + 4 MiB pending + two
  indexes.
- Code: cap chains, epoch DAG, PIO, range tree/coalescing — second largest.
- Clock: needed for HLC minting (degrades to `not_before` without one), for
  cap windows and for `T_gc`; root devices need it for issuance. No threads,
  no OS.
- 16 KiB value bound breaks the 32 KiB blob chunks.

### 6. Migration

- Data: re-sign under the importer's Cap; `ts` must be re-minted inside the
  cap window (old `hlc.physical` predates `not_before`), so original times
  are lost though relative order can be kept; `logical` (u32) does not fit
  the 16-bit `c`. Blob layer re-chunks. If several devices import
  independently, each cell gets one candidate per device **forever** (cross-
  author records are never pruned) — one device must import, the rest wipe.
- ABI: `set/get/delete/exists/scan/session_*` keep shape; `sync_capability_
  root/delegate/encode/decode/grant/revoke` map most naturally onto D's cap
  chains of all four; new: `Clamp`, `Seal`, `cand` read. ~70 % preserved.

### 7. Proof effort

Lean: T-1 (1 pw), T-2/T-3 max-set with `valid(r, S)` re-statement (2),
T-4/T-5 (1), T-9/T-11 (1.5), T-13 HLC (1), T-7 RBSR + frame coalescing (3.5),
T-10 GC with maintenance rule (1): **≈ 11 pw**. SPARK: codec, store + two
indexes, `≻`, view, HLC, cap validation, Rev/Clamp, Seal/DAG, pending, TTL +
maintenance, keyed fp + range structure, RBSR + coalescing, PIO, storage:
**≈ 22–26 pw**. Total **≈ 35 pw**.

### Scores

- **C3 = 3** — 203 B headers, O(authors) per contested cell, auth records forever, cross-author bytes freed only by cooperation or Rev.
- **C4 = 4** — tight RBSR bound, small frames, PIO; keyed fingerprints discard the snapshot cache and cap chains gate data.
- **C6 = 3** — `≻` + max-set is clean, but `valid` is not a function of the record, and HLC, windows, Clamp, epoch DAG, TTL and the maintenance rule each need their own lemma.
- **C7 = 3** — clock-dependent minting and windows, 25 MB at 100k, an annotated tree or a per-session O(n) rebuild, 16 KiB values.
- **C8 = 3** — best conflict surface, but cap expiry blocks writes, `Rev` deletes a device's whole history, and the engine emits its own tombstones.

---

## Ranking

| Rank | Candidate | C3 | C4 | C6 | C7 | C8 | Σ | Est. effort |
|---|---|---|---|---|---|---|---|---|
| 1 | **A** hardened LWW | 4 | 4 | 4 | 4 | 3 | 19 | ≈ 24 pw |
| 2 | **B** causal ORSWOT | 4 | 3 | 4 | 4 | 4 | 19 | ≈ 28 pw |
| 3 | **D** prior art | 3 | 4 | 3 | 3 | 3 | 16 | ≈ 35 pw |
| 4 | **C** signed logs | 2 | 3 | 2 | 3 | 3 | 13 | ≈ 45 pw |

**A over B on a tie.** A's reconciliation is today's RBSR with set-union
semantics and a cacheable fingerprint; its merge (`dom`/`F`) is the same
shape as the current engine's LWW, so most of the C++ → SPARK mirror work and
the M3 session code carry over, and its risks are performance-shaped
(4096-bit sums, a 48 KiB roster element) or policy-shaped (wall-clock LWW,
root liveness for the ceiling) rather than correctness-shaped. B is the
cleaner object for Lean and the only truly clockless core, and its conflict
and delete presentation is better, but its reconciliation protocol *is* the
semantics: finalize infers removals from absence, which forces session-atomic
context joins and a pending buffer that, as written, cannot complete a large
first sync in one session. That is a protocol redesign the document does not
contain, and it sits exactly where a mistake loses data silently. If the
other judges weigh C1/C2/C8 heavily enough to prefer B, the implementer's
condition is: add per-slot live counts to HELLO and prove T-RBSR against the
patched finalize before writing SPARK.

**D third.** It has the best conflict surface and the most ABI-compatible
authorization story, but its per-record header is the heaviest, contested
cells cost O(authors), deletion of other authors' bytes depends on their
cooperation or on root revocation (H7 by proxy), `Rev` erases a device's
entire history, cap windows expire on offline devices, and the keyed
fingerprint discards the snapshot cache that PERF ch.3 showed is the gossip
path's entire win. Twelve mechanisms, several with clocks in them.

**C last.** Signature amortization (1 verify per 64 ops) is genuinely
attractive given PERF's finding, but everything else costs more: history is
retained until a checkpoint, a checkpoint re-ships the writer's full state to
every peer and costs thousands of verifies, tombstone collection needs every
member's checkpoint, `effective` is a fixpoint over covering, the fold is not
monotone under EXCLUDE, and the estimated effort is nearly double A's.

## Single biggest implementation risk per candidate

- **A** — the 4096-bit homomorphic accumulator with a hand-built BLAKE2b
  "XOF" and O(N/64) 512-byte prefix updates, plus roster-before-elements
  ordering inside a session; both are solvable, neither is in the document.
- **B** — contiguity + finalize: `ctx` can only be joined at session end, so
  received elements must be staged until completion; as written a large
  first sync overflows the pending cap and a mid-session loss is either lossy
  or discards all received work.
- **C** — checkpoints: a full state re-ship per writer per peer with up to
  4 096 verifies, and `effective(E)`'s covering fixpoint on top of a fold that
  must be recomputed when an EXCLUDE arrives.
- **D** — `valid` depends on held cap records (so T-2 is mis-stated), and
  deletion/revocation semantics: other authors' bytes are freed only by
  their own Tombs or by a `Rev` that erases a device's whole history.
