# Data model: current, evaluation, and the proposed model

> Output of the data-model design loop. It states what Kome stores today, the
> problems the audit found, the candidate designs considered (with prior art),
> and a concrete recommended model with a migration path. Scope is Kome's actual
> use case: a **private, offline-first, serverless P2P engine for personal /
> structured records** synced across a user's own devices and with explicitly
> trusted contacts — *not* collaborative rich-text editing.

## 1. What we store today

A three-level key-value model: `(namespace, entity, field) -> value`, with two
CRDT types (`include/sync_engine.h:70-103`):

- **LWW register** per field — value + HLC + author, total order `(hlc, author,
  value)`, larger wins (`src/engine.hpp:42-50`, merge at `sync_engine.cpp:480-516`).
- **Causal-length set** for entity existence — a `uint64 causal_length` (odd =
  present), merged by `max(causal_length, then author)` (`engine.hpp:52-61`,
  merge at `sync_engine.cpp:448-477`). Deletion increments the counter; field
  registers under a tombstone are retained.

This is a sound, standard choice *for a key-value record store* — the same
family as Cassandra/Dynamo (LWW) and cr-sqlite. It is deliberately **not** a
rich-document/text CRDT (Automerge/Yjs); that is out of scope for the use case.

## 2. Problems the audit found

| Problem | Where | Impact |
|---|---|---|
| **Causal-length saturation** | `sync_engine.cpp:448-477`, local `+=1` at `:288,:341` | A peer-supplied `causal_length≈UINT64_MAX` pins entity presence; honest deletes (`+=1`) wrap and lose the merge → entity **permanently undeletable** (no-auth in open namespaces; WRITE-delegate-beats-owner in enforced). Confirmed empirically. |
| **No tombstone GC** | export skips `cl==0` only; digest includes hidden registers | Deleted entities + their field bytes are retained forever — unbounded growth for long-lived personal data. |
| **Two integrity surfaces** | causal-length counter *and* HLC | The counter saturates (above); the HLC has its own far-future pinning. Two separate sharp edges with two separate (hard) fixes. |
| **Concurrency semantics are "most-operations-wins"** | counter max | Neither cleanly add-wins nor remove-wins; the side that churned more ops dominates — surprising, though deterministic. |

The root cause is the **bare max-counter** existence model. It cannot be fixed
convergence-safely in place (a bound on the counter would be a clock-/history-
dependent accept/reject, which breaks deterministic convergence).

## 3. Candidate existence/deletion models

| Candidate | Concurrent add/delete | GC in serverless P2P | Metadata | Saturation/griefing | Model fit |
|---|---|---|---|---|---|
| **A. Keep causal-length** | most-ops-wins | none (today) | O(1) | ❌ saturates | special-case |
| **B. OR-Set / ORSWOT** | **add-wins (best)** | ❌ needs causal stability | O(actors) | ✅ immune | separate rule from fields |
| **C. LWW-existence register** | clock decides (LWW) | ✅ tractable (TTL/epoch) | O(1) | ⚠️ inherits HLC far-future (one surface) | **unifies with fields** |

- **B (ORSWOT)** is the gold standard for *correctness* — add-wins, immune to
  timestamp griefing, O(actors) metadata ([rust-crdt ORSWOT](https://docs.rs/crdts/latest/crdts/orswot/index.html),
  [Riak DT history](https://christophermeiklejohn.com/erlang/lasp/2019/03/08/monotonicity.html)).
  But removes are suppressed via a causal-context version vector that can only be
  pruned once the remove is **causally stable** (all actors have seen it). Kome
  is serverless with no membership oracle, so it can't cheaply decide stability —
  the same reason its delete is "best effort" at all. ORSWOT's headline benefit
  (no tombstones) is hard to realize here.
- **C (LWW-existence)** makes presence *just another LWW register*: a record
  `(present: bool, hlc, author)` merged by `(hlc, author)`. This is exactly
  [Earthstar's](https://earthstar-project.org/specs/data-spec-es5) choice for the
  *same* use case (private/offline-first P2P): newest-timestamp-wins, delete =
  newer "absent" write, plus TTL (`deleteAfter`) for physical purging. Willow
  similarly deletes by prune + a single tombstone. The honest caveat both
  document — *"deletion only works if all peers receive and honor the update"* —
  is inherent to open P2P and applies to every option.

## 4. Recommended model: **unify everything under LWW-by-HLC**

**Make entity existence an LWW register too**, so the engine has *one* merge rule
for the whole data model.

### The model

```
namespace
  └─ entity                       ← presence is an LWW register:
       ├─ (present: bool, hlc, author, sig)   (replaces causal_length)
       └─ field → (value, hlc, author, sig)   (unchanged LWW register)
```

- **Presence** = LWW register of a boolean. `set` writes `present=true@hlc`;
  `delete` writes `present=false@hlc`. Merge: larger `(hlc, author)` wins.
- **Fields** = unchanged LWW registers.
- **Delete drops the value bytes immediately** (privacy + space): on
  `present=false`, the entity's field *values* are discarded, keeping only a
  small tombstone `(entity, present=false, hlc)`.
- **Tombstone GC by epoch/TTL**: a tombstone older than a configurable horizon
  (e.g. 30 days, or an explicit `deleteAfter`) is purged. A peer offline longer
  than the horizon may resurrect — the documented, accepted best-effort bound
  (identical to Earthstar).

### Why this is best for Kome

1. **Kills causal-length saturation as a distinct bug.** No counter to saturate.
   Presence is HLC-ordered like everything else.
2. **Makes tombstone GC tractable without causal stability** — the one thing
   ORSWOT can't do cheaply here, and the audit's open growth problem. Earthstar
   proves this works for exactly this use case.
3. **Collapses the engine to a single conflict rule** (LWW by `(hlc, author)`),
   deleting the entire causal-length special case. Huge simplicity and
   ergonomics win — one rule to learn, one to test, one to reason about.
4. **Consolidates two integrity surfaces into one.** The residual griefing (a
   malicious *authorized* writer pins `present=true@hlc=MAX`) becomes the *same*
   already-documented HLC far-future limitation (`SECURITY.md`), with the *same*
   future fix (per-namespace clock domains + drift handling) — instead of two
   separate sharp edges. For the trust model (your devices + trusted contacts),
   this requires a broken trust boundary and is acceptable.

### What it costs (honest)

- **Concurrent add-vs-delete resolves by clock, not add-wins.** A delete with a
  newer HLC beats a concurrent re-add. For low-concurrency personal data this is
  predictable ("last action wins") and matches how fields already behave. If a
  future use case needs true add-wins (untrusted writers, high concurrency),
  **ORSWOT (candidate B) is the documented upgrade** — it slots in behind the
  same existence API.

## 5. The other axes (settled by the use case)

- **Field conflict resolution:** keep LWW register `(hlc, author, value)`.
  Correct for records; matches cr-sqlite/Earthstar. No change.
- **Collections / sets:** model a collection as *entities* (one entity per item),
  never an array inside one value. With LWW-existence, concurrent add/remove of
  items is clean and GC-able. This is a **documentation rule**, not an engine
  change — and it's the single most important guidance for app authors (an array
  stuffed in a value loses concurrent edits; entities don't). Already validated
  by `scn: ConcurrentAddAdd / ConcurrentDeleteDelete`.
- **Counters (optional, phase 2):** LWW can't sum concurrent increments. Add an
  **optional counter value-type** — a per-actor PN-counter (`actor → ±value`
  map, read = sum), O(actors) metadata. Self-contained new value-kind; doesn't
  touch existence or fields. Add only when "quantities/tallies" appear.
- **Schema / typing:** keep values **opaque bytes at the core** (the CRDT
  shouldn't encode schema). Provide a thin *typed-value convention* in the
  bindings (a 1-byte type tag: bytes / utf8 / int / counter) for ergonomics, not
  engine-enforced. Keeps the core simple; makes the API friendly.
- **Query:** out of scope for the CRDT core. Add one ergonomic read primitive —
  **scan entities in a namespace** (prefix iteration over the sorted map) — so
  apps can list a collection without exporting everything. SQLite backing already
  supports app-level queries over materialized state.

## 6. Migration from today

Pre-1.0 / R&D, so a wire change is acceptable. Bump **codec v2 → v3**:

- Existence record signed content changes from `(…, causal_length:u64, author)`
  to `(…, present:u8, hlc:{physical:u64, logical:u32}, author)`
  (`src/codec.cpp:55-69` `encode_signing`).
- **DB upgrade on open of a v2 file**: for each entity with `causal_length = C`,
  synthesize `present = (C & 1)` and `hlc = {physical: 0, logical: C}` so the
  relative order is preserved and any new real-HLC write dominates legacy state;
  drop value bytes for entities that migrate to `present=false`. One-time, gated
  by the existing `meta.schema_version` guard (`sync_engine_open`).
- Bindings (Python/WASM) and `netnode` need no API change — `set`/`delete`/`get`
  signatures are unchanged; only the on-wire/at-rest existence encoding changes.

## 7. Correctness & security implications

- **Convergence:** preserved — LWW-by-`(hlc, author)` is an established
  convergent merge; the digest remains a deterministic hash over sorted state
  (now including the presence register instead of the counter).
- **Authorization:** unchanged — existence writes still go through
  `cap_authorize_write` before touching state/clock.
- **Net integrity:** strictly improved — removes the causal-length saturation
  bug, makes GC possible (bounding tombstone growth), and leaves a single,
  already-documented residual (HLC far-future), not two.

## 8. Recommendation

Adopt **the unified LWW-by-HLC model** (LWW-existence + LWW fields), with
immediate value-byte drop on delete and TTL/epoch tombstone GC. Keep collections
as entities (document the rule). Add the **optional counter** type only when
needed. Hold **ORSWOT** in reserve as the documented upgrade if true add-wins
under untrusted/high-concurrency writes ever becomes a requirement.

This is the minimal change that fixes the audit's structural findings
(saturation + no GC), simplifies the engine to one conflict rule, and matches the
design that a proven peer (Earthstar) shipped for this exact use case.
