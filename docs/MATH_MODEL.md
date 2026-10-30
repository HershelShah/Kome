# Kome, mathematically

This is the model behind `formal/lean/`: what a replica holds, how a record
changes it, and the theorems that make "replicas converge" a fact rather than a
test outcome. It is written to be read without Lean; each theorem names its
Lean counterpart.

The approach is **math first**: state the model, prove the design theorems,
then (separately) prove the code against the model in SPARK. A translation of
the code that is not anchored to proven design theorems only proves that two
implementations agree with each other.

## 1. The objects

**Clock.** An HLC is a pair `(p, l)` with `p ≤ 2^64 − 1`, `l ≤ 2^32 − 1`,
ordered lexicographically. `(0, 0)` is reserved: it means "no assertion".

- `tick(c, now)`: if `now > c.p` then `(now, 0)` else `bump(c)`.
- `bump(p, l)`: `(p, l+1)` if `l < 2^32 − 1`; else `(p+1, 0)` if `p < 2^64 − 1`;
  else `(p, l)` (saturate: no larger clock exists).
- `receive(c, r, now)`: adopt `r.p` only if `r.p ≤ 2^64 − 1 − 2^32`
  (`kMaxAdoptablePhysical`), take the max with `now`, then bump from the
  matching logical, or reset logical to 0 if the wall clock passed both.

**Cells.** Two kinds, both LWW registers:

- a field register `(hlc, author, value)`, ordered by `register_cmp`:
  lexicographic on all three;
- an existence assertion `(hlc, author, present)`, where the order is the
  subject of §4.

Authors are public keys under memcmp, values are byte strings under
lexicographic order; both are total orders, which is the only property used.

**State.** A replica's state `S` is a partial map from keys to cells (a key is
`(namespace, entity, field)` for a register, `(namespace, entity)` for an
existence assertion). `apply(S, k, x)` sets `S[k] := merge(S[k], x)` where
`merge(cur, inc) = inc` if `cur < inc` else `cur`, and `merge(⊥, x) = x`.

This is exactly `apply_change`'s decision: an incoming record is installed iff
it is strictly greater than what is held; otherwise it is dropped as
"dominated". Signature verification and capability checks are gates in front
of `apply`; they decide whether a record enters, not what it does when it
does.

## 2. Theorems proved (Lean, `formal/lean/`)

| Id | Statement | Lean |
|---|---|---|
| T-HLC-1 | `tick` never returns `(0,0)` | `HLC.tick_ne_zero` |
| T-HLC-2 | `tick` strictly increases the clock, except at the saturating fixed point `(2^64−1, 2^32−1)` where it is the identity | `HLC.tick_lt` |
| T-HLC-3 | After receiving `r`, a local write's clock exceeds `r` (unless saturated): a local write beats any record it has seen, regardless of author | `HLC.tick_beats` |
| T-HLC-4 | `receive` never returns `(0,0)` | `HLC.receive_ne_zero` |
| T-HLC-5 | `receive` never moves the clock backwards | `HLC.le_receive` |
| T-HLC-6 | The physical adopted from a peer is bounded by the local clock, the wall clock, or the ceiling, plus one carry | `HLC.receive_phys_bound` |
| T-LWW-1..3 | Over any strict total order, `merge` is idempotent, commutative, associative (a semilattice join) | `LWW.merge_idem/comm/assoc` |
| T-REG | `register_cmp` is a strict total order | `instance StrictTotal Reg` |
| T-EX | `(hlc, author, present)` with absent < present is a strict total order | `instance StrictTotal Ex` |
| T-STATE-1 | Applies to a state commute | `Store.apply_comm` |
| T-STATE-2 | Applying a record twice equals once | `Store.apply_apply` |
| T-STATE-3 | Any permutation of a record sequence gives the same state | `Store.applyAll_perm` |
| T-STATE-4 | Re-delivering a record already applied is a no-op | `Store.applyAll_mem_cons` |
| **T-CONV** | Two replicas that applied the same *set* of records, in any order, with any duplication, from the same start, are equal | `Store.convergence` |
| T-EQUIV-1 | The existence merge as implemented is order-dependent | `mergeImpl_not_comm` |
| T-EQUIV-2 | Because `(hlc, author)` is not total on assertions | `ltImpl_not_trichotomous` |

T-CONV is the statement "convergence is the law" from `README.md`, with its
hypothesis made explicit: **the cell order must be total**. T-REG shows
registers satisfy it. T-EQUIV shows the implemented existence order does not,
and T-EX shows the one-line change (put the present bit in the order) that
makes it satisfy it. That is the fix for the divergence in
`docs/FORMALIZATION_PLAN.md` §5, now with a proof that it is sufficient.

T-HLC-1 and T-HLC-4 are the facts the `{0,0}` rejection rests on; the
engine refuses a `{0,0}` existence record because no honest clock can mint
one. T-HLC-2 and T-HLC-3 are why a local `set` needs no LWW gate: its clock is
strictly newer than anything the engine has received.

## 3. What the model deliberately leaves out

- **Signatures and capabilities.** They gate entry to `apply`; convergence is
  about what happens after entry. A record that one replica accepts and
  another rejects (revoked capability seen on one side only) is a
  *membership* difference between the two record sets, not a merge
  difference. The model's hypothesis "same set of records" is exactly where
  that shows up.
- **Shells.** An entity key with field registers but no existence assertion.
  In the model, state is the set of cells, so a shell has no independent
  existence; the C++ digest bug (`DECISIONS.md`, zero-HLC entry) was the
  implementation's digest depending on something the model does not contain.
  The right theorem is T-DIGEST below.
- **Bytes.** Keys and values are abstract; the codec is a SPARK concern.

## 4. Theorems still to state and prove

| Id | Statement | Why |
|---|---|---|
| T-DIGEST | `digest(S)` is a function of the cell set of `S` only; in particular two states with equal cell sets have equal digests | the zero-HLC incident: four subsystems disagreed about one cell |
| T-RBSR | Range-based set reconciliation over fingerprint sums terminates and leaves both sides holding the union of their cell sets | the sync protocol's correctness claim; needs a model of ranges, fingerprints as a commutative sum of cell hashes, and the split rule |
| T-RBSR-WIRE | Fingerprint equality on a range is equivalent to cell-set equality on that range, under the hash's collision-freedom assumption | what makes T-RBSR's termination condition sound |
| T-CAP | A capability chain verifies iff every link is signed by the previous subject, depth is within bound, and no link is expired or revoked; verification is monotone in revocation | the authorization gate; S1 and S5 security fixes |
| T-GC | Tombstone GC and compaction preserve the cell set and therefore the digest | `sync_engine_compact`'s contract |
| T-HLC-7 | Per-engine clocks: a replica never emits two records with the same HLC (uses T-HLC-2 plus persistence of the clock across reopen) | the honest-writer argument behind the `{0,0}` reservation and behind T-EQUIV being unreachable without a shared identity |

T-DIGEST, T-GC and T-HLC-7 are short. T-RBSR is the substantial one and is
where Lean earns its place: it is an induction over a recursive range split,
which SMT-driven tools do not do well.

## 5. From model to code

Once these are proved, the SPARK work (`formal/spark/`, `docs/FORMALIZATION_PLAN.md`)
has a target: each SPARK contract is the code-level form of a theorem here.
`Kome.HLC.Tick`'s postcondition is T-HLC-1 and T-HLC-2; `Kome.Model.Apply`'s
is `merge` with T-REG/T-EX as its ghost lemmas; the digest's is T-DIGEST. The
translation scaffold already committed under `formal/spark/` (level 0:
byteorder, SHA-256) stays usable for that step, but no further modules should
be translated until the theorems above are checked.

## 6. Status

The Lean development uses only the core library and is **machine-checked**
under Lean 4.35.0 (`formal/lean/build.sh`): every theorem in §2 and the
redesign's theorems in `Kome/Frontier.lean` (see `docs/redesign/DESIGN.md`
§9) build with no `sorry` and only Lean's standard axioms. The first build
needed four kinds of tactic-level fix, none touching a statement: a renamed
core lemma, `omega` not seeing through `True ∧ …` after `simp only`, `omega`
not seeing through an `abbrev` for `Nat`, and `decide` needing to be unwrapped
before a definition under it is unfolded.
