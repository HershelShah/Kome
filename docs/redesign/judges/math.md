# Math judge: adversarial review of candidates A–D

Stance: every convergence, lattice, monotonicity and GC-invisibility claim was
treated as false until I failed to break it. For each candidate I took the
merge/join/fold definition literally and tried to build two replicas that were
offered the same records and ended in different states, using the H8 cases
(equivocating/cloned writers, restored backups, wrong clocks), out-of-order
delivery, and the candidate's own GC/truncation/expiry rule applied at
different times on different replicas. Then I checked each proof obligation
for precision, hidden hypotheses and vacuity, checked H5/H6, and estimated
the hardest theorem's provability in core-only Lean 4 in one week.

Notation: a replica state is written as the candidate defines it (`F`,
`(live, ctx)`, `effective(E)`/`fold`, `store`). "Same records" means both
replicas were *offered* the same multiset of well-formed records.

---

## Candidate A — hardened LWW over a total record order

### What survives

- **T1** (total order on `(t, author, seq, h)`): holds under hash injectivity.
- **T2/T3** (dom monotone; `F(H₁ ∪ H₂) = F(F(H₁) ∪ F(H₂))`, `F(F(H)) = F(H)`):
  I tried to break T3 with mixed PUT/DEL dominators and could not. The proof
  needs one lemma the candidate does not state: *the dominators of `x` are
  upward-closed under domination* (a dominator of a dominator of a PUT is a
  PUT on the same cell or a DEL on the same entity with a larger `v`, hence
  itself a dominator). With that, a maximal dominator is in `F(H₁)∪F(H₂)` and
  T3 follows. T10 (equivocation by `h`) and T12 follow from T3. The pure
  lattice core is sound.

### Counterexample 1 — T4 (exchange form) and T9 are false: admissibility is not monotone

The ceiling gate `t > ceil ⇒ not applied, as if it had not arrived` makes the
applied set depend on *which* ROSTER a replica held at arrival time, and
ROSTER dominance `(gen, h)` lets a roster with a **lower** ceiling win at
equal `gen`. "The root engine refuses to lower a ceiling" is a local policy of
one emitter; it cannot hold across a root restored from backup (H8) or two
root-holding devices, both of which the candidate explicitly allows ("any
root-holding device").

Records (`ns` fixed, one cell `c = (E, f)`):

```
R_hi : ROSTER gen=3, ceiling_t=5000, h=0x01…   (issued by root device 1)
R_lo : ROSTER gen=3, ceiling_t=4000, h=0xF0…   (issued by root device 2 / restored root; wins by h)
p    : PUT c, v=(t=4500, W, seq=1, h_p)        (honest writer W, emitted under R_hi: 4500 ≤ 5000)
```

Replica A receives `R_hi, p, R_lo`:
- after `R_hi`: ceil=5000; `p` admissible, applied; after `R_lo`: `R_hi`
  dominated and dropped. `F_A = {R_lo, p}`.

Replica B receives `R_lo, R_hi, p`:
- `R_lo` max, `R_hi` dropped, ceil=4000; `p` inadmissible, skipped.
  `F_B = {R_lo}`.

Both were offered the same three records. Now run T7 to completion: A offers
`p`; B skips it (inadmissible under its — and A's — maximal roster). A never
evicts `p` (nothing in the spec removes an already-applied record when the
ceiling drops). `F_A ≠ F_B` after every reconciliation until some root issues
a roster with ceiling > 4500. T4's second clause ("after a complete
reconciliation both hold `F(H_A ∪ H_B)`") is false; T9's "no admissible record
has `t > ceiling_t` of the maximal held ROSTER" is false at A. The divergence
is repaired only by an external event (A3's refresh), i.e. the convergence
theorem silently depends on root liveness.

### Counterexample 2 — T11 is false and A6 is untrue: TTL GC depends on clock agreement

The GC predicate's second clause uses `now_local`, and "an expired DEL is also
*not applied* on arrival". Two honest, A4-compliant replicas with any nonzero
clock skew can be split by a DEL that arrives near its expiry (e.g. via a
mailbox or relay, which A4 permits for up to `del_ttl`).

`del_ttl = 100`. Records:

```
p : PUT (E, f) v=(990,  W, 1)
d : DEL  E     v=(1000, W, 2)
```

Both replicas hold `p`. `d` arrives at both at the same real instant; replica
A's clock reads 1101, replica B's reads 1099.
- A: `1101 ≥ 1000 + 100` ⇒ `d` not applied. `F_A = {p}`, view: E exists.
- B: applies `d`; `p` dominated and dropped. `F_B = {d}`, view: E absent.

Reconcile: B offers `d`, A refuses (expired). A offers `p`, B drops it
(dominated). Divergent. Two ticks later B's clock passes 1100 and B drops `d`;
on the next session A's `p` is admitted at B. Final: `F_A = F_B = {p}` —
**the entity is resurrected on every replica**, with A4 satisfied and only a
2-unit clock skew. "A slow-clocked peer re-offering it costs bytes, never
state" is false. A6 ("no clock assumption of any kind for convergence") is
false: convergence of the GC'd system needs bounded skew between replicas,
which is nowhere in A1–A6.

### Obligations rejected

- **T4, second clause**: false (counterexample 1). First clause is fine but is
  not the system (the system has the ceiling gate).
- **T9**: false (counterexample 1).
- **T11**: false (counterexample 2). Even as intended it hides a clock
  assumption (bounded skew) and a liveness assumption (A4) inside a safety
  claim ("changes no view on any replica, ever").
- **T7**: "finitely many rounds under loss/duplication/reorder" is a liveness
  claim that needs a fairness hypothesis (eventually a descriptor gets
  through); not stated. "Inadmissible elements are skipped and the session
  continues" also means the roster-first ordering is not guaranteed under
  reorder, so a single session can end with admissible records unapplied.
- **T8**: fine as stated, but note "read-your-writes" fails exactly when
  `floor.t = ceil`, and the theorem's hypothesis excludes that case rather
  than bounding it.

### H5/H6

Good: no sentinel, `t = 0` and `seq = 0` ordinary, Option-typed views,
exhaustion refuses. Residuals: `t = ceil` is a regime with special semantics
(ties by author, `SHADOWED` possible) — a bound whose attainment means
something; `n_members ≤ 64` / `n_revoked ≤ 1024` are runtime checks on `u8`/
`u16`, not types; `del_ttl` expiry injects a per-replica value (`now_local`)
into a membership decision, which is a derived, replica-dependent invariant.

### Hardest theorem

T7 (RBSR with 16-way split, loss/dup/reorder, plus inadmissibility). Not in a
week in core Lean; T3 is (lists as finite sets, perm-invariance, decidable
strict order; 2–4 days).

### Scores

- **C1 = 3** — the frontier lattice is sound and clock-free, but the stated
  convergence theorem (exchange form) has a counterexample and the GC
  theorem hides a clock-skew assumption.
- **C6 = 3** — `F`/`dom` are a clean finite-set core, but admissibility and
  the TTL clause sit outside the model the theorems quantify over.
- **C9 = 4** — best hygiene of the four; only the `t = ceil` regime and the
  `now_local` clause blemish it.

---

## Candidate B — ORSWOT with evidence-backed context

### What survives

- **T-JOIN** is correct, and cleaner than the candidate says. Define
  `status_S(d)` per dot as in §2 and `seen_S(d)`. Then
  `seen_{S⊔T}(d) = seen_S(d) ∨ seen_T(d)` (because `k ≤ max(n₁,n₂) ⟺ k ≤ n₁ ∨
  k ≤ n₂` and `k > min(f₁,f₂) ⟺ k > f₁ ∨ k > f₂` with `None = ∞`), and
  `status_{S⊔T}(d) = status_S(d) ⊔ status_T(d)` in the chain
  `unknown < live(·) < removed`. So the state join *is* a product of per-dot
  lattices; T-CONV as a corollary of T-JOIN holds for **whole-state joins**.
- T-DOT, T-ENTRY (modulo the `ev` tie below), T-FENCE, T-EVID: fine.

### Counterexample 1 — T-RBSR is false on the ordinary catch-up path; honest writes are killed

The protocol (§4) does not join states. It adopts the peer's **context**
(`ctx_A := ctx_A ⊔ ctx_B`) while transferring **live dots** separately through
a bounded pending buffer, because the invariant `d ∈ dom live ⇒ seen(ctx, d)`
forbids inserting a dot `(s, k)` with `k > ctx[s].n`, and a peer's live set
for a slot normally has gaps (removed dots). So almost every dot of a slot the
receiver is behind on sits in the pending buffer until the end-of-session
context join. The buffer is "≤ 4 096 elements … overflow drops them and a later
sync refetches". The refetch is the problem.

Slot 1 (prolific writer) has issued dots `(1,1)…(1,6000)`; `(1,1)…(1,4)` were
removed, `(1,5)…(1,6000)` are live at replica B (`ctx_B[1].n = 6000`).
Replica A has `ctx_A[1] = Unseen`, `live_A = {}`.

Session 1, A ← B: `(1,5)…(1,4100)` go pending (none is contiguous with `n = 0`);
`(1,4101)…(1,6000)` overflow and are dropped. End of session:
`ctx_A[1] := Seen{6000, ev_6000}`; pending released; `live_A ∋ (1,5)…(1,4100)`.
State A: `(1,4101)…(1,6000)` are `seen ∧ ∉ live` = **removed**.

Session 2, A ↔ B: for `d ∈ B∖A = {(1,4101)…(1,6000)}` received at A: "drop if
`seen(ctx₀_A, d)`" ⇒ dropped. At B: for `d ∈ B∖A`: `seen(ctx_A, d)` and A is RW
⇒ **B drops them too**. Final: both replicas hold `live = {(1,5)…(1,4100)}`.
1 900 honest, never-observed writes are gone everywhere, and every replica
that joins A or B afterwards removes them as well. No clone, no malice, no
message loss. This directly violates the promise in T-NOKILL's conclusion
("live at every replica after join until some replica *that observed it*
drops it") — A never observed them. The two states are equal, so this is not
a divergence; it is worse: convergence to the wrong fixed point.

The structural cause is the one DATA_MODEL.md §3 gestured at and B dismissed:
an ORSWOT delta is only safe under causal delivery or whole-state join;
"removal = absence from an RW peer's live set" cannot be distinguished from
"not yet received" once the context has moved. Enlarging the buffer changes
the number 4 096, not the theorem.

### Counterexample 2 — T-GATE is false: the RW gate makes the implemented merge non-commutative

Slot 1 (RW) writes `(1,1)`. Slot 2 (RW) deletes it: `S₂ = (live {}, ctx{1↦1, 2↦0})`.
Reader R (slot 3, role R) syins with S₂: `S_R = (live {}, ctx{1↦1})`. Device A
(slot 1) still holds `S_A = (live {(1,1)}, ctx{1↦1})`. A ↔ R:
- at A: `(1,1) ∈ A∖R`, `seen(ctx_R, (1,1))` but R is not RW ⇒ A keeps it.
- at R: `(1,1)` received, `seen(ctx₀_R, (1,1))` ⇒ R drops it.
`live_A = {(1,1)}`, `live_R = {}`: same joined information, different states,
and if slot 2's device is lost (honest), permanently. This is lesson row 7
(accept/reject gate non-monotone) in a new coat; "once in, every fact is a
lattice element" is false for removals, which are not elements.

### Counterexample 3 — the context is not canonical: converged replicas disagree on the digest

`Entry` join picks "`ev` of the larger `n`"; on equal `n` with different `ev`
it is undefined. Clone C₁/C₂ on slot 1 both mint dot `(1,5)` with payloads
`e₁` (`H = 0x0A…`) and `e₂` (`H = 0x0B…`); or one device signs the same dot
twice (Ed25519 allows a signer to produce several valid signatures). Replica
A holds `ctx[1] = Seen{5, ev₁}`, replica B `Seen{5, ev₂}`; `live` agrees
(`argmin H`). `BLAKE2b-256(ctx_A) ≠ BLAKE2b-256(ctx_B)`, so the digest
(defined as `fp(dots)` combined with the context hash) differs forever, HELLO
exchanges the entries every session, and the join rule cannot pick. T-FP's
"digest is a function of `(live, ctx)`" is true and useless: `ctx` carries a
witness (a signature) as if it were identity. Candidate A got this right
("the signature is a witness, not part of identity"); B did not.

### Obligations rejected

- **T-RBSR**: false (counterexample 1); also assumes the pending buffer is
  "not state" when it determines state.
- **T-GATE**: false (counterexample 2); conflates gated *elements* (retained,
  joined later) with gated *omissions* (never retained).
- **T-NOKILL**: true as literally stated (about `seen` of unissued seqs), but
  its informal conclusion is contradicted by counterexample 1; the theorem is
  stated about the wrong object (context) rather than the one that matters
  (status after the protocol).
- **T-ENTRY / T-JOIN**: the join is not a function on `n`-ties with different
  `ev` (counterexample 3); needs a tie-break on `H` and must exclude the
  signature bytes from identity.
- **T-CONV**: true for whole-state joins, but the system never performs one
  (H4 forbids O(state) sessions), so the theorem does not describe the system.

### H5/H6

Good: `Unseen` variant, `seq = 0` rejected by the decoder, `2^63` a refusal,
slot bounded by `u8`. Residuals: the invariant `d ∈ dom live ⇒ seen(ctx, d)`
spans two structures and is derived, not represented (H6); a signature in the
state as identity (above); fence `f = 0` is legal and kills a slot entirely
(not reserved, but a footgun); the pending buffer is state that is declared
not to be.

### Hardest theorem

T-JOIN itself is a week's work in core Lean (state as `Dot → Status`,
`Dot = Fin 256 × Nat`, `funext`): yes. T-RBSR (finalize = join with `ctx₀`
under reorder/dup with a bounded buffer) is the one that matters and is false
as specified.

### Scores

- **C1 = 2** — the strongest lattice of the four, attached to a sync protocol
  whose convergence claim fails on the ordinary catch-up path with permanent
  silent loss.
- **C6 = 3** — the lattice proof is cheap; the trusted core must include the
  session protocol, which is not modelled and is where it breaks; the context
  is non-canonical.
- **C9 = 3** — clean variants and bounds, but a cross-structure derived
  invariant, a witness-as-identity in state, and a "not state" buffer that
  decides state.

---

## Candidate C — signed logs with checkpoints

### What survives

- **T-ORDER**, **T-FOLD**: `(height, writer, seq, id)` is total under id
  injectivity and the per-key argmax fold is the LWW join. Fine.
- **T-FORK**: fine.

### Counterexample 1 — T-GC is false: truncation changes `effective` and the change is *folded*

The well-heighted check `h(prev)+1 ≤ h(e) ≤ 1 + max(h(prev), h(link))` is
evaluated against held entries, and for a `link` that is covered-but-truncated
"the unknown height is bounded by `h(c)`". That makes the check **weaker** at a
replica that truncated than at one that did not.

Writer W: entries `W₁…W₈` with heights `1…8`; checkpoint `c` of W covering
`seq 1…8`, `prev = W₈`, so `h(c) = 9`. Writer X (malicious, buggy, or merely
computing `h(link)` from the bound because *it* truncated) emits
`y = (X, seq 1, prev = cid, link = (W, 7), h = 9)`.

Replica B holds `W₁…W₈, c, y`: `h(link) = 7`, check `9 ≤ 1 + max(0, 7) = 8`
fails ⇒ `y` is pending forever. `fold(E_B)` excludes `y`'s ops.

Replica A holds `c, y` and truncated `W₁…W₈` (all void by V1, which T-GC
says is invisible): `h(link)` bounded by `h(c) = 9`, check `9 ≤ 1 + max(0, 9)`
passes ⇒ `y ∈ effective(E_A)`, folded with key `(9, X, 1, id_y)`, and every
later entry of X chains from `y` and is effective at A, pending at B.

`E_A = E_B \ void(E_B)` yet `effective(E_A) ≠ effective(E_B)` and the folds
differ on every entity `X` touches. T-GC (`effective(E \ void(E)) = effective(E)`)
is false; so is the §6 claim "deletion never changes `effective(E)` now or
later". The split is permanent: B can never validate `y`, A can never
un-validate it, and a late joiner (who only ever receives `c`) sides with A.
Any writer can trigger it on purpose.

### Counterexample 2 — `effective` is not a function of `E`: T-CONV is vacuous and T-EFF false

`effective(E)` includes "decryptable", which depends on the replica's keys,
not on `E`. Two members with identical `E`, one of whom has not yet folded the
owner's `EPOCH(n)` entry (its `link` is pending), have different `effective`
sets, different folds and different digests (the digest is "over
`effective(E)`"), and RBSR is run "over `effective(E)`" so the undecryptable
entries are not even in the reconciled set while being "held and replicated"
by an unspecified path. T-CONV as stated (`effective(E_A) = effective(E_B) ⇒
fold equal`) is a tautology about a function applied to equal arguments; the
non-trivial claim — that sync makes effective sets equal — is false by
counterexamples 1 and 2.

### Counterexample 3 — T-AUTH is circular: "authorized" has multiple fixed points

Authorization of `e` is defined by the greatest-`from_seq` GRANT/EXCLUDE in
`effective(E)`, and `effective(E)` requires authorization. After the specified
owner rotation `GRANT(B, owner)` + `EXCLUDE(A, 10)` in B's log, a backup-
restored A (H8) at seq 12 writes `EXCLUDE(B, 1)`. Fixed point 1: B's exclude
effective ⇒ `A₁₂` unauthorized ⇒ B's exclude stands. Fixed point 2: `A₁₂`
effective ⇒ B's entries from seq 1 void ⇒ B's exclude void ⇒ `A₁₂` authorized.
Both are consistent with the definition; the spec gives no least-fixed-point
or stratification rule, so replicas may legitimately compute different member
sets from the same `E`. Not malice: a restored owner device is an H8 case.

### Obligations rejected

- **T-GC, T-EFF** (false: counterexample 1; `effective` is also not a function
  of `E`: counterexample 2).
- **T-CONV** (vacuous as stated; false as intended).
- **T-AUTH** (ill-defined: counterexample 3).
- **T-CKPT** hypothesis "`E` contains every entry … plus every dominator `c`
  relied on" is exactly what a truncated replica lacks, so it proves nothing
  about the truncated case that T-GC needs.
- **T-TOMB** hypothesis "every checkpoint … on the branch W observed" excludes
  the fork case, which §3 admits resurrects collected tombstones; and the
  collection predicate quantifies over "every authorized member" — a
  membership oracle in the GC rule, contrary to H7.
- **T-HEIGHT** "bounded by `|past(e)|`" is false at a truncated replica
  (counterexample 1: `h(y) = 9` with a past of size 2 in `E_A`).

### H5/H6

No sentinels, counts not flags, bounds are refusals: fine. But the state is
almost entirely derived — `valid`, `authorized`, `void` (three clauses),
`covered`, `pending`, `decryptable`, "complete series" — seven predicates
whose conjunction is the replicated set, with no representation of any of
them (H6 in spirit). The pending set is bounded per writer (good); the
checkpoint `frontier` is a version vector by another name (≤ 64 × 40 B),
which H4 told us not to need.

### Hardest theorem

T-GC/T-EFF: well-foundedness of `effective` over a DAG with truncation,
coverage and the height bound. Not provable in a week; not provable at all
as stated.

### Scores

- **C1 = 1** — the convergence theorem is a tautology, GC invisibility has a
  permanent, writer-triggerable counterexample, and `effective` depends on
  per-replica keys.
- **C6 = 1** — seven derived predicates with a circular one in the middle;
  the trusted core is the largest of the four and its key lemma is false.
- **C9 = 3** — bounds and sum types are clean; the model's state is a tower
  of derivations.

---

## Candidate D — prior-art assembly (prune order, max-set store, view)

### What survives

- **T-1**: `≻` is irreflexive and transitive — I checked the mixed case
  (same-author chain through a `Rev`) and the prefix/`ts`/`h` cases; it holds.
- **T-2/T-3**: hold *if* `valid` is a function of the record's bytes (the
  hypothesis §10 states): a maximal pruner exists in any finite set because
  `≻` is a strict partial order, so `store(store(A) ∪ B) = store(A ∪ B)`.
  Cloned keys, equivocation, out-of-order delivery and G1 all live inside this
  lattice. This is the most robust convergence core of the four: the only
  gate (`valid`) is monotone in the held set, so a record admitted anywhere
  is admissible everywhere forever.

### Counterexample 1 — T-10 is false: deletion is undone on every replica after `T_gc`, no straggler needed

A `Tomb` prunes only its author's records; other authors' older values stay in
`store` and are merely hidden by `view`. G2 drops the `Tomb` after `T_gc`.

```
v  : Value by B at (E, f), ts=100, in epoch e
tA : Tomb  by A at (E),    ts=200
```

Every replica holds `{v, tA}`; `view(E,f)` = nothing. B's device is offline
longer than `T_gc` (or lost but not yet revoked), so the "maintenance rule"
(B writes its own `Tomb`) never fires. At `now = 200 + T_gc` every replica
drops `tA`: `store = {v}`, `view(E,f) = body(v)`. The entity is back on
**every** replica, with all clocks perfect and every member except B in
constant sync. T-10's hypothesis ("no record `r'` with `author(r') = author(r)`
…") is satisfied — A has no older record under `E` — yet `view` changes.
T-10 is false because it only considers same-author re-admission. The
candidate's own weakness list ("resurrection window … for a writer's own old
data") misstates the scope: it is for *every other* author's old data.
Durable cross-author deletion therefore requires B to return or be revoked —
a membership act — contrary to H7's "without a membership oracle".

### Counterexample 2 — T-2 is false under the spec's own `valid`

§3 defines `valid(r)` via "the chain named by `cap_ref`", and `cap_ref` is a
32-byte reference to `Cap` *records in the set*; §10 then asserts `valid` is a
function of the record's bytes. Take `A = {v_K}` (K's Value), `B = {c_K}`
(K's Cap chain): `store(A) = {}`, `store(store(A) ∪ B) = {c_K}`,
`store(A ∪ B) = {c_K, v_K}`. The pending buffer (≤ 256, timeout G3) papers
over this: replica X receives 300 of K's records before `c_K`, drops 44; Y
receives `c_K` first and keeps all 300. Same records offered, different
stores. Unlike A's ceiling, this is self-healing (Caps are never pruned, Y
re-offers the 44 on the next session), so I class it as a hypothesis mismatch
rather than a structural break — but T-3 as written is false, and the model
the Lean proof would check is not the system.

### Counterexample 3 — HLC `receive` re-imports lesson row 5 at the device level, with an unspecified overflow

`receive` "takes the max with any *valid* stored record's `ts`, clamped to the
device's own `not_after`". A writer K with `ts = b_K` (its window top, ≈ 200
days out) pulls every honest device's `l` to `min(b_K, own not_after)` on
first sight. Honest devices then mint `(l, c)` with `l` pinned and `c` a
16-bit counter ("`ts = l·2^16 + c`"); after 65 536 writes the spec says
nothing. Either `c` wraps (H6: a counter whose wrap means something; the
device's own-subspace order breaks) or minting refuses (H8: one record plus
ordinary use bricks every honest writer for up to the horizon). Candidate A
avoided this by adopting nothing from peers; D's survey said "adopt HLC for
minting, never for acceptance" — minting is where the damage is.

### Obligations rejected

- **T-10** (false: counterexample 1).
- **T-2/T-3** as applied to the specified `valid` (counterexample 2); true
  under the stated-but-unmet hypothesis.
- **T-8** "number of candidates per cell is ≤ W": false over time — expired
  capabilities' records persist ("expired capabilities stay") and
  un-revoked departed authors each leave a candidate, so the bound is
  authors-ever, not `W`.
- **T-5**: `elems(store, now)` depends on local time, so equal stores on
  replicas with different clocks have different digests; the theorem is
  stated for fixed `now` and is thus not the cross-replica fact H1 wants.
- **T-13**: silent on `c` overflow (counterexample 3).
- **T-7**: the Meyer bound is for the unbounded-frame protocol; the
  coalescing "deferred fingerprint range" changes the recursion, and the
  "× ⌈msg/F⌉" multiplier is asserted, not derived.

### H5/H6

Explicit violation: "`clamp` defaults to `2^64−1`" is a reserved value
meaning "no clamp" (should be an Option). `c` overflow unspecified. The
candidates-per-cell bound is derived and false. Existence as a view is fine.
Sum-typed `kind`, bounded paths and frames are good.

### Hardest theorem

T-7 with frame coalescing: not in a week. T-2 (with `valid` as a bytes
predicate) is 2–4 days in core Lean, the same shape as A's T3 but simpler
(no cross-kind domination).

### Scores

- **C1 = 4** — the store lattice is sound with the fewest hypotheses and a
  monotone gate; one off because the spec's `valid` contradicts the theorem's
  hypothesis and the GC theorem is false.
- **C6 = 3** — core is one partial order and one max-set, but `valid`,
  `receive` and `elems(·, now)` are outside the model and T-7 is hard.
- **C9 = 3** — `clamp = 2^64−1` sentinel, unspecified `c` wrap, a false
  per-cell bound.

---

## Ranking

| Rank | Candidate | C1 | C6 | C9 | Most damaging counterexample |
|---|---|---|---|---|---|
| 1 | **D** prior-art | 4 | 3 | 3 | T-10: a `Tomb` over another author's value expires after `T_gc` and the entity returns on every replica; durable deletion needs that author back or revoked |
| 2 | **A** hardened LWW | 3 | 3 | 4 | T4/T9: equal-`gen` rosters with the lower ceiling winning by `h` (restored/duplicate root) leave `p@4500` in `F_A` and inadmissible at B after every reconciliation; plus T11 resurrection under any clock skew |
| 3 | **B** causal ORSWOT | 2 | 3 | 3 | T-RBSR: catch-up beyond the 4 096 pending buffer turns never-received honest dots into "removed", which then propagates and deletes them at every replica |
| 4 | **C** signed logs | 1 | 1 | 3 | T-GC: the height check is weaker at a truncated replica (`h(link)` bounded by `h(c)`), so `y` with `h = h(c)` is folded where `W₁…W₈` were truncated and pending forever where they were kept |

**Justification.** None of the four is clean, so the ranking is by which
central theorem survives its own specification. D's store lattice (strict
partial order + maximal elements) is the only convergence core whose
admission gate is monotone in the held set: every counterexample I could
build against T-3 is repaired by the next reconciliation without any
external actor, whereas A's ceiling gate is non-monotone and its divergence
persists until a root device acts, so by the rule "a real counterexample to
the central theorem cannot rank first" A cannot be first and D can — but only
narrowly, and D buys it with a false GC theorem (cross-author resurrection,
H7 failure), a reintroduced far-future clock pin with an unspecified counter
wrap, and the worst hygiene of the top two. A's frontier lattice is equally
sound and its representation is the best of the four, but it has two concrete
counterexamples to stated theorems (T4-exchange/T9 and T11), and the second
contradicts its headline assumption A6: TTL GC makes convergence depend on
bounded clock skew. B has the strongest and most easily proved lattice, and
I verified it decomposes per dot; it ranks third because the protocol it
ships is not that join — context adoption without the corresponding live
dots converts non-delivery into removal on the ordinary catch-up path, the
RW-only removal gate is lesson row 7 again, and a signature in the context
makes converged replicas disagree on the digest. These are structural
(ORSWOT deltas need causal delivery or whole-state joins, which H4 forbids),
not parameters. C is last: its convergence theorem is a tautology, its GC
invisibility lemma has a permanent, writer-triggerable counterexample, its
authorization predicate has multiple fixed points reachable from an H8 case,
and its replicated set depends on per-replica keys.

If one design must be taken forward, D with three changes would be the one:
make `valid` a true function of bytes (embed the ≤ 4-link chain or make
pending unbounded-by-count), make `Tomb` prune cross-author (which turns `≻`
into A's `dom` and loses nothing D's proofs rely on), and remove `receive`
adoption in favour of A's per-cell floor chase. Equivalently, A with its
ceiling demoted from a gate to a view flag (like `void`) and its TTL clause
changed to apply-then-expire rather than refuse-on-arrival. The two converge
on the same design; neither candidate wrote it.
