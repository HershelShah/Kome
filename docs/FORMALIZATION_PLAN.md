# Formalizing Kome: a proven mirror of the semantic core

**Decision:** build the mirror in **SPARK** (the provable Ada subset), proven
with `gnatprove`, compiled, and run differentially against the C++ engine in
CI. Use **Lean 4** only for two design-level theorems the SPARK toolchain is
poor at (state-wide convergence and reconciliation correctness), and only
after the SPARK mirror exists. Do not start with Lean.

This document records why, what the mirror covers, how it is kept from
drifting, and the phases. It also records a convergence bug found while
scoping the work (§5), which is the kind of defect the proof is meant to make
impossible rather than merely unlikely.

---

## 1. Why SPARK first, Lean second

The choice follows from the repo's own bug history, not from tool preference.
`DECISIONS.md` and `git log` give the classes of defects that have actually
shipped:

| Shipped defect | Where | What would have caught it |
|---|---|---|
| `uint32` wrap in `Hlc::logical` minted the reserved `{0,0}` | `sync_engine.cpp` | SPARK: overflow is a proof obligation on every `+` |
| `carry_logical_overflow` wrong at both call sites | `sync_engine.cpp` | SPARK: `Post => Result > Old` on `tick` |
| Persisted logical clock truncated instead of clamped on restore | `storage.cpp` | SPARK: narrowing conversion is a range-check obligation |
| `now_ms()` sign-converted a pre-epoch clock to `UINT64_MAX` | `sync_engine.cpp` | SPARK: signed-to-unsigned conversion is a range-check obligation |
| Six more "reserved value forged at an integer boundary" defects | sweep, commit `0082bc0` | SPARK: same class, same mechanism |
| Storage frame length unbounded on load (nightly fuzz OOM) | `storage.cpp` | SPARK: precondition on the frame reader |
| Opening a database wrote to it (`komed_test` flake, #58) | `storage.cpp` | SPARK: `Global => (Input => File_System)` flow contract on `Open` |
| `{0,0}` existence record accepted; `exists`, `digest`, `build_snapshot`, and `load` disagreed about one cell | `sync_engine.cpp`, `reconcile.cpp`, `storage.cpp` | SPARK: `Type_Invariant` on `Entity` (`present_v` implies `asserted`); Lean: digest is a function of the element set |
| Causal-length saturation: presence pinned by a peer-supplied `UINT64_MAX` | pre-P1 data model | SPARK: `+= 1` overflow obligation; Lean: merge is not a semilattice over bounded ints |
| Same-author same-HLC existence equivocation diverges permanently (§5, new) | `sync_engine.cpp:884` | Lean or SPARK: the merge order is not total over the element, so `merge` is not commutative |

Nine of the eleven are *integer-boundary* or *flow-contract* defects in
imperative code. That is exactly what SPARK proves automatically, at scale, on
code that compiles and runs. Lean proves the deeper algebra (the last two
rows) but has no link to running code and would not have caught the first
eight at all without hand-modeling every fixed-width integer.

Other reasons SPARK is the right primary tool here:

- **The mirror can execute.** A SPARK package is an Ada package: it compiles
  with GNAT, links as a static library, and can export C-callable functions.
  A Lean model can be run, but awkwardly, and never as a drop-in.
- **Drift control is testable.** Because it runs, the mirror can be driven by
  the *existing* fuzz corpora and scenario tests and compared byte-for-byte
  with the C++ engine. A mirror that is not executed drifts silently.
- **The mirror can become the implementation.** The semantic core is roughly
  3 000 lines of C++. Once the SPARK version is proven and differentially
  equal, it can sit behind the same `sync_engine.h` ABI (the C ABI is the
  product; the implementation language is not). This is an option, not a
  commitment, but it is only available with SPARK.
- **It matches the market.** `docs/GO_TO_MARKET.md` names airlines, defense,
  and embedded as the paying segments. A SPARK-proven core is a credential in
  those segments; a Lean development is not something a procurement office
  recognizes.
- **Proofs are mostly automatic.** SPARK discharges obligations with SMT
  solvers (Alt-Ergo, CVC5, Z3). The contracts in this plan are the kind
  gnatprove proves without manual lemma work. Lean proofs of the same facts
  are hand-written.

What Lean adds, later: two theorems that are about the *design* and are
independent of any implementation:

1. **Convergence.** For the whole state (a map of maps of registers), `apply`
   of any multiset of records in any order yields the same state. This is the
   semilattice property stated once for the full structure. SPARK can prove
   per-cell commutativity but struggles with proofs over unbounded maps.
2. **Reconciliation correctness.** Range-based set reconciliation over
   fingerprint sums terminates and leaves both sides with the union of their
   element sets. This is an inductive argument over a recursive split, and
   it is where Lean is comfortable and SPARK is not.

Neither TLA+ nor model checking is in scope. They would suit the connection
manager and relay state machines, but those are not where the bugs have been.

## 2. What the mirror covers

The **semantic core** is everything that decides state, and nothing that
moves bytes between machines or does cryptography.

In scope:

| Unit | C++ source | Properties to prove |
|---|---|---|
| HLC | `Hlc::tick`, `receive`, `bump_logical`, `hlc_cmp` | strict monotonicity; never returns `{0,0}`; `hlc_cmp` is a total order; adoption ceiling respected; no overflow anywhere |
| Register merge | `register_cmp`, REGISTER branch of `apply_change` | `register_cmp` is a total order; merge is commutative, associative, idempotent |
| Existence merge | EXISTENCE branch of `apply_change` | same three laws; `present_v` implies `asserted` as a type invariant |
| Element set and digest | `build_snapshot`, `sync_engine_digest` | digest is a function of the element set; unasserted shells emit nothing |
| Codec | `put_varint`, `get_varint`, `encode_signing`, `encode_record`, `decode_record` | no runtime error on any input; `decode(encode(x)) = x`; `decode` never reads past `end` |
| Storage framing | frame reader and writer, torn-tail truncation, compaction's rename-as-commit | no runtime error on any file bytes; length prefix bounded; load replays into the same state as the mirror's in-memory merge; `Open` has no write effect |
| Capability decode and authorize | `sync_capability_decode`, `cap_authorize_write` | no runtime error; delegation chain depth bounded; expiry arithmetic cannot wrap |

Out of scope, modeled as opaque oracles with stated assumptions:

- **Crypto** (monocypher). Signatures are a boolean oracle `Verify(record)`.
  Proving Ed25519 is a separate project; SPARKNaCl exists if that is ever
  wanted.
- **Transports, Noise, relay, rendezvous, STUN, WebSocket.** Already covered
  by fuzzers and parity tests; not where state bugs live.
- **Reconciliation session wire protocol.** The *algorithm* is in Lean scope
  (phase 5); the message parser stays with `fuzz_session`.

## 3. Keeping the mirror honest

A proven mirror that does not match the shipped engine is worse than none,
because it certifies the wrong thing. Three mechanisms:

1. **Differential execution in CI.** The mirror links into a small Ada driver
   that reads the same inputs the C++ fuzz and scenario tests use and prints
   its result; a harness runs the C++ engine on the same inputs through the C
   ABI and diffs. Three streams:
   - `fuzz_change_decode` and `fuzz_storage` corpora: decode result and
     post-load digest must match.
   - Scripted HLC sequences: identical `(physical, logical)` after every
     `tick`/`receive`.
   - Record sequences from `convergence_test` and `scenario_test`: identical
     digest after every apply.
   A mismatch fails CI and is a bug in one side or the other.
2. **Frozen interface.** The mirror exposes exactly the decision functions
   the C++ exposes (`tick`, `receive`, `register_cmp`, `apply_decision`,
   `digest`, `decode_record`, `load_frame`). New C++ behavior in the core
   requires a matching mirror change in the same PR.
3. **Shared vectors.** Known-answer files (hex in, hex out) committed under
   `formal/vectors/` and read by both the gtest suite and the Ada driver.

## 4. Phases

Each phase is independently mergeable and leaves CI green.

### Phase 0: toolchain and skeleton

- Add `formal/spark/` as an Alire crate (`alr init --lib kome_spark`),
  with `gnatprove` in `alire.toml`. CI job via `alire-project/setup-alire`
  running `alr build` and `gnatprove --level=2 --mode=all`.
- Add `formal/README.md` stating the scope boundary above.

### Phase 1: HLC and codec

The highest bug density per line. Contract sketch for the clock (this is
what the package spec looks like; it has not yet been run through gnatprove):

```ada
package Kome.HLC with SPARK_Mode is
   type Physical is mod 2**64;
   type Logical  is mod 2**32;
   type Clock is record
      P : Physical;
      L : Logical;
   end record;

   Zero : constant Clock := (P => 0, L => 0);
   Max_Adoptable : constant Physical := Physical'Last - 2**32;

   function Less (A, B : Clock) return Boolean is
     (A.P < B.P or else (A.P = B.P and then A.L < B.L));

   procedure Tick (C : in out Clock; Now : Physical)
     with Post => C /= Zero
              and then (Less (C'Old, C) or else C'Old = (Physical'Last, Logical'Last));

   procedure Receive (C : in out Clock; Remote : Clock; Now : Physical)
     with Post => C /= Zero
              and then not Less (C, C'Old)
              and then (Remote.P > Max_Adoptable or else not Less (C, Remote));
end Kome.HLC;
```

The second disjunct of `Tick`'s postcondition is the saturating fixed point
`engine.hpp` documents; stating it explicitly is the point. The codec package
proves `Get_Varint` never reads past its bound and that `Decode (Encode (R))`
returns `R` for every well-formed record.

### Phase 2: merge rules and the entity invariant

- `Register_Cmp` and `Existence_Cmp` as pure functions with proven totality
  (antisymmetric, transitive, total).
- `Merge` for each cell with proven commutativity, associativity, and
  idempotence, stated as ghost lemmas.
- `Entity` with `Type_Invariant => (if Present_V then Asserted)`.
- The `{0,0}` rejection as a precondition on the existence path.

This phase will force a decision on the bug in §5, because the existence
comparison as written is not a total order over the element and the
commutativity lemma will not prove.

### Phase 3: storage framing and load

- Frame reader with a bounded length precondition and a proof that a short
  read or checksum mismatch truncates to the last good frame and never
  indexes past the buffer.
- `Open` with `Global => (Input => File_System)`: SPARK's flow analysis
  rejects any write path at compile time, which is the #58 class.
- Load-equals-merge: replaying a log through the mirror's `Merge` equals the
  state the writer held. This is the proof that persistence and merge agree.

### Phase 4: differential CI

The harness from §3 wired into `ci.yml` and `nightly.yml`, with the committed
vector files. After this phase the mirror is trustworthy enough to be cited.

### Phase 5 (Lean, optional): the two design theorems

- `formal/lean/` with Lake and Mathlib.
- `Kome/State.lean`: state as `Finmap`-like structure, `apply`, and the
  theorem `apply_comm : apply (apply s a) b = apply (apply s b) a` lifted to
  lists and permutations.
- `Kome/RBSR.lean`: fingerprint reconciliation over a sorted list with a
  termination measure and the union postcondition.

These are design facts. If either fails to prove, the design is wrong, not
the C++. Lean can also execute the model as a fourth stream in the
differential harness if that is ever wanted.

## 5. Finding: existence equivocation diverges permanently

Scoping phase 2 turned up a convergence violation in the shipped engine.

`register_cmp` orders registers by `(hlc, author, value)`, so any two distinct
register elements compare unequal and LWW is a total order. The EXISTENCE
branch of `apply_change` (`src/sync_engine.cpp:884`) orders assertions by
`(hlc, author)` only. Two valid, signed assertions by the same author with the
same HLC and opposite present bits therefore compare *equal*, and whichever
arrives second is dropped as "dominated". State now depends on arrival order.

Reproduced against the current head with two in-memory engines:

```
A: apply add=0 del=0   B: apply del=0 add=0
A exists=1 digest=099e16d63c5bcacc
B exists=0 digest=d7b674cfd7041a75
converged: NO
after export/apply both ways: converged: NO
```

The full-state oracle does not repair it: each side re-exports its own
assertion, the other drops it as a tie, and the digests stay different
forever. Range reconciliation is expected to behave the same way, since the
two elements have different hashes and each replica rejects the other's; that
path was not exercised by the repro.

**Who can produce it.** `Hlc::tick` is strictly monotonic within one engine,
so one honest engine cannot. Two engines sharing an identity can, and that is
not exotic: the Python quickstart in `README.md` derives identity from a
caller-supplied seed, and a user who reuses a seed on two devices has two
independent clocks under one author key. A device restored from a backup of
its log is the same situation. A malicious writer with namespace access can
do it at will.

**Fix shape.** Make the existence order total over the element, matching the
register rule: compare `(hlc, author, present)` and, to be safe against two
valid signatures over the same content, break the final tie on the element
hash. This is a merge-rule change, so it needs the same treatment as the
`{0,0}` fix: a `DECISIONS.md` entry, a regression test in
`convergence_test`, and confirmation that no on-wire or on-disk format moves
(none should). It is left unfixed in this commit so the fix can be reviewed
on its own.

The repro program is below. Build the library, then compile this as C99
against `include/` and link `libsync_engine.a` plus `libmonocypher.a`.

```c
#include <stdio.h>
#include <string.h>
#include "sync_engine.h"

static void mk(sync_change *c, uint64_t present, const uint8_t seed[32]) {
    memset(c, 0, sizeof *c);
    c->kind = SYNC_CHANGE_EXISTENCE;
    c->ns = (const uint8_t*)"ns"; c->ns_len = 2;
    c->entity = (const uint8_t*)"e1"; c->entity_len = 2;
    c->causal_length = present;
    c->hlc.physical = 1000; c->hlc.logical = 7;
    sync_change_sign(c, seed);
}

int main(void) {
    uint8_t sa[32], sb[32], sc[32];
    memset(sa, 1, 32); memset(sb, 2, 32); memset(sc, 3, 32);
    sync_engine *A = sync_engine_create(sa), *B = sync_engine_create(sb);
    sync_change add, del; mk(&add, 1, sc); mk(&del, 0, sc);
    sync_engine_apply(A, &add); sync_engine_apply(A, &del);
    sync_engine_apply(B, &del); sync_engine_apply(B, &add);
    uint8_t da[32], db[32];
    sync_engine_digest(A, da); sync_engine_digest(B, db);
    printf("converged: %s\n", memcmp(da, db, 32) == 0 ? "YES" : "NO");
    sync_engine_destroy(A); sync_engine_destroy(B);
    return 0;
}
```

## 6. Effort

Rough, for one engineer who knows the C++ and has used SPARK before:

| Phase | Weeks |
|---|---|
| 0: toolchain, CI, skeleton | 0.5 |
| 1: HLC + codec, proven | 1.5 |
| 2: merge rules + entity invariant, proven | 2 |
| 3: storage framing + load, proven | 2 |
| 4: differential CI + vectors | 1 |
| 5: Lean theorems | 3 to 4, separately staffed if possible |

Phases 1 through 4 are the mirror the question asked for. Phase 5 is the
part that proves the design rather than the code, and it can wait.
