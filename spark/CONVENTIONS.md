# Conventions for the Kome SPARK implementation

Every package under `spark/src/` follows these rules so the result is a
proved implementation of `docs/design/DESIGN.md`, refining the Lean model in
`lean/Kome/Frontier.lean`, and not merely Ada that compiles.

## What is being built

The design document is the specification. The Lean file proves theorems
about the *functions* the design is made of (the version order, domination,
the frontier, admission, apply). The SPARK code implements those functions
with bounded, in-place data, and its contracts state that it implements
exactly them. gnatprove discharges the contracts. The division of labour is
strict: Lean proves set-level theorems (convergence in any order, the frontier
homomorphism); SPARK proves that the code is the function the theorem is
about, plus every run-time check. Neither is asked to do the other's job.

Where a SPARK contract mirrors a Lean theorem, the comment names it
(`T2'`, `Frontier.lean dominates_trans`). Where the implementation differs
deliberately from the model, the comment says so and DESIGN.md §10 records
it (today: the model holds inadmissible records, the implementation refuses
them).

## Layout

- One DESIGN.md concept = one child package `Kome.<Name>` in
  `kome-<name>.ads` / `kome-<name>.adb`. Helper children are allowed
  (`Kome.Store.Frames`, file `kome-store-frames.ads`).
- One test main per package that has behaviour: `tests/test_<name>.adb`,
  procedure `Test_<Name>`. It prints `PASS <check>` / `FAIL <check>` per
  check and ends with `Set_Exit_Status (Failure)` if anything failed. No test
  framework. Tests are compiled with `-gnata`, so every `Pre`, `Post`,
  `Loop_Invariant`, `Assert` and ghost lemma is also *executed* on the test's
  data; a lemma whose proof is still open is at least checked on examples.
- Known-answer vectors go in `vectors/<name>.txt`, one per line, hex fields
  separated by spaces, `#` comments allowed. For standard algorithms
  (SHA-256, BLAKE2b, Ed25519) the vectors come from the published test suites
  and say so in the header comment.
- Build, run and prove with `spark/check.sh <name>`; `check.sh all` does every
  module. It fetches GNAT 14, gprbuild, gnatprove and the provers from
  nixpkgs when they are not on the path.

## SPARK rules

- `pragma SPARK_Mode (On)` on every spec and body. The only exceptions are
  thin bindings to C (`Kome.Crypto` over monocypher, OS calls in the
  transport layer): their bodies are `SPARK_Mode (Off)` and their specs stay
  `On` with full contracts, so callers remain provable.
- No access types, no exceptions as control flow, no recursion unless
  bounded by a `Subprogram_Variant`, no `Ada.Unchecked_*`, no tasking.
- Every variable-length thing is bounded: an array plus a length, or a
  discriminant that fixes the capacity when the object is created (as
  `Kome.Frontier.State (Cap)` does). The bound comes from `Kome` (root) and
  cites the DESIGN.md section that sets it.
- Semantic integers are *range* types (`U48`, `Epoch`, counts), never
  modular, so every overflow is a proof obligation and no value is reserved
  (H6). Modular types exist only for wire encoding and hashing
  (`Kome.Byteorder`, `Kome.SHA256`), where wrap is the intended semantics.
- An operation that could exceed a bound refuses with a `Status` and leaves
  the state unchanged, and its `Post` says so (T13). Nothing saturates
  silently.
- Contracts are the point. Every public subprogram has `Pre`/`Post`.
  Algebraic laws are ghost lemma procedures named `Lemma_<Law>` with the law
  as `Post`; their bodies are proofs (calls to other lemmas, loops with
  invariants, asserts), not code.
- Keep the prover's view small, and keep equality logical. Two things
  made the frontier proof intractable until they were removed, and both
  are now rules:
  1. In the lattice, identifiers and keys are records of fixed words
     (`Id128`, `Key256`), never byte arrays. Ada equality on a record that
     contains an array is not logical equality for the prover, so it
     cannot substitute inside `Dominates`; on a record of scalars it is.
     The byte-lexicographic order becomes a chain of word comparisons with
     no loop, and T1 proves by unfolding. Bytes exist only at the wire and
     crypto boundary (`Kome.Records`, `Kome.Crypto`).
  2. A public expression function is an axiom in every unit that sees it.
     Quantifier-free ones (`Lt`, `Dominates`, `Admitted`) are harmless and
     should be public so the prover can unfold them. A *quantified* one
     (a set membership, a loop's postcondition) is instantiated on every
     goal in every unit and makes unrelated goals time out: keep it
     private to its package (`Kome.Registers` exports `In_W` and `Extends`
     opaquely with lemmas) or accept that it is only visible where needed.
- Write contracts, assertions and invariants with the public functions of a
  private type (`Held`, `Count`, `Regs`), never its fields, and after every
  state change assert a "bridge" (`for all I => Held (S, I) = Held (Old, I)`).
  SMT provers instantiate a hypothesis only on terms that already exist in
  the goal; the bridge creates them.
- Prefer explicit witnesses to nested existentials in loop invariants: a
  ghost array that records *which* old index each kept element came from is
  first-order and proves; "some index exists" inside "for all" often does
  not.
- `Global`/`Depends` on anything that touches a file or a clock, so flow
  analysis can prove "open never writes".

## Proof hygiene learned in round three

- "Private" in rule 2 means completed in the body. In gnatprove 14 an
  expression function completed in the private part is visible to clients,
  even with a private-part `Hide_Info`. Only a body completion, or
  `Hide_Info "Expression_Function_Body"` in the visible part, hides it. The
  probe is recorded in `kome-accumulator.ads`.
- No `Dynamic_Predicate` on a state type such as `Kome.Frontier.State` or
  `Kome.Store.Store`. gnatprove 14 crashed when such an object was
  assigned. State the invariant as a named function (`Is_Frontier`,
  `Valid`) in each `Pre`/`Post`.
- Decide every refusal before the state changes. State each outcome as an
  iff in the `Post`, with `Unchanged (S'Old, S)` or `S = S'Old` on refusal.
  Do not restore the state after a failed step.
- Every ghost lemma runs under `-gnata`. Bound its quantifiers by the
  object's counts, never by a whole index type. To make a relation hold,
  call a lemma (`Lemma_Unchanged_Refl`), not real code.
  `Assertion_Policy (... => Ignore)` is only for proved steps that would
  make a test quadratic. List each such region in `IMPLEMENTATION_PLAN.md`.
- gnatprove has no extensionality for the array argument of a function.
  For element-wise equal inputs to have equal results, an imported function
  needs a congruence axiom (`Kome.Crypto.Lemma_Blake2b_Congruent`), and each
  layer above it needs its own congruence lemma.
- A `Post` conjunct about the pre-state alone triggers `-gnatw.t`. Move it
  to the caller's `Pre` or into a ghost lemma (`Lemma_Ends_Below`).
- A procedure that a function calls needs `Always_Terminates`. A value
  derived from a secret and used only in contracts is a ghost function
  (`X25519_Shared`), so that no executable temporary holds the secret.
- Proof margin: every goal should prove well under the 20 s step limit,
  by both cvc5 and z3 where possible. Split any goal that only one prover
  proves, or that takes more than about 10 s: restate the invariant at the
  operation's end, or use two witness invariants in place of one. Run one
  gnatprove at a time. `check.sh` takes a lock because gnatprove 14's
  `/dev/shm` semaphore ignores `TMPDIR`.

## Cryptography

`Kome.Crypto` binds monocypher (Ed25519, X25519, BLAKE2b,
ChaCha20-Poly1305). Do not reimplement them. SHA-256 is implemented in SPARK
(`Kome.SHA256`) because the design's fixed primitive set includes it and the
previous engine shipped a tested implementation.
