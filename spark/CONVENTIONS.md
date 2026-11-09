# Conventions for the Kome SPARK implementation

Every package under `spark/src/` must obey these rules. The rules make the
result a proved implementation of `docs/design/DESIGN.md` that refines the
Lean model in `lean/Kome/Frontier.lean`. Ada that only compiles is not
sufficient.

## What the project builds

The design document is the specification. The Lean file proves theorems
about the *functions* of the design (the version order, domination, the
frontier, admission, apply). The SPARK code implements those functions with
bounded, in-place data. Its contracts state that it implements exactly those
functions. gnatprove discharges the contracts.

The division of work is strict. Lean proves set-level theorems (convergence
in any order, the frontier homomorphism). SPARK proves that the code is the
function that the theorem is about, and it proves every run-time check.
Neither tool does the other's work.

If a SPARK contract mirrors a Lean theorem, name the theorem in the comment
(`T2'`, `Frontier.lean dominates_trans`). If the implementation is
intentionally different from the model, say so in the comment and record
the difference in DESIGN.md §10.1, which is the only divergence register:
it lists what the implementation has and the model does not (no
certificates, no `ns`, no capacity, no clock clamp, `Nat` for `u48`, no
journal, and expiry on arrival). A difference that is not listed there is
a bug in one of the two.

## Layout

- Put each DESIGN.md concept in one child package `Kome.<Name>`, in the
  files `kome-<name>.ads` and `kome-<name>.adb`. You can add helper children
  (`Kome.<Name>.<Part>`, file `kome-<name>-<part>.ads`).
- Write one test main for each package that has behaviour:
  `tests/test_<name>.adb`, procedure `Test_<Name>`.
  - The main must print `PASS <check>` or `FAIL <check>` for each check.
  - If a check failed, the main must end with `Set_Exit_Status (Failure)`.
  - Do not use a test framework.

  The tests compile with `-gnata`, so every `Pre`, `Post`,
  `Loop_Invariant`, `Assert` and ghost lemma also *executes* on the test
  data. If the proof of a lemma is still open, the tests at least check the
  lemma on examples.
- Put known-answer vectors in `vectors/<name>.txt`, with one vector on each
  line. Separate the hex fields with spaces. You can use `#` comments. For
  standard algorithms (BLAKE2b, Ed25519, X25519), get the vectors from
  published test suites or from an implementation that is independent of
  monocypher. The header comment must name the source.
- To build, run and prove a module, use `spark/check.sh <name>`.
  `check.sh all` does every module. If GNAT 14, gprbuild, gnatprove or the
  provers are not on the path, the script gets them from nixpkgs.

## SPARK rules

- Put `pragma SPARK_Mode (On)` on every spec and body. The only exceptions
  are thin bindings to C (`Kome.Crypto` over monocypher, OS calls in the
  transport layer). Their bodies must be `SPARK_Mode (Off)`, and their specs
  must stay `On` with full contracts. This keeps the callers provable.
- Do not use access types, exceptions as control flow, `Ada.Unchecked_*` or
  tasking. Do not use recursion unless a `Subprogram_Variant` bounds it.
- Bound every item of variable length. Use an array plus a length, or a
  discriminant that sets the capacity when the object is created (as
  `Kome.Frontier.State (Cap)` does). Take the bound from `Kome` (root), and
  cite the DESIGN.md section that sets it.
- Use *range* types for semantic integers (`U48`, `Epoch`, counts), never
  modular types. Then every overflow is a proof obligation, and no value is
  reserved (H6). `Kome.Byte` and `Kome.U64` are the only modular types.
  `Byte` is the wire unit. `U64` is for the limbs of the accumulator and
  their byte encoding (`Kome.Byteorder`, `Kome.Accumulator`, `Kome.Digest`)
  and for C storage in `Kome.Crypto`. There, wrap is the intended
  semantics.
- If an operation can exceed a bound, it must refuse with a `Status` and
  leave the state unchanged. Its `Post` must say so (T13). Do not let a
  value saturate silently.
- Give every public subprogram a `Pre` and a `Post`. The contracts are the
  most important part of the code. Write each algebraic law as a ghost
  lemma procedure named `Lemma_<Law>`, with the law as its `Post`. A lemma's
  body must be a proof (calls to other lemmas, loops with invariants,
  asserts), not code.
- Keep the prover's view small, and keep equality logical. Without
  these two rules, the frontier proof fails:
  1. In the lattice, make identifiers and keys records of fixed words
     (`Id128`, `Key256`), never byte arrays. For the prover, Ada equality
     on a record that contains an array is not logical equality. So the
     prover cannot substitute it inside `Dominates`. On a record of
     scalars, Ada equality is logical equality. The byte-lexicographic
     order becomes a chain of word comparisons with no loop, and T1 proves
     by unfolding. Use bytes only at the wire and crypto boundary
     (`Kome.Records`, `Kome.Crypto`).
  2. A public expression function is an axiom in every unit that sees it.
     Make quantifier-free expression functions (`Lt`, `Dominates`,
     `Admitted`) public. They cause no problems, and the prover can then
     unfold them. Keep a *quantified* expression function (a set
     membership, the postcondition of a loop) private to its package. The
     prover instantiates a public one on every goal in every unit, and
     unrelated goals time out. (`Kome.Registers` exports `In_W` and
     `Extends` opaquely, with lemmas.) If a unit must see the definition,
     make it visible only to that unit and accept the cost there.
- Write contracts, assertions and invariants with the public functions of a
  private type (`Held`, `Count`, `Regs`), never with its fields. After every
  state change, assert a "bridge"
  (`for all I => Held (S, I) = Held (Old, I)`). SMT provers instantiate a
  hypothesis only on terms that are already in the goal. The bridge makes
  these terms.
- Where possible, use explicit witnesses in loop invariants, not nested
  existentials. A ghost array that records *which* old index each kept
  element came from is first-order, and it proves. "Some index exists"
  inside "for all" frequently does not prove.
- Code that touches a file or a clock declares it in `Global`/`Depends`.
  `Open_From_Log` is `Global => null`. The log is append-only: DESIGN.md
  §10.10 (a) rewrites no byte of it. The data capacity is a parameter of
  each open, and the HEADER keeps the `data_cap` of the open that wrote
  it, so the only writes are appends at `Log_Length` and the rename of
  `Compact`.

## Proof hygiene

- `pragma Assume` and `pragma Annotate` (including justified checks, and
  every other GNATprove annotation) are forbidden in `spark/src` and
  `spark/tests`. `check.sh` greps for both and fails on either. A fact
  that the prover cannot discharge is a ghost lemma with a proof body, a
  tested known gap listed in `docs/design/IMPLEMENTATION_PLAN.md`, or an
  assumed `Post` of a `SPARK_Mode Off` body that a known-answer vector
  checks; it is never an assumption written into the proved code.
- "Private" in rule 2 means "completed in the body". To hide an expression
  function, complete it in the body. `Hide_Info` is a `pragma Annotate`,
  so it is not available; and in gnatprove 14 a private-part `Hide_Info`
  would not have hidden a definition that is completed in the private part
  anyway (`kome-accumulator.ads` records the probe).
- Do not put a `Dynamic_Predicate` on a state type such as
  `Kome.Frontier.State` or `Kome.Store.Store`. gnatprove 14 crashed when
  the code assigned such an object. State the invariant as a named function
  (`Is_Frontier`, `Valid`) in each `Pre`/`Post`.
- Decide every refusal before the state changes. State each outcome as an
  iff in the `Post`, with `Unchanged (S'Old, S)` or `S = S'Old` on refusal.
  Do not restore the state after a failed step.
- Bound a ghost lemma's quantifiers by the object's counts, never by a
  full index type. Every ghost lemma runs under `-gnata`.
- To make a relation true, call a lemma (`Lemma_Unchanged_Refl`), not real
  code.
- Use `Assertion_Policy (... => Ignore)` only for proved steps that would
  make a test quadratic. List each such region in
  `docs/design/IMPLEMENTATION_PLAN.md`.
- If element-wise equal inputs must give equal results, give the imported
  function a congruence axiom (`Kome.Crypto.Lemma_Blake2b_Congruent`). Give
  each layer above it its own congruence lemma. gnatprove has no
  extensionality for the array argument of a function.
- Do not put a conjunct about only the pre-state in a `Post`. Move it to the
  caller's `Pre` or into a ghost lemma (`Lemma_Ends_Below`). Such a
  conjunct triggers `-gnatw.t`.
- If a function calls a procedure, give the procedure `Always_Terminates`.
- If a value comes from a secret and only contracts use it, make it a ghost
  function (`X25519_Shared`). Then no executable temporary holds the
  secret.
- Every goal must prove well under the 20 s step limit. Where possible,
  both cvc5 and z3 must prove it. If only one prover proves a goal, or if a
  goal takes more than approximately 10 s, split the goal. For example,
  restate the invariant at the end of the operation, or use two witness
  invariants in place of one.
- Run only one gnatprove at a time. `check.sh` takes a lock, because
  gnatprove 14's `/dev/shm` semaphore ignores `TMPDIR`.

## Cryptography

`Kome.Crypto` binds monocypher (Ed25519, X25519, BLAKE2b,
XChaCha20-Poly1305). Do not implement these algorithms again.
