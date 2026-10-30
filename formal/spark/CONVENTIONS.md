# Conventions for the Kome SPARK mirror

Every module under `formal/spark/src/` follows these rules so the packages fit
together and so the result is provable, not merely Ada.

## Layout

- One C++ module = one child package `Kome.<Module>` in `kome-<module>.ads`
  (spec) and `kome-<module>.adb` (body). Helper children are allowed
  (`Kome.Storage.Frames`), named `kome-storage-frames.ads`.
- One test main per module: `tests/test_<module>.adb`, procedure
  `Test_<Module>`. It prints `PASS <name>` / `FAIL <name>` per check and ends
  with `Set_Exit_Status (Failure)` if anything failed. No test framework.
- Known-answer vectors generated from the C++ engine go in
  `vectors/<module>.txt`, one line per vector, hex fields separated by
  spaces, `#` comments allowed. The test reads them with `Ada.Text_IO`.
- Build and run with `formal/spark/check.sh <module>`. It builds only the
  closure of your test main, so a sibling module that is mid-edit cannot
  break your build.

## SPARK rules

- `pragma SPARK_Mode (On)` on every spec and body. The only exceptions are
  thin bindings to C (`Kome.Crypto` over monocypher, OS calls in the
  transport layer): their bodies are `SPARK_Mode (Off)` and their specs stay
  `On` with full contracts, so callers remain provable.
- No access types, no exceptions as control flow, no recursion unless
  bounded by a `Subprogram_Variant`, no `Ada.Unchecked_*`, no tasking.
- Variable-length data is a bounded buffer: an array plus a length, or an
  `Ada.Containers.Formal_Vectors` / `Formal_Ordered_Maps` instance with a
  capacity. Bounds come from `Kome` (root) or a constant in your spec with a
  comment saying which C++ limit it mirrors.
- Integer types: `Kome.U64`, `U32`, `U16`, `Byte` are modular. Use them for
  values the C++ holds in `uint64_t` etc. Every arithmetic step that the C++
  guards against wrap (clock bumps, length sums, counters) gets a
  precondition or an explicit saturating/refusing branch with a comment, and
  a postcondition stating the bound. Wrap that the C++ *intends* (hash
  mixing) is fine on modular types.
- Contracts are the point. Every public subprogram has `Pre`/`Post`. Where
  the C++ documents an invariant (monotone clock, never `{0,0}`, digest
  unchanged by compaction, decode(encode(x)) = x), state it as a `Post`, a
  `Type_Invariant`, or a ghost lemma procedure with `Ghost` and the law as its
  `Post`. Algebraic laws (commutative, associative, idempotent merge) are
  ghost lemmas named `Lemma_<Law>`.
- `Global`/`Depends` on anything that touches a file or a clock, so flow
  analysis can prove "open never writes".
- Use `Ada.Containers.Formal_Ordered_Maps` for the C++ `std::map` state;
  keys are bounded byte strings compared byte-lexicographically (the C++
  order is `std::string` `<`, which is `memcmp` order: unsigned bytes).

## Fidelity rules

- Translate behavior, not structure. Match the C++ **observable** semantics
  exactly: same accept/reject decision, same bytes out, same error code,
  same digest. If the C++ has a bug (see `docs/FORMALIZATION_PLAN.md` §5),
  mirror the C++ behavior and add a `--  DIVERGENCE CANDIDATE:` comment at
  the site naming what the proof will want changed. Do not silently fix.
- Where the C++ throws `std::bad_alloc` the mirror returns `Err_Nomem` or has
  a capacity precondition; say which in a comment.
- Cryptography is an oracle: `Kome.Crypto` binds monocypher. Do not
  reimplement Ed25519, X25519, BLAKE2b, or ChaCha20-Poly1305. SHA-256 is
  implemented in the C++ tree (`src/sha256.cpp`) and *is* translated.
- Every differential test vector in `vectors/` is produced by a C program
  under `vectors/gen/` built against `build/libsync_engine.a` and
  `build/libmonocypher.a` in the repo root (already built). Commit the
  generator and the vectors.
