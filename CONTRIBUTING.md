# Contributing

- Sign off every commit (`git commit -s`). CI rejects pull requests with a
  commit that lacks a `Signed-off-by` line (Developer Certificate of Origin).
- A change to the design goes to `docs/design/DESIGN.md` first, with its
  proof obligation added to §9, and must respect the rule in §1: every
  kill predicate is a down-set of the record order on its key.
- A change to the mathematics goes to `lean/` and must build with
  `lean/build.sh` with no `sorry`.
- A change to the implementation goes to `spark/` and must pass
  `spark/check.sh <module>`: the test main runs and gnatprove proves the
  module. Read `spark/CONVENTIONS.md` first.
