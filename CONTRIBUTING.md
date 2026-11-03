# Contributing

- Sign off every commit (`git commit -s`). If a pull request has a commit
  without a `Signed-off-by` line (Developer Certificate of Origin), CI
  rejects the pull request.
- If you change the design, change `docs/design/DESIGN.md` first. Add the
  proof obligation of the change to §9. The change must obey the rule in
  §1: every kill predicate is a down-set of the record order on its key.
- If you change the mathematics, make the change in `lean/`. It must build
  with `lean/build.sh`, with no `sorry`.
- If you change the implementation, make the change in `spark/`. Read
  `spark/CONVENTIONS.md` first. The change must pass
  `spark/check.sh <module>`: the test main runs and gnatprove proves the
  module.
