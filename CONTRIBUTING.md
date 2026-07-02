# Contributing to Kome

Thanks for your interest. Two things are non-negotiable for every
contribution: the tests must pass, and every commit must be signed off
under the Developer Certificate of Origin (DCO). Everything else is
negotiable.

## License terms for contributions

Kome is MIT-licensed ([LICENSE](LICENSE)). Contributions are accepted on
**inbound = outbound** terms: by submitting a contribution you license it
under the same MIT license as the project.

Please note what the MIT license permits, so there are no surprises later:
the project maintainers may incorporate your contribution into future
versions of Kome, including versions distributed under additional or
different license terms (for example commercially licensed builds or
proprietary add-on modules), as the MIT license allows. Your contribution
itself remains MIT-licensed, you retain your copyright, and the required
copyright notice is preserved. If you are not comfortable with that,
please do not submit the contribution.

## Developer Certificate of Origin

Every commit must carry a `Signed-off-by` line certifying the
[Developer Certificate of Origin 1.1](https://developercertificate.org/):

```
Developer Certificate of Origin
Version 1.1

Copyright (C) 2004, 2006 The Linux Foundation and its contributors.

Everyone is permitted to copy and distribute verbatim copies of this
license document, but changing it is not allowed.


Developer's Certificate of Origin 1.1

By making a contribution to this project, I certify that:

(a) The contribution was created in whole or in part by me and I
    have the right to submit it under the open source license
    indicated in the file; or

(b) The contribution is based upon previous work that, to the best
    of my knowledge, is covered under an appropriate open source
    license and I have the right under that license to submit that
    work with modifications, whether created in whole or in part
    by me, under the same open source license (unless I am
    permitted to submit under a different license), as indicated
    in the file; or

(c) The contribution was provided directly to me by some other
    person who certified (a), (b) or (c) and I have not modified
    it.

(d) I understand and agree that this project and the contribution
    are public and that a record of the contribution (including all
    personal information I submit with it, including my sign-off) is
    maintained indefinitely and may be redistributed consistent with
    this project or the open source license(s) involved.
```

To sign off, commit with `-s`:

```bash
git commit -s -m "fix: ..."
```

which appends a line like:

```
Signed-off-by: Your Name <you@example.com>
```

Use your real name and a reachable email address. Pull requests with
unsigned commits fail CI; fix with `git rebase --signoff` and force-push
to your branch.

## Practical expectations

- **Tests gate everything.** Every behavior change needs a test that
  fails without it; see [docs/SCENARIOS.md](docs/SCENARIOS.md) for how
  scenarios map to suites. Run `ctest --test-dir build` locally, and a
  sanitizer build (`-DSYNC_SANITIZER=address`) for anything touching the
  engine, codec, or transport.
- **No new dependencies.** The single vendored dependency (monocypher) is
  a deliberate property of the project, not an accident.
- **Match the codebase.** C11/C++17, existing naming and error-handling
  conventions, comment density as you find it.
- For protocol, data-model, or security-relevant changes, open an issue
  first — [DECISIONS.md](DECISIONS.md) records why things are the way
  they are, and changes there need discussion before code.
- Security issues: follow [SECURITY.md](SECURITY.md), do not open a
  public issue.
