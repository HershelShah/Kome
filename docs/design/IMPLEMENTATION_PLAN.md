# Implementation plan: the frontier store in SPARK

This maps `DESIGN.md` onto SPARK packages, says which Lean theorem each
package refines, and fixes the order of work. The rule throughout: a
package is done when its test main passes and `spark/check.sh <name>`
proves it, and its contracts name the Lean theorems they refine.

## Phases

| Phase | Packages | DESIGN.md | Lean | State |
|---|---|---|---|---|
| 0 | `Kome` (bounds, status), `Kome.Byteorder`, `Kome.SHA256` | §2 bounds | — | done; Byteorder proved; SHA256 tested, 64 of 568 checks open |
| 1 | `Kome.Versions`, `Kome.Headers`, `Kome.Registers`, `Kome.Frontier` | §2, §3, §4 | T1, T2', T4', `applyA`/`keep` refinement | done, proved |
| 2 | `Kome.Crypto` (monocypher binding), `Kome.Records` (canonical encoding, hashing, signing, well-formedness) | §2 | T13 | next |
| 3 | `Kome.Store` (append-only log, index `cell → (offset, v)`, compaction = rewrite `F`), tombstone expiry | §7 | T11 (liveness, stated) | |
| 4 | `Kome.Emit` (chase, `seq_self`, SHADOWED, SEQ_EXHAUSTED) | §5 | T8, T9, T13 | |
| 5 | `Kome.Views` (`cell`, `exists`, `deleted_at`, `void`, `far`, `ROSTER_eff`) | §3, §6 | T5, T12 | |
| 6 | `Kome.Accumulator` (4096-bit homomorphic sum, prefix sums), `Kome.Digest` | §8 | T6 | |
| 7 | `Kome.Reconcile` (range split, HAVE round, module I sketch, register join in HELLO) | §8, §4 | T7 (open in Lean) | |
| 8 | `Kome.Epochs` (hash-chained keys), `Kome.Roster` (members, roots, revocation) | §6 | T14 (paper) | |
| 9 | Transports (Noise XX, sealed bundles), C ABI | §8, §10.7 | — | |
| 10 | Extension F (typed fields) | §4 | F's T15–T17 | after T7 |

## Phase 1 in detail (the lattice core)

`Kome.Versions` is `Version` and `Version.lt`, a chain of word comparisons;
the four lemmas (irreflexive, asymmetric, transitive, trichotomous) are what
every later proof uses, as in Lean where every later theorem uses only the
`StrictTotal` instance.

`Kome.Headers` is `Record` and `dominates`. A header is a record minus its
payload: the lattice never looks at a value. Every kind carries its identity
in one `Version` (a roster's is `(0, signer, gen, h)`, a revocation's is
`(from_t, subject, rev_seq, h)`), so one order serves all four kinds and
`Dominates` is a quantifier-free public definition; the lemmas are
`Lemma_Dominates_Irrefl`, `Lemma_Dominates_Trans` (T2') and
`Lemma_Revoke_Never_Dominated` (T12).

`Kome.Registers` is the pair of grow-only registers (`maxceil`, `W`),
opaque, with `Extends` (writer-set inclusion) and the lemmas that make
admission monotone.

`Kome.Frontier` is `State`, `adm`, `keep`, `applyA`. The state is the held
headers plus the registers. `Apply`'s postcondition is the refinement
statement:

- registers only grow and exactly as the record says (T4');
- every held record was held before or is the record applied (`keep` is a
  filter of `held ++ [r]`);
- every record held before is still held or is dominated by an admitted
  held record (nothing is lost except by domination);
- the held set is always its own frontier, every held record is admitted,
  and no record is held twice;
- `OK` means held, `Dominated` means beaten and not held, `Inadmissible`
  and `No_Space` mean unchanged.

Lean's `convergence` then applies to any two replicas that run `Apply` on
the same set in any order. The one deliberate divergence from the model is
that inadmissible records are refused rather than held (DESIGN.md §10.1);
the test main models the re-offer by applying a record list to a fixpoint.

## Proof hygiene learned in phase 1

The lattice core took one day of design and a day of proof engineering;
all of the second day was spent finding these four rules, now in
`spark/CONVENTIONS.md`:

- Identifiers and keys in the lattice are records of words, not byte
  arrays, so that record equality is logical equality for the prover.
  Every congruence step (`Held (S, J) = R` therefore `Dominates (Q, R)`)
  depends on it, and the byte order becomes quantifier-free.
- Public expression functions are fine when quantifier-free and harmful
  when quantified; the register set is opaque with lemmas for that reason.
- Reason about a private type through its public functions in contracts
  and asserts, and bridge each state change with an explicit equality of
  the public view before and after.
- Replace nested existentials in loop invariants with ghost witness arrays,
  and record in the same invariant every property the witnesses need later
  (the last open goal was a kept record's "not dominated", which the
  witness invariant had not carried).

Result: `Kome.Frontier.Apply` proves with 110 run-time checks, 76
assertions and 88 contract checks discharged by cvc5 and z3, no
justifications, no unproved goals, in under three minutes.
