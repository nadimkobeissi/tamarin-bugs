# Soundness and diagnostic defects in the Tamarin prover

Proof-of-concept theories for two confirmed defects in `tamarin-prover`, a
control that isolates the mechanism of the first, and five differential-testing
harnesses in [`tools/`](tools/).

Every verdict quoted below is actual tool output, not expected output.

## Status

All findings here were reported to the Tamarin maintainers by email on 11 August
2026 and, at their request, in
[issue #917](https://github.com/tamarin-prover/tamarin-prover/issues/917). Felix
Linker responded the same day. The full timeline and correspondence is in
[DISCLOSURE.md](DISCLOSURE.md).

| Finding | Maintainer position | Fix |
|---|---|---|
| `last()` in a restriction defeats `isSafetyFormula`, making induction unsound | Confirmed as a bug. Classification as a *soundness* bug is disputed; see [below](#on-the-soundness-classification) | [PR #915](https://github.com/tamarin-prover/tamarin-prover/pull/915), open |
| The vacuity wellformedness checks are unreachable dead code | Confirmed | [PR #916](https://github.com/tamarin-prover/tamarin-prover/pull/916), open |

One correction to earlier versions of this repository, made after maintainer
feedback and against the interest of the write-up: **PoC 03 is not a wrong
verdict.** The vacuously true lemma really is true, so `verified` is correct.
The defect is that Tamarin has a check for exactly this modelling error and that
check never runs. Earlier drafts filed this as a missed attack. That was wrong.

Of the two defects, the `last()` finding is the soundness defect, and that
classification is argued in full [below](#on-the-soundness-classification).

## Environment

| | |
|---|---|
| Binary under test | `tamarin-prover 1.12.0` (Homebrew), Maude 3.5.1 |
| Source read against | `develop` @ `ef3f0468`, cabal version 1.13.0 |
| Platform | macOS (darwin 25.6.0), arm64 |

The binary is one minor version behind the tree that was read. Every implicated
code path was compared with `git diff 1.12.0 HEAD` and was unchanged at the time
of reporting: `isSafetyFormula`, the `partition isSafetyFormula` in
`formulaToSystem`, and the `incompleteMSRs` guard in `factReports`. PRs #915 and
#916 change all three. Against a build with either PR applied, the corresponding
PoCs are expected to stop reproducing, which is the point of `run.sh`.

## Reproducing

```sh
./run.sh                          # uses tamarin-prover from PATH
./run.sh /path/to/tamarin-prover  # or point at a specific build
```

Exits `0` if every theory still behaves as recorded, `1` if any behaviour has
changed, so it doubles as a regression check against a patched build.

---

## 1. `last()` defeats the safety-formula classifier

Tamarin's induction rule is sound only over a prefix-closed set of traces, and
`formulaToSystem` (`lib/theory/src/Theory/Constraint/System.hs:849-856`) splits
restrictions accordingly, with the authors' own reasoning attached:

```haskell
(safetyRestrictions, otherRestrictions) = partition isSafetyFormula restrictions
-- Non-safety restrictions must be added to the formula, as they render the set
-- of traces non-prefix-closed, which makes the use of induction unsound.
gf2 = gconj $ gf1 : otherRestrictions
```

The classifier it trusts (`Theory/Constraint/System/Guarded.hs:156-164`) tests
for closed and existential-free:

```haskell
isSafetyFormula gf0 = null (frees [gf0]) && noExistential gf0
  where
    noExistential (GAto _)            = True     -- accepts Last atoms
    noExistential (GGuarded Ex _ _ _) = False
```

That is not the same as prefix-closed. `last(#i)` contains no existential, so
`"All x #i. Start(x) @ i ==> not(last(#i))"` is labelled `// safety formula` in
Tamarin's own output. The trace `[Start(x)]` violates the restriction and its
extension `[Start(x), Step(x)]` satisfies it, which is the negation of the
property the docstring names.

**PoC 01** gives one formula two verdicts:

```
NoStart_with_induction    (all-traces): verified (3 steps)
NoStart_without_induction (all-traces): falsified - found trace (2 steps)
```

**PoC 01b is the control.** Same protocol, same lemma, same
non-prefix-closedness, but the restriction is phrased with a guarded existential
(`==> Ex #j. Step(x) @ j`), which lands on the other side of
`partition isSafetyFormula`:

```
NoStart_with_induction    (all-traces): falsified - found trace (6 steps)   correct
```

and the restriction is not annotated `// safety formula`. This rules out the
protocol, the lemma, induction in general, and non-prefix-closed restrictions in
general. What is left is the classification of `Last` atoms.

**PoC 02** chains it into a whole-theory compromise. `[sources]` implies
`UseInduction` with no annotation from the user (`ClosedTheory.hs:120`), and
`[sources]` lemmas are consumed before any proof runs (`CloseRule.hs:426`) for
every lemma in the file:

```
rule Gen: [ Fr(k) ] --[ Gen(k) ]-> [ Out(k) ]     // key sent in the clear
```
```
bogus_sources (all-traces):   verified (3 steps)
secrecy       (all-traces):   verified (2 steps)
gen_reachable (exists-trace): verified (2 steps)
/* All wellformedness checks were successful. */
```

Every hygiene signal a Tamarin user is taught to check comes back green: clean
wellformedness, no `sorry`, no falsified lemma, and an `exists-trace` witness
confirming the model is not vacuous.

### On the soundness classification

The maintainers accept the bug and dispute the label. Felix Linker's position,
from his reply of 12 August 2026:

> As for theories 1 to 2, the issue is that you add a restriction that uses the
> last keyword. That keyword is intended for internal use only. We didn't check
> in enough places that this keyword does not occur. It's debatable whether this
> is a soundness bug as no proof rule was changed. We didn't apply all necessary
> checks to the input, though.

We do not accept this reading and insist that this is a soundness issue:

**The fix that corrects the verdict is a fix to the classifier.** PR #915
contains three changes: a warning when a formula uses `last`, a filter that drops
such restrictions in `formulaToSystem`, and a one-line change to
`isSafetyFormula`. Keep the warning and revert the other two, then run PoC 01.
Tamarin prints the warning and then prints `verified` for a false lemma, with the
same formula reported `falsified` three lines below. The warning labels a wrong
answer without correcting it.

**`isSafetyFormula` is a soundness predicate and it returned the wrong answer.**
It exists to discharge a side condition that induction needs. Its docstring
states the condition: a trace violating the formula can never be extended into
one satisfying it. It answered `True` for a formula where `[Start(x)]` violates
and `[Start(x), Step(x)]` satisfies. Whatever is also true about the input that
reached it, that is a wrong answer to a soundness question.

**"Internal use only" was not a rule a user could have followed.** The manual's
machine-tested grammar (`manual/grammar/grammar.ebnf`) derives `last()` from the
body of a restriction in three steps:

```
restriction ::= ('restriction'|'axiom') ident restriction_attr? ':' '"' (_formula: formula) '"'
_formula    ::= iff | imp | ... | _temporal_variable_operation | ...
_temporal_variable_operation ::= temp_var_induction | temp_var_order | temp_var_eq
temp_var_induction ::= ATOM('last' '(' temporal_var ')')
```

`last` sits in the same production as `temp_var_order` (`#i < #j`) and
`temp_var_eq` (`#i = #j`), which appear in restrictions constantly. The parser
accepted the restriction, the wellformedness checker passed it, and Tamarin
printed `// safety formula` beside it, which was a false statement about that
restriction.

**The hole is as old as the fix.** `9726e4c4` ("fixed two soundness bugs",
August 2012) introduced `isSafetyFormula` to fix soundness bug #108. The body of
the predicate at that commit and at `ef3f0468` is byte identical; it was never
modified. `last` was already surface syntax in that same commit
(`9726e4c4:src/Theory/Text/Parser.hs:340`). So no new construct outran an old
check. The check was wrong on the day it was written, about syntax that existed
on the same day.

The argument as sent to the maintainers is
[here](https://github.com/tamarin-prover/tamarin-prover/issues/917#issuecomment-5267310122).

### Scope, stated against interest

**No shipped case study is affected.** `tools/lastscan.py` classifies every
occurrence of `last(` across all 1042 `.spthy` files under `examples/`:

```
scanned                      : 1042 .spthy files
files containing 'last('     : 36
occurrences in RESTRICTIONS  : 0   <-- the only ones that can trigger the bug
```

All 36 hits are inside Tamarin's own machine-generated proof text saved into
analyzed outputs (`solve( (last(#i)) | (Ex #j. Update(k,r) @ #j & ...) )`), never
in a user-written restriction.

The accurate claim is a live, reachable unsoundness in documented syntax that
currently affects no published Tamarin result. It is a trap that has been armed
for fourteen years and that nobody has stepped on. Anyone citing this should say
so in those words.

### Fix

PR #915. The load-bearing line is
`noExistential (GAto a) = not $ isLastAtom a`. `toInductionHypothesis` already
rejects `last` (`Guarded.hs:619`), so reclassifying makes induction inapplicable
to such theories, which is correct.

---

## 2. The vacuity wellformedness checks are dead code

`lib/theory/src/Theory/Tools/Wellformedness.hs:578-583`:

```haskell
-- | Report on facts usage. Skip checks on non-existant actions if `incompleteMSRs` is True.
factReports incompleteMSRs thy =
    concat [ reservedReport, ..., factUsage, factLhsOccurNoRhs ]
    ++ concat [ inexistentActions ++ inexistentActionsRestrictions | incompleteMSRs ]
```

The guard is the inverse of its own docstring, and the sole production call site
hardcodes `False` (`src/Main/TheoryLoader.hs:602`, with a `TODO`).
`inexistentActions` and `inexistentActionsRestrictions`
(`Wellformedness.hs:706-734`) are fully implemented, with error messages, and
never execute.

**PoC 03** is a lemma referring to `SecrettKey` where the rules emit `SecretKey`:

```
secrecy_typo     (all-traces): verified (2 steps)
secrecy_intended (all-traces): falsified - found trace (3 steps)
/* All wellformedness checks were successful. */
```

`--quit-on-warning` does not help: no warning is generated at all.

### This is not a wrong verdict

No rule emits `SecrettKey`, so `secrecy_typo` quantifies over an empty set and is
vacuously true. `verified` is the correct answer to the question actually asked.
Earlier drafts of this repository filed PoC 03 as a missed attack. That was an
error, corrected here on maintainer feedback:

> In theory 3, the property proven true is in fact true. But you are right that
> a warning should be generated to inform the user about the modeling mistake.

The defect is that Tamarin ships a check for this exact modelling error, the most
common one in the tool, and the check is unreachable. The user gets a clean
wellformedness report and a lemma that asserts nothing.

### Provenance

```sh
git log -L 583,583:lib/theory/src/Theory/Tools/Wellformedness.hs
# 98c3887f Extend ProVerif export module (#725)
```

Before PR #725 both checks were unconditional members of `factReports`. An
unrelated export-backend refactor disabled a working guardrail, and no test
noticed, because the suite compares end-to-end verdicts on case studies and no
case study depends on those checks firing.

### Fix

PR #916, which removes the flag rather than inverting it.

---

## Method: differential testing without ground truth

The harnesses in [`tools/`](tools/) exploit invariants that hold regardless of
what the right answer is.

| Tool | Invariant exploited |
|---|---|
| [`consistency_oracle.py`](tools/consistency_oracle.py) | In one theory, `all-traces φ` and `exists-trace ¬φ` must disagree. verified/verified or falsified/falsified is a self-contradiction. |
| [`stateful.py`](tools/stateful.py) | Same invariant, aimed at injective facts, monotonic state, SAPIC cells and locks. |
| [`differ.py`](tools/differ.py) | `--heuristic`, `--stop-on-trace`, `-s`, `-c`, `-d`, `--auto-sources` are documented to affect only *how* the search runs. All 16 configurations must agree on every lemma. |
| [`diffsym.py`](tools/diffsym.py) | Observational equivalence is symmetric: swapping every `diff(x,y)` to `diff(y,x)` must not change the verdict. |
| [`lastscan.py`](tools/lastscan.py) | Scope check: classifies every `last(` occurrence in a corpus as restriction / lemma / other. |

Controls confirm the oracles discriminate (`ctl_plain` vs `ctl_secret` in
`consistency_oracle.py` correctly return opposite verdicts).

**Completion status, stated because it bounds every negative result below.**
`consistency_oracle.py`, `stateful.py` and `lastscan.py` were run to completion,
and the results below are theirs. `differ.py` and `diffsym.py` were written and
launched but their sweeps did not complete: running 16 configurations over real
case studies, and diff-mode proofs over observational-equivalence models,
exhausted available RAM and the runs were killed. They are shipped because the
invariants they encode are the right ones, not because they returned a clean bill
of health. Nothing below is claimed on their behalf.

## What held up

Reported because negative results locate the defects, and because a write-up
that reported only hits would deserve the suspicion that it went looking for a
conclusion.

- **The core term algebra.** 15 cases across xor (self-cancellation, one-time
  pad, chained pads, `zero`), multiset, Diffie-Hellman, subterm, natural numbers,
  hashing and symmetric encryption, all consistent.
- **Injective facts and stateful reasoning.** The newest and most aggressive
  inference in the solver (`simpInjectiveFactEqMon`, `Simplify.hs:534-660`, which
  derives equalities and orderings from inferred monotonic behaviour) held on
  constant positions, strictly-increasing positions, nat counters, non-fresh
  identifiers, and SAPIC locked and unlocked state cells.
- **Stored-proof replay is sound.** Three separate forgeries against
  `case-studies-regression/Tutorial_analyzed.spthy`, namely weakening a lemma
  while keeping its proof, replacing the proof with a bogus one-step
  contradiction, and relabelling a case, were all caught and downgraded to
  `analysis incomplete`. Published `.spthy` proof artifacts do get re-validated.
- **Observational equivalence is reflexive in the one case measured.**
  `diff(t,t)` over symmetric encryption returned `verified (98 steps)`, as it
  must. The Diffie-Hellman and XOR variants were launched but killed before
  completing (RAM), so those two are unmeasured, not passes.
- **Predicate expansion is capture-free.** `expandFormula`
  (`Theory/Syntactic/Predicate.hs:94-105`) shifts de Bruijn indices correctly; a
  predicate body binding `y`, used at a call site that also binds `y`, gives
  results identical to the non-colliding control. Macro expansion, by contrast,
  is not hygienic: a macro body variable is captured by a same-named rule
  variable, silently and with a clean wellformedness report. Since the dangerous
  sub-case, an *unbound* injected variable, is caught by `unboundReport`, this
  was recorded as a model-integrity wart rather than kept as a PoC.
- **Oracles cannot cause unsoundness.** `oracleRanking`
  (`ProofMethod.hs:604-621`) returns `ranked ++ remaining`; omitted goals are
  appended, not dropped. Only `quitOnEmpty` terminates, and it emits a `Sorry`.
- **The `openGoals` KU-filter is backed.** Goals dropped as "always
  constructible" (`Goals.hs:70-84`) are genuinely decomposed into sub-goals by
  `insertAction` (`Reduction.hs:293-350`).
- **Equation validation.** Non-terminating equations are rejected at parse time;
  non-subterm-convergent ones produce an explicit warning.
- **Precomputation limits are conservative.** Hitting `-s`/`-c` leaves sources
  under-refined, costing completeness rather than soundness
  (`Sources.hs:355-384`).
- **`--auto-sources` works in practice.** All 16 auto-sources case studies in
  `case-studies-regression/` prove their generated `AUTO_typing` lemma.

### One lead, not reproduced

Diff mode can report `ATTACK` on a constraint system it never closed, via the
`trivial` heuristic at `ProofMethod.hs:373-387` (`guard (solved || (trivial sys'
&& notContradictory))`). The load-bearing assumption, that a goal over distinct
message variables is always satisfiable, is asserted in a comment and has failed
before (`37c7285a` "fixed bug when mirroring XOR leading to false attacks";
`07021243` narrowed the check because it was "otherwise unsound"). It is recorded
here rather than as a PoC because it has not been reproduced, and because it has
barely been tested: the single reflexivity case that completed passed, and the
`diffsym.py` symmetry sweep never completed. Absence of a counterexample here is
absence of evidence. It remains the most promising direction for the one result
this set lacks, a false attack.

## Framing

The evidence supports a narrower thesis than "Tamarin is unreliable", and the
narrower version is the defensible one.

Everything that survived contact is the part people assume is hard: AC
unification, DH and XOR reasoning, the constraint solver's newest monotonicity
inference, proof replay. Both confirmed defects sit in the trust boundary around
that core, in how restrictions are classified and whether wellformedness gating
runs. Neither is an inference drawn wrongly. Both are checks that were skipped,
one of them silently disabled by an unrelated refactor.

Of the two, one makes Tamarin too permissive and returns a wrong verdict, and one
withholds a diagnostic while returning a correct verdict. Neither is a place
where the solver reasoned incorrectly.

Two confirmed defects in the most theoretically developed tool in symbolic
protocol analysis, one of them a fourteen-year-old soundness hole in syntax the
grammar accepts, found in an evening by someone who is not a Tamarin developer
and had no Haskell toolchain installed. Several other hypotheses were tested and
did not survive, which is what the rest of this file records.
