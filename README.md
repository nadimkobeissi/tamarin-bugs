# Soundness defects in the Tamarin prover — proof-of-concept suite

Five reproducing defects, two controls that isolate their mechanisms, and five
differential-testing harnesses in [`tools/`](tools/). Every PoC has been run;
the outputs quoted below are actual tool output, not expected output.

The set is deliberately small. Earlier drafts carried more items; anything that
turned out to be subsumed by a stronger PoC, or that could not be reduced to a
reproduction, was dropped rather than padded into the count.

## Environment

| | |
|---|---|
| Binary under test | `tamarin-prover 1.12.0` (Homebrew), Maude 3.5.1 |
| Source verified against | `develop` @ `ef3f0468`, cabal version `1.13.0` |
| Platform | macOS (darwin 25.6.0), arm64 |

The binary is one minor version behind the checked-out tree. Every implicated
code path was compared with `git diff 1.12.0 HEAD` and is unchanged:
`isSafetyFormula`, the `partition isSafetyFormula` in `formulaToSystem`, the
`incompleteMSRs` guard in `factReports`, and the filter in
`gatherReusableLemmas` (which moved file in a refactor but is logically
identical). The defects are present on `develop` HEAD.

## Reproducing

```sh
./run.sh                          # uses tamarin-prover from PATH
./run.sh /path/to/tamarin-prover  # or point at a specific build
```

Exits `0` if every PoC still reproduces, `1` if any behaviour has changed —
so it doubles as a regression check against a patched build.

## Summary

| File | Defect | Class | Severity |
|---|---|---|---|
| [01](01_last_induction_unsound.spthy) | `last()` defeats the safety-formula classifier ⇒ unsound induction | missed attack | **critical** |
| [01b](01b_control_existential_phrasing.spthy) | *control* — same protocol, non-safety restriction phrased with an existential ⇒ correct | — | — |
| [02](02_last_sources_full_chain.spthy) | …chained through `[sources]` ⇒ cleartext key proved secret | missed attack | **critical** |
| [03](03_vacuous_lemma_typo.spthy) | vacuity wellformedness checks are unreachable dead code | missed attack | high |
| [05](05_refuted_sources_lemma.spthy) | refuted `[sources]` lemma still taints precomputation | missed attack | high |
| [08](08_reuse_poisons_both_directions.spthy) | refuted `[reuse]` lemma ⇒ Tamarin **contradicts itself in one run** | missed attack + false "no trace" | high |
| [08b](08b_reuse_control.spthy) | *control* — same theory minus the `[reuse]` token ⇒ all three correct | — | — |

Every confirmed defect makes Tamarin **too permissive** — accepting a proof it
should reject. Not one makes it too strict. That asymmetry is itself a finding;
see [Framing](#framing).

---

## 1. `last()` defeats the safety-formula classifier

`formulaToSystem` (`lib/theory/src/Theory/Constraint/System.hs:849-856`) splits
restrictions into safety and non-safety, with the authors' own reasoning
attached:

```haskell
(safetyRestrictions, otherRestrictions) = partition isSafetyFormula restrictions
-- Non-safety restrictions must be added to the formula, as they render the set
-- of traces non-prefix-closed, which makes the use of induction unsound.
gf2 = gconj $ gf1 : otherRestrictions
```

The classifier it trusts (`Theory/Constraint/System/Guarded.hs:156-164`) tests
for *closed and existential-free*:

```haskell
isSafetyFormula gf0 = null (frees [gf0]) && noExistential gf0
  where
    noExistential (GAto _)            = True     -- accepts Last atoms
    noExistential (GGuarded Ex _ _ _) = False
```

That is not the same as prefix-closed. `last(#i)` is documented user-facing
syntax (`manual/src/011_advanced-features.md:576`) and contains no existential,
so `"All x #i. Start(x) @ i ==> not(last(#i))"` is labelled `// safety formula`
in Tamarin's own output — despite `[Start(x)]` violating it and its extension
`[Start(x), Step(x)]` satisfying it, which is exactly the negation of the
definition in the docstring above.

**PoC 01** — one formula, two verdicts:

```
NoStart_with_induction    (all-traces): verified (3 steps)
NoStart_without_induction (all-traces): falsified - found trace (2 steps)
```

**PoC 01b is the control that makes this airtight.** Same protocol, same
lemma, same non-prefix-closedness — but the restriction is phrased with a
guarded existential (`==> Ex #j. Step(x) @ j`), which lands on the other side
of `partition isSafetyFormula`:

```
NoStart_with_induction    (all-traces): falsified - found trace (6 steps)   correct
```

and the restriction is *not* annotated `// safety formula`. This rules out the
protocol, the lemma, induction in general, and non-prefix-closed restrictions
in general as explanations. The defect is specifically the classification of
`Last` atoms.

**PoC 02** chains it into a whole-theory compromise. `[sources]` implies
`UseInduction` with no annotation from the user (`ClosedTheory.hs:120`), and
`[sources]` lemmas are consumed before any proof runs (`CloseRule.hs:426`) for
*every* lemma in the file:

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

**Also checked:** the `last` restriction *alone* is harmless — with no
induction and no sources lemma, `secrecy` is correctly falsified.

### Provenance

This re-enters soundness bug **#108** (Simon Meier, 2012). `a32cc3f8` added the
original counterexample — still in-tree at
`examples/loops/Axioms_and_Induction.spthy` — and `9726e4c4` ("fixed two
soundness bugs") introduced `isSafetyFormula` as the fix.

Verified precisely:

- The body of `isSafetyFormula` at `9726e4c4` and at HEAD is **byte identical**.
  The predicate has never been modified.
- `last` was *already* surface syntax in that same commit
  (`9726e4c4:src/Theory/Text/Parser.hs:340`).

So the fix and the hole shipped together in August 2012, and the hole has been
open for the entire lifetime of the fix.

### Scope — stated plainly, because it bounds the claim

**No shipped case study is affected.** `tools/lastscan.py` classifies every
occurrence of `last(` across all 1042 `.spthy` files under `examples/`:

```
scanned                      : 1042 .spthy files
files containing 'last('     : 36
occurrences in RESTRICTIONS  : 0   <-- the only ones that can trigger the bug
```

All 36 hits are inside Tamarin's own machine-generated proof text saved into
analyzed outputs (`solve( (last(#i)) | (Ex #j. Update(k,r) @ #j & ...) )`),
never in a user-written restriction.

The correct claim is therefore: **a live, reachable unsoundness in documented
syntax that currently affects no published Tamarin result.** It is a trap
waiting for a user, not evidence that existing verification results are wrong.
Any paper using this should say so in those words.

### Fix

One line: `noExistential (GAto (Last _)) = False`. `toInductionHypothesis`
already rejects `last` (`Guarded.hs:619`), so reclassifying makes induction
inapplicable to such theories, which is correct.

---

## 2. The vacuity wellformedness checks are dead code

`lib/theory/src/Theory/Tools/Wellformedness.hs:578-583`:

```haskell
-- | Report on facts usage. Skip checks on non-existant actions if `incompleteMSRs` is True.
factReports incompleteMSRs thy =
    concat [ reservedReport, ..., factUsage, factLhsOccurNoRhs ]
    ++ concat [ inexistentActions ++ inexistentActionsRestrictions | incompleteMSRs ]
```

The guard is the inverse of its own docstring, and the sole production call
site hardcodes `False` (`src/Main/TheoryLoader.hs:602`, with a `TODO`).
`inexistentActions` and `inexistentActionsRestrictions`
(`Wellformedness.hs:706-734`) are fully implemented, with error messages, and
never execute.

**PoC 03** — a lemma referring to `SecrettKey` where the rules emit
`SecretKey`:

```
secrecy_typo     (all-traces): verified (2 steps)
secrecy_intended (all-traces): falsified - found trace (3 steps)
/* All wellformedness checks were successful. */
```

`--quit-on-warning` does not help: no warning is generated at all.

### Provenance

```sh
git log -L 583,583:lib/theory/src/Theory/Tools/Wellformedness.hs
# 98c3887f Extend ProVerif export module (#725)
```

Before PR #725 both checks were unconditional members of `factReports`. An
unrelated export-backend refactor silently disabled a working guardrail against
the most common modelling error in Tamarin. Unlike defect 1, this one is not
hypothetical for real users: a typo'd action fact is an everyday mistake, and
the check that existed to catch it is gone.

---

## 3. Unproven assumptions are admitted as facts

`gatherReusableLemmas` (`lib/theory/src/CloseRule.hs:181-188`) admits a
`[reuse]` lemma on the basis of its attribute, trace quantifier, source kind
and hide-list. It never checks whether the lemma was *proved*. The admitted
formulas go into `sLemmas` via `insertLemmas` (`CloseRule.hs:179`), and
`sLemmas` constrains the constraint system for **both** trace quantifiers.
`[sources]` lemmas take a hotter path still — consumed during theory closing,
before any proof runs, with no failure path.

**PoC 08 is the sharpest result in the set, because it needs no ground truth
at all.** In one run, on one theory, Tamarin prints both:

```
helper (all-traces):   falsified - found trace (3 steps)
live   (exists-trace): falsified - no trace found (2 steps)
```

where

```
helper = All k #i #j. Secret(k)@i & KU(k)@j ==> F
live   = Ex  k #i #j. Secret(k)@i & KU(k)@j
```

"falsified" on `helper` means *there is* such a trace. "falsified" on `live`
means *there is no* such trace. Same statement, both answers, same summary
block. No modelling judgement and no reading of the protocol is required to see
that one is wrong. (`target` is also reported `verified` and is false.)

**PoC 08b** is the control: the same theory with the single token `[reuse]`
deleted produces all three correct verdicts. **PoC 05** shows the same
mechanism via `[sources]`.

Methodological note on *why* this is visible at all. `helper` and `live` are
exact negations, so the pair is precisely the contradiction condition the
consistency oracle in [`tools/consistency_oracle.py`](tools/consistency_oracle.py)
tests for (`falsified`/`falsified`). The reason the pair disagrees with reality
in only one direction is that `gatherReusableLemmas` draws from `previousItems`
— strictly-earlier lemmas — so **`helper` never reuses itself** and gets the
correct verdict, while every later lemma is evaluated under the refuted
assumption. Verified directly:

```
lemma helper [reuse]: "All k #i #j. Secret(k)@i & KU(k)@j ==> F"
lemma live: exists-trace "Ex k #i #j. Secret(k)@i & KU(k)@j"   // = not helper
-->
helper (all-traces):   falsified - found trace (3 steps)
live   (exists-trace): falsified - no trace found (2 steps)
```

Note the contrast with the `target`/`live` pair, which comes back
`verified`/`falsified` — mutually consistent, and therefore invisible to the
oracle. Detecting this class requires pairing against the reuse lemma itself,
not against another downstream lemma.

### On invalidation — the accurate version

Tamarin has a proof status for exactly this hazard, `InvalidatedProof`,
documented at `Theory/Proof.hs:406` as *"The proof has been Invalidated (eg. by
editing a reuse lemma)"*. The constructor is only ever **set** in
`src/Web/Handler.hs:255`, i.e. the interactive web GUI. `CompleteProof` is
likewise consumed only in `src/Web/Theory.hs`, to colour cells green or red.

The honest framing is *not* "a safety net that fails to fire". The manual
documents this invalidation in its **interactive-mode** section
(`manual/src/007_property-specification.md:229-234` — "Whenever you delete or
edit a lemma marked as `reuse`, all proofs after the deleted or edited lemma
will be invalidated"), so batch mode never promised it. The finding is that the
safety net exists only in the GUI, while batch mode — what CI and every
published artifact use — has no equivalent, and no proof-status gate anywhere
on the reuse path.

---

## Method: differential testing without ground truth

The harnesses in [`tools/`](tools/) exist because hand-reasoning does not scale
past the trust boundary. Each exploits an invariant that must hold regardless of
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
`consistency_oracle.py`, `stateful.py` and `lastscan.py` were run to
completion, and the results below are theirs. `differ.py` and `diffsym.py`
were written and launched but **their sweeps did not complete** — running
16 configurations over real case studies, and diff-mode proofs over
observational-equivalence models, exhausted available RAM and the runs were
killed. They are shipped because the invariants they encode are the right
ones and the harnesses are reusable, **not** because they returned a clean
bill of health. Nothing below is claimed on their behalf.

## What held up

Reported because negative results make the positive ones harder to dismiss as
cherry-picking, and because they locate the defects precisely.

- **The core term algebra.** 15 cases across xor (self-cancellation, one-time
  pad, chained pads, `zero`), multiset, Diffie-Hellman, subterm, natural
  numbers, hashing and symmetric encryption — all consistent.
- **Injective facts and stateful reasoning.** The newest and most aggressive
  inference in the solver (`simpInjectiveFactEqMon`, `Simplify.hs:534-660`,
  which *derives* equalities and orderings from inferred monotonic behaviour)
  held on constant positions, strictly-increasing positions, nat counters,
  non-fresh identifiers, and SAPIC locked/unlocked state cells.
- **Stored-proof replay is sound.** Three separate forgeries against
  `case-studies-regression/Tutorial_analyzed.spthy` — weakening a lemma while
  keeping its proof, replacing the proof with a bogus one-step contradiction,
  and relabelling a case — were **all** caught and downgraded to `analysis
  incomplete`. Published `.spthy` proof artifacts do get re-validated.
- **Observational equivalence is reflexive in the one case measured.**
  `diff(t,t)` over symmetric encryption returned `verified (98 steps)`, as it
  must. The Diffie-Hellman and XOR variants were launched but killed before
  completing (RAM), so **those two are unmeasured** — not passes.
- **Predicate expansion is capture-free.** `expandFormula`
  (`Theory/Syntactic/Predicate.hs:94-105`) shifts de Bruijn indices correctly;
  a predicate body binding `y`, used at a call site that also binds `y`, gives
  results identical to the non-colliding control. (Macro expansion, by
  contrast, is *not* hygienic — a macro body variable is captured by a
  same-named rule variable, silently and with a clean wellformedness report.
  Since the genuinely dangerous sub-case, an *unbound* injected variable, **is**
  caught by `unboundReport`, this was recorded as a model-integrity wart rather
  than kept as a PoC.)
- **Oracles cannot cause unsoundness.** `oracleRanking`
  (`ProofMethod.hs:604-621`) returns `ranked ++ remaining`; omitted goals are
  appended, not dropped. Only `quitOnEmpty` terminates, and it emits a `Sorry`.
- **The `openGoals` KU-filter is backed.** Goals dropped as "always
  constructible" (`Goals.hs:70-84`) are genuinely decomposed into sub-goals by
  `insertAction` (`Reduction.hs:293-350`).
- **Equation validation.** Non-terminating equations are rejected at parse
  time; non-subterm-convergent ones produce an explicit warning.
- **Precomputation limits are conservative.** Hitting `-s`/`-c` leaves sources
  under-refined — costing completeness, not soundness (`Sources.hs:355-384`).
- **`--auto-sources` works in practice.** All 16 auto-sources case studies in
  `case-studies-regression/` prove their generated `AUTO_typing` lemma. The
  path is unguarded in the same way as defect 3, so the risk is structural, but
  it is not currently realised anywhere in the corpus.

### One lead, not reproduced

Diff mode can report `ATTACK` on a constraint system it never closed, via the
`trivial` heuristic at `ProofMethod.hs:373-387` (`guard (solved || (trivial
sys' && notContradictory))`). The load-bearing assumption — that a goal over
distinct message variables is always satisfiable — is asserted in a comment and
has failed before (`37c7285a` "fixed bug when mirroring XOR leading to false
attacks"; `07021243` narrowed the check because it was "otherwise unsound").
It is recorded here rather than as a PoC because it has **not** been
reproduced — and, importantly, because it has barely been *tested*. The single
reflexivity case that completed (`diff(t,t)` over symmetric encryption) passed;
the `diffsym.py` symmetry sweep over real diff-mode case studies never
completed. So this lead is open, not cleared: absence of a counterexample here
is absence of evidence, not evidence of absence. It remains the most promising
direction for the one result this set lacks — a false attack.

## Framing

The evidence supports a sharper thesis than "Tamarin is unreliable", and the
sharper version is the more defensible one.

Everything that survived contact is the part people assume is hard: AC
unification, DH and XOR reasoning, the constraint solver's newest monotonicity
inference, proof replay. Every defect found sits in the **trust boundary
around** that core — how restrictions are classified, whether wellformedness
gating runs, whether lemma dependencies are checked. The engine is sound; the
guardrails around it are load-bearing, under-tested, and in one case silently
disabled by an unrelated refactor.

The direction of failure matters too, and should be stated rather than hidden:
all five defects make Tamarin **too permissive**, never too strict. For a
verifier that is the dangerous direction, and it is consistent with the
pattern — these are all places where a *check was skipped*, not where an
*inference was wrong*.

Two candidates for the headline, with different strengths:

- **PoC 08** is the most rigorous: a self-contradiction visible in a single
  summary block, requiring no ground truth, no modelling judgement, and no
  trust in the reader's reading of the protocol.
- **PoC 02** is the most dramatic: a fourteen-year-old regression of a
  documented, previously-fixed soundness bug, reachable from documented syntax,
  producing a completely clean report on a protocol that publishes its own
  secret key — but, per the scope scan above, affecting no published result
  today.

Leading with 08 and using 02 as the deep-dive is the honest ordering.
