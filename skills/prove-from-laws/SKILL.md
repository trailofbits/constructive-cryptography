---
name: prove-from-laws
description: Last stage of the CC skills (`skills/README.md`); fires after `plan-the-work` and `instantiate` (or an accepted design), at the moment a proof is written, and for the step's builds and checks. Use before writing or repairing any Lean proof in the constructive-cryptography library or a project built on it, whenever a proof grows long, times out or needs unfolding, and before running builds, lints or axiom checks. A proof applies theorems as stated and chains the owning layers' structural laws. A proof that unfolds a composite, recomputes an automaton or re-derives a bound usually means a law is missing upstream, and that law is built first. Opening a composite is allowed only with a recorded argument that it is the only way.
---

# Prove from laws

A proof is a theorem applied to instance equalities, or a short chain of the owning layers'
structural laws. It never re-derives what an existing theorem contains. This skill applies
`README.md` rules 3, 7 and 10, `instantiate` fields 2 and 4 and its acceptance test, and
`AGENTS.md` "Proof workflow" to proofs.

## Before proving

0. **Answer `README.md` "Before writing anything", then write the sketch (rule 12).** The proof
   is the chain of system equations from the step record, one `calc` step per line, each closed
   by the laws its line names. If the record has no sketch, write it first and get it
   reviewed. If a line needs a `rw`/`simp`/`unfold` grind, stop: a law is missing or the
   factoring is wrong.

1. **Name the route** (`AGENTS.md` "Proof workflow" 2). It is one of:
   - T applied;
   - structural rewriting: attachment, parallel, routing, projection and sampling laws; `map_map`,
     `jointLaw_map`, `keyed_map`;
   - substitution (`cc_calc`, `cc_substitute`) or the `cc_*` commands;
   - a fork of an MBO game (`README.md` rule 7): until-bad (F1) or conditional equivalence
     (F2), the MBO introduced inside the proof;
   - an invariant of a primitive automaton, through
     `RandomSystem.exists_invariant_of_ofProbAutomaton_ne_zero`, which is
     `ProbStep.mem_support_belief_of_invariant` read on positive transcripts;
   - a representation or extensionality law in its owner, by induction on transcripts (as
     `TypedSystem.eq_ofFunction`). A law about systems may be proved through a presentation
     (`exists_ofProbAutomaton`, then the presentation law): the automaton stays inside the proof
     and the statement stays about systems. This is for base laws whose statement is already
     component-level and whose proof is short. A presentation proof over about 40 lines, or one
     needed because the hypotheses are about a whole inside system, is a rule-12 stop
     (`README.md`, "Noticing is stopping"): ask before building it;
   - a reduction;
   - a refutation: a counterexample on a primitive test object, computed through its own laws,
     which declines a proposed notion (a negative field 3). At a gate, before the object is
     built, a prose counterexample is allowed if marked "prose", with the build step's test
     module asked to compute it. At the step that builds a primitive component, runs of its
     generated `body` equations on given inside replies are enough, and the test says that no
     statement about the attached system is made; that statement (reply masses of the attached
     system) is asked at the step whose laws give those masses without unfolding the composite;
   - a counting step: a finite sum over a guess or index space, proved as a helper beside the law
     that uses it, in its own section. Upstream forbids unapproved `private` (`AGENTS.md`), so
     the helper is public and named for its conclusion; one that is only about lists or finite
     sets and has a second user goes to the lowest utility module.
2. **List the structural laws the proof uses**, each with its declaration, in the step's record.
   Routine lemmas (`List`, `dite`, `Finsupp`, `funext`, Mathlib group and `ZMod` algebra) need not
   be listed. A probe-proved law with no planned consumer (none named in the plan or a record, or
   none that fits when probed) is recorded with its trigger, not built. A law the plan schedules
   for a later, probe-confirmed consumer is built at its step. A prerequisite law no step
   schedules is proposed for a step in the record, with its trigger; the supervisor amends the
   plan.
3. **If a law is missing, stop.** It is a law of its owning layer, stated over S, with its own
   `instantiate` record (`instantiate`, "Task shapes"). Build it in the owner's local checkout,
   then come back. If the brief forbids edits to the owner, finish without the law only when the
   repeated glue sits in a test; otherwise stop and report. Either way, list it under "Upstream
   candidates" (`README.md`, "Records and filings").

## Rules

1. **Use theorems as stated.** Do not copy a proof, re-run a hybrid or re-prove a bound for an
   instance.
2. **Do not open composites by default.** A composite's facts come from its components'
   contracts through the composition laws. Unfolding a definition down to its assembly (`keyed
   …`, `•`, `∥`, `map`) is always allowed. A primitive component (`build-by-composition` rule 4)
   has its generated DSL `body` equations, or its own hand-written `Program` body, as its
   contract: using them is not opening a composite. Going further, into an automaton, a
   `transition`, a `ProbStep` or a hand-computed transition, needs the argument of "Opening a
   composite" below.
3. **Consumer proofs are short.** An instance obligation is `rfl`, an existing lemma or a few
   rewrites; an endpoint is one application. A longer proof means a missing law or a wrong
   statement. An owner's law has no fixed length, but a rewriting sequence it shares with
   another proof is factored into a law.
4. **Tactics.**
   - Prefer `rw` with the named structural law over `simp` on structural goals; give interfaces
     explicitly (`(A := …)`); prefer term-mode `.trans` chains, as upstream does:
     `(ProbDist.map_map _ _ G).trans hgen`.
   - Under binders `rw` fails: use a `congrArg`/`funext` chain ending in the law, or the owner's
     congruence law (`TypedSystem.keyed_map`, …), never a `simp` rule restating the law.
   - `rw` with a law about `d.1 R` fails ("motive is not type correct") when the goal coerces a
     `TypedSystem` into the distinguisher's subtype: state `have e : ∀ S, d.1 S = …` and close
     with `congrArg`. `rw … at h` does not match when a side of `h` is a projection of a pair of
     systems (`(Secure.systems …).1`): state `h` with its type written out first.
   - A definitional step inside `.trans` is fine if it checks fast; if a reader needs help, a
     comment at the use site, not a lemma. When a contract holds by `rfl`, still name it
     (`have hgen : … := rfl`), so the term keeps the convention's shape.
   - `if_pos`/`if_neg` are deprecated in this toolchain: use `ite_eq_left`/`ite_eq_right`.
   - Runs of a DSL body have no stepping law. Start with `rw [body, C.body_<port>_initial]` (or
     `…_resumed`; unfold a test-local `abbrev` of the body first, `rw` does not see through it),
     then `simp only [callProg, returnProg, ↓reduceDIte]`. Drop `returnProg` when a `match`
     blocks it; close with `rfl` only when a `match` or `cond` is left; a `callProg` under a
     `match` on a table lookup needs the lookup as a simp lemma.
5. **Never raise limits or use decision procedures.** No `maxHeartbeats` or `maxRecDepth`; no
   `decide`, `native_decide` or `bv_decide`. A timeout has three fixes: supply a missing
   structural law, make an implicit argument explicit, or stop opening the composite.
6. **Checks** (one process at a time: `README.md` rule 10).
   - Use focused `lake build --wfail <modules>`. A plain `lake build <modules>` that only brings
     a probe's imports up to date, with no source changed, needs no `--wfail`. Editing an index
     file (`Tests.lean`, `Commons.lean`) is checked by building that index, still a focused build.
   - Capture each build's own exit code (`lake build … > log 2>&1; echo exit=$?`; a pipe or
     wrapper can hide it; this form survives the tool moving a long command to the background)
     and read the log tail.
   - The axioms-audit module joins a focused build only when you add a line to it (it rebuilds
     the layer); when the step also edits a low-layer module, leave it to the final `Tests` build
     and lint it after that build.
   - `--wfail` turns linter warnings into failures. Lemmas over a shared `variable` block trip
     `unusedSectionVars`: drop unused binders with `omit … in` before the first build; if `omit`
     is rejected (the statement's notation mentions the section's carriers), state the lemma
     before the `variable` block.
   - Lint each edited source file before the final build (the Mathlib lint finds what `--wfail`
     misses: a `show` that changes the goal must be `change`; long lines), each finding a source
     edit. Run the owner repository's lints as its `AGENTS.md` gives them: upstream runs `lake
     env lean -Dweak.linter.mathlibStandardSet=true` (not in its lakefile); in a consuming
     project whose lakefile sets that option, its `lake build --wfail` enables it. Scratch
     probes need no lint.
   - Final build: `lake build --wfail Tests` once, after the last source edit (docstrings
     included; a later edit makes the exit code stale); lint only the audit module after it.
     It is required when a step edits a module that other upstream modules import, and it covers
     a low layer's upstream importers. An upstream change can break the consuming project: find
     the direct importers of each changed module by `grep` and build them as focused modules;
     when they are nearly the whole package, run the consuming project's build (`lake build
     --wfail <its root library>`) once at the end. If the changed
     module lies under the package only transitively, say so and leave the full build to the
     supervisor unless the brief asks for it.
   - `#print axioms` shows only the standard three. A worker runs it on each declaration it added
     or re-proved and on each named theorem in its probe, as evidence of no `sorry`. The
     supervisor runs `scripts/check-axioms.sh` and its own full builds at the end of each floor.
   - `scripts/check-sources.sh` is cheap and read-only: run it in each repository you edited.
     `git diff --check` does not see untracked files: for each untracked file you edited, run the
     owner's lint and a trailing-whitespace check (perl, counting characters, not bytes).
   - Delete only files you created, never another file in the scratchpad or the repositories,
     even one that looks temporary. Leave nothing on disk but the step's files: final evidence
     goes in the step's `NN-probe.lean` in the project's step records. A temporary scratchpad
     probe (say, importing only upstream to avoid rebuilding the consuming project), paper
     extractions (`pdftotext`) and logs are deleted
     before writing the result.

## Stop signs

| Sign | Move |
| --- | --- |
| A proof in the consuming project (the top floor) longer than about 15 lines | find the missing law. This includes a primitive's contract proved by an automaton invariant: look for a generic state law (a latch) in its owner (`RandomSystems` for `ProbStep` laws); if none can be stated, keep the proof and record why |
| `unfold`, or `simp only [… transition …]`, on a composite | prove the component's contract and compose; if that cannot work, write the argument below first |
| The same rewriting sequence in two proofs | a chain of two or more structural laws (contracts excluded) in two or more proofs is a law in its owner. Name the sub-chain that recurs as a unit about one owner's object (precedent `map_onFinset_comp_val`). Never fold a convention step into it (forgetting a realization's coins by `map_map`): one law plus a contract is the convention. One generic law reached through `congrArg` (say, through a record update) is not a new law; naming it recreates a restatement |
| A proof re-derives a probability bound, a guessing factor or an until-bad cost | apply the generic lemma (the fork laws, `README.md` rule 7) |
| An isDefEq timeout | do not raise limits; make types explicit or find the structural law |

## Opening a composite

Reasoning about a composite's automaton is allowed only when argued to be the only way. Before
writing the proof, add a section "Opening a composite" to the step's record:
1. **Goal.** The statement, and the consumer that needs it.
2. **Laws tried.** Each composition law that could give it, and why each fails: a counterexample,
   or a component property the parts do not have.
3. **No generic law.** The attempt to state the missing law over S in the owning layer, and why
   it fails (it does not hold in general, or needs more than S provides). If it can be stated,
   it is a missing law: build it instead.
4. **Scope.** One named lemma does the opening; everything else uses it, and no other proof opens
   the same composite.

The supervisor reviews the argument before the proof is written.

## Acceptance

The endpoint's proof is T applied to the instance equalities (`instantiate`, "Acceptance test").
