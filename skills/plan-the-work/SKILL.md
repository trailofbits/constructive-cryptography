---
name: plan-the-work
description: First stage of the CC skills (see `skills/README.md`); runs before `instantiate`. Use before starting, dispatching, briefing or resuming any task that changes more than one declaration or module in the constructive-cryptography library or a project built on it (a rewrite, a refactor, a new layer, a model fix, a pass over names, notation, layout or the DSL), and whenever a user request arrives as a single local change inside a larger structure. It fixes the order, dependencies and rework, the missing pieces to build first, whether each step needs the `instantiate` gate, the clarifying questions, and the brief.
---

# Plan the work before doing it

The planning questions are not this skill's alone: `README.md` "Before writing anything"
and rule 12 (the algebraic sketch) apply in every CC skill, at every declaration. This skill
adds what the supervisor needs to brief and dispatch. A brief for a proof carries the
rule-12 chain, or asks for it as the step's first deliverable, to be reviewed before any Lean.

A request names a change. Do not treat it in isolation: look at the structure it sits in, and
decide the order and scope that cause the least rework. Then brief or start the work. The rules
of `README.md` hold throughout; this skill applies rules 2, 7, 8, 9 and 10 at planning time.

## The questions to answer first

Write the answers in the brief or the step record.

1. **What depends on what?** List the layers or modules the change touches and everything above
   them stated against their interfaces, budgets or names (laws, statements, tests). For the
   key-exchange model: Party → Run → Session → wire → Parties → routing → projection →
   challenger → experiment → Secure and its theorems.
2. **What will be redone, and how often?** If the change or a planned later pass alters an
   interface, a name or a statement, every law above it is touched. Count the passes that touch
   the same statements; more than one means the passes must be merged.
3. **Which order has the least rework?** Bottom-up (`README.md` rule 8). Merge the passes (DSL,
   layout, notation, renames) into one pass per layer; never split them into sequential steps
   that each re-prove the downstream laws. Upper proofs are repaired once, at the end.
4. **Is anything missing below?** Generic blocks, DSL features, laws. List them all at planning
   time, each with its first consumer, so none is discovered mid-proof. Build each one just in
   time: in the order of the work, immediately before the first line or definition that uses it,
   with its own test. Never build a whole phase of tooling up front, so that results land early
   and a law no consumer needs is never built. List each one as an upstream candidate.
5. **Is this the whole request?** Compare it with the stated objectives (the plan, the
   acceptance list). If the request fixes one place, look for the same defect elsewhere and say
   so.
6. **What does the source say?** Model choices follow the paper (`README.md` rule 2); a
   deviation is stated once, at its declaration. Proof devices (MBOs, aborts, guesses) are
   proof objects, never steps of the model (rule 7): do not plan an MBO-carrying game. Before
   designing any bad-event hop, read the three forks of `README.md` rule 7 and any fork design
   in the project's plan. Read the source as follows; record each result in the step record.
   - **Outside the model.** A plan item the source does not model (e.g. one key pair shared by
     the DH and the signature scheme, where the source draws independent pairs) goes to Ideas,
     and the steps citing it are amended. A question the source does not treat is off the path
     to its theorem; it goes to the step whose own source treats it. A plan item may also be
     missing (e.g. an assumption the source's theorem uses that no step had planned).
   - **Errata.** Where the source is mathematically wrong, state what the mathematics gives,
     name the deviation at the statement, and record the erratum in the step record and plan.
   - **Self-disagreement or silence.** The formal game or figure the theorems are about wins over
     the prose. Where the source is silent, take the reading its own instance needs (e.g. in a
     BR game, `Run` is deterministic given the coins, because `RevealRand` returns them as the
     whole randomness). Mark it "Reading" in the record; in the module it is one sentence at its
     declaration (`build-by-composition`, "Comments"). Before writing that figure and prose
     disagree, compute both: they may define the same law (a figure's `b′ ← 0; return
     ⟦b′ = b_test⟧` is the prose's "random bit", as `b_test` is uniform); then there is no
     Reading and no conflict is claimed. Before calling something a gap, read what the source
     says the listed items are (e.g. a BR paper's session fields are what "the security game
     maintains", so protocol-private state is the source's, not an addition).
7. **What is already decided?** Read the decisions in the project's plan, the earlier step
   records that touch the same objects, and memory, before proposing. Do not reopen a settled
   design and do not forget one (a settled design for aborts was once forgotten). See "What
   supersedes what" below.
8. **What does a check cost?** A full `lake build --wfail Tests` takes minutes, and only one
   lake process runs at a time (rule 10). Plan focused builds per layer and the full checks once
   at the end.

## What supersedes what

- A user decision (a decision in the plan, an accepted sketch) is settled. Everything else in
  the plan (its summaries, design notes, port lists, consumer lists) is a proposal: check it
  against the source and by probe. A gate may weaken a design note with an argument, reported
  explicitly.
- A step record supersedes the plan's text (the plan goes stale once an earlier step has
  changed its objects).
- A sub-step's brief supersedes the accepted record on the form of a definition. The worker
  follows the brief and lists the difference under "Corrections to the gate record" in the
  result file.
- The owner's naming convention supersedes a name in a brief or a record. The built name goes
  in the rename table, and later briefs cite the built name, not the record's.

## Gate or build

- **Design open.** Each step gets the `instantiate` gate. Split it into a gate step (record and
  probe in the project's step records, no source edit) and build sub-steps (`Na`, `Nb`, …) that
  implement the record's build list in its owners.
- **Design known.** When the user has accepted a concrete design (a decision in the plan with
  its design note, a plan with sketches), dispatch the build directly, with no
  separate gate or probe round (`README.md` rule 9). If a gate is run anyway and its probe
  confirms the definitions, with every alternative found equivalent (`Iff.rfl`), that is neither
  a fourth outcome nor a "new definition" stop: proceed and list the alternatives in the record.
  Stop only when the gate would change the design (e.g. it would redefine `DecidesBy` or
  `NullFallback`, which the accepted fork design fixes).

## Clarifying questions

Ask the user only what the source, the plan, the code and these questions cannot settle: a
genuine choice between valid designs, a taste decision (symbols, names), or a scope question
(is X part of this request). Ask before the work, in one message, with a recommendation. Never
ask what the paper answers.

## In a brief to a worker

- State the order and why, the layers in scope, what is not re-proved until the end, the
  missing pieces to build first, and the stop-and-report rule for blockers.
- Tell the worker that rule-12 problems are asked at once, by message to the supervisor, not
  recorded and carried past (`README.md`, "Noticing is stopping"). "Stop only on a genuine
  blocker" never covers them. Answer such a message before the worker builds on it.
- Keep the model and the proof in separate steps. A brief that writes a model cites no proof law
  and no hop, and it ends with a review of the model against the source. Proof steps start
  only after that review. Putting a model and its first hop in one brief invites shaping the
  model to fit the proof.
- Interrupt at once. When a result or a review shows a rule only partly followed, message
  the running worker immediately with the change. Do not wait for its round to end, and do
  not queue the fix for a later round.
- Review the sketch's missing-law table by consumer: for each hypothesis, how does the
  consuming line discharge it? Any hypothesis about a whole inside system is sent back.
- For a known design: fewer, larger build workers; a short brief that points at the accepted
  plan; a short result file (changes, rename table, checks, blockers).
- Give the source's path. Pass on the owner's names, not names from a record that break its
  convention.
- Never restate a skill rule in weaker form (e.g. "remove an import only if the lint or build
  says so" contradicts `build-by-composition`). Point at the skill instead.
- When the skills changed in this session, tell the worker to read `skills/*/SKILL.md`
  from disk (`README.md`).
