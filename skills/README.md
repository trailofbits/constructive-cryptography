# CC skills

The five skills that govern constructive-cryptography and random-systems work in this library and
in projects built on it. When a skill was edited during a session, read `*/SKILL.md` from disk
again: a cached copy may be stale.

## Using the skills

Each skill is a folder holding one `SKILL.md`: YAML front matter (`name`, `description`, which says
when the skill applies), then Markdown instructions. The format is plain text and tool-neutral.
- An agent runtime that loads skill folders: point it at `skills/`, or copy or symlink the folders
  into the directory it scans.
- Any other model or agent: give it this README and the `SKILL.md` whose description matches the
  task, as instructions.

The rules below are shared; each skill applies them and adds its local details.

## Flow

```text
(every skill: "Before writing anything", rule 12 sketch)
plan-the-work  →  instantiate (gate)  →  build-by-composition (definitions)
                                      →  state-over-structures (statements)
                                      →  prove-from-laws (proofs)
```

| Skill | Fires |
| --- | --- |
| `plan-the-work` | a task that touches more than one declaration or module is given, dispatched, briefed or resumed; a request for one local change inside a larger structure |
| `instantiate` | after the plan, for each step whose design is open, before its first Lean edit and again on resume after a context reset |
| `build-by-composition` | before writing or changing a definition (def, structure, instance, system, converter, game, DSL program) |
| `state-over-structures` | before writing or changing a theorem, lemma, security definition or endpoint |
| `prove-from-laws` | before writing or repairing a proof; when a proof grows long, times out or needs unfolding; for the step's checks |

The last three fire within a step, each at the moment its kind of declaration is written.

## Before writing anything (every skill, every declaration)

Planning is not a separate stage. Every skill opens by answering these questions for the object
it is about to write, and writes the answers in the step record:

1. **Where is it in the whole?** The layers it touches, and everything above them that is stated
   against their interfaces, names or budgets.
2. **What changes, at which layer?** One component. Its interface stays the same, and the
   context is not touched (rule 12).
3. **What is the sketch?** For a definition: the composition, written in operators. For a
   statement: the line of the proof chain it is. For a proof: the chain (rule 12).
4. **What is missing below?** Laws and blocks that the sketch cites but that do not exist. List
   them all now, each with its first consumer. Build each one just before that consumer, never
   as an up-front phase, and never discover one mid-proof.
5. **Which order causes the least rework?** Bottom-up; passes merged (rule 8).
6. **What does the source say, and what is already decided?** The paper (rule 2), the decisions
   in the project's plan, the step records and memory. Do not reopen a settled design, and do
   not forget one.

If an answer contradicts the plan or an accepted design, stop and report. Do not build around
it. `plan-the-work` adds what only a supervisor needs: briefs, what supersedes what, and gate or
build.

## Rules for every CC skill

Each rule is stated here once; the skills apply it and give only its local details.

1. **ECC rule** (modelled on Mathlib's elliptic curves: `AddCommGroup` is a class of
   assumptions, `W.Point` a concrete object, an instance connects them). Classes are assumptions; concrete objects live at the
   systems level; instances connect them, each field a systems-level object and each axiom a
   systems-level theorem; no intermediate duplicates. Inside the systems level, automata are
   presentations: laws are about systems (transcripts, conditional distributions, decisions),
   and an automaton is one instance.
2. **Follow the paper.** The source settles assumptions, model and bounds; use them as stated
   and do not put such a question to the user. Deviate only where the source is mathematically
   wrong (theorem and proof disagree, a step fails): state what the mathematics gives and record
   the erratum. A weaker or stronger variant is an Idea. Details: `plan-the-work` question 6.
3. **Compositionality**: parameters in proofs, concrete algorithms as instances. Proofs are over
   scheme structures and assumption hypotheses. A concrete algorithm is a value of its
   structure, with its contract proved about that value, plugged in last, and never reopens a
   proof; security assumptions about it stay hypotheses, since no code discharges them.
   Nothing is built standalone: an object is an assembly of blocks, and a missing block is built
   first, generically, in its owner.
4. **The source's decomposition.** One block per object the source names (party, session,
   oracle, challenger, experiment), joined by the library's operations, so the top-level
   definition reads like the figure. State that is a fold of the transcript is computed from the
   transcript. Details: `build-by-composition` rules 0 and 4.
5. **Paper names and notation.** Public names are the source's terms or the library's; no
   invented role names (`guard`, `evidence`, `raw`, `world`). Statements and definitions read
   like the source to a reader who does not know Lean, through each owner's notation module.
   Comments follow upstream `AGENTS.md` "Documentation policy". Details: `build-by-composition`,
   "Names, notation, comments, layout".
6. **Definitions apart from laws.** A definitions module states the model only (the composed
   object and its parts, in reading order); laws, invariants and correspondence lemmas live in
   the owner's laws module.
7. **MBOs and aborts are proof objects.** There is no abort world. Every abort of the source is
   a fork of an MBO game, with one law by what the decision does after the fork:
   - F0, the free fork (null fallback): an equality;
   - F1, the costly fork (a rare bad event): the fundamental lemma, cost Pr[bad];
   - F2, the guessed fork (constant unset probability 1/n, null fallback): conditional
     equivalence, an exact factor 1/n. Until-bad is not used for guesses (it gives 2(1 − 1/n)).

   The model never carries an MBO: a proof factors the system by equalities so the worlds differ
   in one component, replaces that component by its MBO version, and applies the law.
   A forgery event is bounded by EUF-CMA in its pair form (`SignatureScheme.EUFCMA`: the real
   system against the one whose `verify` rejects signatures on unsigned messages), through a
   distinguisher that runs the reduction stopped at the event and tests `verify`; there is no
   game-form EUF-CMA. Security is stated as `W₀ ≃[ε] W₁`, in two-world units (`|p₀ − p₁|`),
   with a one-line corollary in the paper's units (`state-over-structures` rule 3).
8. **Bottom-up, re-prove once.** Settle each layer in its final form (definition, DSL, names,
   notation, definitions/laws split, its own laws) before moving up; build only that layer as
   you go; repair upper proofs once, at the end. Merge passes that would re-touch the same
   statements. Details: `plan-the-work` question 3.
9. **No gate when the design is known.** An accepted design (a decision in the plan with its
   note, an accepted plan with sketches) is built directly; probe only what is genuinely
   unknown, inside the build, and report a blocker instead of redesigning. Details:
   `plan-the-work`, "Gate or build".
11. **The spec, then the BR adapter.** A key-exchange protocol, or any protocol in the
    Bellare–Rogaway model, is: the specification's own operations (roles, message flows, no
    `Send`) in their own modules;
    a BR adapter built by composition, `Run` dispatching on role and stage to one spec operation
    per branch, and `Session` adding setup, state, coins and reveal ports; the population
    (`Parties`); then the game. The adapter is the only layer that knows `Send`; never write a
    separate `Run` that only claims to match the spec. A law states that a session's run follows
    the spec's message flow.
12. **The algebraic sketch first; the proof follows it.** Before any Lean for a proof that crosses
    a layer (a security proof, a hop, a reduction, a law about a composite), write the proof as a
    chain of system equations in the step record, as on paper:
    ```text
    W_b  = C_b • Sess • wire • (Users ∥ R)                       def.
         = C_b • K • X                                           factor: <named laws>
         ≈[ε] C_b • K • X'                                       replace X: <law / assumption / fork>
    ```
    Each line either **factors** (a rewrite by named structural laws so that one component
    stands alone) or **replaces one component** (by an equality law, an assumption
    `Real ≃[ε] Ideal`, or an MBO fork), lifted by congruence (`C • S = C • S'`,
    `S ≃[ε] S' → C • S ≃[ε] C • S'`). The context stays the same, line after line. A replacement
    keeps the component's interface, so the outer interface never changes. The Lean proof is
    this chain, one `calc` step per line, each closed by citing the laws its line names. No proof is
    a long `rw`/`simp`/`unfold` grind. If a line does not close by citing laws, either a law is
    missing (build it at its layer, then return) or the factoring is wrong (fix the sketch).
    **Plan the bridging ("nop") lines.** Never let one line both restructure and replace. If
    a source step swallows a transition (for example, one game hop that adds the tables
    `Sent`/`S` and changes the session code), split it. First an equality line that only
    adds a convenience converter or component: an inert table, a write-only record, a split of
    a resource, a converter that names a sub-computation as a resource. It is unobservable,
    so it costs nothing. Then a line that replaces one component. An extra cost-free line is
    always cheaper than a replacement that needs lower-level fiddling. If a replacement line
    needs a law about how the component is wired, a bridging line is missing.
    **Stop signs:** a hop that changes an outer interface, or needs a law about the context
    (renamings through the challenger, the filter, the projection), means the factoring is
    wrong. Do not build laws for it. The same holds one level earlier: a law whose hypotheses
    its consuming line can discharge only by pushing them through other components or the
    wiring is stated at the wrong layer. State it over the component it is about (an
    `ofFunction` beside the inside, a program, a table), so the line discharges it by that
    component's own laws. For each missing law, the sketch says how its consuming line
    discharges every hypothesis. The supervisor reviews the sketch, and that column, before
    any Lean.
    **Noticing is stopping.** A worker that notices a rule-12 problem (a statement that needs
    context laws to use, a proof that needs a grind, a line that does not close by its named
    laws) does not record it and carry on. It asks the supervisor at once, by whatever messaging the agent setup provides,
    and continues with independent items while it waits. "Recorded as a candidate"
    is not an answer to a rule-12 problem. Any proof over about 40 lines (presentation or not)
    is asked about before it is built: first look for the existing laws of its owner that
    it would duplicate.
    **Rules are not suggestions.** When a review finds work that only partly follows these
    rules, the supervisor interrupts the running worker at once, and the
    work is changed or deleted in that round. It is never left for a later round. Bad
    habits that are kept spread to every later step.
10. **One lake process at a time.** This counts every `lake build` and `lake env lean` you start;
    language servers (yours or other sessions') do not count and are left alone. Run focused
    builds per layer and the full checks once, at the end. Details: `prove-from-laws` rule 6.

## Review order

Every step, by supervisor and worker, is reviewed in this order before fields, laws or builds:
(1) the top-level definition against the source's figure (rule 4); (2) every public name
(rule 5); (3) comments (rule 5). A comparison between a decomposed and a merged option chooses
the decomposed one; the size of a bound, a budget or extra wiring is not a reason.

## Records and filings

The skills name three kinds of project record by convention; each project fixes where they live.
A suggested layout, in a scratch folder outside the built sources:

```text
<scratch>/PLAN.md                  the project's plan: floors, steps, decisions, Ideas list
<scratch>/UPSTREAM-CANDIDATES.md   the project's list of upstream candidates
<scratch>/steps/NN-<name>.md       the project's step records (with NN-probe.lean, NN-result.md)
```

- **The project's step records** hold each step's record, probes and result files; gate
  bookkeeping (inheritance and assembly tables) never goes in permanent source.
- **The project's plan** holds the floors (one per layer, bottom-up, from probability to the
  consuming project, which is the top floor), the steps and the decisions taken with the user.
  Its **Ideas list** ("Ideas kept for later") holds each set-aside option with future value, as
  a row with its trigger, added in the same edit as the decision. Ideas are never steps.
- **The project's list of upstream candidates**: a missing generic block or law is listed in
  the record's "Upstream candidates" and in this list. No issues, PRs or commits unless the
  user asks.
