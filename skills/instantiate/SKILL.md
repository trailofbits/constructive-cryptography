---
name: instantiate
description: Second stage of the CC skills (`skills/README.md`), after `plan-the-work`. The gate for every step whose design is open, at every layer (probability, random systems and converters, the constructive-cryptography classes, schemes, security definitions and the DSL, the consuming project, and any layer a project adds). Run it when such a task is given, proposed or resumed after a context reset, and before its first Lean edit; a design the user already accepted is built directly (`plan-the-work`, "Gate or build"). It restates the task as an instance of a structure the library already has, names the theorem used as stated, type-checks an assembly probe with components as variables, lists only the missing components, and writes the inheritance table. Nothing is built before the instance statement exists.
---

# Instantiate, never re-prove

A task in this library is never "build X". It is "X is an instance of a structure S the library
already has; the theorem T about S is used as stated; the only new mathematics is showing that X
is an instance". A result in ring theory is not re-proved over the integers. The instance
statement below must exist before the first edit of a Lean file.

The library is a tower of layers (upstream `AGENTS.md`, "Scope and layering"), and the rule
applies at every floor: the probability floor (`Probability`: distributions, kernels,
couplings); the systems floor (`RandomSystems`: random systems, converters, distances, games,
their typed forms on interfaces, the DSL's programs), whose objects realize the probability
laws; the CC floor (`ConstructiveCryptography`: the classes of cryptographic algebras,
specifications, constructions, substitution), whose classes the systems floor instantiates;
the scheme floor (`Commons`: ideal systems, security definitions, schemes), whose schemes
instantiate the DSL's notions and the security definitions; and the consuming project on top
(the top floor), whose objects are values of the floors below. A layer that a project adds (a
model of computation, a resolution structure) is a floor of its own. A task names a floor, and
S usually lives on the floor above. When X is an instance of a structure
on its own floor or lower (e.g. a task whose structure is `ProbDist`, on the probability
floor), write that structure, and also name the floor's own structures that supply the laws
being realized.

## When to run

Running the skill means producing the instance statement (reading this file and writing it
counts); the statement is what is checked, not the tool call. Run it:
- after `plan-the-work`, which runs first for a multi-declaration task and decides whether the
  step needs this gate (**plan first**);
- when a task is given, before reading code for it; when a task is proposed (`TaskCreate`):
  write it in instance form, or do not create it;
- after a context reset: redo the statement from the task description (the summary preserved
  facts, not the discipline), or check the accepted record ("Resuming an accepted record");
- before the first Lean edit, and whenever the plan turns into "define a new kind of object".

## The instance statement

First answer `README.md` "Before writing anything". For a step that proves, the gate's
assembly probe is the rule-12 chain: each line an instance of a named law, with the
components as variables.


Write the six fields, in order, into the task description (`TaskUpdate`) when a task list is
available, otherwise into the step's record, and keep them in the final report.

1. **Structure above.** S with its module and declaration: a class, a predicate, a signature of
   operations and laws. Write its whole signature, not the part the next theorem needs; for a
   large owner, every operation and law the task touches, not every lemma.
2. **Theorem used as stated.** The declaration T over S whose conclusion is the task's goal. If
   none gives the goal, name the layer that should own the missing law and stop: that law is the
   task, stated over S, not over X, and it goes into its owner first.
3. **The object as an instance.** X is a value of S's carrier, a predicate or subtype on S's
   semantic objects, or a morphism into S. A syntax type with an erasure map is never the primary
   object; syntax is a generator set. Check each pair of parallel notions for the same shape. A
   probe may settle field 3 negatively (the type of candidate instances is empty): record that
   result. An argument without a probe is acceptable when the refuting object belongs to a later
   step; flag it as a deviation for the supervisor.
4. **Assembly probe.** The target statement with components as variables and their contracts as
   hypotheses, type-checked, proved through the library's structural laws only. Then the probe
   instantiated with the chosen existing objects: carriers, domains, budgets, sampling scope and
   side conditions must fit, not just names.
   Consumer objects of a later step are instantiated at the presentation they will be built
   from and the owner's constructors (e.g. `TypedGame.ofAutomaton`,
   `TypedDistinguisher.ofLaw`), their obligations
   "deferred to step N" with a route. A probe of an edit imports the edited module's own
   imports, not the whole package, which would hide a missing import. A replacement is probed
   probe-locally first, then checked by `rfl` (or an equality) against the live object.
5. **Missing components only.** Each a component (a presentation, an equality of two existing
   objects, a term, a code, a law of the owning layer), none a re-derivation of a bound, a
   reduction or a law that T already contains. Check the owning layer's own constraints before
   assuming a component exists; one uniform object on one floor may be one object per parameter
   on another. Moving a consumer's definition upstream in generic form (ADAPT) lists the generic
   object here; the statements change only by the generalization.
6. **Inheritance table.** For each operation of S, the line by which X inherits it: `rfl`, an
   existing lemma, or a constructor of a generated class. A missing line is unfinished work. A
   line backed only by a probe, for a law no current consumer needs, is "deferred to step N
   (probe-proved)", not missing. The table goes in the step's record; the module docstring
   states the inherited operations in prose (`README.md`, "Records and filings").

## Outcomes

- **Accepted, rewritten or declined.** If a field cannot be filled, the task is not in instance
  form: rewrite it (field 2 usually names the real task) or report why no instance exists. Do not
  start building to find out. A rewrite goes through the same six fields; when its probe fails to
  instantiate (field 4), name the component that does not fit and decline the rewrite too.
- **A choice between valid instances.** When the fields can be filled for several options and
  the rules do not decide, fill them per option, compare them in a table, and stop for the
  supervisor. When one option is the source's own order of hops, it is the choice unless it is
  mathematically wrong; compare options only for cost (e.g. the source's hop on bad draws, as an
  MBO fork, over a split at `sound()`). Before calling an option "outside the form" of a later
  law, check whether that law is generic in the system it takes.
- A design the plan already accepted is not a fourth outcome (`plan-the-work`, "Gate or build").

## Task shapes

- **Several objects in one step.** Write each field in parts, one per object. A declined object
  still gets field 6: the inheritance of the expression used instead. A convention with no
  declaration gets a `REUSE.md` row (precedent: the coin-realization convention).
- **Delete or rewrite only.** Field 5 is "none"; field 6 lists the replacement terms.
- **The task is a missing law.** S is the owner's presentation or structure; T is the precedent
  it generalizes or composes (`eq_memoryless_of_snoc` for `eq_ofConditional_of_snoc`).
- **A scheme structure** (a new record of algorithms, such as `KeyExchange.Protocol`). No goal
  theorem. Field 1 names the sibling structures whose shape it takes. Field 2 lists the existing
  constructors and laws that later steps apply to objects built from it, each used as stated in
  the probe. Field 3 names the systems-level object built from the record and shows two values
  of it (a toy and the path's instance, by type). On building, the toy becomes the owner's test
  module, written with the owner's constructors, not probe-only helpers. A record of algorithms
  is generator data, not syntax as the primary object, when every later statement is about the
  system built from it and the record has no laws of its own beyond well-formedness.
- **The object built from a scheme structure** (the parties' system from a `Protocol`). No goal
  theorem. Field 1 is the systems-level carrier (a typed system or converter over a stated
  interface); field 2 the stock laws later steps apply (projections, sampling, attachment), each
  applied at the object in the probe; field 3 the assembly expression. Check the port list
  against the source's figure line by line first. When the step also gives the security
  definition over that object, write one six-field statement: the definition's fields are those
  of its systems, with one inheritance table.

## Procedure

1. Read `REUSE.md`, then the owning module's docstring and live signatures: domains, budgets and
   sampling scope, not just names.
2. Search for S and T by concept, not by the task's nouns (`grep -rn "structure \|class "
   src/<layer>`, `grep -rn "theorem <concept>" src`).
3. Write the probe (scratchpad or the project's step records); build only it:
   `export PATH="$HOME/.elan/bin:$PATH"; lake env lean <probe>`.
4. Fill the six fields; only then edit sources: field 5's components, in their owners, ending
   with the acceptance test.

## Resuming an accepted record

Check a record the supervisor accepted field by field against the live code. Record corrections
in the step's result file and leave the accepted record as it is; write a fresh statement only
if a field fails. Where the brief and the record disagree, or a name breaks the owner's
convention, apply `plan-the-work`, "What supersedes what". When the build list moves from a probe
into its owners, probe-local names change to the owners' naming: put a rename table (probe name,
built name, why) in the result file (e.g. a probe's `KI.guess_hop` built as
`KI.abs_sub_eq_card_mul_of_guess`). A probe keeps proving its own copies inside its namespace and
no longer exercises the built declarations; say so.

## Stop signs

Each sign means the primary object or the task is wrong. Make the move instead of continuing.

| Sign | Move |
| --- | --- |
| A new `inductive` or syntax is the primary object | a generator set over the existing semantic objects |
| Closure under an operation needs an agreement, normalization or compiler theorem | put the operation's result into the generated sub-structure; prove nothing |
| A bound or a security statement is proved for one scheme or one system | find T over S and show the instance; the bound is T's |
| A conclusion mentions one instance's internals (a hash, a key, a table, a state) | the conclusion is T applied to the instance equalities |
| A quantity is declared data but read as a theorem | say "declared"; do not prove around it |
| Two presentations of one object must be kept in agreement | one object; the other presentation is one lemma about it |
| The task says "build", "add a measure", "implement" with no S and T | rewrite in instance form before accepting |
| Parallel notions have different shapes, one semantic and one syntactic | make them alike |
| A theorem's statement changed to make the instance fit | generalize at the level where the theorem lives, with the same proof, and say so |
| A law is proved in a consumer's module | move it to the layer that owns its concept, stated over S |

## Acceptance test

The endpoint's proof is T applied to the instance equalities. If it re-runs a hybrid, a bound or
a reduction, the gate was skipped. If a lemma restates a law of S for X, an operation was
redefined instead of inherited. If the inheritance table has a missing line, the step is not
finished, whatever has been proved.

## Examples across the floors

- **A scheme.** S: `MAC` with `MAC.SUFCMA` over any admitted class. T: a game bound as stated. X:
  the scheme as a value of `MAC`. Missing: equalities of typed systems identifying the notion's
  two systems with the bound's. Endpoint: the bound applied to them; nothing is proved again.
- **A reduction.** S: the cryptographic algebra with its distinguisher action. T:
  `substitutesWithin_attach` (a substitution within `ε` survives attaching a converter). X: the
  game factored as `K • Real`, with the assumption `Real ≃[ε] Ideal` as a hypothesis. Missing: the
  factoring equalities. Endpoint: `K • Real ≃[ε] K • Ideal`; the bound is never re-proved.
- **A bad-event hop.** S: MBO games over random systems. T:
  `RandomSystem.GameEquivalent.transcriptDistance_visible_le` (equivalent games are within the
  probability of provoking the MBO). X: the two worlds as games whose visible systems are the
  hop's systems, differing in one component. Missing: the game equivalence and the per-step
  cost. Endpoint: the bound applied.
- **Declined.** "A per-activation work measure on programs." No S: program bodies are Lean
  functions, no layer owns their cost, and closure would need a compiler theorem; such a work is
  declared data. The rewrite as term erasures failed field 4 on two side conditions (recorded as
  limits of the instance) and was declined too.
