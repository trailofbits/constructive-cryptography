# Independent exploration for open proof design

This file gives a project workflow for mathematical exploration. It is advice,
not a theorem about which proof method is complete or optimal.

## Contents

- [When to explore in parallel](#when-to-explore-in-parallel)
- [Freeze the question](#freeze-the-question)
- [Choose non-overlapping briefs](#choose-non-overlapping-briefs)
- [Preserve independence](#preserve-independence)
- [Evaluate proposals](#evaluate-proposals)
- [Move one route into Lean](#move-one-route-into-lean)

## When to explore in parallel

Use independent scouts only when delegation is authorized and the subtasks can
make progress independently. It is most useful when:

- the target bound or correct proof object is not known;
- several genuinely different decompositions could apply;
- a published proof appears loose for a construction-specific reason; or
- a terminology or theorem-interpretation claim needs independent review.

Do not parallelize a single elaboration error or split one proof into dependent
fragments that require constant synchronization.

## Freeze the question

Give every scout the same mathematical statement and evidence set:

- exact systems and observation model;
- exact distance or advantage quantity and orientation;
- query and parameter restrictions;
- desired finite bound, if known;
- published baseline and primary sources;
- allowed techniques and excluded assumptions; and
- required output format.

All scouts must retain this one comparison as their common spine. Exact or
hybrid bounds, transcript factorization, H-coefficient, CE, coupling, games,
observation restriction, and direct-environment routes are competing or
composable certificates for the same fixed distance, not permission to change
the security objective. Require every proposal to display the bridge from the
original distance through its auxiliary objects to the final bound.

Separate established premises from conjectures. If a premise itself is under
review, ask the scout to verify it rather than inherit it.

For an independent audit, identify the source snapshot by hash. Do not let the
source change during review; audit a later rewrite as a separate delta.

## Choose non-overlapping briefs

Possible angles include:

- exact transcript-law computation, data processing, or a named hybrid;
- transcript-system-factor equality or likelihood analysis;
- exact likelihood or fiber counting;
- H ratio or finite-cell analysis;
- strict conditional-equivalence monitor and simulator design;
- honest sequential or maximal coupling;
- game/blind-winning reformulation with an explicit bridge;
- bounded common-domain observation restriction;
- attack/lower-bound construction; and
- small-instance computation used only to test conjectures.

These categories can overlap. State each scout's distinctive question and ask
it to report when the route collapses into another one.

Changing a game condition, target, simulator, cell partition, coupling, hybrid,
or observer creates the proof obligations of that exact object. A ready-made
predicate or construction is a candidate, not evidence that the desired
identity or rate follows.

Treat representative attainment, abstract winnability, and signed virtual
joints as research proposals unless a current production endpoint, focused
build, and axiom receipt are supplied.

## Preserve independence

For a blind first pass:

- give raw sources, declarations, and the claim to review;
- withhold earlier verdicts and intended corrections;
- prevent scouts from reading each other's reports;
- require them to record accidental exposure or shared context; and
- ask for precise negative results, not only promising ideas.

A second pass may compare reports. Resolve disagreements by direct source or
Lean inspection, not by counting votes.

Paper-design scouts should normally return mathematics rather than edit the
formal tree. A small formal probe is appropriate when it resolves a specific
signature, counterexample, or elaboration uncertainty; record it as evidence.

## Evaluate proposals

For each proposal, require:

1. a precise finite statement;
2. definitions of every new object;
3. a complete implication chain from premises to conclusion;
4. the exact place each inequality enters;
5. adaptation to the construction rather than transcription of a source
   proof;
6. comparison with existing bounds in every claimed regime;
7. a matching attack or an explicit statement that none is known; and
8. the remaining unproved lemma, if any.

Consensus is evidence only of shared conclusions under the supplied premises.
It can also reflect a shared blind spot, false premise, insufficient effort, or
poor task decomposition.

Choose a route by mathematical validity first. Then compare theorem strength,
scope, explanatory simplicity, and formalization cost. Preserve the strongest
runner-up when it offers a different regime or a useful fallback.

## Move one route into Lean

Before implementation:

1. merge the winning paper argument into one coherent sketch;
2. list every theorem-sized obligation;
3. mark source facts, existing Lean facts, and new lemmas separately;
4. state unresolved claims as conjectures rather than silently assuming them;
5. apply the intended endpoint in a focused skeleton; and
6. compare generated Lean goals with the obligation list.

The formalization validates the selected argument; it does not retroactively
turn an incomplete paper proposal into a proved bound.
