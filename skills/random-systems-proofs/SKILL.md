---
name: random-systems-proofs
description: "Formalize, finish, repair, or review Random Systems advantage and distance proofs in Lean 4, including Random Systems proof leaves used inside RandomSystemsCC. Start from the exact distance between two specified systems, then route composable certificates using exact reshaping, H-technique, strict conditional equivalence, coupling, representative selection, winnability, signed expansion, or counting. Do not use as the sole workflow for CC composition, AC/resource lifting, or full multi-interface indifferentiability assembly. Requires primary-source, signature, build, and axiom checks."
---

# Random Systems proof workflow

> **Reliability rule.** This package is a workflow and navigation aid, not a
> mathematical source. Verify source claims on rendered primary pages and
> library claims against current signatures, focused builds, and axiom
> receipts.

This workflow routes Random Systems obligations. It may be used for an RS leaf
inside `RandomSystemsCC`, but it does not route CC composition, AC/resource
lifting, or full multi-interface indifferentiability assembly.

## Begin with the repository contract

1. Read the applicable `AGENTS.md`.
2. In this repository, read `DESIGN.md` and `STATUS.md` before changing a model
   or proof. Treat their current build and quarantine information as
   repository state, not as a mathematical theorem.
3. Decide whether the request asks for explanation, diagnosis, review, or an
   implementation. Do not edit merely because inspection found a possible fix.
4. For a new mathematical result, write a paper-level sketch before committing
   to a Lean endpoint. For a repair whose statement is already fixed, inspect
   the current goal and theorem signature first.

## Start from one distance between two systems

Before choosing a proof technique, write the common comparison spine:

- the two systems `S` and `T` at their observable interfaces, often the real
  and ideal systems;
- the allowed environments or distinguishers and any query filter or horizon;
- the exact distance or advantage expression, including its orientation; and
- the finite theorem to prove, normally a bound on that expression.

Keep this same comparison visible throughout the proof. Every auxiliary
system, representative, monitor, game, joint law, or signed expression must
enter through a named equality or inequality whose hypotheses are checked.

The methods below are alternative and often composable certificates for the
same distance; they are not different security objectives.

| Certificate shape | What it contributes to the common comparison |
| --- | --- |
| Exact equivalence, relabelling, or post-processing | Preserves or contracts the selected distance under a checked theorem |
| Hybrid | Splits the selected distance by a triangle inequality |
| H-technique | Bounds it from transcript equality or a one-sided ratio plus controlled bad mass |
| Strict conditional equivalence | Bounds it through a monitored source whose no-win response law matches the target |
| Honest coupling | Bounds it by disagreement under a nonnegative joint law with the required marginals |
| Equivalent representatives | Re-expresses the same observable systems in a form where another certificate is easier to construct |
| Winnability | Connects the distinguishing problem to success in a specified game under the applicable theorem |
| Signed or virtual expansion | Rewrites the transcript-law difference and bounds its norm after exploiting cancellation |
| Counting | Discharges a concrete event-mass, disagreement, fiber, or finite-sum leaf produced by an earlier certificate |

Techniques may be chained. For example, after proving every bridge and its
hypotheses, a proof may have the form:

```text
Adv(S, T)
  = Adv(S', T')
  <= rawDelta(S', T')
  <= disagreementMass(joint(S', T'))
  <= epsilon.
```

Here representative equivalence justifies the first equality, a checked
operational-to-law bridge justifies the next inequality, the coupling bound
justifies the disagreement inequality, and counting may justify the last.
For specially attaining representatives some intermediate inequalities can
be equalities, but that requires the corresponding attainment theorem. No
certificate inherits the obligations of another merely because both address
the same distance.

## Control declaration growth with a root DAG

For a task that may add more than one declaration, change a model, or explore
competing certificate routes, also use the routed
`$constructive-cryptography-proof-engineering` suite:

1. use its modeling subworkflow when the system carrier, observation,
   equality, domain, interface, action, or ownership boundary is unsettled;
2. use this RS skill to select and compose the mathematical certificates for
   the fixed comparison;
3. use the CC proof-routing subworkflow to turn the selected certificate chain
   and checked endpoint signatures into the obligation DAG consumed by the CC
   construction;
4. use its Lean-implementation subworkflow to discharge only those nodes and
   deduplicate proof plumbing; and
5. use its pruning-and-verification subworkflow before calling the RS result
   releasable.

Treat the selected system comparison and requested finite bound as the formal
root, and the intended observable behavior as the functional contract. An
obligation points to the theorem that consumes it; every task-created
production declaration must have a path to that root.

Do not create a helper family merely because a certificate route might need
it. Apply the selected endpoint, inspect its actual goals, and add only those
obligations. If the certificate or model changes, redraw the affected branch
and remove task-created declarations that no longer reach the comparison.
Preserve unrelated and pre-existing work.

The generic suite governs lifecycle, not RS mathematics. Keep H-technique,
strict conditional equivalence, coupling, representative selection,
winnability, signed expansion, and counting in this skill and its
route-specific references.

## Evidence discipline

Keep three kinds of statement separate:

- **Mathematical claim:** verify it in a primary paper or prove it directly.
- **Lean-surface claim:** verify the current declaration, hypotheses, imports,
  build state, and axioms.
- **Workflow recommendation:** label it as advice; do not present it as a
  theorem or a completeness guarantee.

The following are distinct certificate objects and relations for a common
system comparison. Keep their names, types, and hypotheses separate; compose
them only through an explicit bridge theorem:

- strict one-sided conditional equivalence;
- symmetric monitored games;
- H-technique bad predicates;
- honest probability couplings;
- equivalence-class representatives;
- winnability; and
- signed or virtual law expansions.

When a paper is cited, use extraction only to locate a passage and verify the
rendered page before relying on it. When a Lean theorem is cited, inspect its
current signature; a declaration name or docstring does not establish the
prose interpretation placed on it.

## Choose and compose a route

Use the certificate table above as a routing heuristic, not as an exhaustive
taxonomy. A proof may compose several rows, but every row must remain a step
in the displayed comparison that starts from the selected system distance.

Before selecting an endpoint:

1. Complete the generic modeling subworkflow first if changing the model would
   alter what either compared system means.
2. Copy the common comparison spine into the paper sketch, including the
   systems, observation model, metric orientation, and parameter restrictions.
3. Display the proposed chain from that distance to the numerical bound and
   label the certificate used at every hop.
4. State the mathematical argument in enough detail to identify each
   certificate's principal hypotheses.
5. Inspect the exact endpoint signatures.
6. Record every equivalence, model, normalization, totality, metric, or
   conversion bridge that the endpoints do not supply.
7. Check whether the target module already exposes the required interfaces.
8. Seed the generic obligation DAG from the checked signatures and actual Lean
   goals; do not infer a theorem family from the certificate category.

Read only the references relevant to the chosen route:

- [sketch-and-plan.md](references/sketch-and-plan.md) for the paper sketch,
  obligation ledger, and reuse search.
- [h-technique.md](references/h-technique.md) for current H endpoints and their
  scopes.
- [conditional-equivalence.md](references/conditional-equivalence.md) for
  strict CR18 conditional equivalence and blind-game wrappers.
- [reshape-and-exact.md](references/reshape-and-exact.md) for data processing,
  coupling, representative attainment, winnability, and metric bridges.
- [counting.md](references/counting.md) for event-mass and finite-union
  obligations.
- [creative-search.md](references/creative-search.md) when the mathematical
  route or target bound is genuinely unknown.

## Build an obligation ledger

Start from the exact hypotheses of the selected theorem. Add construction
lemmas and conversion steps that the signature does not expose. Record four
independent fields for each node:

- **origin:** `REUSE` for a checked matching declaration, `ADAPT` for a
  justified generalization or wrapper around existing work, or `NEW` for a
  new argument; and
- **needed by:** the direct consumer on the path to the selected comparison;
- **fate:** `INLINE`, `SCRATCH`, or `PRODUCTION`; and
- **status:** `OPEN` or `CLOSED`.

A `PRODUCTION` node without a consumer path to the requested comparison is not
an obligation. Inline it, keep it in scratch, or remove it.

Record a possible tactic under a separate `automation candidate` field.
Automation is a way to attempt a node, not its mathematical origin or proof
status. If most origins are `NEW`, recheck the route and reuse search, but do
not infer that the route is wrong.

For each `REUSE` node, record the declaration name and its material hypotheses.
For each `ADAPT` or `NEW` node, record the searches performed and the exact
bridge or helper required.

Search in this order when it is useful:

1. `CHEATSHEET.md` and route-specific status notes;
2. `rg` over `RandomSystems/` and `RandomSystemsCC/`;
3. Lean-LSP declaration, local, and goal-state search;
4. Mathlib search for construction-independent mathematics; and
5. the primary paper for the intended statement and scope.

Inspect a plausible hit before using it. Continue searching when its strength,
route, build status, or hypotheses do not match the obligation. Generalize an
existing theorem only when ownership, dependencies, and API stability make
that appropriate; otherwise use a justified wrapper or local bridge.

## Work in Lean from the goal state

Follow the repository development loop:

- Prefer Lean-LSP goal inspection.
- If it is unavailable, run `lake env lean <single-file>` so existing oleans
  are reused.
- Use a small scratch file to probe a doubtful signature or elaboration issue.
- Do not iterate with a full `lake build`; reserve repository gates for stale
  oleans and final verification as directed by `AGENTS.md`.

Apply the selected endpoint early enough to expose its actual obligations. Use
named intermediate statements for the mathematical leaves. Temporary holes may
be useful in a scratch or work-in-progress skeleton, but the delivered theorem
must pass the repository's admission and axiom checks.

### Automation is a finite registered surface

Tactics such as `cr18_total`, `cr18_prob`, `cr18_routine`,
`htechnique_total`, `htechnique_compress`, and `htechnique_adv_le` attempt
registered goal shapes. They are not completeness procedures.

If a tactic fails, inspect:

1. whether its module is imported;
2. whether the target constructor or theorem shape is registered;
3. the exact remaining goal and inferred instances; and
4. only then whether the model or statement is wrong.

Do not replace a named proof merely because automation missed it. Conversely,
do not hide genuine partiality or normalization failure behind an ad hoc proof.

`htechnique_compress` is currently a narrow rewrite tactic for registered SoP
transcript-law shapes. `compressedQuery_bound` is a numerical side-condition
lemma. Neither is a generic theorem that repeated queries may be removed from
an arbitrary stateful system. Use an exact, model-specific compression theorem
before changing a query schedule.

## Preserve the mathematical proof shape

Prefer a top-level `calc` whose displayed quantities match the paper argument.
State substantial ingredients as named `have`s before the chain. Give bad
events, couplings, simulators, and intermediate systems stable names. Keep
normalization and totality plumbing out of the middle of the mathematical
hops when possible.

This is a readability policy, not part of Lean's soundness. A proof can compile
without making its argument reviewable.

## Modeling checks that prevent silent slack

- `transcriptDist` is defined as a pushforward of the source law. Apply data
  processing only with the hypotheses of the current theorem.
- A deterministic post-hoc observation refinement of the same execution law
  can often be handled by a forgetful projection and data processing. Extra
  information revealed during interaction may change later queries and can
  require a different interactive model.
- The repository's `Adv S T` orientation corresponds to raw `Delta(T,S)` under
  the hypotheses of `adv_eq_maxAdvantage_swap`. At unequal weight, do not use
  probability-law symmetry implicitly.
- The unrestricted-carrier strict metric comparison requires normalized laws.
  Equality with `ofReal maxAdvantage` additionally requires the shared-domain
  hypotheses of
  `maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain` (or an applicable scoped
  corollary).
- Distinguish raw maximal coupling of two normalized laws from a theorem that
  selects equivalent system representatives. The former does not by itself
  prove representative-level or interactive optimality.
- Treat files containing admissions, failed focused builds, or quarantined
  migration code as incomplete surfaces. Do not cite downstream headlines as
  completed without an axiom receipt.

## Finish with receipts

Before reporting completion:

1. Compile the changed file with Lean-LSP or `lake env lean <file>`.
2. Run the focused gates required by `AGENTS.md` for the affected surface.
3. Inspect `#print axioms` for the delivered theorem and any headline
   corollary.
4. Check that no new `sorry`, `admit`, or unintended axiom dependency remains.
5. Record the exact theorem proved, its restrictions, reused declarations, new
   lemmas, and any intentionally open obligation.
6. Do not call a source file or route complete merely because its final theorem
   text is `sorry`-free; transitive `sorryAx` still matters.

If a result is only a paper proof, a partial formalization, or a conjectured
improvement, say exactly that.
