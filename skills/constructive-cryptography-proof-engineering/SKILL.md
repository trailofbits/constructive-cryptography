---
name: constructive-cryptography-proof-engineering
description: "Engineer nontrivial Constructive Cryptography proofs in Lean when resource/converter modeling, composition or simulation routes, Random Systems proof leaves, dependent migration, and declaration cleanup interact. Use for CC-style construction theorems and their supporting mathematical APIs. Use `random-systems-proofs` alone for standalone RS comparisons; do not use this for unrelated formal cryptography or trivial local Lean edits."
---

# Constructive Cryptography proof-engineering suite

Develop source-grounded CC construction theorems and their supporting
mathematical APIs with the smallest justified production surface. This package
is a routed suite: load the subworkflow for the current kind of decision
instead of mixing resource/converter modeling, CC composition or simulation,
Random Systems leaves, Lean implementation, and cleanup into one
undifferentiated activity.

This workflow is not mathematical authority. Follow repository instructions,
owning-module documentation, primary sources, current Lean signatures, and
build and axiom evidence. The DAG is temporary control state, not a published
architecture document or progress ledger.

## Keep two contracts explicit

Record these before creating declarations:

- **Functional contract:** the behavior or mathematical result the user needs,
  independent of the current representation.
- **Formal root:** the exact Lean declaration or buildable API endpoint that
  currently realizes that contract.

When the user requested an exact public signature, both contracts are fixed.
Otherwise, a modeling revision may replace the formal root only if it preserves
the functional contract and records the modeling delta. Never let a convenient
proof silently weaken, strengthen, or redirect the requested result.

Each separately requested public endpoint is a root. Do not invent additional
roots to justify helpers.

## Route to the relevant subworkflow

Read only the references needed for the current kind of work:

| Situation | Subworkflow | Required exit artifact |
| --- | --- | --- |
| A CC resource, converter, system, interface, action, equality, quotient, ownership boundary, or construction statement may change | [modeling.md](references/modeling.md) | CC modeling receipt and consumer probe |
| The CC root is known but its composition, simulation, transport, or RS-leaf route is not | [proof-routing.md](references/proof-routing.md) | displayed CC proof spine and seeded DAG |
| The route is stable and Lean declarations or proofs must be written, migrated, or deduplicated | [lean-implementation.md](references/lean-implementation.md) | compiling root-path nodes only |
| The CC root works and the diff must be made releasable | [pruning-and-verification.md](references/pruning-and-verification.md) | closure audit and verification receipts |

The usual order is modeling, proof routing, implementation, then pruning, but
this is a feedback loop rather than a one-way checklist. A
representation-shaped impossible goal returns to modeling. A false or badly
matched endpoint returns to proof routing. Replace an abandoned branch rather
than accumulating it beside the live branch. Preserve the functional contract
across revisions unless the user changes it.

## Establish the formal root

1. Read the repository instructions and the owning module's documentation.
2. State the exact final Lean theorem, definition, API behavior, or buildable
   migration currently selected for the functional contract.
3. Record any allowed signature or modeling latitude explicitly.
4. Put a temporary DAG in the repository's ignored scratch area. If the
   repository has no such convention, keep it in a disposable external file
   or the working commentary, never in production documentation.

Read [references/dag-schema.md](references/dag-schema.md) when the task needs
more than one new declaration, has competing proof routes, or changes a model.

## Maintain the root-path invariant

An edge points from an obligation to the node that consumes it. Every
production node created by the task must have a directed path to an explicit
root.

Seed the DAG with the root only. Add a child only when one of these exposes the
exact obligation:

- the paper-level equality or inequality chain;
- the checked signature of a selected endpoint theorem;
- the current Lean goal after applying that endpoint; or
- a concrete representation, normalization, or ownership bridge required by
  that goal.

Do not add speculative sibling lemmas, convenience theorem families, or APIs
for proof routes that have not generated an obligation. Search for reuse
before classifying a node as new.

For every node record its exact symbolic statement, its consumer, origin
(`REUSE`, `ADAPT`, or `NEW`), evidence, intended fate (`INLINE`, `SCRATCH`, or
`PRODUCTION`), and status. A tactic is an implementation candidate, not a
reason for the node to exist.

## Admit declarations reluctantly

Before adding a named production declaration, verify all of the following:

- its statement is fixed enough to type-check as a DAG node;
- it has a named consumer edge and a path to a requested root;
- the owning module and dependency direction are correct;
- a signature-aware reuse search found no suitable existing declaration;
- it expresses a stable mathematical or API boundary better than a local
  `have`, `let`, direct calculation, or definition unfolding; and
- its generality is demanded by the consumer, not by imagined future use.

A theorem proved by `rfl`, a one-step `simp`, or a definitional unfolding is
not automatically an API. Keep it named only when it is a deliberate stable
rewrite boundary with an actual consumer or an explicitly requested public
surface. Otherwise inline it with `rfl`, `simp [definition]`, `_`, `<;>`, or a
local fact as appropriate.

Factor repeated proof text only when the fact has one meaningful statement
and represents a recurring mathematical obligation. Prefer proof
combinators, `_`, and `<;>` for duplicated elaboration bookkeeping. Do not
turn syntactic repetition into a theorem family.

Follow repository visibility policy. A local proof fact is not permission to
introduce a `private` production declaration where the repository forbids it.

## Iterate without accumulating debris

Apply the outer endpoint early enough to expose its real hypotheses, then work
on one open node at a time. Implement stable leaves before adding broader
interfaces.

When a proof route or model fails:

1. preserve the same functional root unless the user changes it;
2. record the concrete failed assumption or Lean goal;
3. redraw the affected DAG rather than appending a second speculative route;
4. reclassify useful nodes against the new route; and
5. remove task-created production declarations that no longer reach a root.

Preserve pre-existing work and unrelated user changes. Move investigative
material to ignored scratch storage when it may be useful later; do not delete
existing declarations merely because the current root does not consume them.

## Close by pruning the diff

Before completion:

1. Compare every new or materially generalized declaration in the diff with
   the final DAG.
2. Remove task-created nodes without a root path, abandoned-route wrappers,
   unused simp lemmas, named definitional reductions, and imports needed only
   by them.
3. Distinguish kernel dependencies from source-elaboration dependencies. If a
   simp lemma or tactic helper is absent from the kernel closure, delete it
   only after rewriting its firing site and rebuilding the source.
4. Run the focused build, representative downstream build, axiom check, and
   repository-required static scans.
5. Treat new unused-simp, unused-tactic, or dead-import warnings as failed
   cleanup unless they predate the task and are reported explicitly.

The final report names the root deliverable, the retained new declarations and
their consumer paths, any preserved scratch route, and the verification
receipts. Do not report progress by DAG size or percentage.

## Compose with domain skills

This suite owns the CC-level proof spine and declaration lifecycle. Use
`$random-systems-proofs` for a distance, advantage, conditional-equivalence,
coupling, H-technique, or counting leaf once the CC proof has exposed that
exact leaf. Keep the CC construction as the root; an RS certificate is a child
obligation, not a replacement objective.

For a standalone RS theorem with no CC construction, use
`$random-systems-proofs` alone. Do not broaden this suite to computational
cryptography reductions, protocol verification, cryptographic implementation,
or unrelated Lean developments merely because they also contain proofs.
