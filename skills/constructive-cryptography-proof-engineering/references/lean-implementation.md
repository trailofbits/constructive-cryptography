# Constructive Cryptography Lean implementation subworkflow

Use this subworkflow when the formal root, proof route, and initial DAG are
stable. Implement one obligation at a time while preventing mathematical
structure from being confused with elaboration convenience.

## Start from the consumer

Apply the outer endpoint or state the root skeleton early enough to expose the
real goal state. Work backward through its obligations, then implement stable
leaves. Do not create a helper until its consumer exists in the source or the
DAG with an exact expected type.

After every material elaboration change, update the node statement and edges.
The Lean goal wins over a stale planning paraphrase.

## Search before declaring

For each open node:

1. search by mathematical concept and likely declaration-name atoms;
2. inspect candidate signatures, namespaces, imports, hypotheses, and axioms;
3. test a candidate at the actual firing site; and
4. classify it as `REUSE`, `ADAPT`, or `NEW`.

A familiar name is not a match. A downstream theorem is not reusable upstream
if importing it reverses the dependency graph; consider moving the genuinely
general theorem with only its true prerequisites.

## Choose the smallest proof boundary

Use, in preference order when the mathematics permits:

1. an existing declaration;
2. a direct term, `calc` step, or rewrite;
3. a local `have` or `let` with a meaningful name;
4. a shared proof combinator for repeated elaboration structure; and
5. a production declaration that passes the parent skill's declaration gate.

Do not add speculative generality. Generalize only as far as an actual current
consumer requires. Put a new declaration in the module owning its principal
concept, then migrate only the dependants required to exercise that boundary.

## Deduplicate proof text without inventing APIs

Classify repetition before factoring it:

- **Same mathematical proposition:** share a local fact, or a production
  theorem only when multiple real consumers need a durable boundary.
- **Same tactic over several generated goals:** use `_`, `<;>`, `all_goals`, a
  small tactic combinator, or a structured cases proof.
- **Same definitional reduction:** unfold at the firing site or use
  `simp [definition]`; do not name a family of `rfl` wrappers.
- **Same expression construction:** use a local definition or existing
  constructor; do not restate its projections as theorems without consumers.
- **Visually similar but type-distinct mathematics:** keep the proofs separate
  unless there is a natural common statement. Syntax alone is not an API.

A new `[simp]` theorem needs an intentional stable normal form, termination or
shrinking behavior, and an actual source consumer. Simplifier convenience
during one proof is not sufficient justification.

## Keep proofs readable at the mathematical level

Prefer a top-level proof whose named steps match the selected semantic spine.
Name substantive intermediate objects and mathematical facts. Keep coercion,
normalization, and instance bookkeeping local to the step that needs it.

Use the repository's established CC proof language for deterministic
construction, composition, context, simulator, filtering, and equality
replacement steps. Do not unfold specifications or recreate those rules with
ad hoc theorem families. Once the CC rule exposes a behavioral, metric, or
probability leaf, prove that leaf in the owning RS or probability layer.

Avoid broad automation that chooses semantic objects or proof routes. Use
deterministic automation only after the mathematical choice is explicit and
the remaining goal matches its documented surface.

Do not raise heartbeat or recursion limits to conceal an ordinary modeling,
normalization, or search problem.

## React to failure precisely

- If the required statement is false or the endpoint is misoriented, return to
  proof routing.
- If the goal requires an unjustified equality, completion, finiteness
  assumption, or global instance, return to modeling.
- If elaboration alone fails, reduce to a focused probe, fix the exact
  namespace, coercion, implicit parameter, or instance issue, then apply the fix
  in the target and delete the probe. Never grow the probe into the deliverable.
  A probe carrying a statement from the DAG is not a probe; put that statement
  in the target under `sorry` and elaborate there instead.
- If a block fails to elaborate, fix that block only. Do not regenerate the
  file or rewrite blocks that already elaborate: a rewrite discards checked
  work and pays its elaboration cost again. Target files are advanced one
  `sorry` at a time, and a partially proved target beats a finished scratch.
- If a chosen route is abandoned, stop extending its helpers and mark its
  task-created production nodes for pruning.

Preserve unrelated and pre-existing work. Investigative code worth retaining
belongs in ignored scratch storage, not an imported production module.

## Implementation exit condition

The root and each required dependant elaborate from source, every retained new
declaration has a DAG consumer path, and no temporary admission remains. Then
run the pruning and verification subworkflow; a compiling theorem is not yet a
clean deliverable.
