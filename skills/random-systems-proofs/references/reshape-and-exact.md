# Exactness, reshaping, coupling, winnability, and metric bridges

Use this reference to simplify a comparison before choosing a transcript or
game argument, or when the proof explicitly uses a joint distribution,
representative theorem, or contextual metric.

## Contents

- [One comparison spine](#one-comparison-spine)
- [Check exact statements first](#check-exact-statements-first)
- [Reshape with named inequalities](#reshape-with-named-inequalities)
- [Observation refinement](#observation-refinement)
- [Coupling](#coupling)
- [Representatives and winnability](#representatives-and-winnability)
- [Signed expansions](#signed-expansions)
- [Metric and orientation receipts](#metric-and-orientation-receipts)
- [Build-status discipline](#build-status-discipline)

## One comparison spine

Begin with the selected distance or distinguishing advantage between two
specified observable systems. This reference supplies ways to preserve,
re-express, characterize, or bound that same comparison:

- an exact bridge can replace a system by an equivalent presentation;
- a hybrid or deterministic map can relate two distance expressions;
- a representative theorem can expose a more tractable law;
- a coupling can bound the resulting distance by disagreement;
- a winnability theorem can identify it with a game value in its stated
  setting; and
- a signed expansion can expose cancellation in the law difference before a
  valid norm inequality is applied.

Keep the complete equality-and-inequality chain visible. These constructions
are composable certificates for one comparison, while their individual
hypotheses and mathematical types remain distinct.

## Check exact statements first

Before proving a numerical upper bound, check whether the relevant transcript
laws are exactly equal or equivalent after a justified transformation. Useful
possibilities include:

- behavioral/transcript-law equivalence;
- a bijective relabelling theorem;
- equality after a proved restriction or deterministic post-processing; and
- an exact, construction-specific repeated-query compression theorem.

Do not cite `compressedQuery_bound` for exact compression: it is a numerical
side-condition lemma. The exact evaluator-law result is
`transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress`, within its
function-evaluator scope.

Lanzenberger's nonadaptive-sufficiency result concerns exact transcript-law
equivalence under its hypotheses. It does not say that an arbitrary numerical
adaptive advantage can be computed by simply deleting adaptive environments.

## Reshape with named inequalities

Common current declarations include triangle, data-processing/application,
parallel-composition, and query-filter inequalities. Inspect their exact
signatures before use; normalization, nonnegativity, totality, emulation, or
domain hypotheses vary.

A readable hybrid proof exposes the intermediate system:

```lean
calc
  Δ(Real, Ideal)
      ≤ Δ(Real, Hybrid) + Δ(Hybrid, Ideal) := maxAdvantage_triangle _ _ _
  _   ≤ headline := ...
```

Choosing the hybrid is mathematical work. The inequality only justifies the
hop once the objects and orientations are correct.

The library also has additivity lemmas for suitable disjoint-support
decompositions. Use the hypotheses of the current declaration, including any
nonnegativity premise. Do not infer that a premise is logically necessary
merely because the current theorem requires it, and do not remove it without a
generalized proof.

## Observation refinement

`transcriptDist` is a deterministic pushforward of the source distribution.
Consequently, data processing can compare two observations of the same
execution law when the coarser observation is a deterministic function of the
finer one and the theorem's nonnegativity hypotheses hold.

This pattern is appropriate for post-hoc annotations that do not alter the
interaction. It is not a universal replacement for a new interactive system:
information revealed during interaction can change later queries and may
require a wider interface or a simulation theorem.

State the source law, fine observation, forgetful map, and recovery equality.
Then apply the exact data-processing declaration. Do not summarize an
interactive model change as “one DPI application” without these objects.

## Coupling

An unqualified coupling is an honest nonnegative joint distribution with the
required marginals. In the library, inspect `DistCoupling` and
`coupling_bound`. A usual application has three obligations:

1. construct the joint law;
2. prove its two marginals; and
3. bound its disagreement probability.

The current theorem
`RandomSystems.CR18.optimal_probability_coupling_exists` says that two normalized
PDS laws admit a normalized joint law on pairs of DDS values whose disagreement
mass equals the raw statistical distance `δ S.val T.val`.

This is a maximal coupling theorem for two fixed normalized laws. By itself it
does not:

- choose equivalent interactive-system representatives;
- identify the class distance of two random systems;
- construct a causal online coupling; or
- estimate the resulting exact disagreement expression.

A tractable sequential coupling can be looser than a maximal coupling. When a
coupling proof loses sharpness, separate loss in the chosen joint from loss in
the estimate of its disagreement.

## Representatives and winnability

Representative selection is governed by transcript-law equivalence, not by
strict conditional equivalence. Lanzenberger's attainment and coupling
theorems operate in their finite, common-domain setting and make the required
representative hypotheses explicit.

Thesis Theorem 2.37 proves that the supremum winning probability `ν(S^A)`
equals the infimum winnability `ω(S^A)`, and gives an equivalent
representative whose probability of being winnable attains `ω(S^A)`.
Do not restate it as a generic inequality `Delta <= nu(S^A)`, and do not add an
MBO requirement unless the particular game definition has one.

Conditional equivalence, winnability, and representative attainment may be
combined by separately proved bridges, but none is a synonym for another.

Before citing the Lean wrappers in `LanzenbergerChain.lean` or
`GameWinnability.lean`, consult the current `STATUS.md`, run a focused build,
and inspect axioms after the file elaborates. Rechecked 2026-08-06 in the
working tree used by the post-rewrite audit, their aggregate path was blocked
by the signed-distribution migration. This build failure is not evidence of an
admission; check axioms after the path is restored.

## Signed expansions

A signed or virtual joint can be a useful algebraic representation of a
difference of laws. It is not an honest coupling because negative coefficients
are not probabilities. To use such an expansion soundly:

1. prove the signed identity for the actual transcript laws;
2. specify the norm or positive-part inequality that converts it to a valid
   distance bound; and
3. keep any cancellation estimate separate from coupling terminology.

Signed representatives cannot be substituted into a theorem whose premise is
an ordinary distribution or `DistCoupling` without proving a new theorem for
the signed carrier.

## Metric and orientation receipts

The repository's one-sided quantities are orientation-sensitive outside the
probability-law setting. Under the nonnegativity hypotheses of
`adv_eq_maxAdvantage_swap`, the repository relates

```text
Adv S T = Delta(T, S).
```

Inspect the named theorem rather than swapping arguments by intuition.

For the strict contextual metric:

```lean
theorem maxEDist_le_maxAdvantage
    (left right : PFunPDS X Y)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist) :
    maxEDist left right ≤ ENNReal.ofReal Δ(left, right)
```

The equality theorem additionally requires a common fixed domain:

```lean
theorem maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain
    (left right : PFunPDS X Y)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist)
    {D : Set (List X)}
    (leftDom : PFunPDS.HasFixedDomain left D)
    (rightDom : PFunPDS.HasFixedDomain right D) :
    maxEDist left right = ENNReal.ofReal Δ(left, right)
```

Use a narrower `filterDom` corollary only when the systems have exactly that
shape. Do not call the inequality unconditional or the equality a theorem for
arbitrary domains.

## Build-status discipline

Legacy condition-based, composition, amplification, representative, and
winnability files may contain useful source statements while failing a current
focused build or depending on admissions. This status is snapshot-sensitive:
consult the current `STATUS.md`, run `lake env lean <file>`, and obtain a clean
`#print axioms` receipt after the file elaborates.

Rechecked 2026-08-06 in the working tree used by the post-rewrite audit, the
legacy amplification source contained an admission and its focused path was
not clean. Do not present its headline as complete until both checks succeed.
See [counting.md](counting.md) for the separate CBC structure-graph status.
