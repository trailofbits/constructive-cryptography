# H-technique endpoints

Use this reference when the comparison is naturally stated as equality or a
one-sided likelihood bound outside a predicate on transcript prefixes.

Fix the two systems, observation model, query horizon, and distance orientation
before defining `Bad`. The H argument is a certificate for that selected
distance, not a new security objective. It may follow an exact representative
or model bridge and may hand its remaining probability leaf to counting.

## Contents

- [Core endpoint shapes](#core-endpoint-shapes)
- [Choosing an analysis](#choosing-an-analysis)
- [Adaptivity and the bad-mass premise](#adaptivity-and-the-bad-mass-premise)
- [Compression is model-specific](#compression-is-model-specific)
- [Automation](#automation)
- [Proof plan](#proof-plan)

## Core endpoint shapes

The ordinary fixed-query endpoints in
`RandomSystems/HTechnique/Derivation.lean` compare the fixed-query transcript
laws and lift the result to adaptive transcript advantage. Inspect the exact
current declaration before applying one.

The equality-on-good endpoint has the shape:

```lean
theorem adv_le_of_fixedQuery_eq_on_good
    (S T : ProbPDS X Y)
    (Bad : TranscriptPrefix X Y q → Prop)
    (δb : NNReal)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (h_eq : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      ¬ Bad t → (tr(S, xs)) t = (tr(T, xs)) t)
    (h_bad : ∀ E : QQueryEnvironment X Y q,
      Pr[Bad ∣ tr[q](T, E.1)] ≤ δb) :
    Adv[q](S, T) ≤ (δb : ℝ)
```

The ratio-on-good endpoint replaces equality by:

```lean
(1 - eps) * (tr(T, xs)) t ≤ (tr(S, xs)) t
```

for every good transcript and concludes a bound by `δb + eps`. This
orientation is specific to the repository's one-sided H statement: ideal mass
is on the left and real mass on the right.

The derivation file also contains expectation and partition forms and selected
extended-transcript and filtered variants. These are related analyses, not a
complete Cartesian-product API. Do not infer that every transcript model,
analysis, and filter combination exists from the naming convention.

## Choosing an analysis

The following is a workflow recommendation, not a theorem hierarchy:

| Available pointwise fact | Candidate endpoint |
| --- | --- |
| Exact equality outside `Bad` | equality-on-good |
| Uniform multiplicative loss outside `Bad` | ratio-on-good |
| Transcript-dependent loss with an average bound | expectation |
| A finite cell decomposition with cellwise control | partition |
| The proof requires hidden auxiliary transcript data | an applicable extended endpoint |

Prefer the narrowest endpoint whose exact hypotheses match the argument. If no
current declaration has the required combination, either prove a justified
bridge from an existing theorem or add a general endpoint at the correct
layer. Do not claim an endpoint exists because a naming table suggests it.

The sibling `ccprover` project contains selector and labelled-spine tooling.
Those commands are not declarations in this repository and must not be used
unless the sibling project is actually in scope.

## Adaptivity and the bad-mass premise

The displayed H endpoints quantify the bad-probability hypothesis over every
`QQueryEnvironment`. They do not hand the caller a single fixed blind schedule.
A counting lemma for one externally chosen schedule is insufficient unless a
separate theorem transfers it uniformly to the required environments.

Keep these obligations distinct:

1. a pointwise equality or ratio for every fixed query vector;
2. totality hypotheses used by the transcript factorization/lift; and
3. a uniform ideal bad-mass bound for every adaptive query environment.

This differs from the packaged conditional-equivalence leaf, which is stated
over each blind winner's fixed `blindQueryList`. Do not move fixed-schedule
language from that theorem into an H proof.

## Compression is model-specific

Repeated queries may affect a general stateful system. Replace a query vector
by a distinct-entry vector only after proving or citing an exact compression
theorem for the chosen transcript laws.

In the current tree:

- `transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress` is an exact
  compression result for its function-evaluator scope;
- `compressedQuery_bound` transports a numerical cubic side condition after
  compression; and
- `htechnique_compress` is a narrow rewrite tactic over registered SoP
  transcript-law lemmas.

None of these is a generic stateful-query compression theorem.

## Automation

The H tactics are finite collections of rewrites and registered constructors.
They attempt common goals; they do not decide totality, normalization,
compression, or security reductions in general.

- `htechnique_total` tries registered totality rules.
- `htechnique_compress` rewrites registered SoP compression shapes.
- `htechnique_adv_le` tries registered security-shell reductions.

Before diagnosing a model, check the import and the current goal. A named
totality or probability theorem may exist even when a tactic does not know it.
Rechecked 2026-08-06 in the working tree used by the post-rewrite audit, the
aggregate `RandomSystems.HTechnique.Tactics` build is blocked by an imported
SoP migration file. This status is snapshot-sensitive: consult the current
`STATUS.md` and run a focused check before relying on it. Use focused imports
rather than treating an aggregate build failure as a mathematical failure.

## Proof plan

Write the plan from the selected signature. A common equality-on-good proof has
the following principal nodes:

```text
define Bad
├── real and ideal q-step totality
├── fixed-query transcript equality outside Bad
└── uniform ideal bad-mass bound over every query environment
```

The construction can add normalization, projection, filtering, compression,
or representation bridges. Inspect generated goals rather than assuming the
diagram is complete.

With the endpoint's transcript-space and totality premises in scope, a checked
schematic top-level application is:

```lean
open RandomSystems.CR18
open scoped RandomSystems.CR18.HTechniqueDerivation

have h_good : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
    ¬ Bad t → (tr(S, xs)) t = (tr(T, xs)) t := ...
have h_bad : ∀ E : QQueryEnvironment X Y q,
    Pr[Bad ∣ tr[q](T, E.1)] ≤ δb := ...

exact RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_eq_on_good
  S T Bad δb hS hT h_good h_bad
```

For a ratio proof, state the exact one-sided inequality before applying the
endpoint. For an extended endpoint, state both projection hypotheses explicitly
and verify all nonnegativity, weight, and totality assumptions in its current
signature.

Finish with a focused compile and `#print axioms` on the delivered headline.
