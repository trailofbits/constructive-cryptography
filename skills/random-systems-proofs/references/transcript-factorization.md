# Transcript factorization

Use this route to separate a deterministic environment's contribution from a
PDS system's contribution to an observed transcript law. It is an exact bridge
used by H-coefficient and direct transcript calculations, not a numerical
bound by itself.

## Live factorization

`RandomSystems.TranscriptFactor` defines:

- `System.transcriptEnvironmentEvent` for the environment equations and final
  stopping condition;
- `PDS.transcriptSystemFactor` for the PDS mass of systems consistent with a
  transcript; and
- `PDS.transcriptEnvironmentFactorPartial`, a zero-one environment factor.

The central equalities are:

```lean
PDS.trLaw_some_factorization
PDS.trLaw_none_eq_zero
```

For a compatible environment, a concrete transcript has law

```text
environmentFactor(environment, transcript)
  * transcriptSystemFactor(system, transcript).
```

For a stopping environment, the `none` observation has mass zero.

## Function-system specialization

`RandomSystems.TranscriptFactor.Filter` provides:

- `transcriptSystemFactor_fTransform_filterDom_functionEvaluator`; and
- `transcriptSystemFactor_fTransform_filterDom_functionEvaluator_eq_if`.

Use these to reduce a filtered random-function transcript factor to an event
over the sampled function. The second theorem uses prefix closure to collapse
round-by-round admission to the complete query-history predicate.

## Workflow

1. Fix the exact environment and prove compatibility and stopping.
2. Rewrite concrete `some transcript` observations with
   `trLaw_some_factorization` and `none` with `trLaw_none_eq_zero`.
3. Cancel or bound only the common environment factor; do not erase it by
   informal reasoning.
4. Rewrite the system factor with a construction-specific theorem.
5. Hand the resulting ratio, equality, event mass, or count to the selected
   endpoint.

Do not infer that a factorization for a function evaluator applies to a
general stateful DDS. Do not replace compatibility or stopping with a stale
totality assumption from the old API.
