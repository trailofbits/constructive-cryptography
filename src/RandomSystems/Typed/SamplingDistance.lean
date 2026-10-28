import RandomSystems.Distance.Mixture
import RandomSystems.Typed.Functional

/-!
# Distance between systems sampled with a common law

Let `R k` and `S k` be systems on the same interface, at transcript distance at most
`error` for every `k`. `TypedSystem.transcriptDistance_sample_le` proves that choosing a
component with law `P` in either family preserves this bound. Each experiment retains its
choice throughout the interaction; the two experiments use the same distribution `P`.
The law may be nonuniform, and only its support, not the sample type, must be finite.

```text
             sample P R                           sample P S
       ┌─────────────────────┐              ┌─────────────────────┐
 D ◄──►│ k ← P, once; R k    │        D ◄──►│ k ← P, once; S k    │
       └─────────────────────┘              └─────────────────────┘
```

These are separate experiments with the same fixed distinguisher `D` and sampling law `P`.
Each wire carries queries and replies; each box retains its own component choice.

## Proof

* `RandomSystem.transcriptDistance_le_of_advantage_le` reduces the conclusion to the
  advantage of an arbitrary distinguisher compatible with the shared interface domain.
* `Domain.Distinguisher.probability_mix` in `RandomSystems.Distance.Mixture` expresses both
  decision probabilities as component averages.
* `abs_average_sub_le` in `RandomSystems.Distance.Transcript` preserves a common bound on
  their component gaps: its triangle inequality uses nonnegative weights summing to one.
* `Domain.Distinguisher.advantage_le_transcriptDistance` bounds each component advantage
  by the component distance, which is at most `error` by hypothesis.
-/

open Probability
open scoped NNReal

namespace SystemAlgebra

/-- **A common distance bound survives initial sampling**: if each `R k` is within `error`
of `S k`, their mixtures with the same normalized law `P` are also within `error`.
The component bound is uniform in `k`; nonnegativity and unit total mass of `P` make the
weighted bound equal to `error`. Sampling retains the chosen component for all queries. -/
lemma TypedSystem.transcriptDistance_sample_le {A : Interface} {K : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (h : ∀ k, (R k).1.transcriptDistance (S k).1 ≤ (error : ENNReal)) :
    (TypedSystem.sample P R).1.transcriptDistance (TypedSystem.sample P S).1 ≤
      (error : ENNReal) := by
  -- Distance is the supremum of advantages, so fix any compatible distinguisher D.
  apply RandomSystem.transcriptDistance_le_of_advantage_le
    (TypedSystem.sample P R).2 (TypedSystem.sample P S).2
  intro D
  -- Typed sampling is a mixture; express both decision probabilities as component averages.
  simp only [TypedSystem.sample, Domain.Distinguisher.probability_mix]
  -- Averaging with a normalized law preserves a common bound on the component gaps.
  apply abs_average_sub_le ⟨P, Distribution.IsProbability.isProbDist P⟩
  intro k
  -- D's component advantage is at most the distance bounded by h k; read it as a real gap.
  exact (ENNReal.ofReal_le_coe).mp
    ((D.advantage_le_transcriptDistance (R k).2 (S k).2).trans (h k))

end SystemAlgebra
