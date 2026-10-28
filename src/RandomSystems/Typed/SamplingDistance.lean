import RandomSystems.Distance.Mixture
import RandomSystems.Typed.Functional

/-!
# Distance between systems sampled with a common law

Let `R k` and `S k` be systems on the same interface, at transcript distance at most
`error` for every `k`. `TypedSystem.transcriptDistance_sample_le` proves that choosing a
component with law `P` in either family preserves this bound. Each experiment retains its
choice throughout the interaction; the two experiments use the same distribution `P`.
The law may be nonuniform, and only its support, not the sample type, must be finite.

## Proof

* `RandomSystem.transcriptDistance_le_of_advantage_le` reduces the conclusion to the
  advantage of an arbitrary distinguisher compatible with the shared interface domain.
* `Domain.Distinguisher.probability_mix` in `RandomSystems.Distance.Mixture` expresses both
  decision probabilities as component averages. The common weights let their difference
  be bounded by the average of the component advantages, using the triangle inequality.
* `Domain.Distinguisher.advantage_le_transcriptDistance` bounds each component advantage
  by `error`. The weights are nonnegative and sum to one, so their average is at most `error`.
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
  -- Typed sampling is the mixture of the underlying random systems on this domain.
  change |D.probability (RandomSystem.mix ⟨P, Distribution.IsProbability.isProbDist P⟩
      (fun k => (R k).1)) -
    D.probability (RandomSystem.mix ⟨P, Distribution.IsProbability.isProbDist P⟩
      (fun k => (S k).1))| ≤ _
  -- Express D's two decision probabilities as averages over their common sampling law.
  rw [Domain.Distinguisher.probability_mix, Domain.Distinguisher.probability_mix]
  -- Subtract under the common sum: each term compares R k with S k at the same weight.
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  calc
    -- The absolute gap of the averages is at most the sum of the absolute component gaps.
    _ ≤ ∑ k ∈ P.support, |P k * D.probability (R k).1 - P k * D.probability (S k).1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ P.support, P k * error := by
      refine Finset.sum_le_sum fun k _ => ?_
      -- Nonnegative sampling weights preserve each component's upper bound.
      have hp := (Distribution.IsProbability.isProbDist P).1 k
      -- D's advantage on R k and S k is at most their distance, bounded by h k.
      have hk := (D.advantage_le_transcriptDistance (R k).2 (S k).2).trans (h k)
      rw [← mul_sub, abs_mul, abs_of_nonneg hp]
      -- Convert the finite ENNReal bound to a real bound on the absolute probability gap.
      exact mul_le_mul_of_nonneg_left ((ENNReal.ofReal_le_coe).mp hk) hp
    _ = error := by
      -- Averaging the constant error leaves error because P has total mass one.
      rw [← Finset.sum_mul]
      change P.weight * error = error
      rw [(Distribution.IsProbability.isProbDist P).weight_eq, one_mul]

end SystemAlgebra
