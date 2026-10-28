import RandomSystems.Distance.Mixture
import RandomSystems.Typed.Functional

/-!
# Distance under a common initial sample

A componentwise bound remains valid after mixing both systems with the same normalized
law. This derives the averaging rule from the existing observer characterization of distance;
there is no additional security notion or computational assumption.
-/

open Probability
open scoped NNReal

namespace SystemAlgebra

/-- Averaging pointwise distance bounds over a common choice preserves the bound. -/
lemma TypedSystem.transcriptDistance_sample_le {A : Interface} {K : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (h : ∀ k, (R k).1.transcriptDistance (S k).1 ≤ (error : ENNReal)) :
    (TypedSystem.sample P R).1.transcriptDistance (TypedSystem.sample P S).1 ≤
      (error : ENNReal) := by
  -- Bound each admitted observer, then take the existing distance supremum.
  apply RandomSystem.transcriptDistance_le_of_advantage_le
    (TypedSystem.sample P R).2 (TypedSystem.sample P S).2
  intro D
  change |D.probability (RandomSystem.mix ⟨P, Distribution.IsProbability.isProbDist P⟩
      (fun k => (R k).1)) -
    D.probability (RandomSystem.mix ⟨P, Distribution.IsProbability.isProbDist P⟩
      (fun k => (S k).1))| ≤ _
  -- The observer sees the same initial sample in both experiments.
  rw [Domain.Distinguisher.probability_mix, Domain.Distinguisher.probability_mix]
  -- Average the component bounds using the normalized nonnegative sample weights.
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ P.support, |P k * D.probability (R k).1 - P k * D.probability (S k).1| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ P.support, P k * error := by
      refine Finset.sum_le_sum fun k _ => ?_
      have hp := (Distribution.IsProbability.isProbDist P).1 k
      have hk := (D.advantage_le_transcriptDistance (R k).2 (S k).2).trans (h k)
      rw [← mul_sub, abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left ((ENNReal.ofReal_le_coe).mp hk) hp
    _ = error := by
      rw [← Finset.sum_mul]
      change P.weight * error = error
      rw [(Distribution.IsProbability.isProbDist P).weight_eq, one_mul]

end SystemAlgebra
