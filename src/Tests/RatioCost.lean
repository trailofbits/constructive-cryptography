module

public import RandomSystems.Distance.RatioCost
public import RandomSystems.Typed.Interface

/-!
# Zero ratio loss and zero transcript cost

An unchanged system supplies its entire cumulative mass as the good submass. Normalization
pays zero at every query, so both error terms vanish, for arbitrary finite port alphabets.
-/

@[expose] public section

namespace Tests.RatioCost

open SystemAlgebra Probability
open scoped NNReal BigOperators

/-- The ratio-and-cost theorem recovers zero distance with no discarded good mass. -/
lemma identity_bound {A : Interface} (R : TypedSystem A) : R.1.transcriptDistance R.1 ≤ 0 := by
  have bound := RandomSystem.transcriptDistance_le_add_of_ratio_and_transcriptCost
    R.2 R.2 (g := R.1) (error₁ := 0) (error₂ := 0)
    R.1.mass_nonneg (fun _ => le_rfl) R.1.mass_nil
    (by intro h; simp only [NNReal.coe_zero, sub_zero, one_mul, le_refl])
    (cost := fun _ _ => 0) (by
      intro h x _ hx
      have normal : (∑ y, R.1 (h ++ [(x, y)])) = R.1 h := by
        calc
          _ = (R.1.extensionLaw h x).weight := by
            rw [Distribution.weight_eq_sum]
            exact Finset.sum_congr rfl fun y _ => (R.1.extensionLaw_apply h x y).symm
          _ = R.1 h := (R.1.extensionLaw_weight h x).trans (ite_eq_left hx)
      simp only [normal, sub_self, zero_mul, le_refl])
    (by intro h _; simp only [transcriptCost_zero, NNReal.coe_zero, le_refl])
  simpa only [ENNReal.coe_zero, add_zero] using bound

#print axioms identity_bound
#print axioms RandomSystem.transcriptDistance_le_add_of_ratio_and_transcriptCost

end Tests.RatioCost
