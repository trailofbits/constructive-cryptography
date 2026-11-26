module

public import Probability.StatisticalDistance

/-!
# Affine distance laws

A signed offset and unequal weights exercise the directed distance on an infinite carrier.
The probability example reads a mixture error from the same signed-law identity.
-/

public section

open Probability Probability.Distribution

namespace Tests.AffineDistance

/-- A common signed offset: mass `-5` at `0` and mass `3` at `7`. -/
noncomputable def offset : Distribution ℕ :=
  Finsupp.single 0 (-5) + Finsupp.single 7 3

example :
    statDist (offset + (2 : ℝ) • Finsupp.single 0 (-1))
      (offset + (2 : ℝ) • Finsupp.single 0 (-3)) = 4 := by
  rw [statDist_add_smul_add_smul_of_nonneg _ _ _ (by norm_num)]
  have support : ((Finsupp.single 0 (-1) : Distribution ℕ) -
      Finsupp.single 0 (-3)).support ⊆ {0} := by
    apply Finsupp.support_sub.trans
    simp only [Finsupp.support_single 0 (by norm_num : (-1 : ℝ) ≠ 0),
      Finsupp.support_single 0 (by norm_num : (-3 : ℝ) ≠ 0), Finset.union_self,
      Finset.Subset.refl]
  rw [statDist_eq_sum_of_support_subset _ _ support]
  norm_num [Finsupp.single_apply]

example :
    statDist (offset + (0 : ℝ) • Finsupp.single 2 9)
      (offset + (0 : ℝ) • Finsupp.single 8 (-4)) = 0 := by
  rw [statDist_add_smul_add_smul_of_nonneg _ _ _ (by norm_num), zero_mul]

/-- Keep a fair bit with probability `2/3`; otherwise return `true`. -/
example :
    statDist ((2 / 3 : ℝ) • 𝒰[Bool].1 +
      (1 / 3 : ℝ) • (ProbDist.single true).1) 𝒰[Bool].1 = 1 / 6 := by
  have same : (2 / 3 : ℝ) • 𝒰[Bool].1 +
      (1 / 3 : ℝ) • 𝒰[Bool].1 = 𝒰[Bool].1 := by
    rw [← add_smul]
    norm_num
  conv_lhs => rhs; rw [← same]
  rw [statDist_add_smul_add_smul_of_nonneg _ _ _ (by norm_num)]
  norm_num [statDist_eq_sum_univ, ProbDist.uniform, uniform_apply, Finsupp.single_apply,
    ProbDist.single]

/-- A negative scalar reverses excess mass; absolute scaling is false at unequal weights. -/
example :
    statDist ((-1 : ℝ) • (Finsupp.single () 2 : Distribution Unit))
      ((-1 : ℝ) • Finsupp.single () 1) ≠
      |(-1 : ℝ)| * statDist (Finsupp.single () 2) (Finsupp.single () 1) := by
  norm_num [statDist_eq_sum_univ, Finsupp.smul_apply, Finsupp.single_apply]

#print axioms statDist_add_smul_add_smul_of_nonneg

end Tests.AffineDistance
