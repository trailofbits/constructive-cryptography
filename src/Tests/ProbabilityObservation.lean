import Probability.Kernel
import Probability.Lift

/-!
# Probability-level comparisons through a common function

These checks import only probability modules. Different conditional kernels can give joint
laws at distance one with identical first marginals; data processing bounds pushforwards along
one common map. The mass-two example on `ℕ` applies the ratio theorem to two laws of equal
weight two.
-/

namespace Probability.Tests.Observation

open Distribution Distribution.ProbDist

/-- The same public outcome `()` completed with records `false` or `true` has distance one:
`δ(δ_{((), false)}, δ_{((), true)}) = 1`. -/
example : statDist
    (jointLaw (ProbDist.single ()) (fun _ => ProbDist.single false)).1
    (jointLaw (ProbDist.single ()) (fun _ => ProbDist.single true)).1 = 1 := by
  -- Both joint laws are point masses; `δ = ∑_a max(X a − Y a, 0)` has the one term
  -- `max(1 − 0, 0) = 1`, at `((), false)`.
  simp only [jointLaw, ProbDist.bind_val, ProbDist.map_val, ProbDist.single,
    bindK_single, one_smul, fTransform_single]
  norm_num [statDist_eq_sum_univ, Fintype.sum_prod_type, Fintype.sum_bool,
    Finsupp.single_apply]

/-- Either completion still has the public marginal `fst_* (jointLaw δ_() (δ_b)) = δ_()`. -/
example (b : Bool) :
    ProbDist.map Prod.fst (jointLaw (ProbDist.single ()) (fun _ => ProbDist.single b)) =
      ProbDist.single () := jointLaw_fst _ _

/-- Two laws of weight two on `ℕ`, `P = 2δ₀`, `Q = 2δ₁`, remain within their ideal loss two
under `f = Nat.succ`. This exercises arbitrary outcome types and weights greater than one. -/
example :
    statDist (fTransform Nat.succ (Finsupp.single 0 2 : Distribution ℕ))
      (fTransform Nat.succ (Finsupp.single 1 2 : Distribution ℕ)) ≤ 2 := by
  have hratio : ∀ a : ℕ,
      (1 - (1 : ℝ)) * (Finsupp.single 1 2 : Distribution ℕ) a ≤
        (Finsupp.single 0 2 : Distribution ℕ) a := by
    -- With `ε = 1` the ratio reads `0 ≤ P a`, true since `P = 2δ₀ ≥ 0`.
    intro a
    simp only [sub_self, zero_mul]
    exact single_nonNeg (by norm_num) 0 a
  -- The constant loss one has expectation `1 · weight Q = 2`.
  simpa only [expect_const, weight_single, one_mul] using
    statDist_fTransform_le_expect_of_ratio
      (Finsupp.single 0 2 : Distribution ℕ) (Finsupp.single 1 2) Nat.succ (fun _ => 1)
      (by simp only [weight_single]) (single_nonNeg (by norm_num) 1)
      (fun _ => zero_le_one) hratio

#print axioms statDist_fTransform_le_expect_of_ratio
#print axioms Distribution.weight_smul_normalizeOr
#print axioms Distribution.ProbDist.jointLaw_fst
#print axioms Distribution.ProbDist.jointLaw_map

end Probability.Tests.Observation
