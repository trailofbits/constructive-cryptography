module

public import Probability.Expectation

/-!
# Expectations of finite class scores

Signed weights on natural outcomes are grouped by a noninjective class map. A negative
score and an unselected class check that neither positivity nor finite ambient types is used.
-/

@[expose] public section

noncomputable section

namespace Probability.Tests.FiniteScoreExpectation

open Distribution

/-- `law = −2δ₀ + 3δ₁ + 4δ₄` is a signed finite law on `ℕ`. -/
def law : Distribution ℕ :=
  Finsupp.single 0 (-2) + Finsupp.single 1 3 + Finsupp.single 4 4

/-- The sole scored class is `0`, with score `−3`. -/
def score (c : ℕ) : ℝ := if c = 0 then -3 else 0

/-- Grouping `0` and `1` gives mass `1`; class `2` contributes zero, so expectation is `−3`. -/
example : law.expect (fun n => score (n / 2)) = -3 := by
  rw [expect_comp_eq_sum_mass_of_eq_zero law (fun n => n / 2) score {0}
    (by
      intro c outside
      exact ite_eq_right (by simpa only [Finset.mem_singleton] using outside))]
  simp only [Finset.sum_singleton, score, ↓reduceIte, law, mass_add, mass_single]
  norm_num

/-- The existing finite-class theorem groups a Boolean score by its two class masses. -/
example (X : Distribution Bool) :
    X.expect (fun b => if b then (2 : ℝ) else 0) =
      2 * X.mass (fun b => b = true) := by
  have grouped := expect_comp_eq_sum_mass X id (fun b => if b then (2 : ℝ) else 0)
  simpa only [id_eq, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
    using grouped

#print axioms Distribution.expect_comp_eq_sum_mass_of_eq_zero
#print axioms Distribution.expect_comp_eq_sum_mass

end Probability.Tests.FiniteScoreExpectation
