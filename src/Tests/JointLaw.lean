module

public import Probability.Expectation

/-!
# Averaging values and events over successive draws

The signed-kernel check uses negative weights on an infinite carrier. The joint-event check
uses a nonuniform first draw and a second law that depends on it.
-/

@[expose] public section

noncomputable section

namespace Probability.Tests.JointLaw

open Distribution

/-- A signed first law `-2δ₀ + 3δ₁` and the kernel `n ↦ δ_{n+1}` have mean `4`. -/
example :
    (bindK (Finsupp.single 0 (-2) + Finsupp.single 1 3 : Distribution ℕ)
      (fun n => Finsupp.single (n + 1) 1)).expect (fun n => (n : ℝ)) = 4 := by
  rw [expect_bindK, expect_add_left]
  simp only [expect, Finsupp.sum_single_index, zero_mul]
  norm_num

/-- `first` puts probability `1/3` at `1` and `2/3` at `0`, on the carrier `ℕ`. -/
def first : ProbDist ℕ :=
  (𝒰[Fin 3]).map fun i => if i = 0 then 1 else 0

/-- At `0`, return `1`; elsewhere, return one fair bit as a natural number. -/
def next (n : ℕ) : ProbDist ℕ :=
  if n = 0 then ProbDist.single 1 else (𝒰[Bool]).map fun b => if b then 1 else 0

/-- The joint event `h = 1 ∧ z = 0` has probability `(1/3) · (1/2) = 1/6`. -/
example : (ProbDist.jointLaw first next).1.mass (fun hz => hz.1 = 1 ∧ hz.2 = 0) = 1 / 6 := by
  rw [ProbDist.jointLaw_mass_eq_expect]
  simp only [first, ProbDist.map_val, expect_fTransform]
  rw [expect_eq_sum]
  norm_num [next, ProbDist.map_val, mass_fTransform, ProbDist.single,
    mass_single, mass_eq_sum, ProbDist.uniform, uniform_apply, Fintype.sum_bool,
    Fin.sum_univ_succ]

#print axioms Distribution.expect_bindK
#print axioms Distribution.ProbDist.expect_jointLaw
#print axioms Distribution.ProbDist.jointLaw_mass_eq_expect

end Probability.Tests.JointLaw
