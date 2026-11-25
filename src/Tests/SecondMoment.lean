module

public import Probability.Expectation

/-! # Sharp and degenerate cases of the second-moment bound -/

@[expose] public section

namespace Tests.SecondMoment

open Probability Distribution

/-- For an indicator, both moments and the event probability are the same mass. -/
example {A : Type*} (P : Distribution A) (event : A → Prop) [DecidablePred event] :
    P.expect (fun x => if event x then (1 : ℝ) else 0) ^ 2 =
      P.mass event * P.expect (fun x => (if event x then (1 : ℝ) else 0) ^ 2) := by
  have indicator (x : A) : (if event x then (1 : ℝ) else 0) ^ 2 =
      (if event x then 1 else 0) := by split <;> norm_num
  simp only [indicator, expect_indicator, pow_two]

/-- A zero count is admitted by the bound without dividing by its zero second moment. -/
example {A : Type*} (P : Distribution A) (weights : P.NonNeg) :
    P.expect (fun _ => (0 : ℝ)) ^ 2 ≤
      P.mass (fun _ => (0 : ℝ) < 0) * P.expect (fun _ => (0 : ℝ) ^ 2) :=
  expect_sq_le_mass_pos_mul_second weights (fun _ => 0) (fun _ => le_rfl)

/-- A negative constant uses the nonzero event without a sign assumption on its value. -/
example : (uniform Bool).expect (fun _ => (-1 : ℝ)) ^ 2 ≤
    (uniform Bool).mass (fun _ => (-1 : ℝ) ≠ 0) *
      (uniform Bool).expect (fun _ => (-1 : ℝ) ^ 2) :=
  expect_sq_le_mass_ne_zero_mul_second _ uniform_nonNeg _

#print axioms expect_sq_le_mass_ne_zero_mul_second
#print axioms expect_sq_le_mass_pos_mul_second

end Tests.SecondMoment
