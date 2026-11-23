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

end Tests.SecondMoment
