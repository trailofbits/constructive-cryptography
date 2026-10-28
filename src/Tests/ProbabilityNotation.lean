import Probability

/-!
# Uniform law notation at the probability layer

The notation elaborates after importing `Probability`, without any systems or DSL import.
-/

open Probability

noncomputable example : Distribution.ProbDist Bool := 𝒰[Bool]

example : (𝒰[Bool] : Distribution.ProbDist Bool).1 = Distribution.uniform Bool := by
  rfl
