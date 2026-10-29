import Probability

/-!
# Uniform law notation at the probability layer

`𝒰[A]` elaborates from `Probability` alone, with no systems or DSL import, as a normalized law
whose raw distribution `𝒰[A].1` is `Distribution.uniform A`.
-/

open Probability

noncomputable example : Distribution.ProbDist Bool := 𝒰[Bool]

example : (𝒰[Bool] : Distribution.ProbDist Bool).1 = Distribution.uniform Bool := by
  rfl
