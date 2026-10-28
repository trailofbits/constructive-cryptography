import RandomSystems.Typed.DSL.Probability

/-!
# DSL uniform law compatibility

The old exported name and the general notation denote the same normalized law.
-/

open Probability SystemAlgebra.DSL

example : (𝒰[Bool] : Distribution.ProbDist Bool).1 = Distribution.uniform Bool := by
  rw [SystemAlgebra.DSL.uniform]
