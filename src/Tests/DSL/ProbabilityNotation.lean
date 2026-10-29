import RandomSystems.Typed.DSL.Probability

/-!
# The DSL name of the uniform law

`SystemAlgebra.DSL.uniform Bool` is the normalized law `𝒰[Bool]`, and rewriting with it exposes
the raw law `Distribution.uniform Bool` underlying `𝒰[Bool]`.
-/

open Probability SystemAlgebra.DSL

example : (𝒰[Bool] : Distribution.ProbDist Bool).1 = Distribution.uniform Bool := by
  rw [SystemAlgebra.DSL.uniform]

example : SystemAlgebra.DSL.uniform Bool = (𝒰[Bool] : Distribution.ProbDist Bool) := rfl
