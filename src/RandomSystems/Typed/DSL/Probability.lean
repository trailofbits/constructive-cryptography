import RandomSystems.Typed.Functional

/-!
# Probability law compatibility

The uniform probability law and its notation now belong to `Probability.Distribution`.
The exported `uniform` name keeps existing DSL terms and rewrite proofs elaborating.
Component bodies may sample any closed law of type `Distribution.ProbDist A`.

## Main definitions

* `uniform`: export of `Distribution.ProbDist.uniform`; `𝒰[A]` is available from `Probability`.
-/

namespace SystemAlgebra.DSL

open Probability

-- Existing DSL users refer to this name in rewrite proofs; export the Probability definition.
export Probability.Distribution.ProbDist (uniform)

end SystemAlgebra.DSL
