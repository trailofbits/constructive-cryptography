import RandomSystems.Typed.Functional

/-!
# The uniform law in the DSL namespace

`SystemAlgebra.DSL.uniform A` is `Distribution.ProbDist.uniform A`, the normalized uniform law
`𝒰[A]` of `Probability.Distribution`. Component bodies sample closed laws of type
`Distribution.ProbDist A`.

## Main definitions

* `uniform`: `Distribution.ProbDist.uniform`, exported into `SystemAlgebra.DSL`
-/

namespace SystemAlgebra.DSL

open Probability

-- `DSL.uniform`, and `uniform` under `open SystemAlgebra.DSL`, name the Probability definition.
export Probability.Distribution.ProbDist (uniform)

end SystemAlgebra.DSL
