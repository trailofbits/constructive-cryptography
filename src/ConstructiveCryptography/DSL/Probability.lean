import ConstructiveCryptography.Functional

/-!
# Laws

Uniform laws on finite normalized distributions, the usual laws that component bodies sample
from; any closed law of type `Distribution.ProbDist A` may be sampled.

## Main definitions

* `uniform` (notation `𝒰[A]`)
-/

namespace SystemAlgebra.DSL

universe u

open Probability

noncomputable def uniform (A : Type u) [Fintype A] [Nonempty A] :
    Distribution.ProbDist A := ⟨Distribution.uniform A, Distribution.uniform_isProbDist⟩

scoped notation "𝒰[" A "]" => uniform A

end SystemAlgebra.DSL
