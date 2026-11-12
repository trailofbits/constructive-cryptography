module

public import Probability.Expectation

/-!
# Finite mixtures of cumulative behaviors

`mixMass P p h` averages the whole-transcript mass `p i h` over one retained draw `i ∼ P`.
The index type may be infinite: the probability law supplies its finite support.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

/-- Draw `i ∼ P` once and use the cumulative behavior `p i` throughout the interaction. -/
noncomputable def mixMass
    -- `ι` carries retained choices; `A`, `B` carry queries and replies.
    {ι A B : Type} (P : ProbDist ι)
    -- `p i h` is the mass of the complete transcript `h` with retained choice `i`.
    (p : ι → List (A × B) → ℝ) (h : List (A × B)) : ℝ :=
  P.1.expect (fun i => p i h)

end SystemAlgebra
