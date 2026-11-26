module

public import Probability.DependentProduct
public import RandomSystems.Typed.Functional

/-!
# Random functions with prescribed coordinate laws

`randomFunction A μ` draws one table with independent entries `f i x ∼ μ i x`, then
answers every admitted query `i(x)` with the retained value `f i x`. The domain is `A.domain`.
Thus repeating an input reads the same draw, while distinct coordinates are independent.
`Commons.URF.eq_randomFunction` in `Commons.Definitions.Ideal` identifies uniform coordinates
with the existing uniform random function.

This is the finite-alphabet form of [1, Definition 6, p. 12]: "each O(x) for x ∈ D is
sampled independently", with a specified law at each coordinate.

## References

1. G. Herold, D. Khovratovich, M. Kudinov, S. Tessaro, B. Wagner.
   *Aborting Random Oracles: How to Build them, How to Use them.* 2026. ePrint 2026/016.
-/

@[expose] public section

namespace Commons

open SystemAlgebra Probability Probability.Distribution

/-- Draw `f ∼ ⨂ᵢ ⨂ₓ μ i x` once; answer every admitted `i(x)` with `f i x`. -/
noncomputable def randomFunction
    -- `A` supplies ports, finite query/reply alphabets and the admitted input histories.
    (A : Interface)
    -- `μ i x` is the normalized law of the retained reply at port `i` and input `x`.
    (μ : ∀ i, A.X i → ProbDist (A.Y i)) : TypedSystem A :=
  TypedSystem.sample (ProbDist.piDep (fun i => ProbDist.piDep (μ i))).1
    TypedSystem.ofFunction

end Commons
