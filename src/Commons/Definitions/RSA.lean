module

public import Probability.Group
public import Mathlib.Data.Nat.Totient

/-!
# RSA blinding on units

`RSA.blinding_success_eq` specializes the finite-group success law to `(ZMod N)ˣ`.
Its order is `φ(N)`, so an exponent coprime to `φ(N)` makes `y * r^e` uniform.
Unblinding the solver's returned root by `r⁻¹` then preserves its success law.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons.RSA

open Probability Probability.Distribution

/-- The randomized solver has its uniform-challenge success law at every fixed unit challenge:
“for every y ∈ Z∗n” [1, Exercise 10.28, Hint, p. 432]. -/
lemma blinding_success_eq
    -- `N` is a nonzero modulus; `(ZMod N)ˣ` is its finite group of units.
    (N e : ℕ) [NeZero N]
    -- `he` makes exponentiation by `e` a permutation of the `φ(N)` units.
    (he : (Nat.totient N).Coprime e)
    -- `A z` returns a proposed unit root or `none`; `y` is the fixed unit challenge.
    (A : (ZMod N)ˣ → ProbDist (Option (ZMod N)ˣ)) (y : (ZMod N)ˣ) :
    ProbDist.rootSuccessLaw (ProbDist.blindRootSolver A e) e y =
      𝒰[(ZMod N)ˣ].bind (ProbDist.rootSuccessLaw A e) := by
  -- The group-order hypothesis is exactly `gcd(φ(N), e) = 1`.
  have he' : (Nat.card (ZMod N)ˣ).Coprime e := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using he
  exact ProbDist.blinding_success_eq (G := (ZMod N)ˣ) A e he' y

end Commons.RSA
