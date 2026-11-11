module

public import Probability.Kernel

/-!
# Normalized probability calculations

`map_uniform_coordinates` draws a uniform bit and a uniform element of `Fin 3`, flips the bit,
then reads the finite value as a natural number. Its three equations split the uniform pair
and move each transformation to its own independent factor, using normalized laws throughout.
The output alphabet `Bool × ℕ` exercises coordinate maps with an infinite carrier.
-/

@[expose] public section

namespace Tests.NormalizedProbability

open Probability.Distribution

/-- Flipping a uniform bit and reading an independent `Fin 3` value as a natural number
gives the product of those transformed laws. -/
lemma map_uniform_coordinates :
    ((𝒰[Bool × Fin 3]).map (Prod.map Bool.not id)).map (Prod.map id Fin.val) =
      prodProbDist ((𝒰[Bool]).map Bool.not) ((𝒰[Fin 3]).map Fin.val) := by
  calc
    -- The uniform pair is the product of its independent uniform coordinates.
    ((𝒰[Bool × Fin 3]).map (Prod.map Bool.not id)).map (Prod.map id Fin.val) =
        ((prodProbDist 𝒰[Bool] 𝒰[Fin 3]).map (Prod.map Bool.not id)).map
          (Prod.map id Fin.val) := by rw [prodProbDist_uniform]
    -- Flipping the first coordinate transforms only its factor.
    _ = (prodProbDist ((𝒰[Bool]).map Bool.not) 𝒰[Fin 3]).map
        (Prod.map id Fin.val) := by rw [prodProbDist_map_left]
    -- Reading the second coordinate as a natural number transforms the other factor.
    _ = prodProbDist ((𝒰[Bool]).map Bool.not) ((𝒰[Fin 3]).map Fin.val) :=
      (prodProbDist_map_right Fin.val _ _).symm

#print axioms map_uniform_coordinates

end Tests.NormalizedProbability
