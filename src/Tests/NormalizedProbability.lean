module

public import Probability.Kernel

/-!
# Normalized probability calculations

`map_uniform_coordinates` starts from one uniform pair and transforms its coordinates in
successive steps. The result is the product of the two transformed uniform laws. Every step
uses normalized operations and equations, so a client keeps normalization throughout.
-/

@[expose] public section

namespace Tests.NormalizedProbability

open Probability.Distribution

/-- Successive coordinate transformations preserve the independence of uniform inputs. -/
lemma map_uniform_coordinates
    -- `A`, `B` are finite nonempty input alphabets; `X`, `Y` are the output alphabets.
    {A B X Y : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    -- `f` transforms the first uniform coordinate and `g` the second.
    (f : A → X) (g : B → Y) :
    ((𝒰[A × B]).map (Prod.map f id)).map (Prod.map id g) =
      prodProbDist ((𝒰[A]).map f) ((𝒰[B]).map g) := by
  -- Separate the uniform coordinates, then move each transformation to its own factor.
  rw [← prodProbDist_uniform, ← prodProbDist_map_left, ← prodProbDist_map_right]

#print axioms map_uniform_coordinates

end Tests.NormalizedProbability
