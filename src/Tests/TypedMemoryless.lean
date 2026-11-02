module

public import RandomSystems.Typed.Memoryless

/-!
# Memoryless systems in a common context

The typed parallel equation rewrites under an arbitrary converter. The concrete assembly
places the fair-bit source beside a memoryless component on its selected interface.
-/

@[expose] public section

open SystemAlgebra Probability Probability.Distribution

/-- Replacing the component pair by its combined reply law preserves the context `α`. -/
example
    -- `A`, `B` are the component interfaces; `C` is the interface exposed by `α`.
    {A B C : Interface}
    (α : TypedConverter C (Interface.tensor A B))
    -- `ν₁ i x` and `ν₂ j y` give the two components' fresh reply laws.
    (ν₁ : ∀ i, A.X i → ProbDist (A.Y i)) (ν₂ : ∀ j, B.X j → ProbDist (B.Y j)) :
    α • TypedSystem.parallel (TypedSystem.ofMemoryless A ν₁)
        (TypedSystem.ofMemoryless B ν₂) =
      α • TypedSystem.ofMemoryless (Interface.tensor A B)
        (RandomSystem.parallelLaw ν₁ ν₂) := by
  rw [TypedSystem.parallel_ofMemoryless]

/-- A fair-bit source fits beside an arbitrary memoryless system under `α`. -/
example
    -- `q` bounds the source's triggers; `B` retains its domain; `C` is exposed by `α`.
    {B C : Interface} (q : ℕ)
    (α : TypedConverter C (Interface.tensor (Interface.source Bool q) B))
    -- `ν j x` is the fresh reply law at query `x` on port `j` of `B`.
    (ν : ∀ j, B.X j → ProbDist (B.Y j)) :
    α • TypedSystem.parallel (TypedSystem.source 𝒰[Bool] q)
        (TypedSystem.ofMemoryless B ν) =
      α • TypedSystem.ofMemoryless (Interface.tensor (Interface.source Bool q) B)
        (RandomSystem.parallelLaw (fun _ _ => 𝒰[Bool]) ν) := by
  rw [TypedSystem.source_eq_ofMemoryless, TypedSystem.parallel_ofMemoryless]

#print axioms TypedSystem.ofMemoryless
#print axioms TypedSystem.ofMemoryless_val
#print axioms TypedSystem.source_eq_ofMemoryless
#print axioms TypedSystem.parallel_ofMemoryless
