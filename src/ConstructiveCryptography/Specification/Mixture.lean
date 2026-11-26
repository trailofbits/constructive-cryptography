module

public import ConstructiveCryptography.Specification.Metric

/-!
# Constructions from mixtures

`ConstructsWithin.mixture` picks an ideal component for each index, then mixes these witnesses.
The construction commutes with the chosen mixture. Closure places the mixed ideal in the target
specification, and the distance bound for mixing gives the total error.
-/

@[expose] public section

namespace ConstructiveCryptography.Specification

/-- Component constructions with errors `ε k` yield a construction on mixtures with error `δ`
when mixing preserves the target and aggregates the component distances within `δ`. -/
theorem ConstructsWithin.mixture
    -- `K` indexes the components. The construction maps resources of type `X` to type `Y`.
    {K X Y : Type*} [EDist Y] {f : X → Y}
    -- Component `k` has input specification `source k` and chooses an ideal in `target`.
    {source : K → Specification X} {target : Specification Y} {ε : K → ENNReal}
    (component : ∀ k, ConstructsWithin f (source k) target (ε k))
    -- `mixX` and `mixY` assemble a family before and after applying `f`.
    (mixX : (K → X) → X) (mixY : (K → Y) → Y)
    (commutes : ∀ r, f (mixX r) = mixY (f ∘ r))
    -- `closed` admits one joint mixture of the selected ideal components.
    (closed : ∀ s, (∀ k, s k ∈ target) → mixY s ∈ target)
    -- `δ` bounds the mixed distance; for a common sampling law it can be the mean of `ε k`.
    {δ : ENNReal} (mixed : ∀ a b, (∀ k, edist (a k) (b k) ≤ ε k) →
      edist (mixY a) (mixY b) ≤ δ) :
    ConstructsWithin f (mixX '' {r | ∀ k, r k ∈ source k}) target δ := by
  rintro _ ⟨r, admitted, rfl⟩
  -- Choose one ideal for each admitted component and mix them with the prescribed operation.
  choose s member close using fun k => component k (r k) (admitted k)
  refine ⟨mixY s, closed s member, ?_⟩
  rw [commutes]
  exact mixed (f ∘ r) s close

end ConstructiveCryptography.Specification
