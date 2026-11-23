module

public import ConstructiveCryptography.Construction.Defs
public import ConstructiveCryptography.Specification.Metric

/-!
# Separating every ideal in a metric specification

`unconstructible_of_test_gap` uses observations to exclude the ideal witness required by
`ConstructsWithin`. The input can depend on the constructor, and the test can depend on
the ideal chosen for that input.
-/

@[expose] public section

namespace ConstructiveCryptography.Specification

/-- If every candidate has an input whose output can be distinguished from each permitted
ideal with gap above `ε`, the target specification is unconstructible within `ε`. -/
theorem unconstructible_of_test_gap {C X Y D : Type*} [EDist Y]
    -- Each admitted constructor `c ∈ constructors` acts on inputs by `maps c : X → Y`.
    (maps : C → X → Y) (constructors : Set C) (inputs : Specification X)
    -- `ideals` is the set of permitted outputs and `ε` is the allowed distance.
    (ideals : Specification Y) (ε : ENNReal)
    -- `gap d r i` measures how well test `d` distinguishes output `r` from ideal `i`.
    (tests : Set D) (gap : D → Y → Y → ENNReal)
    (dominated : ∀ d ∈ tests, ∀ r i, gap d r i ≤ edist r i)
    -- On the same input `x`, each possible ideal `i` admits its own separating test.
    (separates : ∀ c ∈ constructors, ∃ x ∈ inputs,
      ∀ i ∈ ideals, ∃ d ∈ tests, ε < gap d (maps c x) i) :
    Construction.Unconstructible (fun c s t => ConstructsWithin (maps c) s t ε)
      constructors inputs ideals := by
  rintro ⟨c, hc, works⟩
  obtain ⟨x, hx, separated⟩ := separates c hc
  -- Construction supplies an ideal close to the output on x.
  obtain ⟨i, hi, close⟩ := works x hx
  -- Its separating test gives ε < gap ≤ distance ≤ ε.
  obtain ⟨d, hd, far⟩ := separated i hi
  exact far.not_ge ((dominated d hd _ _).trans close)

end ConstructiveCryptography.Specification
