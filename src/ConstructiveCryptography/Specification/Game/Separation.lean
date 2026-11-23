module

public import ConstructiveCryptography.Construction.Basic
public import ConstructiveCryptography.Specification.Basic
public import ConstructiveCryptography.Specification.Game.Basic

/-!
# Separating tests for game specifications

`unconstructible_of_test` rules out every admitted constructor by pulling one failed
output test back to an admitted input. Each constructor can have its own witness.
-/

@[expose] public section

namespace ConstructiveCryptography.Specification

/-- A failed test for each candidate rules out construction of the test guarantee. -/
theorem unconstructible_of_test {C X Y B : Type*} [LE B]
    -- Each admitted constructor `c ∈ constructors` implements a map `maps c : X → Y`.
    (maps : C → X → Y) (constructors : Set C) (inputs : Specification X)
    -- Each admitted test must score at most `ε` on an output.
    (tests : Set (Y → B)) (ε : B)
    -- The input `x` and the violating test `t` may depend on `c`.
    (separates : ∀ c ∈ constructors, ∃ x ∈ inputs, ∃ t ∈ tests, ¬ t (maps c x) ≤ ε) :
    Construction.Unconstructible (fun c => Constructs (maps c)) constructors inputs
      (gameSpec tests ε) := by
  rintro ⟨c, hc, works⟩
  obtain ⟨x, hx, t, ht, fails⟩ := separates c hc
  -- The promised output guarantee admits every test pulled back through this candidate.
  have bounded : x ∈ (maps c) ⁻¹' gameSpec tests ε := works hx
  rw [preimage_gameSpec] at bounded
  exact fails (bounded (t ∘ maps c) ⟨t, ht, rfl⟩)

end ConstructiveCryptography.Specification
