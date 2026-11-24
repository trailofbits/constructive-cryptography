module

public import ConstructiveCryptography.CryptographicAlgebra.Star

/-!
# Serial composition of right-port simulator images

```text
H ───────────────── H
P ── σ ── Q ── τ ── R
```

`simulatorImage_comp` combines two right-port images into the image of the composites
`σ ≫ τ`. A budgeted simulator class admits this image whenever it admits those composites
(`simulatorImage_comp_subset`).
-/

@[expose] public section

namespace ConstructiveCryptography.CryptographicAlgebra.Specification

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C] {Φ : C → Type*} [ResourceTheory C Φ]

/-- The right-port image consists of all attachments of an admitted `σ` to a resource in `S`. -/
lemma simulatorImage_eq_image2 {H P Q : C} (simulators : Set (P ⟶ Q))
    (S : Specification (Φ (H ⊗ Q))) :
    simulatorImage simulators S = Set.image2 (fun σ r => attach (H ◁ σ) r) simulators S :=
  Set.iUnion_image_right _

/-- Two successive simulator images are the image of their serial composites. -/
theorem simulatorImage_comp {H P Q R : C}
    -- `outer` serves `P` using `Q`; `inner` serves `Q` using `R`.
    (outer : Set (P ⟶ Q)) (inner : Set (Q ⟶ R))
    -- The input resources in `S` have honest port `H` and inside port `R`.
    (S : Specification (Φ (H ⊗ R))) :
    simulatorImage outer (simulatorImage inner S) =
      simulatorImage (Set.image2 (· ≫ ·) outer inner) S := by
  simp only [simulatorImage_eq_image2]
  -- On each resource the two attachments compose, with the honest wire unchanged.
  apply Eq.symm
  apply Set.image2_assoc
  intro σ τ r
  rw [whiskerLeft_comp, attach_serial]

/-- A selected composite class may use a different budget from either input class. -/
lemma simulatorImage_comp_subset {H P Q R : C}
    {outer : Set (P ⟶ Q)} {inner : Set (Q ⟶ R)} {composites : Set (P ⟶ R)}
    -- `admitted` certifies the composite under the caller's chosen resource accounting.
    (admitted : ∀ σ ∈ outer, ∀ τ ∈ inner, σ ≫ τ ∈ composites)
    (S : Specification (Φ (H ⊗ R))) :
    simulatorImage outer (simulatorImage inner S) ⊆ simulatorImage composites S := by
  rw [simulatorImage_comp]
  simp only [simulatorImage_eq_image2]
  exact Set.image2_subset_right (Set.image2_subset_iff.mpr admitted)

end ConstructiveCryptography.CryptographicAlgebra.Specification
