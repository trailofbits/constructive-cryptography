import RandomSystems.Typed.Context
import ConstructiveCryptography.Substitution.Relaxation
import ConstructiveCryptography.InterfaceAlgebra

set_option autoImplicit false

/-!
# Substitution images and parallel composition

For interfaces, the fixed contexts `TypedConverter.rightContext` and `TypedConverter.leftContext`
realize parallel composition with a fixed typed system. A single-substitution relaxation whose
transformation class is closed under both contexts is therefore compatible with parallel
composition.

## Main results

* `singleSubstitutionRelaxation_parallelCompatible`

Source: Banfi 2023, §4.1.4; Jost, §2.2.2.
-/

namespace SystemAlgebra.Substitution

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

open ConstructiveCryptography.CryptographicAlgebra


/-- The literal one-use substitution relaxation preserves independent
parallel under explicit closure of the admitted transformations in both
ordered context positions.

Banfi, Section 4.1.4 (printed p. 76), requires an "(efficient) transformation".
These closure hypotheses do not assert that arbitrary converters are efficient.
Jost's locality equation, Proposition 2.2.3 (printed p. 18), supplies
"composition order independence"; its concrete RS realization is already
proved by the two context-attachment equations. -/
theorem singleSubstitutionRelaxation_parallelCompatible {D : Interface}
    (transformations : ∀ A : Interface, Set (A ⟶ D))
    (left right : TypedSystem D)
    (diagonal : ∀ (A : Interface) (R : TypedSystem A),
      ∃ transformation ∈ transformations A,
        transformation • left = R ∧
        transformation • right = R)
    (rightClosed : ∀ (A B : Interface) (context : TypedSystem B)
      (transformation : A ⟶ D), transformation ∈ transformations A →
        TypedConverter.rightContext A context ≫ transformation ∈ transformations (A ⊗ B))
    (leftClosed : ∀ (A B : Interface) (context : TypedSystem A)
      (transformation : B ⟶ D), transformation ∈ transformations B →
        TypedConverter.leftContext context B ≫ transformation ∈ transformations (A ⊗ B)) :
    Specification.Relaxation.ParallelCompatible
      (fun A => Specification.singleSubstitutionRelaxation
        (transformations A) left right (diagonal A)) := by
  intro A B source target
  dsimp only
  simp only [Specification.singleSubstitutionRelaxation_apply]
  constructor
  · rintro R ⟨original, ⟨transformation, allowed, leftEq, center⟩,
      context, admitted, rfl⟩
    -- Put the fixed right context around the same single transformation.
    refine ⟨TypedConverter.rightContext A context ≫ transformation,
      rightClosed A B context transformation allowed, ?_, ?_⟩
    · exact (congrArg (fun R : TypedSystem A =>
        TypedSystem.parallel R context) leftEq).trans
        ((TypedConverter.attach_rightContext
          (transformation • left) context).symm.trans
          (Interface.comp_smul
            (TypedConverter.rightContext A context) transformation left).symm)
    · -- Its other endpoint is the same context around the admitted center.
      refine ⟨transformation • right,
        center, context, admitted, ?_⟩
      exact (TypedConverter.attach_rightContext
        (transformation • right) context).symm.trans
        (Interface.comp_smul
          (TypedConverter.rightContext A context) transformation right).symm
  · rintro R ⟨context, admitted,
      original, ⟨transformation, allowed, leftEq, center⟩, rfl⟩
    -- The left context uses the other ordered converter, without a swap.
    refine ⟨TypedConverter.leftContext context B ≫ transformation,
      leftClosed A B context transformation allowed, ?_, ?_⟩
    · exact (congrArg (fun R : TypedSystem B =>
        TypedSystem.parallel context R) leftEq).trans
        ((TypedConverter.attach_leftContext context
          (transformation • left)).symm.trans
          (Interface.comp_smul
            (TypedConverter.leftContext context B) transformation left).symm)
    · -- Membership of the unchanged component and the original center suffice.
      refine ⟨context, admitted,
        transformation • right, center, ?_⟩
      exact (TypedConverter.attach_leftContext context
        (transformation • right)).symm.trans
        (Interface.comp_smul
          (TypedConverter.leftContext context B) transformation right).symm

end

end SystemAlgebra.Substitution
