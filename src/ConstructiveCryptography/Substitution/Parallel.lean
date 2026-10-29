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

This module is concrete: interfaces are `Interface`, resources on `A` are typed systems
`TypedSystem A`, an arrow `A ⟶ D` is a typed converter with outside `A` and inside `D`, and
`ρ • R` is attachment. For `S : TypedSystem B` and `R : TypedSystem A`:

```text
rightContext A S : A ⊗ B ⟶ A     rightContext A S • R = R ∥ S   (attach_rightContext)
leftContext R B  : A ⊗ B ⟶ B     leftContext R B • S  = R ∥ S   (attach_leftContext)
```

So placing a fixed system beside a one-use image `ρ(X₀)` is the one-use image under the
composite transformation `context ≫ ρ`, with the same fixed system beside `ρ(X₁)`. These are
exact equalities of typed systems; no error is involved.

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
proved by the two context-attachment equations.

With `φ_A = singleSubstitutionRelaxation (transformations A) left right (diagonal A)`, for
specifications `𝒮` on `A` and `𝒯` on `B`:

```text
φ_A(𝒮) ∥ 𝒯 ⊆ φ_{A⊗B}(𝒮 ∥ 𝒯)       ρ(X₀) ∥ T = (rightContext A T ≫ ρ)(X₀)
𝒮 ∥ φ_B(𝒯) ⊆ φ_{A⊗B}(𝒮 ∥ 𝒯)       S ∥ ρ(X₀) = (leftContext S B ≫ ρ)(X₀)
```

Here `S ∈ 𝒮`, `T ∈ 𝒯`, and `ρ` is the admitted transformation witnessing the relaxed
component. Its `X₁`-side `ρ(X₁)` lies in `𝒮` (resp. `𝒯`), so `ρ(X₁) ∥ T` (resp.
`S ∥ ρ(X₁)`) lies in `𝒮 ∥ 𝒯`.
The two positions are handled by different contexts, so no symmetry of `∥` is used. The
closure hypotheses quantify over every fixed system `context`. -/
theorem singleSubstitutionRelaxation_parallelCompatible
    -- `D : Interface` is the interface of the assumption's two systems.
    {D : Interface}
    -- `transformations A` is the admitted set of typed converters `ρ : A ⟶ D` at each outside
    -- interface `A`.
    (transformations : ∀ A : Interface, Set (A ⟶ D))
    -- `left = X₀` and `right = X₁` are the assumption's typed systems on `D`.
    (left right : TypedSystem D)
    -- `diagonal A R` gives an admitted `ρ` with `ρ • X₀ = R = ρ • X₁`, as required by
    -- `singleSubstitutionRelaxation` at every `A`.
    (diagonal : ∀ (A : Interface) (R : TypedSystem A),
      ∃ transformation ∈ transformations A,
        transformation • left = R ∧
        transformation • right = R)
    -- `rightClosed` says admitted `ρ : A ⟶ D` gives admitted `rightContext A context ≫ ρ` at
    -- `A ⊗ B`, for every fixed `context : TypedSystem B`.
    (rightClosed : ∀ (A B : Interface) (context : TypedSystem B)
      (transformation : A ⟶ D), transformation ∈ transformations A →
        TypedConverter.rightContext A context ≫ transformation ∈ transformations (A ⊗ B))
    -- `leftClosed` says admitted `ρ : B ⟶ D` gives admitted `leftContext context B ≫ ρ` at
    -- `A ⊗ B`, for every fixed `context : TypedSystem A`.
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
