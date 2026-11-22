module

public import RandomSystems.Typed.Context
public import ConstructiveCryptography.Substitution.Relaxation
public import ConstructiveCryptography.Instances.Algebra
public import ConstructiveCryptography.Notation.Basic

/-!
# Typed substitution and parallel composition

For interfaces, the fixed contexts `TypedConverter.rightContext` and `TypedConverter.leftContext`
realize parallel composition with a fixed typed system. A single-substitution relaxation whose
transformation class is closed under both contexts is therefore compatible with parallel
composition. The closure is a hypothesis of the corollary, not a property of the instances.

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

`TypedConverter.substitutesWithin_attach` transports a selected-test bound through attachment,
with the typed reduced test `d.absorb α`. `singleSubstitutionRelaxation_parallelCompatible`
lifts one-use substitution images through both ordered parallel contexts.

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
2. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis,
   Diss. ETH No. 26723, ETH Zurich, 2020.
-/

@[expose] public section

set_option autoImplicit false

namespace SystemAlgebra.Substitution

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

open ConstructiveCryptography.CryptographicAlgebra


/-- One-use substitution preserves independent parallel composition when admitted transformations
are closed under both ordered contexts for every fixed system.
Write `φ_A = singleSubstitutionRelaxation (transformations A) left right (diagonal A)`.
For specifications `𝒮` on `A` and `𝒯` on `B`, with `X₀ = left`, `X₁ = right`:

```text
φ_A(𝒮) ∥ 𝒯 ⊆ φ_{A⊗B}(𝒮 ∥ 𝒯)       ρ(X₀) ∥ T = (rightContext A T ≫ ρ)(X₀)
𝒮 ∥ φ_B(𝒯) ⊆ φ_{A⊗B}(𝒮 ∥ 𝒯)       S ∥ ρ(X₀) = (leftContext S B ≫ ρ)(X₀)
```

Here `S ∈ 𝒮`, `T ∈ 𝒯`, and `ρ` is the admitted witness at the replaced interface. The same
context at `X₁` gives `ρ(X₁) ∥ T ∈ 𝒮 ∥ 𝒯` or `S ∥ ρ(X₁) ∈ 𝒮 ∥ 𝒯`, respectively.
[1, §4.1.4, p. 76] requires an “(efficient) transformation”; `transformations` is an explicit
admitted class whose efficiency is a property of the caller's model.
[2, Proposition 2.2.3, p. 18] gives “composition order independence”, instantiated here by
the two context-attachment equations. -/
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

namespace SystemAlgebra.TypedConverter

open ConstructiveCryptography

/-- A selected-test bound survives attachment through `α`, at the reduced test `d.absorb α`. -/
lemma substitutesWithin_attach
    -- The instance selects the admitted tests at every interface.
    [AdmissibleDistinguishers Interface TypedDistinguisher]
    -- `A` is the outside interface; `B` carries the compared inside systems.
    {A B : Interface} (α : TypedConverter A B)
    -- `closed` admits `d.absorb α` whenever the outside test `d` is admitted.
    (closed : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) α)
    -- `h` bounds the advantage between `R`, `S` by the inside-test-dependent error `ε`.
    {R S : TypedSystem B} {ε : TypedDistinguisher B → ENNReal} (h : R ≃[ε] S) :
    α • R ≃[fun d => ε (d.absorb α)] α • S := by
  -- The interface instance interprets abstract absorption as typed converter absorption.
  simpa only [DistinguisherAction.absorb] using
    (AdmissibleDistinguishers.substitutesWithin_attach α closed h)

end SystemAlgebra.TypedConverter
