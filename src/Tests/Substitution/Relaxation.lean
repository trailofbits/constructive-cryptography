import ConstructiveCryptography.Substitution.Relaxation

set_option autoImplicit false

/-!
# Substitution-relaxation tests

The serial test uses typed intermediate and target interfaces, separate inner
and transported simulators, and an explicit protocol/simulator commutation
equation. The negative check ensures that equation cannot be omitted.
-/

namespace Tests.Substitution.Relaxation

open CategoryTheory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra

universe u v w

variable {C : Type u} [Category.{v} C]
variable {Phi : C → Type w} [ResourceTheory C Phi]

-- The literal one-use statement works with a supplied transformation and two
-- exact endpoints, without an unrelated substitution relation or reflexivity axiom.
theorem construction_of_single_substitution {A B D E : C}
    (transformations : Set (A ⟶ B)) (left right : Phi B)
    (protocol : A ⟶ D) (simulator : A ⟶ E)
    (real : Phi D) (ideal : Phi E)
    (transformation : A ⟶ B) (allowed : transformation ∈ transformations)
    (realEq : attach protocol real = attach transformation left)
    (idealEq : attach transformation right = attach simulator ideal) :
    Specification.Constructs protocol {real}
      (Specification.substitutionImage transformations left right
        {attach simulator ideal}) := by
  apply (Specification.constructs_singleton_substitutionImage_iff
    transformations left right protocol simulator real ideal).mpr
  exact ⟨transformation, allowed, realEq, idealEq⟩

-- No transformation witnesses means no diagonal elements. Extensivity cannot
-- be claimed for an arbitrary one-use image without Jost's additional condition.
example {A B : C} (left right : Phi B) (resource : Phi A) :
    resource ∉ Specification.substitutionImage (∅ : Set (A ⟶ B)) left right {resource} := by
  rintro ⟨transformation, impossible, _, _⟩
  exact impossible

-- A literal one-use image embeds in the finite-chain presentation with
-- exactly one forward use of the sole assumption. The converse is not assumed.
theorem single_image_has_one_use {A B : C}
    (transformations : Set (A ⟶ B)) (left right : Phi B)
    (source : Specification (Phi A))
    (resource : Phi A)
    (member : resource ∈ Specification.substitutionImage transformations left right source) :
    let systems : Unit → Bool → Phi B := fun _ bit =>
      match bit with | false => left | true => right
    ∃ center ∈ source,
      ∃ implication : SubstitutionRelation.Implication (fun _ : Unit => B) systems A 0,
        implication.targetLeft = resource ∧ implication.targetRight = center ∧
          implication.usageCount () = 1 := by
  intro systems
  obtain ⟨transformation, _, leftEq, center⟩ := member
  let implication := SubstitutionRelation.Implication.single
    (systems := systems) () false transformation
  refine ⟨attach transformation right, center, implication, leftEq.symm, rfl, ?_⟩
  exact (SubstitutionRelation.Implication.usageCount_single
    (systems := systems) () () false transformation).trans (if_pos rfl)

-- Admitted-transform closure, rather than mere type correctness, is required
-- for converter compatibility of a computationally restricted one-use image.
example {B : C} (transformations : ∀ A : C, Set (A ⟶ B))
    (left right : Phi B)
    (diagonal : ∀ A (resource : Phi A),
      ∃ transformation ∈ transformations A,
        attach transformation left = resource ∧
        attach transformation right = resource)
    (closed : ∀ {A D : C} (converter : A ⟶ D) transformation,
      transformation ∈ transformations D → converter ≫ transformation ∈ transformations A) :
    Specification.Relaxation.Compatible (fun A =>
      Specification.singleSubstitutionRelaxation (transformations A) left right (diagonal A)) := by
  fail_if_success
    exact Specification.singleSubstitutionRelaxation_compatible
      transformations left right diagonal (fun _ _ allowed => allowed)
  exact Specification.singleSubstitutionRelaxation_compatible
    transformations left right diagonal closed

example
    (relation : SubstitutionRelation C)
    (reflexive : ∀ A, Std.Refl (relation.substitutes A))
    {A : C}
    (source : Specification (Phi A)) :
    Specification.substitutionRelaxation relation reflexive
        (Specification.substitutionRelaxation relation reflexive source) =
      Specification.substitutionRelaxation relation reflexive source :=
  Specification.substitutionRelaxation_idem relation reflexive source

example
    (relation : SubstitutionRelation C)
    (reflexive : ∀ A, Std.Refl (relation.substitutes A))
    {A B D : C} (outerProtocol : A ⟶ B) (innerProtocol : B ⟶ D)
    (innerSimulator : B ⟶ B)
    (transportedSimulator outerSimulator : A ⟶ A)
    (real : Phi D) (middle : Phi B) (ideal : Phi A)
    (inner : Specification.Constructs innerProtocol
      {real}
      (Specification.substitutionRelaxation relation reflexive
        {attach innerSimulator middle}))
    (outer : Specification.Constructs outerProtocol
      {middle}
      (Specification.substitutionRelaxation relation reflexive
        {attach outerSimulator ideal}))
    (commutes : outerProtocol ≫ innerSimulator =
      transportedSimulator ≫ outerProtocol) :
    Specification.Constructs (outerProtocol ≫ innerProtocol)
      {real}
      (Specification.substitutionRelaxation relation reflexive
        {attach (transportedSimulator ≫ outerSimulator) ideal}) := by
  fail_if_success
    exact inner.substitutionRelaxation_serial_simulators relation reflexive outer rfl
  exact inner.substitutionRelaxation_serial_simulators relation reflexive outer commutes

#print axioms Specification.singleSubstitutionRelaxation_compatible
#print axioms Specification.constructs_singleton_substitutionImage_iff
#print axioms construction_of_single_substitution
#print axioms single_image_has_one_use

end Tests.Substitution.Relaxation
