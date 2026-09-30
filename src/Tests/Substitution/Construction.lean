import ConstructiveCryptography.Substitution.Construction

set_option autoImplicit false

/-!
# Implication witnesses under serial composition

Use counts of assumptions from two source families stay separate after serial composition, and
constructions of disjoint parts compose.
-/

namespace Tests.Substitution.Construction

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SubstitutionRelation

universe u v w x y

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
variable {ι : Type x} {κ : Type y}
variable {innerBoundary : ι → C} {outerBoundary : κ → C}
variable {innerSystems : ∀ i, Bool → Phi (innerBoundary i)}
variable {outerSystems : ∀ i, Bool → Phi (outerBoundary i)}

-- Two uses of one premise in the first proof and one use in a distinct
-- source family stay 2 and 1 after serial composition. The families may be
-- infinite and their individual assumptions may have heterogeneous interfaces.
theorem repeated_assumption_counts [DecidableEq ι] [DecidableEq κ] {A : C}
    (innerAssumption : ι) (outerAssumption : κ)
    (innerTransformation : A ⟶ innerBoundary innerAssumption)
    (outerTransformation : A ⟶ outerBoundary outerAssumption)
    (join : attach innerTransformation (innerSystems innerAssumption false) =
      attach outerTransformation (outerSystems outerAssumption false)) :
    ∃ combined : Implication (Sum.elim innerBoundary outerBoundary)
        (Sum.rec innerSystems outerSystems) A 2,
      combined.targetLeft = attach innerTransformation
        (innerSystems innerAssumption false) ∧
      combined.targetRight = attach outerTransformation
        (outerSystems outerAssumption true) ∧
      combined.usageCount (Sum.inl innerAssumption) = 2 ∧
      combined.usageCount (Sum.inr outerAssumption) = 1 := by
  let single := Implication.single (systems := innerSystems) innerAssumption false innerTransformation
  let inner := single.append single.reverse rfl
  let outer := Implication.single (systems := outerSystems) outerAssumption false outerTransformation
  have one : single.usageCount innerAssumption = 1 :=
    (Implication.usageCount_single innerAssumption innerAssumption false
      innerTransformation).trans (if_pos rfl)
  have two : inner.usageCount innerAssumption = 2 :=
    (single.usageCount_append single.reverse rfl innerAssumption).trans
      (congrArg₂ Nat.add one ((single.usageCount_reverse innerAssumption).trans one))
  obtain ⟨combined, firstEq, lastEq, firstCounts, lastCounts⟩ :=
    Implication.exists_serial_simulators inner outer (𝟙 A) (𝟙 A) (𝟙 A) (𝟙 A) (𝟙 A)
      single.targetLeft single.targetLeft outer.targetRight
      (attach_identity single.targetLeft).symm
      (attach_identity single.targetLeft).symm
      (join.symm.trans (attach_identity single.targetLeft).symm)
      (attach_identity outer.targetRight).symm rfl
  refine ⟨combined, ?_, ?_, (firstCounts _).trans two, ?_⟩
  · simpa only [Category.id_comp, attach_identity, single, Implication.single] using firstEq
  · simpa only [Category.id_comp, attach_identity, outer, Implication.single,
      Bool.not_false] using lastEq
  · exact (lastCounts _).trans
      ((Implication.usageCount_single outerAssumption outerAssumption false
        outerTransformation).trans (if_pos rfl))

-- Banfi's existential simulator statement, with honest/adversarial locality
-- proved by ordered tensor. Resources are arbitrary joint resources: none
-- is assumed to factor into an honest and an adversarial component.
theorem construction_serial_disjoint [MonoidalCategory C]
    {A B D E : C} (innerProtocol : B ⟶ D) (outerProtocol : A ⟶ B)
    (real : Phi (D ⊗ E)) (middle : Phi (B ⊗ E))
    (ideal : Phi (A ⊗ E))
    (inner : ∃ simulator : E ⟶ E,
      Specification.Constructs (innerProtocol ⊗ₘ 𝟙 E) {real}
        {resource | derivable innerBoundary innerSystems resource
          (attach (𝟙 B ⊗ₘ simulator) middle)})
    (outer : ∃ simulator : E ⟶ E,
      Specification.Constructs (outerProtocol ⊗ₘ 𝟙 E) {middle}
        {resource | derivable outerBoundary outerSystems resource
          (attach (𝟙 A ⊗ₘ simulator) ideal)}) :
    ∃ simulator : E ⟶ E,
      Specification.Constructs ((outerProtocol ≫ innerProtocol) ⊗ₘ 𝟙 E) {real}
        {resource | derivable (Sum.elim innerBoundary outerBoundary)
          (Sum.rec innerSystems outerSystems) resource
          (attach (𝟙 A ⊗ₘ simulator) ideal)} := by
  obtain ⟨innerSimulator, innerConstruction⟩ := inner
  obtain ⟨outerSimulator, outerConstruction⟩ := outer
  refine ⟨innerSimulator ≫ outerSimulator, ?_⟩
  have commutes : (outerProtocol ⊗ₘ 𝟙 E) ≫ (𝟙 B ⊗ₘ innerSimulator) =
      (𝟙 A ⊗ₘ innerSimulator) ≫ (outerProtocol ⊗ₘ 𝟙 E) := by
    simp only [← converter_parallel_serial, Category.id_comp, Category.comp_id]
  have result := Specification.Constructs.derivable_serial_simulators
    innerConstruction outerConstruction (by
      rw [← attach_serial, ← attach_serial, commutes])
  simpa only [← converter_parallel_serial, Category.id_comp] using result

end Tests.Substitution.Construction
