module

public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution
public import Tests.TypedComposition

/-!
# Composite notation in source and displayed terms

Direct operations display with the same serial, tensor, identity, attachment and parallel
notation accepted by the frontend. An alternative local tensor keeps the explicit canonical
operation; the printer must not make it appear to use that alternative.
-/

@[expose] public section

namespace Tests.CompositeNotation

open SystemAlgebra CategoryTheory CategoryTheory.MonoidalCategory
open scoped SystemAlgebra NNReal

section
variable (A B C D : Interface) (α : TypedConverter A B) (β : TypedConverter B C)
  (γ : TypedConverter C D) (R : TypedSystem B) (S : TypedSystem C)

/-- info: α ≫ β : TypedConverter A C -/
#guard_msgs in
#check TypedConverter.comp α β

/-- info: α ⊗ₘ γ : TypedConverter (A ⊗ C) (B ⊗ D) -/
#guard_msgs in
#check TypedConverter.parallel α γ

/-- info: 𝟙 A : TypedConverter A A -/
#guard_msgs in
#check TypedConverter.id A

/-- info: α • R : TypedSystem A -/
#guard_msgs in
#check TypedConverter.attach α R

/-- info: R ∥ S : TypedSystem (B ⊗ C) -/
#guard_msgs in
#check TypedSystem.parallel R S

/-- info: A ⊗ B : Interface -/
#guard_msgs in
#check Interface.tensor A B

section
variable [_selected : MonoidalCategoryStruct Interface]

/-- info: α.parallel γ : TypedConverter (A.tensor C) (B.tensor D) -/
#guard_msgs in
#check TypedConverter.parallel α γ
end

section
variable [_action : HSMul (TypedConverter A B) (TypedSystem B) (TypedSystem A)]

/-- info: α.attach R : TypedSystem A -/
#guard_msgs in
#check TypedConverter.attach α R
end

-- The complete assembly needs no categorical type annotations.
example (T : TypedSystem D) :
    (α ≫ β ≫ γ) • (𝟙 D • T) = α • (β • (γ • T)) := by
  cc_normalize

end

section
open scoped SystemAlgebra.Tests.TypedComposition.Selected
variable (A : Interface) (f g : (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A)

/-- info: TypedConverter.comp f g : TypedConverter { down := A }.down { down := A }.down -/
#guard_msgs in
#check TypedConverter.comp f g
end

-- The family notation infers both the interface and the canonical identity operation.
example {K : Type} [Fintype K] (A : K → Interface) :
    (⨂ₘ k, 𝟙 (A k)) = TypedConverter.parallelAll (fun k => TypedConverter.id (A k)) := rfl

/-- A certified DDC enters the same calculation through its existing typed presentation. -/
example {A B : Interface} {b : ℕ}
    (raw : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y)
    (certificate : IsDDCFrom B.domain A.domain b raw)
    (R S : TypedSystem B) (ε : ℝ≥0) (bound : Δ R S ≤ ε) :
    let α : TypedConverter A B := TypedConverter.ofDDC raw certificate
    Δ (α • R) (α • S) ≤ ε := by
  intro α
  cc_calc statistical
    α • R ≈[ε] α • S := bound

end Tests.CompositeNotation
