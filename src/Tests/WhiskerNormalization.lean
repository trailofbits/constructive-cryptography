module

public import ConstructiveCryptography.Notation
public import RandomSystems.Typed.DSL.Syntax

/-!
# Tests for `cc_normalize` monoidal unitor and whiskering automation

Exercises `cc_normalize` on unitor (`λ_`, `ρ_`), associator (`α_`), and whiskering (`◁`, `▷`)
goals in both an arbitrary `CryptographicAlgebra` and on `Interface` / `TypedSystem` under full
CC custom notation (`•`, `∥`, `◁`, `▷`, `⊗ₘ`, `≫`, `sample`).
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.WhiskerNormalization

open CategoryTheory MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra

section Abstract

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CryptographicAlgebra C Phi]

/-- Forward and inverse left unitors normalize in public `•` and `∥` notation. -/
example {A : C} (R : Phi A) :
    (λ_ A).hom • R = (dummy (C := C)) ∥ R ∧
      (λ_ A).inv • ((dummy (C := C)) ∥ R) = R := by
  constructor <;> cc_normalize

/-- Forward and inverse right unitors normalize in public `•` and `∥` notation. -/
example {A : C} (R : Phi A) :
    (ρ_ A).hom • R = R ∥ (dummy (C := C)) ∧
      (ρ_ A).inv • (R ∥ (dummy (C := C))) = R := by
  constructor <;> cc_normalize

/-- Inverse associator regroups left-bracketed parallel resources. -/
example {A B D : C} (L : Phi A) (M : Phi B) (R : Phi D) :
    (α_ A B D).inv • ((L ∥ M) ∥ R) = L ∥ (M ∥ R) := by
  cc_normalize

/-- Left- and right-whiskering act on their respective components. -/
example {A A' B B' : C} (α : A' ⟶ A) (β : B' ⟶ B) (R : Phi A) (S : Phi B) :
    (A ◁ β) • (R ∥ S) = R ∥ (β • S) ∧
      (α ▷ B) • (R ∥ S) = (α • R) ∥ S := by
  constructor <;> cc_normalize

/-- Serial composition inside right- and left-whiskering splits and normalizes in one step. -/
example {H H' H'' P Q Q' Q'' : C}
    (κ : H' ⟶ H) (π : H ⟶ H'') (σ : Q' ⟶ Q) (τ : Q ⟶ Q'')
    (R : Phi H'') (S : Phi P) (U : Phi H) (V : Phi Q'') :
    ((κ ≫ π) ▷ P) • (R ∥ S) = (κ • (π • R)) ∥ S ∧
      (H ◁ (σ ≫ τ)) • (U ∥ V) = U ∥ (σ • (τ • V)) := by
  constructor <;> cc_normalize

/-- Right-whiskering moves inside left-whiskering (indifferentiability simulator exchange). -/
example {H H' P Q : C} (κ : H' ⟶ H) (σ : P ⟶ Q) (T : Phi (H ⊗ Q)) :
    (κ ▷ P) • ((H ◁ σ) • T) = (H' ◁ σ) • ((κ ▷ Q) • T) := by
  cc_normalize

/-- Identity whiskering drops out cleanly. -/
example {A B : C} (R : Phi (A ⊗ B)) :
    (A ◁ 𝟙 B) • R = R ∧ (𝟙 A ▷ B) • R = R := by
  constructor <;> cc_normalize

/-- Two converters on the same port require their own commutation argument. -/
example {A B : C} (α β : A ⟶ A) (R : Phi A) (S : Phi B)
    (commute : α • (β • R) = β • (α • R)) :
    ((α ≫ β) ▷ B) • (R ∥ S) = ((β ≫ α) ▷ B) • (R ∥ S) := by
  cc_normalize
  guard_target = parallel (α • (β • R)) S = parallel (β • (α • R)) S
  fail_if_success solve | rfl
  rw [commute]

end Abstract

section Interfaces

open SystemAlgebra Probability
open scoped SystemAlgebra.DSL

/-- Forward and inverse left/right unitors normalize on `Interface` for both `λ_`/`ρ_` and
`Interface.leftUnitor`/`Interface.rightUnitor`. -/
example {A : Interface} (R : TypedSystem A) :
    (λ_ A).hom • R = TypedSystem.dummy ∥ R ∧
      (λ_ A).inv • (TypedSystem.dummy ∥ R) = R ∧
      (Interface.leftUnitor A).inv • (dummy ∥ R) = R ∧
      (ρ_ A).hom • R = R ∥ TypedSystem.dummy ∧
      (ρ_ A).inv • (R ∥ TypedSystem.dummy) = R ∧
      (Interface.rightUnitor A).inv • (R ∥ dummy) = R := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cc_normalize

/-- Inverse associator normalizes on `Interface` for both `(α_ A B C).inv` and
`(Interface.associator A B C).inv`. -/
example {A B C : Interface} (R : TypedSystem A) (S : TypedSystem B) (T : TypedSystem C) :
    (α_ A B C).inv • ((R ∥ S) ∥ T) = R ∥ (S ∥ T) ∧
      (Interface.associator A B C).inv • ((R ∥ S) ∥ T) = R ∥ (S ∥ T) := by
  constructor <;> cc_normalize

/-- Left- and right-whiskering normalize on `Interface`, including serial composition inside `▷`
and `◁`. -/
example {H H' H'' P Q Q' Q'' : Interface}
    (κ : H' ⟶ H) (π : H ⟶ H'') (σ : Q' ⟶ Q) (τ : Q ⟶ Q'')
    (R : TypedSystem H'') (S : TypedSystem P) (U : TypedSystem H) (V : TypedSystem Q'') :
    (H ◁ τ) • (U ∥ V) = U ∥ (τ • V) ∧
      (π ▷ P) • (R ∥ S) = (π • R) ∥ S ∧
      ((κ ≫ π) ▷ P) • (R ∥ S) = (κ • (π • R)) ∥ S ∧
      (H ◁ (σ ≫ τ)) • (U ∥ V) = U ∥ (σ • (τ • V)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cc_normalize

/-- Indifferentiability simulator exchange on `Interface`, both directly and through a retained
sample. -/
example {H H' P Q : Interface} {K : Type} (law : Distribution K) [Distribution.IsProbability law]
    (κ : H' ⟶ H) (σ : P ⟶ Q) (T : TypedSystem (H ⊗ Q)) (F : K → TypedSystem (H ⊗ Q)) :
    (κ ▷ P) • ((H ◁ σ) • T) = (H' ◁ σ) • ((κ ▷ Q) • T) ∧
      (κ ▷ P) • (sample k ← law; (H ◁ σ) • F k) =
        (sample k ← law; (H' ◁ σ) • ((κ ▷ Q) • F k)) := by
  constructor <;> cc_normalize

/-- Multi-step protocol assembly combining `(α ⊗ₘ 𝟙)` and `(α_ K L P).hom` with a whiskered
right-port converter reduces to the component equation `hshare`. -/
example {A K L P M : Interface}
    (α : A ⟶ K ⊗ L) (share : L ⊗ P ⟶ M)
    (R : TypedSystem K) (S : TypedSystem M) (T : TypedSystem L) (U : TypedSystem P)
    (hshare : share • S = T ∥ U) :
    ((α ⊗ₘ 𝟙 P) ≫ (α_ K L P).hom ≫ (K ◁ share)) • (R ∥ S) =
      (α • (R ∥ T)) ∥ U := by
  cc_normalize
  -- The assembly laws leave exactly the supplied component equation to use.
  fail_if_success solve | rfl
  rw [hshare]
  cc_normalize

end Interfaces

#print axioms ConstructiveCryptography.CryptographicAlgebra.attach_whiskerLeft
#print axioms ConstructiveCryptography.CryptographicAlgebra.attach_whiskerRight
#print axioms ConstructiveCryptography.CryptographicAlgebra.whisker_attach_comm
#print axioms SystemAlgebra.Interface.whiskerLeft_smul
#print axioms SystemAlgebra.Interface.whiskerRight_smul
#print axioms SystemAlgebra.Interface.whisker_smul_comm

end Tests.WhiskerNormalization
