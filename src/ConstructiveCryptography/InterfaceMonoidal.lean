import ConstructiveCryptography.ConverterCoherence
import ConstructiveCryptography.InterfaceTensorRename
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The monoidal category of interfaces

The tensor of interfaces is the parallel interface and the tensor of converters is their
parallel composition; the associator and the unitors are the regrouping renamings.

## Main definitions

* `Interface.monoidal`: the monoidal category of interfaces and converters
-/

namespace SystemAlgebra.Interface

open CategoryTheory MonoidalCategory

noncomputable instance monoidalStruct : MonoidalCategoryStruct Interface where
  tensorObj := tensor
  tensorHom := parallelConverter
  whiskerLeft A _ _ β := parallelConverter (𝟙 A) β
  whiskerRight α B := parallelConverter α (𝟙 B)
  tensorUnit := unit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

theorem tensorHom_eq {A B C D : Interface} (α : A ⟶ B) (β : C ⟶ D) :
    α ⊗ₘ β = parallelConverter α β := rfl

theorem id_tensor_id (A B : Interface) : (𝟙 A ⊗ₘ 𝟙 B : A ⊗ B ⟶ A ⊗ B) = 𝟙 (A ⊗ B) :=
  PDCBehavior.tensor_id A.nonempty_prefix B.nonempty_prefix

theorem tensor_comp {A B C D E F : Interface}
    (α : A ⟶ B) (β : C ⟶ D) (γ : B ⟶ E) (δ : D ⟶ F) :
    (α ⊗ₘ β) ≫ (γ ⊗ₘ δ) = (α ≫ γ) ⊗ₘ (β ≫ δ) :=
  PDCBehavior.comp_tensor α β γ δ

theorem associator_naturality {A B C D E F : Interface}
    (α : A ⟶ D) (β : B ⟶ E) (γ : C ⟶ F) :
    ((α ⊗ₘ β) ⊗ₘ γ) ≫ (α_ D E F).hom = (α_ A B C).hom ≫ (α ⊗ₘ (β ⊗ₘ γ)) :=
  comp_associator α β γ

theorem leftUnitor_naturality {A B : Interface} (α : A ⟶ B) :
    (𝟙 (𝟙_ Interface) ⊗ₘ α) ≫ (λ_ B).hom = (λ_ A).hom ≫ α :=
  comp_leftUnitor α

theorem rightUnitor_naturality {A B : Interface} (α : A ⟶ B) :
    (α ⊗ₘ 𝟙 (𝟙_ Interface)) ≫ (ρ_ B).hom = (ρ_ A).hom ≫ α :=
  comp_rightUnitor α

theorem pentagon (A B C D : Interface) :
    ((α_ A B C).hom ⊗ₘ 𝟙 D) ≫ (α_ A (B ⊗ C) D).hom ≫ (𝟙 A ⊗ₘ (α_ B C D).hom) =
      (α_ (A ⊗ B) C D).hom ≫ (α_ A B (C ⊗ D)).hom := by
  change parallelConverter (associator A B C).hom (𝟙 D) ≫
      (associator A (tensor B C) D).hom ≫ parallelConverter (𝟙 A) (associator B C D).hom =
    (associator (tensor A B) C D).hom ≫ (associator A B (tensor C D)).hom
  rw [← rename_refl D, ← rename_refl A]
  simp only [associator, isoOf]
  erw [parallelConverter_rename (A := tensor (tensor A B) C) (B := tensor A (tensor B C))
    (C := D) (D := D)]
  erw [parallelConverter_rename (A := A) (B := A) (C := tensor (tensor B C) D) (D := tensor B (tensor C D))]
  simp only [rename_comp]
  erw [rename_comp]
  congr 1
  · apply Equiv.ext
    intro x
    rcases x with ((a | b) | c) | d <;> rfl
  · apply Equiv.ext
    intro x
    rcases x with ⟨(((a | b) | c) | d), x⟩ <;> rfl
  · apply Equiv.ext
    intro y
    rcases y with ⟨(((a | b) | c) | d), y⟩ <;> rfl

theorem triangle (A B : Interface) :
    (α_ A (𝟙_ Interface) B).hom ≫ (𝟙 A ⊗ₘ (λ_ B).hom) = (ρ_ A).hom ⊗ₘ 𝟙 B := by
  change (associator A unit B).hom ≫ parallelConverter (𝟙 A) (leftUnitor B).hom =
    parallelConverter (rightUnitor A).hom (𝟙 B)
  rw [← rename_refl A, ← rename_refl B]
  simp only [associator, leftUnitor, rightUnitor, isoOf]
  erw [parallelConverter_rename (A := A) (B := A) (C := tensor unit B) (D := B)]
  erw [parallelConverter_rename (A := tensor A unit) (B := A) (C := B) (D := B)]
  simp only [rename_comp]
  congr 1
  · apply Equiv.ext
    intro x
    rcases x with (a | e) | b
    · rfl
    · exact e.elim
    · rfl
  · apply Equiv.ext
    intro x
    rcases x with ⟨((a | e) | b), x⟩
    · rfl
    · exact e.elim
    · rfl
  · apply Equiv.ext
    intro y
    rcases y with ⟨((a | e) | b), y⟩
    · rfl
    · exact e.elim
    · rfl

noncomputable instance monoidal : MonoidalCategory Interface :=
  MonoidalCategory.ofTensorHom id_tensor_id (fun _ _ _ _ => rfl) (fun _ _ => rfl)
    tensor_comp associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon triangle

end SystemAlgebra.Interface
