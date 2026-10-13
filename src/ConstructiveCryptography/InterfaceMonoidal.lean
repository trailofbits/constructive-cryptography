import ConstructiveCryptography.InterfaceCategory
import RandomSystems.Typed.ConverterCoherence
import RandomSystems.Typed.TensorRename
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The monoidal category of interfaces

A renaming `TypedConverter.rename` of interfaces is an isomorphism of the category of
interfaces: its inverse is the renaming by the inverse bijections, and the two compose to the
identity by `TypedConverter.rename_comp` and `TypedConverter.rename_refl`. Interfaces are an
instance of `MonoidalCategory`: `tensorObj` is the parallel interface `Interface.tensor`,
`tensorHom` is the parallel composition `TypedConverter.parallel` of typed converters, the unit
is `Interface.unit`, and the associator and the unitors are the isomorphisms of the regrouping
renamings. The axioms are discharged by `PDCBehavior.comp_tensor`, `PDCBehavior.tensor_id`,
`TypedConverter.comp_associator`, `TypedConverter.comp_leftUnitor`,
`TypedConverter.comp_rightUnitor`, and, for the pentagon and the triangle,
`TypedConverter.parallel_rename` and `TypedConverter.rename_comp`.

## Main definitions

* `Interface.isoOf`: the isomorphism of a renaming
* `Interface.associator`, `Interface.leftUnitor`, `Interface.rightUnitor`, `Interface.swap`: the
  regrouping isomorphisms
* `Interface.monoidal`: the monoidal category of interfaces and typed converters
-/

namespace SystemAlgebra.Interface

open CategoryTheory MonoidalCategory

/-- A bijection of interfaces is an isomorphism of the existing converter category. -/
noncomputable def isoOf {A B : Interface} (e : A.I ≃ B.I)
    (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (g : (Σ i, A.Y i) ≃ (Σ j, B.Y j))
    (hf : ∀ x, (f x).1 = e x.1) (hg : ∀ y, (g y).1 = e y.1)
    (hd : ∀ h, B.domain (h.map f) ↔ A.domain h) : A ≅ B where
  hom := TypedConverter.rename e f g hf hg hd
  inv := TypedConverter.rename e.symm f.symm g.symm (alphabet_symm_label e f hf)
    (alphabet_symm_label e g hg)
    (fun h => by
      have he := (hd (h.map f.symm)).symm
      simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)
  hom_inv_id := by
    change TypedConverter.comp _ _ = TypedConverter.id A
    rw [TypedConverter.rename_comp]
    simpa only [Equiv.self_trans_symm] using TypedConverter.rename_refl A
  inv_hom_id := by
    change TypedConverter.comp _ _ = TypedConverter.id B
    rw [TypedConverter.rename_comp]
    simpa only [Equiv.symm_trans_self] using TypedConverter.rename_refl B

noncomputable def associator (A B C : Interface) :
    tensor (tensor A B) C ≅ tensor A (tensor B C) :=
  isoOf (Equiv.sumAssoc A.I B.I C.I) (assocAlphabet A.X B.X C.X) (assocAlphabet A.Y B.Y C.Y)
    (assocAlphabet_fst A.X B.X C.X) (assocAlphabet_fst A.Y B.Y C.Y) (parallelDomain_assoc A B C)

noncomputable def leftUnitor (A : Interface) : tensor unit A ≅ A :=
  isoOf (Equiv.emptySum Empty A.I) (leftUnitAlphabet A.X) (leftUnitAlphabet A.Y)
    (leftUnitAlphabet_fst A.X) (leftUnitAlphabet_fst A.Y) (parallelDomain_unit_left A)

noncomputable def rightUnitor (A : Interface) : tensor A unit ≅ A :=
  isoOf (Equiv.sumEmpty A.I Empty) (rightUnitAlphabet A.X) (rightUnitAlphabet A.Y)
    (rightUnitAlphabet_fst A.X) (rightUnitAlphabet_fst A.Y) (parallelDomain_unit_right A)

/-- Exchange the two interface families without changing their message values. -/
noncomputable def swap (A B : Interface) : tensor A B ≅ tensor B A :=
  isoOf (Equiv.sumComm A.I B.I) (swapAlphabet A.X B.X) (swapAlphabet A.Y B.Y)
    (by rintro ⟨(i | j), x⟩ <;> rfl) (by rintro ⟨(i | j), y⟩ <;> rfl)
    (parallelDomain_swap A B)

noncomputable instance monoidalStruct : MonoidalCategoryStruct Interface where
  tensorObj := tensor
  tensorHom := TypedConverter.parallel
  whiskerLeft A _ _ β := TypedConverter.parallel (𝟙 A) β
  whiskerRight α B := TypedConverter.parallel α (𝟙 B)
  tensorUnit := unit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

lemma tensorHom_eq {A B C D : Interface} (α : A ⟶ B) (β : C ⟶ D) :
    α ⊗ₘ β = TypedConverter.parallel α β := rfl

lemma id_tensor_id (A B : Interface) : (𝟙 A ⊗ₘ 𝟙 B : A ⊗ B ⟶ A ⊗ B) = 𝟙 (A ⊗ B) :=
  PDCBehavior.tensor_id A.nonempty_prefix B.nonempty_prefix

lemma tensor_comp {A B C D E F : Interface}
    (α : A ⟶ B) (β : C ⟶ D) (γ : B ⟶ E) (δ : D ⟶ F) :
    (α ⊗ₘ β) ≫ (γ ⊗ₘ δ) = (α ≫ γ) ⊗ₘ (β ≫ δ) :=
  PDCBehavior.comp_tensor α β γ δ

lemma associator_naturality {A B C D E F : Interface}
    (α : A ⟶ D) (β : B ⟶ E) (γ : C ⟶ F) :
    ((α ⊗ₘ β) ⊗ₘ γ) ≫ (α_ D E F).hom = (α_ A B C).hom ≫ (α ⊗ₘ (β ⊗ₘ γ)) :=
  TypedConverter.comp_associator α β γ

lemma leftUnitor_naturality {A B : Interface} (α : A ⟶ B) :
    (𝟙 (𝟙_ Interface) ⊗ₘ α) ≫ (λ_ B).hom = (λ_ A).hom ≫ α :=
  TypedConverter.comp_leftUnitor α

lemma rightUnitor_naturality {A B : Interface} (α : A ⟶ B) :
    (α ⊗ₘ 𝟙 (𝟙_ Interface)) ≫ (ρ_ B).hom = (ρ_ A).hom ≫ α :=
  TypedConverter.comp_rightUnitor α

lemma pentagon (A B C D : Interface) :
    ((α_ A B C).hom ⊗ₘ 𝟙 D) ≫ (α_ A (B ⊗ C) D).hom ≫ (𝟙 A ⊗ₘ (α_ B C D).hom) =
      (α_ (A ⊗ B) C D).hom ≫ (α_ A B (C ⊗ D)).hom := by
  change TypedConverter.comp
      (TypedConverter.parallel (associator A B C).hom (TypedConverter.id D))
      (TypedConverter.comp (associator A (tensor B C) D).hom
        (TypedConverter.parallel (TypedConverter.id A) (associator B C D).hom)) =
    TypedConverter.comp (associator (tensor A B) C D).hom (associator A B (tensor C D)).hom
  rw [← TypedConverter.rename_refl D, ← TypedConverter.rename_refl A]
  simp only [associator, isoOf]
  erw [TypedConverter.parallel_rename (A := tensor (tensor A B) C) (B := tensor A (tensor B C))
    (C := D) (D := D)]
  erw [TypedConverter.parallel_rename (A := A) (B := A) (C := tensor (tensor B C) D)
    (D := tensor B (tensor C D))]
  simp only [TypedConverter.rename_comp]
  erw [TypedConverter.rename_comp]
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

lemma triangle (A B : Interface) :
    (α_ A (𝟙_ Interface) B).hom ≫ (𝟙 A ⊗ₘ (λ_ B).hom) = (ρ_ A).hom ⊗ₘ 𝟙 B := by
  change TypedConverter.comp (associator A unit B).hom
      (TypedConverter.parallel (TypedConverter.id A) (leftUnitor B).hom) =
    TypedConverter.parallel (rightUnitor A).hom (TypedConverter.id B)
  rw [← TypedConverter.rename_refl A, ← TypedConverter.rename_refl B]
  simp only [associator, leftUnitor, rightUnitor, isoOf]
  erw [TypedConverter.parallel_rename (A := A) (B := A) (C := tensor unit B) (D := B)]
  erw [TypedConverter.parallel_rename (A := tensor A unit) (B := A) (C := B) (D := B)]
  simp only [TypedConverter.rename_comp]
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
