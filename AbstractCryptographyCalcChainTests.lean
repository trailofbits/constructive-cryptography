/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import ConstructiveCryptography.Multiparty.Basic

/-!
# Typed construction chains

This focused test checks that the single `ResourceAlgebra` presentation
supports paper-shaped serial calculations. Exact and scalar-error construction
use `calc`; distance, constructor-class, and multiparty composition expose the
additional mathematical premises that their conclusions require.
-/

namespace ConstructiveCryptography.CalcChain.Tests

open CategoryTheory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open ConstructiveCryptography.Multiparty
open scoped ConstructiveCryptography

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

/-! ## Exact and scalar-error construction -/

/-- Three exact typed constructions compose in the paper's order. -/
example {A B D E : C} {π₁ : D ⟶ E} {π₂ : B ⟶ D} {π₃ : A ⟶ B}
    {key : Specification Phi E} {insecure : Specification Phi D}
    {authenticated : Specification Phi B} {secure : Specification Phi A}
    (first : key —[π₁]→ insecure)
    (second : insecure —[π₂]→ authenticated)
    (third : authenticated —[π₃]→ secure) :
    key —[π₃ ≫ (π₂ ≫ π₁)]→ secure :=
  calc
    key —[π₁]→ insecure := first
    _ —[π₂]→ authenticated := second
    _ —[π₃]→ secure := third

/-- Three scalar-error constructions compose and add their bounds. -/
example {A B D E : C} {π₁ : D ⟶ E} {π₂ : B ⟶ D} {π₃ : A ⟶ B}
    {error₁ error₂ error₃ : ENNReal}
    {key : Specification Phi E} {insecure : Specification Phi D}
    {authenticated : Specification Phi B} {secure : Specification Phi A}
    (first : key —[π₁; error₁]→ insecure)
    (second : insecure —[π₂; error₂]→ authenticated)
    (third : authenticated —[π₃; error₃]→ secure) :
    key —[π₃ ≫ (π₂ ≫ π₁); error₁ + error₂ + error₃]→ secure :=
  calc
    key —[π₁; error₁]→ insecure := first
    _ —[π₂; error₂]→ authenticated := second
    _ —[π₃; error₃]→ secure := third

/-! ## Distance and admitted constructors -/

/-- The fibre triangle inequality adds two distance bounds. -/
example {A : C} {left middle right : Resource Phi A}
    {firstError secondError : ENNReal}
    (first : distance (Phi := Phi) left middle ≤ firstError)
    (second : distance (Phi := Phi) middle right ≤ secondError) :
    distance (Phi := Phi) left right ≤ firstError + secondError := by
  -- Apply the triangle inequality in the selected resource fibre.
  exact (ResourceAlgebra.distance_triangle left middle right).trans
    (add_le_add first second)

/-- Typed constructor classes compose when the supplied result classes
contain every required categorical composite. -/
example {A B D E : C}
    {firstConstructors : Set (D ⟶ E)}
    {secondConstructors : Set (B ⟶ D)}
    {thirdConstructors : Set (A ⟶ B)}
    {firstTwoConstructors : Set (B ⟶ E)}
    {allConstructors : Set (A ⟶ E)}
    (firstTwoAdmitted : ∀ second ∈ secondConstructors,
      ∀ first ∈ firstConstructors,
        second ≫ first ∈ firstTwoConstructors)
    (allAdmitted : ∀ third ∈ thirdConstructors,
      ∀ firstTwo ∈ firstTwoConstructors,
        third ≫ firstTwo ∈ allConstructors)
    {source : Specification Phi E} {firstMiddle : Specification Phi D}
    {secondMiddle : Specification Phi B} {target : Specification Phi A}
    (first : Specification.Constructible (Phi := Phi)
      firstConstructors source firstMiddle)
    (second : Specification.Constructible (Phi := Phi)
      secondConstructors firstMiddle secondMiddle)
    (third : Specification.Constructible (Phi := Phi)
      thirdConstructors secondMiddle target) :
    Specification.Constructible (Phi := Phi)
      allConstructors source target := by
  -- Compose the first two admitted constructor classes.
  have firstTwo := Specification.Constructible.serial
    firstTwoAdmitted first second
  -- Compose their result with the third admitted constructor class.
  exact Specification.Constructible.serial allAdmitted firstTwo third

/-! ## Multiparty construction -/

/-- Construction for every dishonest set composes pointwise. -/
example {n : Nat} {interfaces : Fin n → C}
    {π π' : Finite.ConverterTuple interfaces}
    {source middle target : Set (Fin n) →
      Specification Phi (Finite.interface n interfaces)}
    (first : ConstructsForAll (Phi := Phi) π source middle)
    (second : ConstructsForAll (Phi := Phi) π' middle target) :
    ConstructsForAll (Phi := Phi)
      (fun i => π' i ≫ π i) source target :=
  first.serial second

end ConstructiveCryptography.CalcChain.Tests
