/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ConstructiveCryptography

/-!
# Selected Constructive Cryptography resource-algebra surface

This module checks the carrier-independent typed surface directly:
attachment, distance, exact and approximate construction, ordered parallel,
and filtered endpoints. It installs no concrete resource carrier and assumes
no symmetry.
-/

namespace ConstructiveCryptography.Tests.ResourceAlgebra

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ConstructiveCryptography.Categorical
open ConstructiveCryptography.Categorical.ResourceAlgebra
open ConstructiveCryptography.Categorical.ResourceAlgebra.Specification

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

/-- Abstract converter attachment uses the heterogeneous action `•`. -/
example {A B : C} (converter : A ⟶ B) (resource : Resource Phi B) :
    (converter • resource : Resource Phi A) =
      attach (Phi := Phi) converter resource :=
  rfl

/-- A singleton scalar-error construction is exactly its resource-distance
bound. -/
example {A B : C} {converter : A ⟶ B}
    {real : Resource Phi B} {ideal : Resource Phi A} {error : ENNReal}
    (close : distance (Phi := Phi) (attach (Phi := Phi) converter real)
      ideal ≤ error) :
    Constructs (Phi := Phi) converter
      ({real} : ResourceAlgebra.Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({ideal} : ResourceAlgebra.Specification Phi A)) :=
  constructs_singleton_epsilonRelaxation_iff.mpr close

/-- Attachment is non-expanding in the selected fibre distances. -/
example {A B : C} (converter : A ⟶ B)
    (left right : Resource Phi B) :
    distance (Phi := Phi) (attach (Phi := Phi) converter left)
        (attach (Phi := Phi) converter right) ≤
      distance (Phi := Phi) left right :=
  distance_attach_le converter left right

/-- Exact constructions compose componentwise in ordered parallel. -/
example {A A' B B' : C}
    {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : ResourceAlgebra.Specification Phi A'}
    {leftTarget : ResourceAlgebra.Specification Phi A}
    {rightSource : ResourceAlgebra.Specification Phi B'}
    {rightTarget : ResourceAlgebra.Specification Phi B}
    (leftConstruction : Constructs (Phi := Phi) leftConverter
      leftSource leftTarget)
    (rightConstruction : Constructs (Phi := Phi) rightConverter
      rightSource rightTarget) :
    Constructs (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
      (Specification.parallel (Phi := Phi) leftSource rightSource)
      (Specification.parallel (Phi := Phi) leftTarget rightTarget) :=
  leftConstruction.parallel rightConstruction

/-- Ordered resource parallel reassociates only through the selected routed
associator. -/
example {A B D : C} (left : Resource Phi A) (middle : Resource Phi B)
    (right : Resource Phi D) :
    attach (Phi := Phi) (α_ A B D).inv
        (parallel (Phi := Phi) (parallel (Phi := Phi) left middle) right) =
      parallel (Phi := Phi) left
        (parallel (Phi := Phi) middle right) :=
  parallel_assoc left middle right

/-- The routed left unitor removes the selected dummy resource. -/
example {A : C} (resource : Resource Phi A) :
    attach (Phi := Phi) (λ_ A).inv
        (parallel (Phi := Phi) (dummy (C := C) (Phi := Phi)) resource) =
      resource :=
  parallel_dummy_left resource

/-- The routed right unitor removes the selected dummy resource. -/
example {A : C} (resource : Resource Phi A) :
    attach (Phi := Phi) (ρ_ A).inv
        (parallel (Phi := Phi) resource
          (dummy (C := C) (Phi := Phi))) = resource :=
  parallel_dummy_right resource

/-- A simulator distance bound gives the corresponding construction between
filtered endpoints. -/
example {A : C}
    {converters : EndoFamily (Opposite.op A)}
    {converter sourceFilter targetFilter simulator : CategoryTheory.End A}
    {real ideal : Resource Phi A} {error : ENNReal}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (simulatorAdmitted : simulator.op ∈ converters)
    (close : distance (Phi := Phi)
      (attach (Phi := Phi) converter
        (attach (Phi := Phi) sourceFilter real))
      (attach (Phi := Phi) simulator
        (attach (Phi := Phi) targetFilter ideal)) ≤ error) :
    Constructs (Phi := Phi) converter
      (filteredAt (Phi := Phi) converters sourceFilter real)
      (epsilonRelaxation (Phi := Phi) error
        (filteredAt (Phi := Phi) converters targetFilter ideal)) :=
  filteredAt_constructs_epsilonRelaxation_of_distance_le
    commutes simulatorAdmitted close

end ConstructiveCryptography.Tests.ResourceAlgebra
