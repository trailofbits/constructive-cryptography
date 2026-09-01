/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import ConstructiveCryptography
import ConstructiveCryptography.Tactics.ProofAutomation

/-!
# Constructive Cryptography selected-surface test

The two explicit bounds below become typed scalar-error construction
judgments over the sole `ResourceAlgebra` surface.  The test assembles no
interface carrier and installs no action or parallel instance.
-/

open CategoryTheory
open ConstructiveCryptography.Categorical
open ConstructiveCryptography.Categorical.ResourceAlgebra
open ConstructiveCryptography.Categorical.ResourceAlgebra.Specification

namespace ConstructiveCryptography.Tests.SelectedSurface

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

/-- Scalar approximate construction is definitionally exact construction into
the selected epsilon relaxation; it is not a second construction relation. -/
example {A B : C} (converter : A ⟶ B) (error : ENNReal)
    (source : ResourceAlgebra.Specification Phi B) (target : ResourceAlgebra.Specification Phi A) :
    ResourceAlgebra.Specification.ApproximatelyConstructs (Phi := Phi) converter error
        source target ↔
      ResourceAlgebra.Specification.Constructs (Phi := Phi) converter source
        (epsilonRelaxation (Phi := Phi) error target) :=
  Iff.rfl

example {A B : C}
    {availableConverter adversarialConverter : A ⟶ B}
    {filter simulator : A ⟶ A}
    {real : Resource Phi B} {ideal : Resource Phi A} {error : ENNReal}
    (availability : distance (Phi := Phi)
      (attach (Phi := Phi) availableConverter real)
      (attach (Phi := Phi) filter ideal) ≤ error)
    (security : distance (Phi := Phi)
      (attach (Phi := Phi) adversarialConverter real)
      (attach (Phi := Phi) simulator ideal) ≤ error) :
    (Constructs (Phi := Phi) availableConverter
      ({real} : ResourceAlgebra.Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({attach (Phi := Phi) filter ideal} : ResourceAlgebra.Specification Phi A))) ∧
    (Constructs (Phi := Phi) adversarialConverter
      ({real} : ResourceAlgebra.Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({attach (Phi := Phi) simulator ideal} : ResourceAlgebra.Specification Phi A))) := by
  constructor
  · cc_construct using availability
  · cc_construct using security

end ConstructiveCryptography.Tests.SelectedSurface
