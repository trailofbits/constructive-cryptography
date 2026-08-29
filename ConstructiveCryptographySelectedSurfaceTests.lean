/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import ConstructiveCryptography
import AbstractCryptography.Tactics.ProofAutomation

/-!
# Constructive Cryptography selected-surface test

The two explicit bounds below become typed scalar-error construction
judgments over the sole `ResourceAlgebra` surface.  The test assembles no
interface carrier and installs no action or parallel instance.
-/

open CategoryTheory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open AbstractCryptography.Categorical.ResourceAlgebra.Specification

namespace ConstructiveCryptography.SelectedSurface.Tests

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

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
      ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({attach (Phi := Phi) filter ideal} : Specification Phi A))) ∧
    (Constructs (Phi := Phi) adversarialConverter
      ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({attach (Phi := Phi) simulator ideal} : Specification Phi A))) := by
  constructor
  · ac_construct using availability
  · ac_construct using security

end ConstructiveCryptography.SelectedSurface.Tests
