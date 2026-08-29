/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ProofAutomation

/-!
# Typed construction-proof packaging test

This non-default module compares an ordinary proof structure with a local
proof-bearing class for one two-leg scalar-error construction.  Every choice
is a field of the indexed problem.  Both presentations delegate to the same
`ResourceAlgebra` serial theorem and introduce no second construction
semantics or ambient instance.
-/

open CategoryTheory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open AbstractCryptography.Categorical.ResourceAlgebra.Specification

namespace AbstractCryptography.Categorical.ResourceAlgebra.ConstructionWorkflow.Tests

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

/-- All explicit data of one two-leg scalar-error construction problem. -/
structure ConstructionProblem (Phi : Opposite C ⥤ Type w)
    (A B D : C) where
  source : Specification Phi D
  middle : Specification Phi B
  target : Specification Phi A
  innerConverter : B ⟶ D
  outerConverter : A ⟶ B
  innerError : ENNReal
  outerError : ENNReal

/-- Ordinary structure containing the two construction proofs. -/
structure ConstructionProof {A B D : C}
    (problem : ConstructionProblem Phi A B D) : Prop where
  inner : Constructs (Phi := Phi) problem.innerConverter problem.source
    (epsilonRelaxation (Phi := Phi) problem.innerError problem.middle)
  outer : Constructs (Phi := Phi) problem.outerConverter problem.middle
    (epsilonRelaxation (Phi := Phi) problem.outerError problem.target)

/-- The two proof fields imply the serial scalar-error construction.

Maurer--Renner 2016, Lemma 1 (printed p. 11): “This construction notion is
composable.”  Jost--Maurer 2020, Theorem 2 (printed p. 11): “First, the errors
just add up.” -/
theorem ConstructionProof.constructs {A B D : C}
    {problem : ConstructionProblem Phi A B D}
    (proof : ConstructionProof problem) :
    Constructs (Phi := Phi)
      (problem.outerConverter ≫ problem.innerConverter) problem.source
      (epsilonRelaxation (Phi := Phi)
        (problem.innerError + problem.outerError) problem.target) := by
  ac_compose proof.inner, proof.outer

/-- Local typeclass presentation with the same two explicit proof fields. -/
class ConstructionProofClass {A B D : C}
    (problem : ConstructionProblem Phi A B D) : Prop where
  inner : Constructs (Phi := Phi) problem.innerConverter problem.source
    (epsilonRelaxation (Phi := Phi) problem.innerError problem.middle)
  outer : Constructs (Phi := Phi) problem.outerConverter problem.middle
    (epsilonRelaxation (Phi := Phi) problem.outerError problem.target)

/-- A locally installed construction proof class uses the same serial theorem. -/
theorem ConstructionProofClass.constructs {A B D : C}
    (problem : ConstructionProblem Phi A B D)
    [proof : ConstructionProofClass problem] :
    Constructs (Phi := Phi)
      (problem.outerConverter ≫ problem.innerConverter) problem.source
      (epsilonRelaxation (Phi := Phi)
        (problem.innerError + problem.outerError) problem.target) := by
  ac_compose proof.inner, proof.outer

section Coexistence

variable {A B D : C}
variable (source : Specification Phi D)
variable (middleOne middleTwo : Specification Phi B)
variable (target : Specification Phi A)
variable (innerConverterOne innerConverterTwo : B ⟶ D)
variable (outerConverterOne outerConverterTwo : A ⟶ B)
variable (innerErrorOne outerErrorOne innerErrorTwo outerErrorTwo : ENNReal)

private def problemOne : ConstructionProblem Phi A B D where
  source := source
  middle := middleOne
  target := target
  innerConverter := innerConverterOne
  outerConverter := outerConverterOne
  innerError := innerErrorOne
  outerError := outerErrorOne

private def problemTwo : ConstructionProblem Phi A B D where
  source := source
  middle := middleTwo
  target := target
  innerConverter := innerConverterTwo
  outerConverter := outerConverterTwo
  innerError := innerErrorTwo
  outerError := outerErrorTwo

variable
  (innerOne : Constructs (Phi := Phi) innerConverterOne source
    (epsilonRelaxation (Phi := Phi) innerErrorOne middleOne))
  (outerOne : Constructs (Phi := Phi) outerConverterOne middleOne
    (epsilonRelaxation (Phi := Phi) outerErrorOne target))
  (innerTwo : Constructs (Phi := Phi) innerConverterTwo source
    (epsilonRelaxation (Phi := Phi) innerErrorTwo middleTwo))
  (outerTwo : Constructs (Phi := Phi) outerConverterTwo middleTwo
    (epsilonRelaxation (Phi := Phi) outerErrorTwo target))

private def proofOne : ConstructionProof
    (problemOne source middleOne target innerConverterOne outerConverterOne
      innerErrorOne outerErrorOne) where
  inner := innerOne
  outer := outerOne

private def proofTwo : ConstructionProof
    (problemTwo source middleTwo target innerConverterTwo outerConverterTwo
      innerErrorTwo outerErrorTwo) where
  inner := innerTwo
  outer := outerTwo

example :
    Constructs (Phi := Phi) (outerConverterOne ≫ innerConverterOne) source
      (epsilonRelaxation (Phi := Phi) (innerErrorOne + outerErrorOne)
        target) :=
  (proofOne source middleOne target innerConverterOne outerConverterOne
    innerErrorOne outerErrorOne innerOne outerOne).constructs

example :
    Constructs (Phi := Phi) (outerConverterTwo ≫ innerConverterTwo) source
      (epsilonRelaxation (Phi := Phi) (innerErrorTwo + outerErrorTwo)
        target) :=
  (proofTwo source middleTwo target innerConverterTwo outerConverterTwo
    innerErrorTwo outerErrorTwo innerTwo outerTwo).constructs

example :
    (Constructs (Phi := Phi) (outerConverterOne ≫ innerConverterOne) source
      (epsilonRelaxation (Phi := Phi) (innerErrorOne + outerErrorOne)
        target)) ∧
    (Constructs (Phi := Phi) (outerConverterTwo ≫ innerConverterTwo) source
      (epsilonRelaxation (Phi := Phi) (innerErrorTwo + outerErrorTwo)
        target)) := by
  letI : ConstructionProofClass
      (problemOne source middleOne target innerConverterOne outerConverterOne
        innerErrorOne outerErrorOne) := {
    inner := innerOne
    outer := outerOne
  }
  letI : ConstructionProofClass
      (problemTwo source middleTwo target innerConverterTwo outerConverterTwo
        innerErrorTwo outerErrorTwo) := {
    inner := innerTwo
    outer := outerTwo
  }
  constructor
  · exact ConstructionProofClass.constructs
      (problemOne source middleOne target innerConverterOne outerConverterOne
        innerErrorOne outerErrorOne)
  · exact ConstructionProofClass.constructs
      (problemTwo source middleTwo target innerConverterTwo outerConverterTwo
        innerErrorTwo outerErrorTwo)

/-- error: Fields missing: `outer` -/
#guard_msgs (substring := true) in
private def incompleteProof : ConstructionProof
    (problemOne source middleOne target innerConverterOne outerConverterOne
      innerErrorOne outerErrorOne) where
  inner := innerOne

end Coexistence

section MissingInstance

variable {A B D : C}

/-- error: failed to synthesize instance of type class
  ConstructionProofClass problem -/
#guard_msgs (substring := true) in
example (problem : ConstructionProblem Phi A B D) :
    Constructs (Phi := Phi)
      (problem.outerConverter ≫ problem.innerConverter) problem.source
      (epsilonRelaxation (Phi := Phi)
        (problem.innerError + problem.outerError) problem.target) :=
  ConstructionProofClass.constructs problem

end MissingInstance

end AbstractCryptography.Categorical.ResourceAlgebra.ConstructionWorkflow.Tests
