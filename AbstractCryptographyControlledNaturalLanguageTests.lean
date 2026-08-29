/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ControlledNaturalLanguage

/-!
# Typed Abstract Cryptography controlled-language tests

Each sentence below lowers to the deterministic `ResourceAlgebra` proof
frontend. The tests use ordered typed converters through `ResourceAlgebra`.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open AbstractCryptography.Categorical.ResourceAlgebra.Specification
open scoped CryptoControlledNaturalLanguage

namespace AbstractCryptography.Categorical.ResourceAlgebra.ControlledNaturalLanguage.Tests

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

example {A B : C} (converter : A ⟶ B)
    (real : Resource Phi B) (ideal : Resource Phi A)
    (attachmentEquation : attach (Phi := Phi) converter real = ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  The construction follows from attachmentEquation

example {A B : C} (converter : A ⟶ B)
    (real : Resource Phi B) (ideal : Resource Phi A) (error : ENNReal)
    (distanceBound : distance (Phi := Phi)
      (attach (Phi := Phi) converter real) ideal ≤ error) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({ideal} : Specification Phi A)) := by
  The construction follows from distanceBound

example {A B : C} {left right : A ⟶ B}
    (resource : Resource Phi B) (converterEquation : left = right) :
    attach (Phi := Phi) left resource =
      attach (Phi := Phi) right resource := by
  The equality follows from converterEquation

example {A B : C} {left right : A ⟶ B}
    {source : Specification Phi B} {target : Specification Phi A}
    (converterEquation : left = right)
    (construction : Constructs (Phi := Phi) left source target) :
    Constructs (Phi := Phi) right source target := by
  Replacing the converter in construction using converterEquation,
    we obtain the required construction

example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (epsilonRelaxation (Phi := Phi) innerError middle))
    (outer : Constructs (Phi := Phi) first middle
      (epsilonRelaxation (Phi := Phi) outerError target)) :
    Constructs (Phi := Phi) (first ≫ second) source
      (epsilonRelaxation (Phi := Phi) (innerError + outerError) target) := by
  The construction follows by composing inner and outer

example {A B : C} (converter : A ⟶ B)
    (real : Resource Phi B) (ideal : Resource Phi A) (error : ENNReal)
    (distanceBound : distance (Phi := Phi)
      (attach (Phi := Phi) converter real) ideal ≤ error) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({ideal} : Specification Phi A)) := by
  We have construction :
      Constructs (Phi := Phi) converter ({real} : Specification Phi B)
        (epsilonRelaxation (Phi := Phi) error
          ({ideal} : Specification Phi A)) by
    The construction follows from distanceBound
  The construction follows from construction

example {A B : C} (converter : A ⟶ B)
    (real : Resource Phi B) (ideal : Resource Phi A)
    (existingConstruction :
      Constructs (Phi := Phi) converter ({real} : Specification Phi B)
        ({ideal} : Specification Phi A)) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  We have construction :
      Constructs (Phi := Phi) converter ({real} : Specification Phi B)
        ({ideal} : Specification Phi A) from existingConstruction
  The construction follows from construction

example {A B : C} (converter : A ⟶ B) (simulator : A ⟶ A)
    (converters : EndoFamily (Opposite.op A))
    (real : Resource Phi B) (ideal : Resource Phi A) (error : ENNReal)
    (simulatorMembership : simulator.op ∈ converters)
    (distanceBound : distance (Phi := Phi)
      (attach (Phi := Phi) converter real)
      (attach (Phi := Phi) simulator ideal) ≤ error) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        (star (Phi := Phi) converters
          ({ideal} : Specification Phi A))) := by
  We use simulator to prove the construction
  · exact simulatorMembership
  · exact distanceBound

example {A A' B : C} {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    (context : Specification Phi B)
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) := by
  With context as the right parallel context,
    the construction follows from construction

example {A B B' : C} {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    (context : Specification Phi A)
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) := by
  With context as the left parallel context,
    the construction follows from construction

example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source middle)
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source target := by
  The construction follows by composing
    inner ("The inner converter reaches the intermediate specification.") and
    outer ("The outer converter reaches the target specification.")

/-! Sentence traces identify the mathematical step after its backend succeeds. -/

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.follows_from -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example {A B : C} (converter : A ⟶ B)
    (real : Resource Phi B) (ideal : Resource Phi A)
    (equation : attach (Phi := Phi) converter real = ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  The construction follows from equation

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.equality.follows_from -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example {A B : C} {left right : A ⟶ B}
    (resource : Resource Phi B) (equation : left = right) :
    attach (Phi := Phi) left resource = attach (Phi := Phi) right resource := by
  The equality follows from equation

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.replace_converter -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example {A B : C} {left right : A ⟶ B}
    {source : Specification Phi B} {target : Specification Phi A}
    (equation : left = right)
    (construction : Constructs (Phi := Phi) left source target) :
    Constructs (Phi := Phi) right source target := by
  Replacing the converter in construction using equation,
    we obtain the required construction

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.by_composition -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source middle)
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source target := by
  The construction follows by composing inner and outer

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.argument.named_fact -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example (proposition : Prop) (proof : proposition) : proposition := by
  We have intermediateFact : proposition by
    exact proof
  exact intermediateFact

/-- error: ac_construct could not use the supplied equality, distance bound, or pointwise proof -/
#guard_msgs (substring := true) in
example (irrelevantFact : True) : True := by
  The construction follows from irrelevantFact

/-- error: ac_transport expected attachment equality or construction equivalence induced by the supplied converter equality -/
#guard_msgs (substring := true) in
example {A B : C} {left right : A ⟶ B}
    (converterEquation : left = right) : True := by
  The equality follows from converterEquation

/-- error: ac_transport could not replace the converter in the supplied construction using the supplied equality -/
#guard_msgs (substring := true) in
example {A B : C} {left right : A ⟶ B}
    (converterEquation : left = right) (irrelevantFact : True) : True := by
  Replacing the converter in irrelevantFact using converterEquation,
    we obtain the required construction

/-- error: ac_compose expected two composable typed construction proofs -/
#guard_msgs (substring := true) in
example (firstFact secondFact : True) : True := by
  The construction follows by composing firstFact and secondFact

/-- error: expected `construction` or `equality` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (fact : True) : True := by
  The result follows from fact

/-- error: expected `follows` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (fact : True) : True := by
  The construction follow from fact

/-- error: expected `composing` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (firstFact secondFact : True) : True := by
  The construction follows by combining firstFact and secondFact

/-- error: expected `left` or `right` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (context construction : Prop) : True := by
  With context as the middle parallel context,
    the construction follows from construction

/-- error: expected `use` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example {A : C} (simulator : A ⟶ A) : True := by
  We choose simulator to prove the construction

end AbstractCryptography.Categorical.ResourceAlgebra.ControlledNaturalLanguage.Tests
