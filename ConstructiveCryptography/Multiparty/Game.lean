/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
-/
import ConstructiveCryptography.Multiparty.Basic

set_option autoImplicit false

/-!
# Test-defined multiparty specifications

This module contains repository-level specification constructors used by
applications. They are separate from the Liu--Maurer multiparty construction
definitions in `ConstructiveCryptography.Multiparty.Basic`.
-/

namespace ConstructiveCryptography.Multiparty

open CategoryTheory
open ConstructiveCryptography.Categorical
open ConstructiveCryptography.Categorical.ResourceAlgebra
open scoped ENNReal

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-- Resources on which every admitted test is bounded by `error`. This is a
repository-level specification constructor, not a Liu--Maurer definition. -/
def gameSpec {A : C} (tests : Set (Resource Phi A → ENNReal))
    (error : ENNReal) : ResourceAlgebra.Specification Phi A :=
  {resource | ∀ test ∈ tests, test resource ≤ error}

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A larger error bound gives a weaker game specification. -/
theorem gameSpec_mono {A : C} {tests : Set (Resource Phi A → ENNReal)}
    {error error' : ENNReal} (included : error ≤ error') :
    gameSpec (Phi := Phi) tests error ⊆ gameSpec (Phi := Phi) tests error' :=
  fun _ admitted test testAdmitted =>
    le_trans (admitted test testAdmitted) included

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- More admitted tests give a stronger game specification. -/
theorem gameSpec_antitone {A : C}
    {tests tests' : Set (Resource Phi A → ENNReal)}
    (included : tests ⊆ tests') {error : ENNReal} :
    gameSpec (Phi := Phi) tests' error ⊆ gameSpec (Phi := Phi) tests error :=
  fun _ admitted test testAdmitted =>
    admitted test (included testAdmitted)

/-- A test family is closed under precomposition with an admitted converter
class. -/
def ClosedUnderConverterClass {A : C}
    (converters : EndoFamily (Opposite.op A))
    (tests : Set (Resource Phi A → ENNReal)) : Prop :=
  ∀ test ∈ tests, ∀ converter : CategoryTheory.End A,
    converter.op ∈ converters →
      (fun resource => test (attach (Phi := Phi) converter resource)) ∈ tests

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A game bound on the ideal is inherited by its joint-converter closure. -/
theorem zStar_subset_gameSpec {I : Type*} {A : C}
    {converters : Set I → EndoFamily (Opposite.op A)}
    {dishonest : Set I} {tests : Set (Resource Phi A → ENNReal)}
    {error : ENNReal} {ideal : Resource Phi A}
    (closed : ClosedUnderConverterClass (Phi := Phi)
      (converters dishonest) tests)
    (idealAdmitted : ideal ∈ gameSpec (Phi := Phi) tests error) :
    zStar (Phi := Phi) converters dishonest
        ({ideal} : ResourceAlgebra.Specification Phi A) ⊆
      gameSpec (Phi := Phi) tests error := by
  intro resource relaxed
  -- Decompose membership in the joint-converter closure.
  rcases Specification.mem_star_iff.mp relaxed with
    ⟨converter, converterAdmitted, original,
      originalAdmitted, equation⟩
  have originalEquals : original = ideal :=
    Set.mem_singleton_iff.mp originalAdmitted
  subst original
  rw [← equation]
  intro test testAdmitted
  -- Apply the ideal bound to the test precomposed with the admitted converter.
  exact idealAdmitted
    (fun original => test (attach (Phi := Phi) converter original))
    (closed test testAdmitted converter converterAdmitted)

/-- Close a base test family under precomposition with one converter class. -/
noncomputable def testClosure {A : C}
    (converters : EndoFamily (Opposite.op A))
    (baseTests : Set (Resource Phi A → ENNReal)) :
    Set (Resource Phi A → ENNReal) :=
  {test | ∃ baseTest ∈ baseTests,
    ∃ converter : CategoryTheory.End A,
      converter.op ∈ converters ∧
        test = fun resource =>
          baseTest (attach (Phi := Phi) converter resource)}

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Every base test belongs to its converter closure. -/
theorem subset_testClosure {A : C}
    (converters : EndoFamily (Opposite.op A))
    (baseTests : Set (Resource Phi A → ENNReal)) :
    baseTests ⊆ testClosure (Phi := Phi) converters baseTests := by
  intro test admitted
  -- The identity converter witnesses the original test.
  refine ⟨test, admitted, 𝟙 A, converters.one_mem, ?_⟩
  funext resource
  rw [attach_identity]

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Converter closure is closed under the same converter class. -/
theorem closedUnderConverterClass_testClosure {A : C}
    (converters : EndoFamily (Opposite.op A))
    (baseTests : Set (Resource Phi A → ENNReal)) :
    ClosedUnderConverterClass (Phi := Phi) converters
      (testClosure (Phi := Phi) converters baseTests) := by
  intro test testAdmitted outer outerAdmitted
  rcases testAdmitted with
    ⟨baseTest, baseAdmitted, inner, innerAdmitted, rfl⟩
  -- Compose the two admitted converters in function-application order.
  refine ⟨baseTest, baseAdmitted, inner ≫ outer, ?_, ?_⟩
  · change (inner ≫ outer).op ∈ converters
    simpa using converters.mul_mem innerAdmitted outerAdmitted
  · funext resource
    rw [attach_serial]

/-- An ordered family of game-test sets. This repository-level structure
packages the monotonicity used by application-specific test families. -/
structure MonotoneTestFamily {A : C} where
  /-- The test family at each index. -/
  tests : Nat → Set (Resource Phi A → ENNReal)
  /-- A higher level admits every test from a lower level. -/
  monotone : Monotone tests

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A bound at a higher index implies the same bound at every lower index. -/
theorem MonotoneTestFamily.mem_gameSpec_of_le {A : C}
    (family : MonotoneTestFamily (Phi := Phi))
    {lower higher : Nat} (ordered : lower ≤ higher)
    {error : ENNReal} {resource : Resource Phi A}
    (admitted : resource ∈
      gameSpec (Phi := Phi) (family.tests higher) error) :
    resource ∈ gameSpec (Phi := Phi) (family.tests lower) error :=
  gameSpec_antitone (family.monotone ordered) admitted

end ConstructiveCryptography.Multiparty
