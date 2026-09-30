import ConstructiveCryptography.Specification.Game.Basic
import ConstructiveCryptography.Specification.Star

/-!
# Test bounds under converter-class closure

Test families closed under precomposition with admitted converters retain
their bounds on the converter-class closure of an ideal resource.
`testClosure` closes a selected family under this precomposition.
-/

namespace ConstructiveCryptography.Specification

universe u v w

variable {C : Type u} {X : Type v} {Bound : Type w}
variable [Monoid C] [MulAction C X]

/-- A test family is closed under precomposition with an admitted converter class. -/
def ClosedUnderConverterClass (converters : Submonoid C)
    (tests : Set (X → Bound)) : Prop :=
  ∀ test ∈ tests, ∀ converter ∈ converters,
    (fun resource => test (converter • resource)) ∈ tests

/-- A test bound on the ideal is inherited by its converter-class closure. -/
theorem star_subset_gameSpec [Preorder Bound]
    {converters : Submonoid C} {tests : Set (X → Bound)}
    {error : Bound} {ideal : X}
    (closed : ClosedUnderConverterClass converters tests)
    (idealAdmitted : ideal ∈ gameSpec tests error) :
    star converters {ideal} ⊆ gameSpec tests error := by
  -- Decompose the relaxed resource into its admitted converter and ideal.
  rintro resource ⟨converter, converterAdmitted, original, rfl, rfl⟩
  intro test testAdmitted
  -- Apply the ideal bound to the test precomposed with that converter.
  exact idealAdmitted (fun original => test (converter • original))
    (closed test testAdmitted converter converterAdmitted)

/-- Close a base test family under precomposition with one converter class. -/
def testClosure (converters : Submonoid C) (baseTests : Set (X → Bound)) :
    Set (X → Bound) :=
  {test | ∃ baseTest ∈ baseTests, ∃ converter ∈ converters,
    test = fun resource => baseTest (converter • resource)}

/-- Every base test belongs to its converter closure. -/
theorem subset_testClosure (converters : Submonoid C)
    (baseTests : Set (X → Bound)) :
    baseTests ⊆ testClosure converters baseTests := by
  intro test admitted
  -- The identity converter witnesses the original test.
  refine ⟨test, admitted, 1, converters.one_mem, ?_⟩
  funext resource
  rw [one_smul]

/-- Converter closure is closed under the same converter class. -/
theorem closedUnderConverterClass_testClosure (converters : Submonoid C)
    (baseTests : Set (X → Bound)) :
    ClosedUnderConverterClass converters (testClosure converters baseTests) := by
  intro test testAdmitted outer outerAdmitted
  rcases testAdmitted with ⟨baseTest, baseAdmitted, inner, innerAdmitted, rfl⟩
  -- Precomposition first attaches the outer argument, then the inner witness.
  refine ⟨baseTest, baseAdmitted, inner * outer,
    converters.mul_mem innerAdmitted outerAdmitted, ?_⟩
  funext resource
  rw [mul_smul]

end ConstructiveCryptography.Specification
