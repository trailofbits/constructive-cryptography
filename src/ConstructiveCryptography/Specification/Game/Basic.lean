import ConstructiveCryptography.Specification.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Nat

/-!
# Specifications defined by test bounds

`gameSpec tests error` consists of the resources whose admitted tests are
bounded by `error`. The test values belong to a selected preordered type.
`MonotoneTestFamily` indexes increasing sets of tests by natural numbers.
-/

namespace ConstructiveCryptography.Specification

universe u v

variable {X : Type u} {Bound : Type v} [Preorder Bound]

/-- Resources on which every admitted test is bounded by `error`.

Jost, Section 2.2.1 (printed p. 15): “the set R of objects satisfying that
property”. Here the property is the repository's selected family of test bounds. -/
def gameSpec (tests : Set (X → Bound)) (error : Bound) : Specification X :=
  {resource | ∀ test ∈ tests, test resource ≤ error}

/-- A larger error bound gives a weaker game specification. -/
theorem gameSpec_mono {tests : Set (X → Bound)}
    {error error' : Bound} (included : error ≤ error') :
    gameSpec tests error ⊆ gameSpec tests error' :=
  fun _ admitted test testAdmitted =>
    le_trans (admitted test testAdmitted) included

/-- More admitted tests give a stronger game specification. -/
theorem gameSpec_antitone {tests tests' : Set (X → Bound)}
    (included : tests ⊆ tests') {error : Bound} :
    gameSpec tests' error ⊆ gameSpec tests error :=
  fun _ admitted test testAdmitted => admitted test (included testAdmitted)

/-- An increasing family of admitted tests. -/
structure MonotoneTestFamily (X : Type u) (Bound : Type v) where
  /-- The test family at each index. -/
  tests : Nat → Set (X → Bound)
  /-- A higher index admits every test from a lower index. -/
  monotone : Monotone tests

/-- A bound at a higher index implies the same bound at every lower index. -/
theorem MonotoneTestFamily.mem_gameSpec_of_le
    (family : MonotoneTestFamily X Bound)
    {lower higher : Nat} (ordered : lower ≤ higher)
    {error : Bound} {resource : X}
    (admitted : resource ∈ gameSpec (family.tests higher) error) :
    resource ∈ gameSpec (family.tests lower) error :=
  gameSpec_antitone (family.monotone ordered) admitted

end ConstructiveCryptography.Specification
