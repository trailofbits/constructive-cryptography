import ConstructiveCryptography.Specification.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Nat

/-!
# Specifications defined by test bounds

`gameSpec tests error` consists of the resources whose admitted tests are
bounded by `error`. The test values belong to a selected preordered type.
`MonotoneTestFamily` indexes increasing sets of tests by natural numbers. A smaller threshold
is a stronger resource guarantee; this does not reverse the solver's performance order, since
bounding a solver's success more tightly is a stronger guarantee about the resource. Distance
budgets in `Specification.Metric` are a separate, `ENNReal`-valued notion.

```text
gameSpec tests error = {resource | ∀ test ∈ tests, test resource ≤ error}
```

The specification shrinks as `error` decreases (`gameSpec_mono`) or as tests are added
(`gameSpec_antitone`). With no tests it admits every resource.
-/

namespace ConstructiveCryptography.Specification

universe u v

variable
    -- `X` is an arbitrary type of resources.
    {X : Type u}
    -- `Bound` is the type of test values, preordered so that a value `≤ error` is acceptable;
    -- no arithmetic, bottom element, boundedness or totality is assumed.
    {Bound : Type v} [Preorder Bound]

/-- Resources on which every admitted test is bounded by `error`: `R` meets
`gameSpec tests error` when `test R ≤ error` for every `test ∈ tests`, uniformly over the
tests, each evaluated on the resource alone.

Jost, Section 2.2.1 (printed p. 15): “the set R of objects satisfying that
property”. Here the property is the repository's selected family of test bounds. -/
def gameSpec
    -- `tests` is a selected set of tests `test : X → Bound`, each valuing a resource, e.g. a
    -- distinguisher's advantage; no efficiency or closure condition is imposed.
    (tests : Set (X → Bound))
    -- `error : Bound` is the threshold every selected test must meet.
    (error : Bound) : Specification X :=
  {resource | ∀ test ∈ tests, test resource ≤ error}

/-- A larger error bound gives a weaker game specification: `error ≤ error'` in `Bound`
implies `gameSpec tests error ⊆ gameSpec tests error'`, by transitivity of the preorder. -/
lemma gameSpec_mono {tests : Set (X → Bound)}
    {error error' : Bound} (included : error ≤ error') :
    gameSpec tests error ⊆ gameSpec tests error' :=
  fun _ admitted test testAdmitted =>
    le_trans (admitted test testAdmitted) included

/-- More admitted tests give a stronger game specification: `tests ⊆ tests'` implies
`gameSpec tests' error ⊆ gameSpec tests error`, at the same threshold `error`. -/
lemma gameSpec_antitone {tests tests' : Set (X → Bound)}
    (included : tests ⊆ tests') {error : Bound} :
    gameSpec tests' error ⊆ gameSpec tests error :=
  fun _ admitted test testAdmitted => admitted test (included testAdmitted)

/-- An increasing family of admitted tests, so the specifications `gameSpec (tests n) error`
shrink as `n` grows. The family is selected by the user; no asymptotic notion of efficiency or
negligibility is attached to it. -/
structure MonotoneTestFamily
    -- `X` is the type of resources and `Bound` the type of test values; no order on `Bound`
    -- is needed, only inclusion of test sets.
    (X : Type u) (Bound : Type v) where
  /-- The tests admitted at level `n`, for instance tests with resource budget `n`. -/
  tests : Nat → Set (X → Bound)
  /-- A higher index admits every test from a lower index: `m ≤ n → tests m ⊆ tests n`. -/
  monotone : Monotone tests

/-- A bound at a higher index implies the same bound at every lower index, because the lower
test set is a subset. -/
lemma MonotoneTestFamily.mem_gameSpec_of_le
    (family : MonotoneTestFamily X Bound)
    -- `ordered` says index `lower` is at most `higher`, so `family.tests lower` is smaller.
    {lower higher : Nat} (ordered : lower ≤ higher)
    {error : Bound} {resource : X}
    -- `admitted`: every test admitted at `higher` is at most `error` on `resource`.
    (admitted : resource ∈ gameSpec (family.tests higher) error) :
    resource ∈ gameSpec (family.tests lower) error :=
  gameSpec_antitone (family.monotone ordered) admitted

end ConstructiveCryptography.Specification
