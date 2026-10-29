import ConstructiveCryptography.Specification.Game.Basic
import ConstructiveCryptography.Specification.Star

/-!
# Test bounds under converter-class closure

Test families closed under precomposition with admitted converters retain
their bounds on the converter-class closure of an ideal resource.
`testClosure` closes a selected family under this precomposition. Precomposing a test with a
converter `σ` (sigma) gives the test `R ↦ test (σ • R)`, which attaches `σ` and then runs
`test`:

```text
R ── attach σ ──▶ σ • R ── test ──▶ test (σ • R) : Bound
```

If every precomposed test is again admitted, a bound on `ideal` transfers to every
`σ • ideal` with `σ` admitted (`star_subset_gameSpec`). `testClosure converters baseTests`
is the set of all such precompositions of a base set; it contains the base set and is closed
under the same class.
-/

namespace ConstructiveCryptography.Specification

universe u v w

-- `C` is the type of converters, `X` the type of resources and `Bound` the type of test
-- values, as in `Specification.Game.Basic`.
variable {C : Type u} {X : Type v} {Bound : Type w}
-- `Monoid C` gives the identity `1` and serial `*`; `MulAction C X` attaches `σ : C` to
-- `R : X` as `σ • R`.
variable [Monoid C] [MulAction C X]

/-- A test family is closed under precomposition with an admitted converter class: for every
`test ∈ tests` and `σ ∈ converters`, the test `R ↦ test (σ • R)` belongs to `tests`. -/
def ClosedUnderConverterClass
    -- `converters` is the selected admitted class, a submonoid of `C`.
    (converters : Submonoid C)
    -- `tests` is a selected set of tests `X → Bound`.
    (tests : Set (X → Bound)) : Prop :=
  ∀ test ∈ tests, ∀ converter ∈ converters,
    (fun resource => test (converter • resource)) ∈ tests

/-- A test bound on the ideal is inherited by its converter-class closure, at the same
threshold: every `σ • ideal` with `σ ∈ converters` meets `gameSpec tests error`, since
`test (σ • ideal)` is the value at `ideal` of the admitted test `R ↦ test (σ • R)`. -/
lemma star_subset_gameSpec
    -- Only this result orders `Bound`; smaller thresholds are stronger guarantees.
    [Preorder Bound]
    -- `converters` is the admitted class and `tests` the selected tests.
    {converters : Submonoid C} {tests : Set (X → Bound)}
    -- `error : Bound` is the threshold and `ideal : X` the ideal resource.
    {error : Bound} {ideal : X}
    -- `closed` says `tests` is closed under precomposition with every converter in
    -- `converters`.
    (closed : ClosedUnderConverterClass converters tests)
    -- `idealAdmitted` says `test ideal ≤ error` for every `test ∈ tests`.
    (idealAdmitted : ideal ∈ gameSpec tests error) :
    star converters {ideal} ⊆ gameSpec tests error := by
  -- Decompose the relaxed resource into its admitted converter and ideal.
  rintro resource ⟨converter, converterAdmitted, original, rfl, rfl⟩
  intro test testAdmitted
  -- Apply the ideal bound to the test precomposed with that converter.
  exact idealAdmitted (fun original => test (converter • original))
    (closed test testAdmitted converter converterAdmitted)

/-- Close a base test family under precomposition with one converter class:

```text
testClosure converters baseTests
  = {R ↦ baseTest (σ • R) | baseTest ∈ baseTests, σ ∈ converters}
```

It is generated from the selected base set and class only; it is not asserted to equal any
class of efficient tests. -/
def testClosure
    -- `converters` is the class closed over; `baseTests` is an arbitrary set of tests.
    (converters : Submonoid C) (baseTests : Set (X → Bound)) :
    Set (X → Bound) :=
  {test | ∃ baseTest ∈ baseTests, ∃ converter ∈ converters,
    test = fun resource => baseTest (converter • resource)}

/-- Every base test belongs to its converter closure, as its precomposition with the identity
converter `1 ∈ converters`. -/
lemma subset_testClosure (converters : Submonoid C)
    (baseTests : Set (X → Bound)) :
    baseTests ⊆ testClosure converters baseTests := by
  intro test admitted
  -- The identity converter witnesses the original test.
  refine ⟨test, admitted, 1, converters.one_mem, ?_⟩
  funext resource
  rw [one_smul]

/-- Converter closure is closed under the same converter class. Precomposing
`R ↦ baseTest (inner • R)` with an admitted `outer` gives

```text
R ↦ baseTest (inner • (outer • R)) = baseTest ((inner * outer) • R)     (mul_smul)
```

and `inner * outer ∈ converters`. -/
lemma closedUnderConverterClass_testClosure (converters : Submonoid C)
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
