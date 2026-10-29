import ConstructiveCryptography.Construction.Defs

set_option autoImplicit false

/-!
# Laws of constructibility

Notation as in `ConstructiveCryptography.Construction.Defs`; `constructors` is MR16's `Γ`.

* `Constructible.of_imp`, `Unconstructible.of_imp`: a supplied implication between two
  judgments, for each admitted `γ`, transfers constructibility forward and impossibility
  backward (MR16, Section 2.3).
* `Constructible.mono_constructors`, `Unconstructible.mono_constructors`: admitting more
  constructors can only add constructions, and so can only remove impossibilities.
* `Constructible.serial`: MR16's serial composition `R —γ→ S ∧ S —γ′→ T ⇒ R —γ′∘γ→ T`, with
  the judgment law and the class closure as explicit hypotheses:

```text
  source ──inner ∈ innerClass──▶ middle ──outer ∈ outerClass──▶ target
     └──────────── compose outer inner ∈ resultClass ─────────────┘
```

No category, composition or efficiency structure is assumed on constructors; closure of the
admitted classes under composition is the explicit hypothesis `closed`.
-/

namespace ConstructiveCryptography.Construction

universe u v w u' v' w'

variable
    -- `Constructor` is the opaque type of constructors `γ`; `Source` contains the objects `R`
    -- constructed from and `Target` the objects `S` constructed.
    {Constructor : Type u} {Source : Type v} {Target : Type w}
-- `judgment γ R S` is the statement “`γ : Constructor` constructs `S : Target` from
-- `R : Source`”, MR16's `R —γ→ S`.
variable {judgment : Constructor → Source → Target → Prop}

/-- A consequence of each admitted judgment is constructible with the same
constructor. MR16, Section 2.3 (printed p. 5):
“R —γ→ S =⇒ R′ —γ→ S′ if R′ ⊆ R and S ⊆ S′.”
For arbitrary judgments the implication replaces the inclusions and is supplied explicitly. -/
lemma Constructible.of_imp
    -- `Source'` and `Target'` are the possibly different carriers of the new pair `R′`, `S′`.
    {Source' : Type v'} {Target' : Type w'}
    -- `judgment' γ R′ S′` is a second judgment over the same `Constructor` type.
    {judgment' : Constructor → Source' → Target' → Prop}
    -- `constructors` is the admitted class Γ (Gamma), the same on both sides.
    {constructors : Set Constructor}
    -- `source : Source` and `target : Target` are the original pair `R`, `S`.
    {source : Source} {target : Target}
    -- `source' : Source'` and `target' : Target'` are the new pair `R′`, `S′`.
    {source' : Source'} {target' : Target'}
    -- `implication` says that for each admitted `γ`, `R —γ→ S` implies `R′ —γ→ S′`; in MR16
    -- this follows from `R′ ⊆ R` and `S ⊆ S′`.
    (implication : ∀ constructor ∈ constructors,
      judgment constructor source target → judgment' constructor source' target')
    -- `construction` gives some `γ ∈ constructors` with `R —γ→ S`; that `γ` also gives
    -- `R′ —γ→ S′`.
    (construction : Constructible judgment constructors source target) :
    Constructible judgment' constructors source' target' := by
  -- Retain the admitted constructor and apply the judgment implication.
  obtain ⟨constructor, admitted, constructs⟩ := construction
  exact ⟨constructor, admitted, implication constructor admitted constructs⟩

/-- Enlarging the admitted constructor class preserves constructibility: if
`constructors ⊆ constructors'` and some `γ ∈ constructors` constructs `target` from `source`,
the same `γ` witnesses constructibility relative to the larger class `constructors'`. -/
lemma Constructible.mono_constructors
    -- `constructors` is the smaller admitted class and `constructors'` the larger one.
    {constructors constructors' : Set Constructor}
    -- `included` is the inclusion `constructors ⊆ constructors'`; `source`, `target` are
    -- `R`, `S`.
    (included : constructors ⊆ constructors') {source : Source} {target : Target}
    -- `construction` gives some `γ ∈ constructors` with `R —γ→ S`.
    (construction : Constructible judgment constructors source target) :
    Constructible judgment constructors' source target := by
  -- The same constructor belongs to the larger class.
  obtain ⟨constructor, admitted, constructs⟩ := construction
  exact ⟨constructor, included admitted, constructs⟩

/-- An impossibility result pulls back along a judgment implication.

MR16, Section 2.3 (printed p. 6):
“R ↛ S =⇒ R′ ↛ S′ if R ⊆ R′ and S′ ⊆ S.”
The constructor class is the same on both sides. -/
lemma Unconstructible.of_imp
    -- `Source'` and `Target'` are the possibly different carriers of the new pair `R′`, `S′`.
    {Source' : Type v'} {Target' : Type w'}
    -- `judgment' γ R′ S′` is a second judgment over the same `Constructor` type.
    {judgment' : Constructor → Source' → Target' → Prop}
    -- `constructors` is the admitted class Γ (Gamma), the same on both sides.
    {constructors : Set Constructor}
    -- `source : Source` and `target : Target` are the original pair `R`, `S`.
    {source : Source} {target : Target}
    -- `source' : Source'` and `target' : Target'` are the new pair `R′`, `S′`.
    {source' : Source'} {target' : Target'}
    -- `implication` runs backwards: for each admitted `γ`, `R′ —γ→ S′` implies `R —γ→ S`;
    -- in MR16 this follows from `R ⊆ R′` and `S′ ⊆ S`.
    (implication : ∀ constructor ∈ constructors,
      judgment' constructor source' target' → judgment constructor source target)
    -- `impossible` says no `γ ∈ constructors` gives `R —γ→ S`; hence none gives `R′ —γ→ S′`.
    (impossible : Unconstructible judgment constructors source target) :
    Unconstructible judgment' constructors source' target' :=
  fun construction => impossible (construction.of_imp implication)

/-- Non-constructibility against a class implies non-constructibility against
each smaller class: if `constructors ⊆ constructors'` and no `γ ∈ constructors'` constructs
`target` from `source`, then no `γ ∈ constructors` does. -/
lemma Unconstructible.mono_constructors
    -- `constructors` is the smaller admitted class and `constructors'` the larger one.
    {constructors constructors' : Set Constructor}
    -- `included` is the inclusion `constructors ⊆ constructors'`; `source`, `target` are
    -- `R`, `S`.
    (included : constructors ⊆ constructors') {source : Source} {target : Target}
    -- `impossible` says no `γ ∈ constructors'` gives `R —γ→ S`.
    (impossible : Unconstructible judgment constructors' source target) :
    Unconstructible judgment constructors source target :=
  fun construction => impossible (construction.mono_constructors included)

/-- Admitted constructors compose when the judgment composes and their classes
are closed under the supplied composition.

MR16, Section 2.2 (printed p. 4):
“R —γ→ S ∧ S —γ′→ T =⇒ R —γ′◦γ→ T.”
Jost, Theorem 2.2.5.1 (printed p. 19), derives the judgment law for resource
maps from image inclusion.

```text
  source : X ──first inner──▶ middle : Y ──second outer──▶ target : Z
       └──────── result (compose outer inner) ────────────────┘
```

The composite of the two witnesses witnesses the composite construction. -/
theorem Constructible.serial
    -- `Inner` contains first-leg constructors `γ`, `Outer` second-leg constructors `γ′`, and
    -- `Composite` their composites; the three types may differ.
    {Inner : Type u} {Outer : Type u'} {Composite : Type w'}
    -- `X`, `Y`, `Z` contain the starting object `R`, intermediate `S` and final `T`.
    {X : Type v} {Y : Type w} {Z : Type v'}
    -- `first γ R S` is the first leg `R —γ→ S`; `second γ′ S T` is the second leg `S —γ′→ T`.
    {first : Inner → X → Y → Prop} {second : Outer → Y → Z → Prop}
    -- `result c R T` is the composite judgment `R —c→ T` for `c : Composite`.
    {result : Composite → X → Z → Prop}
    -- `compose γ′ γ` is MR16's `γ′ ∘ γ`, with the later (outer) constructor first.
    (compose : Outer → Inner → Composite)
    -- `composable` is the judgment law, for all constructors and objects: `R —γ→ S` and
    -- `S —γ′→ T` give `R —compose γ′ γ→ T`.
    (composable : ∀ outer inner {source middle target},
      first inner source middle → second outer middle target →
        result (compose outer inner) source target)
    -- `innerClass`, `outerClass`, `resultClass` are the admitted subsets of `Inner`, `Outer`,
    -- `Composite`.
    {innerClass : Set Inner} {outerClass : Set Outer} {resultClass : Set Composite}
    -- `closed` says `compose γ′ γ ∈ resultClass` whenever `γ′ ∈ outerClass`, `γ ∈ innerClass`.
    (closed : ∀ outer ∈ outerClass, ∀ inner ∈ innerClass,
      compose outer inner ∈ resultClass)
    -- `source : X`, `middle : Y`, `target : Z` are `R`, `S`, `T`.
    {source : X} {middle : Y} {target : Z}
    -- `inner` constructs `middle` from `source` within `innerClass`; `outer` constructs
    -- `target` from `middle` within `outerClass`.
    (inner : Constructible first innerClass source middle)
    (outer : Constructible second outerClass middle target) :
    Constructible result resultClass source target := by
  -- Compose the explicit witnesses and use the selected class closure.
  obtain ⟨inner, innerAdmitted, firstLeg⟩ := inner
  obtain ⟨outer, outerAdmitted, secondLeg⟩ := outer
  exact ⟨compose outer inner, closed outer outerAdmitted inner innerAdmitted,
    composable outer inner firstLeg secondLeg⟩

end ConstructiveCryptography.Construction
