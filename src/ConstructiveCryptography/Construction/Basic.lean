import ConstructiveCryptography.Construction.Defs

set_option autoImplicit false

/-!
# Laws of constructibility

Judgment implication and enlargement of the constructor class preserve
constructibility. Composition uses an explicit law for the judgment and an
explicit closure condition for the constructor classes.
-/

namespace ConstructiveCryptography.Construction

universe u v w u' v' w'

variable {Constructor : Type u} {Source : Type v} {Target : Type w}
variable {judgment : Constructor → Source → Target → Prop}

/-- A consequence of each admitted judgment is constructible with the same
constructor. MR16, Section 2.3 (printed p. 5):
“R —γ→ S =⇒ R′ —γ→ S′ if R′ ⊆ R and S ⊆ S′.”
For arbitrary judgments the implication is supplied explicitly. -/
theorem Constructible.of_imp {Source' : Type v'} {Target' : Type w'}
    {judgment' : Constructor → Source' → Target' → Prop}
    {constructors : Set Constructor} {source : Source} {target : Target}
    {source' : Source'} {target' : Target'}
    (implication : ∀ constructor ∈ constructors,
      judgment constructor source target → judgment' constructor source' target')
    (construction : Constructible judgment constructors source target) :
    Constructible judgment' constructors source' target' := by
  -- Retain the admitted constructor and apply the judgment implication.
  obtain ⟨constructor, admitted, constructs⟩ := construction
  exact ⟨constructor, admitted, implication constructor admitted constructs⟩

/-- Enlarging the admitted constructor class preserves constructibility. -/
theorem Constructible.mono_constructors {constructors constructors' : Set Constructor}
    (included : constructors ⊆ constructors') {source : Source} {target : Target}
    (construction : Constructible judgment constructors source target) :
    Constructible judgment constructors' source target := by
  -- The same constructor belongs to the larger class.
  obtain ⟨constructor, admitted, constructs⟩ := construction
  exact ⟨constructor, included admitted, constructs⟩

/-- An impossibility result pulls back along a judgment implication.

MR16, Section 2.3 (printed p. 6):
“R ↛ S =⇒ R′ ↛ S′ if R ⊆ R′ and S′ ⊆ S.” -/
theorem Unconstructible.of_imp {Source' : Type v'} {Target' : Type w'}
    {judgment' : Constructor → Source' → Target' → Prop}
    {constructors : Set Constructor} {source : Source} {target : Target}
    {source' : Source'} {target' : Target'}
    (implication : ∀ constructor ∈ constructors,
      judgment' constructor source' target' → judgment constructor source target)
    (impossible : Unconstructible judgment constructors source target) :
    Unconstructible judgment' constructors source' target' :=
  fun construction => impossible (construction.of_imp implication)

/-- Non-constructibility against a class implies non-constructibility against
each smaller class. -/
theorem Unconstructible.mono_constructors {constructors constructors' : Set Constructor}
    (included : constructors ⊆ constructors') {source : Source} {target : Target}
    (impossible : Unconstructible judgment constructors' source target) :
    Unconstructible judgment constructors source target :=
  fun construction => impossible (construction.mono_constructors included)

/-- Admitted constructors compose when the judgment composes and their classes
are closed under the supplied composition.

MR16, Section 2.2 (printed p. 4):
“R —γ→ S ∧ S —γ′→ T =⇒ R —γ′◦γ→ T.”
Jost, Theorem 2.2.5.1 (printed p. 19), derives the judgment law for resource
maps from image inclusion. -/
theorem Constructible.serial
    {Inner : Type u} {Outer : Type u'} {Composite : Type w'}
    {X : Type v} {Y : Type w} {Z : Type v'}
    {first : Inner → X → Y → Prop} {second : Outer → Y → Z → Prop}
    {result : Composite → X → Z → Prop}
    (compose : Outer → Inner → Composite)
    (composable : ∀ outer inner {source middle target},
      first inner source middle → second outer middle target →
        result (compose outer inner) source target)
    {innerClass : Set Inner} {outerClass : Set Outer} {resultClass : Set Composite}
    (closed : ∀ outer ∈ outerClass, ∀ inner ∈ innerClass,
      compose outer inner ∈ resultClass)
    {source : X} {middle : Y} {target : Z}
    (inner : Constructible first innerClass source middle)
    (outer : Constructible second outerClass middle target) :
    Constructible result resultClass source target := by
  -- Compose the explicit witnesses and use the selected class closure.
  obtain ⟨inner, innerAdmitted, firstLeg⟩ := inner
  obtain ⟨outer, outerAdmitted, secondLeg⟩ := outer
  exact ⟨compose outer inner, closed outer outerAdmitted inner innerAdmitted,
    composable outer inner firstLeg secondLeg⟩

end ConstructiveCryptography.Construction
