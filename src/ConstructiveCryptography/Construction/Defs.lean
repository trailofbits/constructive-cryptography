import Mathlib.Data.Set.Defs

set_option autoImplicit false

/-!
# Constructor-indexed judgments

A construction judgment is a predicate `Constructor → Source → Target → Prop`.
Constructibility quantifies over a selected set of constructors.
-/

namespace ConstructiveCryptography.Construction

universe u v w

variable {Constructor : Type u} {Source : Type v} {Target : Type w}

/-- Existence of an admitted constructor satisfying the construction judgment.

MR16, Section 2.1 (printed p. 4): “Typically one considers a certain set Γ of
constructors, possibly restricted in terms of efficiency or implementation cost.”
Jost, Section 2.2.2 (printed p. 17), instead keeps converters explicit; a
constructor class is an optional restriction of that presentation. -/
def Constructible (judgment : Constructor → Source → Target → Prop)
    (constructors : Set Constructor) (source : Source) (target : Target) : Prop :=
  ∃ constructor ∈ constructors, judgment constructor source target

/-- Non-constructibility within a selected constructor class.

MR16, Section 2.1 (printed p. 4): “R ↛ S :⇐⇒ ¬∃ γ ∈ Γ : R —γ→ S.” -/
def Unconstructible (judgment : Constructor → Source → Target → Prop)
    (constructors : Set Constructor) (source : Source) (target : Target) : Prop :=
  ¬ Constructible judgment constructors source target

end ConstructiveCryptography.Construction
