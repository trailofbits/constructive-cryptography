import Mathlib.Data.Set.Defs

set_option autoImplicit false

/-!
# Resource specifications

`Specification X` is the set of objects in `X` satisfying a predicate.
-/

namespace ConstructiveCryptography

/-- A specification is the set of resources satisfying it.

Maurer--Renner 2016, Section 2.3 (printed p. 5): “often a specification is
understood as the subset of a universe Φ of objects, namely those that satisfy
the specification.” -/
abbrev Specification (Φ : Type*) := Set Φ

end ConstructiveCryptography
