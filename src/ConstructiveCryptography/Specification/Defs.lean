module

public import Mathlib.Data.Set.Defs

/-!
# Resource specifications

A value of type `Specification X` is a set of objects in `X` satisfying a predicate.

The carrier `X` is an arbitrary type, the source's universe Φ (Phi) of objects. Nothing
about its elements is assumed here: they may be concrete random systems, abstract resources
or any other values. Inclusion `R ⊆ S` of specifications reads “every object meeting `R` also
meets `S`”, so a smaller specification is the stronger guarantee.
-/

@[expose] public section

set_option autoImplicit false

namespace ConstructiveCryptography

/-- A specification is the set of resources satisfying it.

Maurer--Renner 2016, Section 2.3 (printed p. 5): “often a specification is
understood as the subset of a universe Φ of objects, namely those that satisfy
the specification.”

A reducible abbreviation, so all `Set` operations apply unchanged. No nonemptiness is
required: the empty specification admits no objects. -/
abbrev Specification
    -- Φ (Phi) is the type of resources.
    -- `Specification Φ` abbreviates `Set Φ`, the type of sets of resources.
    (Φ : Type*) := Set Φ

end ConstructiveCryptography
