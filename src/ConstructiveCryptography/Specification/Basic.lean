import ConstructiveCryptography.Specification.Defs
import Mathlib.Data.Set.Function

set_option autoImplicit false

/-!
# Specification maps and exact construction

`Constructs f source target` is `Set.MapsTo f source target`, equivalently
`f '' source ⊆ target`. Identity, serial composition and refinement use
`Set.mapsTo_id`, `Set.MapsTo.comp` and `Set.MapsTo.mono`.

`Constructs.map` lifts a construction through compatible specification maps.
-/

namespace ConstructiveCryptography.Specification

universe u v

variable {X : Type u} {Y : Type v}

/-- Exact construction by a function between resource carriers.

Maurer--Renner 2016, Definition 1 (printed p. 11):
“R —π→ S :⇐⇒ πR ⊆ S.”

The two specifications are sets in the source and target carriers.
`Set.mapsTo_iff_image_subset` gives the direct-image formulation. Jost,
Theorem 2.2.5.1 (printed p. 19), derives serial construction from image
monotonicity and subset transitivity. -/
abbrev Constructs (f : X → Y) (source : Specification X)
    (target : Specification Y) : Prop :=
  Set.MapsTo f source target

/-- Paper notation for exact construction by a resource map. -/
scoped notation:50 source " —[" f "]→ " target:51 => Constructs f source target

/-- Compatible specification maps preserve an exact construction.

Jost, Corollary 3.3.4 (printed p. 38), uses
“π′(τ(S)) = τ(π′S) ⊆ τ(τ′(T))”.

The hypotheses are a compatibility inclusion and monotonicity of the target
specification map. -/
theorem Constructs.map {f : X → Y}
    {source : Specification X} {target : Specification Y}
    (construction : Constructs f source target)
    (sourceMap : Specification X → Specification X)
    (targetMap : Specification Y → Specification Y)
    (monotone : Monotone targetMap)
    (compatible : ∀ specification,
      f '' sourceMap specification ⊆ targetMap (f '' specification)) :
    Constructs f (sourceMap source) (targetMap target) := by
  apply Set.mapsTo_iff_image_subset.mpr
  -- Move the source map through f, then weaken the target specification.
  exact (compatible source).trans (monotone construction.image_subset)

end ConstructiveCryptography.Specification
