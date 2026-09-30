import ConstructiveCryptography.Specification.Basic
import Mathlib.Data.Set.NAry

/-!
# Parallel composition and locality

A selected operation `parallel : X → Y → Z` combines resources. Its action
on specifications is `Set.image2 parallel`. Locality is the equation relating
component maps to the map on the combined carrier. Each result uses its
supplied equation; associativity, units and reordering are additional laws.
-/

namespace ConstructiveCryptography.Specification

universe u v w u' v' w'

variable {X : Type u} {Y : Type v} {Z : Type w}
variable {X' : Type u'} {Y' : Type v'} {Z' : Type w'}

/-- Compatible parallel maps preserve component constructions.

Jost, Proposition 2.2.3 (printed p. 18): “[π_P^{γ_P} R,S] = π_P^{γ_P}[R,S]”.
Theorem 2.2.5.2 (printed p. 19) derives context construction from this
locality equation and inclusion. Here both component maps are supplied. -/
theorem Constructs.parallel {f : X → X'} {g : Y → Y'}
    {source : Specification X} {target : Specification X'}
    {context : Specification Y} {context' : Specification Y'}
    (left : Constructs f source target) (right : Constructs g context context')
    (parallel : X → Y → Z) (parallel' : X' → Y' → Z') (combined : Z → Z')
    (locality : ∀ x y, combined (parallel x y) = parallel' (f x) (g y)) :
    Constructs combined (Set.image2 parallel source context)
      (Set.image2 parallel' target context') := by
  -- Locality moves the combined map to the two component images.
  apply Set.mapsTo_iff_image_subset.mpr
  rw [Set.image_image2_distrib locality]
  -- Each component image is contained in its target specification.
  exact Set.image2_subset left.image_subset right.image_subset

/-- Adjoining an unchanged right context preserves construction.

Jost, Theorem 2.2.5.2 (printed p. 19):
“R —π→ S ⇒ [R,T] —π→ [S,T].” -/
theorem Constructs.left_context {f : X → X'}
    {source : Specification X} {target : Specification X'}
    (construction : Constructs f source target) (context : Specification Y)
    (parallel : X → Y → Z) (parallel' : X' → Y → Z') (combined : Z → Z')
    (locality : ∀ x y, combined (parallel x y) = parallel' (f x) y) :
    Constructs combined (Set.image2 parallel source context)
      (Set.image2 parallel' target context) :=
  construction.parallel (Set.mapsTo_id context) parallel parallel' combined locality

/-- Adjoining an unchanged left context preserves construction.

Jost, Proposition 2.2.3 (printed p. 18): “[π_P^{γ_P} R,S] = π_P^{γ_P}[R,S]”.
Here locality is supplied for attachment to the right component. -/
theorem Constructs.right_context {g : Y → Y'}
    {source : Specification Y} {target : Specification Y'}
    (context : Specification X) (construction : Constructs g source target)
    (parallel : X → Y → Z) (parallel' : X → Y' → Z') (combined : Z → Z')
    (locality : ∀ x y, combined (parallel x y) = parallel' x (g y)) :
    Constructs combined (Set.image2 parallel context source)
      (Set.image2 parallel' context target) :=
  Constructs.parallel (Set.mapsTo_id context) construction parallel parallel' combined locality

end ConstructiveCryptography.Specification
