module

public import ConstructiveCryptography.Specification.Basic
public import Mathlib.Data.Set.NAry

/-!
# Parallel composition and locality

A selected operation `parallel : X → Y → Z` combines resources. Its action
on specifications is `Set.image2 parallel`. Locality is the equation relating
component maps to the map on the combined carrier. Each result uses its
supplied equation; associativity, units and reordering are additional laws. Locality is a
hypothesis, not derived from any structure of the carriers.

```text
  x ─ f ─▶ f x
  y ─ g ─▶ g y
parallel x y ── combined ──▶ parallel' (f x) (g y)        (locality)
```
-/

@[expose] public section

namespace ConstructiveCryptography.Specification

universe u v w u' v' w'

-- `X`, `Y` and `Z` are arbitrary types of left components, right components and combined
-- resources before construction.
variable {X : Type u} {Y : Type v} {Z : Type w}
-- `X'`, `Y'` and `Z'` are the corresponding types after construction.
variable {X' : Type u'} {Y' : Type v'} {Z' : Type w'}

/-- To transport the left input of a binary image, it suffices to transport each image
with its right input fixed. The target map may enlarge specifications monotonically. -/
lemma image2_subset_of_fixed_right
    -- `place x y` combines an input `x : X` with a context `y : Y` to give an output in `Z`.
    {place : X → Y → Z} {source base : Set X} {contexts : Set Y}
    -- `target` acts on output specifications and respects inclusion.
    {target : Set Z → Set Z} (mono : Monotone target)
    -- For each admitted `y`, its image of `source` meets the guarantee for its image of `base`.
    (fixed : ∀ y ∈ contexts, (place · y) '' source ⊆ target ((place · y) '' base)) :
    Set.image2 place source contexts ⊆ target (Set.image2 place base contexts) :=
  Set.image2_subset_iff_right.mpr fun y hy =>
    (fixed y hy).trans (mono (Set.image_subset_image2_left hy))

/-- Transport the right input of a binary image, keeping the left context fixed in each image. -/
lemma image2_subset_of_fixed_left
    -- `place x y` places the varying input `y` on the right of context `x`.
    {place : X → Y → Z} {contexts : Set X} {source base : Set Y}
    {target : Set Z → Set Z} (mono : Monotone target)
    (fixed : ∀ x ∈ contexts, place x '' source ⊆ target (place x '' base)) :
    Set.image2 place contexts source ⊆ target (Set.image2 place contexts base) :=
  Set.image2_subset_iff_left.mpr fun x hx =>
    (fixed x hx).trans (mono (Set.image_subset_image2_right hx))

/-- Compatible parallel maps preserve component constructions: `combined` constructs
`{parallel' x' y' | x' ∈ target, y' ∈ context'}` from `{parallel x y | x ∈ source, y ∈ context}`.

Jost, Proposition 2.2.3 (printed p. 18): “[π_P^{γ_P} R,S] = π_P^{γ_P}[R,S]”.
Theorem 2.2.5.2 (printed p. 19) derives context construction from this
locality equation and inclusion. The quotation's π_P^{γ_P} (pi and gamma, indexed by `P`) is a
specific attachment; here arbitrary maps are linked only by `locality`. -/
theorem Constructs.parallel
    -- `f : X → X'` constructs left components and `g : Y → Y'` right components.
    {f : X → X'} {g : Y → Y'}
    -- `source : Specification X` and `target : Specification X'` are the left specifications.
    {source : Specification X} {target : Specification X'}
    -- `context : Specification Y` and `context' : Specification Y'` are the right specifications.
    {context : Specification Y} {context' : Specification Y'}
    -- `left`: `f` constructs `target` from `source`; `right`: `g` constructs `context'` from
    -- `context`.
    (left : Constructs f source target) (right : Constructs g context context')
    -- `parallel` and `parallel'` are the source's `[R, S]` before and after construction:
    -- arbitrary placements, not assumed associative, commutative, unital or injective.
    (parallel : X → Y → Z) (parallel' : X' → Y' → Z')
    -- `combined : Z → Z'` maps combined resources, e.g. attaching a converter at one
    -- interface of `[R, S]`.
    (combined : Z → Z')
    -- `locality`: `combined` acts on a pair placed by `parallel` componentwise by `f` and `g`.
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
“R —π→ S ⇒ [R,T] —π→ [S,T].”

Here R, S, T are `source`, `target` and `context`, and π is `f` on the left component. This
is `Constructs.parallel` with `g = id`. -/
theorem Constructs.left_context {f : X → X'}
    {source : Specification X} {target : Specification X'}
    -- `construction`: `f` constructs `target` from `source` on the left; right components
    -- range over the unchanged `context : Specification Y`.
    (construction : Constructs f source target) (context : Specification Y)
    -- `parallel` and `parallel'` place pairs before and after; `parallel'` keeps the right
    -- type `Y`. `combined : Z → Z'` maps combined resources.
    (parallel : X → Y → Z) (parallel' : X' → Y → Z') (combined : Z → Z')
    -- `locality`: `combined` applies `f` to the left component and keeps `y`.
    (locality : ∀ x y, combined (parallel x y) = parallel' (f x) y) :
    Constructs combined (Set.image2 parallel source context)
      (Set.image2 parallel' target context) :=
  construction.parallel (Set.mapsTo_id context) parallel parallel' combined locality

/-- Adjoining an unchanged left context preserves construction.

Jost, Proposition 2.2.3 (printed p. 18): “[π_P^{γ_P} R,S] = π_P^{γ_P}[R,S]”.
Here locality is supplied for attachment to the right component. This is
`Constructs.parallel` with `f = id`. -/
theorem Constructs.right_context {g : Y → Y'}
    {source : Specification Y} {target : Specification Y'}
    -- `context : Specification X` contains the unchanged left components.
    -- `construction` says `g` constructs `target` from `source` on the right.
    (context : Specification X) (construction : Constructs g source target)
    -- `parallel` and `parallel'` place pairs before and after; `parallel'` keeps the left
    -- type `X`. `combined : Z → Z'` maps combined resources.
    (parallel : X → Y → Z) (parallel' : X → Y' → Z') (combined : Z → Z')
    -- `locality`: `combined` keeps `x` and applies `g` to the right component.
    (locality : ∀ x y, combined (parallel x y) = parallel' x (g y)) :
    Constructs combined (Set.image2 parallel context source)
      (Set.image2 parallel' context target) :=
  Constructs.parallel (Set.mapsTo_id context) construction parallel parallel' combined locality

end ConstructiveCryptography.Specification
