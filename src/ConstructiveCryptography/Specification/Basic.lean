import ConstructiveCryptography.Specification.Defs
import Mathlib.Data.Set.Function

set_option autoImplicit false

/-!
# Specification maps and exact construction

`Constructs f source target` is `Set.MapsTo f source target`, equivalently
`f '' source ⊆ target`. Identity, serial composition and refinement use
`Set.mapsTo_id`, `Set.MapsTo.comp` and `Set.MapsTo.mono`.

`Constructs.map` lifts a construction through compatible specification maps, such as a
relaxation or a closure applied to both ends. MR16's construction by a converter is the special
case where `f` attaches it; that action is supplied in `Specification.Action`.

```text
source           ── f ──▶ target              Constructs: f '' source ⊆ target
  │ sourceMap               │ targetMap
  ▼                         ▼
sourceMap source ── f ──▶ targetMap target    Constructs.map
```
-/

namespace ConstructiveCryptography.Specification

universe u v

-- `X` is the type of source resources and `Y` the type of target resources; no distance,
-- order, action or category structure is assumed on either.
variable {X : Type u} {Y : Type v}

/-- Exact construction: every `x ∈ source` has `f x ∈ target`, i.e. `f '' source ⊆ target`
(`Set.mapsTo_iff_image_subset`). No error is involved; an empty `source` constructs every
`target`. MR16's converter π acting on one universe is the case `f = (α • ·)`, `X = Y`.

Maurer--Renner 2016, Definition 1 (printed p. 11):
“R —π→ S :⇐⇒ πR ⊆ S.”
Jost, Theorem 2.2.5.1 (printed p. 19), derives serial construction from image
monotonicity and subset transitivity. -/
abbrev Constructs
    -- `f : X → Y`, the source's π (pi), sends each source resource to a target resource; it
    -- is an arbitrary function, not necessarily a converter attachment.
    (f : X → Y)
    -- `source : Specification X` is the assumed specification R.
    (source : Specification X)
    -- `target : Specification Y` is the guaranteed specification S; a smaller `target` is stronger.
    (target : Specification Y) : Prop :=
  Set.MapsTo f source target

/-- Paper notation `source —[f]→ target` for `Constructs f source target`, the source's
`R —π→ S`. -/
scoped notation:50 source " —[" f "]→ " target:51 => Constructs f source target

/-- Compatible specification maps preserve an exact construction.

Jost, Corollary 3.3.4 (printed p. 38), uses
“π′(τ(S)) = τ(π′S) ⊆ τ(τ′(T))”.

In the quotation π′ (pi prime) is the constructing map `f`, and τ, τ′ (tau, tau prime) are
event-renaming maps; Jost requires π′ not to depend on the renamed events to obtain the
equality. Here the two maps may differ and `compatible` supplies the inclusion explicitly:

```text
f '' sourceMap source ⊆ targetMap (f '' source) ⊆ targetMap target
                     compatible            monotone ∘ construction
``` -/
theorem Constructs.map
    -- `f : X → Y` is the constructing function, the quotation's π′.
    {f : X → Y}
    -- `source : Specification X` is assumed and `target : Specification Y` guaranteed.
    {source : Specification X} {target : Specification Y}
    -- `construction` says `f '' source ⊆ target`.
    (construction : Constructs f source target)
    -- `sourceMap` transforms specifications on `X`, e.g. a relaxation; its monotonicity is
    -- not required.
    (sourceMap : Specification X → Specification X)
    -- `targetMap` transforms specifications on `Y`, the quotation's τ.
    (targetMap : Specification Y → Specification Y)
    -- `monotone` says `R ⊆ S` implies `targetMap R ⊆ targetMap S`.
    (monotone : Monotone targetMap)
    -- `compatible` says `f` moves `sourceMap` into `targetMap` on every specification on `X`,
    -- not only on `source`: `f '' sourceMap R ⊆ targetMap (f '' R)`.
    (compatible : ∀ specification,
      f '' sourceMap specification ⊆ targetMap (f '' specification)) :
    Constructs f (sourceMap source) (targetMap target) := by
  apply Set.mapsTo_iff_image_subset.mpr
  -- Move the source map through f, then weaken the target specification.
  exact (compatible source).trans (monotone construction.image_subset)

end ConstructiveCryptography.Specification
