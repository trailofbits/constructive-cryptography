import ConstructiveCryptography.Specification.Basic
import Mathlib.Order.Hom.CompleteLattice

set_option autoImplicit false

/-!
# Union lifts of resource maps

`lift r` extends a set-valued resource map by union and preserves all suprema.
Ordinary resource maps are the singleton-valued case. General monotone
specification maps use `OrderHom`; union-preserving maps use `sSupHom`.
-/

namespace ConstructiveCryptography.Specification

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Union lift of a set-valued resource map.

Jost, Definition 2.2.6 (printed p. 20): “Rφ := ⋃R∈R φ(R)”.
Liu's thesis, Definition 3.4.1 (printed p. 24), uses the same union.
The lift and its union laws apply to arbitrary source and target carriers. -/
def lift (r : X → Set Y) : sSupHom (Specification X) (Specification Y) where
  toFun source := ⋃ x ∈ source, r x
  map_sSup' specifications := by
    -- A center in a union belongs to one of its specifications.
    change (⋃ x ∈ ⋃₀ specifications, r x) =
      ⋃₀ ((fun source => ⋃ x ∈ source, r x) '' specifications)
    rw [Set.sUnion_image]
    ext y
    simp only [Set.mem_iUnion, Set.mem_sUnion, exists_prop]
    constructor
    · rintro ⟨x, ⟨source, admitted, member⟩, related⟩
      exact ⟨source, admitted, x, member, related⟩
    · rintro ⟨source, admitted, x, member, related⟩
      exact ⟨x, ⟨source, admitted, member⟩, related⟩

/-- Membership in a union lift is witnessed by an admitted center. -/
@[simp] theorem mem_lift_iff {r : X → Set Y} {source : Specification X} {y : Y} :
    y ∈ lift r source ↔ ∃ x ∈ source, y ∈ r x := by
  change y ∈ (⋃ x ∈ source, r x) ↔ _
  simp only [Set.mem_iUnion, exists_prop]

/-- The lift of a singleton specification recovers the resource map. -/
@[simp] theorem lift_singleton (r : X → Set Y) (x : X) :
    lift r {x} = r x :=
  Set.biUnion_singleton x r

/-- Singleton-valued resource maps lift to ordinary specification images. -/
theorem lift_singleton_eq_setImage (f : X → Y) :
    lift (fun x => {f x}) = sSupHom.setImage f := by
  ext source y
  -- The relational witness is exactly the direct-image witness.
  change y ∈ (⋃ x ∈ source, ({f x} : Set Y)) ↔ y ∈ f '' source
  simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff, Set.mem_image, eq_comm]

/-- Every union-preserving specification map is the lift of its singleton
values. The calculation uses Jost's union extension (Definition 2.2.6,
printed p. 20) and the decomposition of a set into singletons. -/
theorem lift_singletons (f : sSupHom (Specification X) (Specification Y)) :
    lift (fun x => f {x}) = f := by
  apply sSupHom.ext
  intro source
  -- Apply union preservation to the singleton decomposition.
  change (⋃ x ∈ source, f {x}) = f source
  exact (map_iSup₂ f (fun x (_ : x ∈ source) => ({x} : Specification X))).symm.trans
    (congrArg f (Set.biUnion_of_singleton source))

/-- Lifting relational composition gives composition of specification maps.

Jost, Definition 2.2.6 (printed p. 20): “Rφ := ⋃R∈R φ(R)”.
Two successive lifts retain the intermediate resource as an existential witness. -/
theorem lift_comp (outer : Y → Set Z) (inner : X → Set Y) :
    lift (fun x => lift outer (inner x)) = (lift outer).comp (lift inner) := by
  ext source z
  simp only [mem_lift_iff, sSupHom.comp_apply]
  constructor
  · -- Retain the intermediate resource produced by the inner relation.
    rintro ⟨x, admitted, y, first, second⟩
    exact ⟨y, ⟨x, admitted, first⟩, second⟩
  · -- Recover the original center from the intermediate lift.
    rintro ⟨y, ⟨x, admitted, first⟩, second⟩
    exact ⟨x, admitted, y, first, second⟩

end ConstructiveCryptography.Specification
