import ConstructiveCryptography.Specification.Maps

set_option autoImplicit false

/-!
# Pointwise relaxations

A relaxation assigns to each resource a set containing it. Application to a
specification is the union lift. The `sSupHomClass` instance supplies Mathlib's
monotonicity, arbitrary-union, binary-union and empty-set laws.
-/

namespace ConstructiveCryptography

universe u

/-- A reflexive set-valued resource map.

Jost, Definition 2.2.6 (printed p. 20): “A relaxation φ is a function
φ : Θ → 2Θ ... such that R ∈ φ(R) for all R ∈ Θ.”
Liu's thesis, Definition 3.4.1 (printed p. 24), uses the same definition. -/
structure Relaxation (X : Type u) where
  /-- Resources admitted by the relaxation of one resource. -/
  toPointwise : X → Set X
  /-- Every resource is admitted by its own relaxation. -/
  self_mem (resource : X) : resource ∈ toPointwise resource

namespace Relaxation

variable {X : Type u}

instance : FunLike (Relaxation X) (Specification X) (Specification X) where
  coe relaxation := Specification.lift relaxation.toPointwise
  coe_injective left right equal := by
    -- Singleton specifications recover the pointwise resource map.
    have pointwise : left.toPointwise = right.toPointwise := funext fun resource => by
      simpa only [Specification.lift_singleton] using congrFun equal {resource}
    cases left
    cases right
    cases pointwise
    rfl

instance : sSupHomClass (Relaxation X) (Specification X) (Specification X) where
  map_sSup relaxation := map_sSup (Specification.lift relaxation.toPointwise)

/-- A relaxation is determined by its action on specifications. -/
@[ext] theorem ext {left right : Relaxation X}
    (equal : ∀ source, left source = right source) : left = right :=
  DFunLike.ext left right equal

/-- Paper-order application to a specification. -/
@[reducible] def relaxedBy (source : Specification X)
    (relaxation : Relaxation X) : Specification X :=
  relaxation source

scoped[ConstructiveCryptography] notation:max source:max " ^ᵣ[" relaxation "]" =>
  Relaxation.relaxedBy source relaxation

/-- Construct a relaxation from its pointwise map and reflexivity law. -/
def ofPointwise (relaxation : X → Specification X)
    (self_mem : ∀ resource, resource ∈ relaxation resource) : Relaxation X :=
  ⟨relaxation, self_mem⟩

/-- Specification membership is witnessed by an admitted center.

Jost, Definition 2.2.6 (printed p. 20): “Rφ := ⋃R∈R φ(R)”. -/
@[simp] theorem mem_apply_iff {relaxation : Relaxation X}
    {source : Specification X} {resource : X} :
    resource ∈ relaxation source ↔
      ∃ center ∈ source, resource ∈ relaxation.toPointwise center :=
  Specification.mem_lift_iff

@[simp] theorem mem_ofPointwise_iff {relaxation : X → Specification X}
    {self_mem : ∀ resource, resource ∈ relaxation resource}
    {source : Specification X} {resource : X} :
    resource ∈ ofPointwise relaxation self_mem source ↔
      ∃ center ∈ source, resource ∈ relaxation center :=
  mem_apply_iff

/-- Singleton specifications recover the pointwise relaxation. -/
@[simp] theorem apply_singleton (relaxation : Relaxation X) (resource : X) :
    relaxation {resource} = relaxation.toPointwise resource :=
  Specification.lift_singleton _ _

/-- Every specification is included in its relaxation.

Jost, Proposition 2.2.7.1 (printed p. 21): “R ⊆ Rφ”. -/
theorem subset_apply (relaxation : Relaxation X) (source : Specification X) :
    source ⊆ relaxation source := by
  -- Use the original resource as its own center.
  intro resource admitted
  exact mem_apply_iff.mpr ⟨resource, admitted, relaxation.self_mem resource⟩

/-- Relaxation preserves refinement.

Jost, Proposition 2.2.7.2 (printed p. 21): “R ⊆ S =⇒ Rφ ⊆ Sφ”. -/
theorem mono (relaxation : Relaxation X) : Monotone relaxation :=
  OrderHomClass.mono relaxation

end Relaxation
end ConstructiveCryptography
