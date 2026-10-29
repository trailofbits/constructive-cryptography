import ConstructiveCryptography.Specification.Maps

set_option autoImplicit false

/-!
# Pointwise relaxations

A relaxation assigns to each resource a set containing it. Application to a
specification is the union lift. The `sSupHomClass` instance supplies Mathlib's
monotonicity, arbitrary-union, binary-union and empty-set laws.

For a relaxation `φ : Relaxation X` (phi) on an arbitrary carrier `X`, the pointwise map
`φ.toPointwise : X → Set X` gives the resources “close to” a center, and application to a
specification `R : Specification X` is

```text
φ R = ⋃ center ∈ R, φ.toPointwise center  ⊇ R     (source notation: Rφ, here R ^ᵣ[φ])
```

The relation need not be symmetric or transitive, and no distance is assumed; the scalar
ε-relaxation (`Specification.epsilonRelaxation`) and `Relaxation.kernel` are examples.
Relaxing makes a specification weaker (larger), so `φ R` is the guarantee “close to some
resource in `R`”.

* `Relaxation.subset_apply`: `R ⊆ φ R`.
* `Relaxation.mono`: `R ⊆ S` implies `φ R ⊆ φ S`.
* `Relaxation.mem_apply_iff`: membership is witnessed by an admitted center.
-/

namespace ConstructiveCryptography

universe u

/-- A reflexive set-valued resource map.

Jost, Definition 2.2.6 (printed p. 20): “A relaxation φ is a function
φ : Θ → 2Θ ... such that R ∈ φ(R) for all R ∈ Θ.”
Liu's thesis, Definition 3.4.1 (printed p. 24), uses the same definition.

A relaxation is thus a reflexive relation, presented as a set-valued map; it applies to
specifications through the `FunLike` instance below, by union lift. -/
structure Relaxation
    -- `X` is the source's universe Θ (Theta) of resources; 2Θ is the power set `Set X`.
    (X : Type u) where
  /-- The source's φ (phi): `toPointwise center` is the set of resources the relaxation
  accepts in place of `center`. -/
  toPointwise : X → Set X
  /-- Reflexivity: every resource is admitted by its own relaxation,
  `resource ∈ toPointwise resource`. -/
  self_mem (resource : X) : resource ∈ toPointwise resource

namespace Relaxation

-- `X` is the type of resources on which each relaxation acts.
variable {X : Type u}

/-- A relaxation `φ` acts on specifications by its union lift,
`φ R = Specification.lift φ.toPointwise R`. The action determines `φ`, since singletons
recover `toPointwise`. -/
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

/-- Relaxation of a union of specifications is the union of their relaxations; Mathlib then
supplies monotonicity, binary unions and `φ ∅ = ∅`. -/
instance : sSupHomClass (Relaxation X) (Specification X) (Specification X) where
  map_sSup relaxation := map_sSup (Specification.lift relaxation.toPointwise)

/-- A relaxation is determined by its action on specifications: if `left R = right R` for
every specification `R`, then `left = right`. -/
@[ext] lemma ext {left right : Relaxation X}
    (equal : ∀ source, left source = right source) : left = right :=
  DFunLike.ext left right equal

/-- Paper-order application to a specification: `relaxedBy source φ = φ source`, the source's
postfix `Rφ` with the specification written first. -/
@[reducible] def relaxedBy (source : Specification X)
    (relaxation : Relaxation X) : Specification X :=
  relaxation source

-- Paper notation `R ^ᵣ[φ]` for the relaxation `Rφ` of a specification `R` by `φ`.
scoped[ConstructiveCryptography] notation:max source:max " ^ᵣ[" relaxation "]" =>
  Relaxation.relaxedBy source relaxation

/-- Construct a relaxation from its pointwise map and reflexivity law. -/
def ofPointwise
    -- `relaxation center : Set X` is the set of resources accepted in place of `center : X`.
    (relaxation : X → Specification X)
    -- `self_mem` is reflexivity: each resource is accepted in place of itself.
    (self_mem : ∀ resource, resource ∈ relaxation resource) : Relaxation X :=
  ⟨relaxation, self_mem⟩

/-- Specification membership is witnessed by an admitted center.

Jost, Definition 2.2.6 (printed p. 20): “Rφ := ⋃R∈R φ(R)”.

`resource ∈ φ source` exactly when some `center ∈ source` has
`resource ∈ φ.toPointwise center`. -/
@[simp] lemma mem_apply_iff {relaxation : Relaxation X}
    {source : Specification X} {resource : X} :
    resource ∈ relaxation source ↔
      ∃ center ∈ source, resource ∈ relaxation.toPointwise center :=
  Specification.mem_lift_iff

/-- `mem_apply_iff` for a relaxation built by `ofPointwise`: membership in the relaxed
`source` is witnessed by a center `center ∈ source` with `resource ∈ relaxation center`. -/
@[simp] lemma mem_ofPointwise_iff {relaxation : X → Specification X}
    {self_mem : ∀ resource, resource ∈ relaxation resource}
    {source : Specification X} {resource : X} :
    resource ∈ ofPointwise relaxation self_mem source ↔
      ∃ center ∈ source, resource ∈ relaxation center :=
  mem_apply_iff

/-- Singleton specifications recover the pointwise relaxation:
`φ {resource} = φ.toPointwise resource`. -/
@[simp] lemma apply_singleton (relaxation : Relaxation X) (resource : X) :
    relaxation {resource} = relaxation.toPointwise resource :=
  Specification.lift_singleton _ _

/-- Every specification is included in its relaxation.

Jost, Proposition 2.2.7.1 (printed p. 21): “R ⊆ Rφ”.

Here R is `source` and φ is `relaxation`; the inclusion follows from reflexivity `self_mem`,
taking each resource as its own center. -/
theorem subset_apply (relaxation : Relaxation X) (source : Specification X) :
    source ⊆ relaxation source := by
  -- Use the original resource as its own center.
  intro resource admitted
  exact mem_apply_iff.mpr ⟨resource, admitted, relaxation.self_mem resource⟩

/-- Relaxation preserves refinement.

Jost, Proposition 2.2.7.2 (printed p. 21): “R ⊆ S =⇒ Rφ ⊆ Sφ”.

For specifications `R ⊆ S` on `X`, the relaxed `relaxation R` is included in
`relaxation S`; centers admitted by `R` are admitted by `S`. -/
theorem mono (relaxation : Relaxation X) : Monotone relaxation :=
  OrderHomClass.mono relaxation

end Relaxation
end ConstructiveCryptography
