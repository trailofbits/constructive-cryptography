/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Specification.Defs
import Mathlib.Data.Set.Lattice

set_option autoImplicit false

/-!
# Relaxations of resource specifications

This module owns only the carrier-independent relaxation object and its set
laws.  Converter compatibility, parallel compatibility, metrics, and
converter-class closures belong to the semantic modules selecting those
operations.
-/

namespace AbstractCryptography

universe u

variable {Phi : Type u}

/-- An extensive monotone endomap on resource specifications.

Jost--Maurer 2020, Definition 2 (printed p. 10): “A relaxation `φ` is a
function `φ : Θ → 2^Θ` ... such that `R ∈ φ(R)` for all `R ∈ Θ`.”  For a
specification, the paper defines the union of those pointwise relaxations.
Proposition 3 (printed p. 10) states `R ⊆ R^φ` and monotonicity.  The structure
below retains exactly those two laws for a possibly non-pointwise endomap;
`ofPointwise` is the paper's specialization. -/
structure Relaxation (Phi : Type*) where
  /-- The underlying map on specifications. -/
  toFun : Specification Phi → Specification Phi
  /-- Every specification is contained in its relaxation. -/
  le_toFun (source : Specification Phi) : source ⊆ toFun source
  /-- Relaxation preserves specification inclusion. -/
  mono : Monotone toFun

namespace Relaxation

instance : CoeFun (Relaxation Phi)
    fun _ => Specification Phi → Specification Phi :=
  ⟨toFun⟩

/-- Paper-order application of a relaxation. -/
@[reducible] def relaxedBy (source : Specification Phi)
    (relaxation : Relaxation Phi) : Specification Phi :=
  relaxation source

scoped[AbstractCryptography] notation:max source:max " ^ᵣ[" relaxation "]" =>
  Relaxation.relaxedBy source relaxation

/-- Lift a pointwise relaxation to specifications by union.

Jost--Maurer 2020, Definition 2 (printed p. 10): “for a specification `R`, we
define `R^φ := ⋃_{R∈R} φ(R)`.” -/
def ofPointwise (relaxation : Phi → Specification Phi)
    (self_mem : ∀ resource, resource ∈ relaxation resource) : Relaxation Phi where
  toFun source := ⋃ resource ∈ source, relaxation resource
  le_toFun _ resource admitted := Set.mem_biUnion admitted (self_mem resource)
  mono _ _ included := Set.biUnion_mono included fun _ _ => le_rfl

@[simp]
theorem mem_ofPointwise_iff {relaxation : Phi → Specification Phi}
    {self_mem : ∀ resource, resource ∈ relaxation resource}
    {source : Specification Phi} {resource : Phi} :
    resource ∈ ofPointwise relaxation self_mem source ↔
      ∃ center ∈ source, resource ∈ relaxation center := by
  simp [ofPointwise]

/-- Relaxation of an intersection is contained in the intersection of the
relaxations. -/
theorem inter_subset (relaxation : Relaxation Phi)
    (left right : Specification Phi) :
    relaxation (left ∩ right) ⊆ relaxation left ∩ relaxation right :=
  Set.subset_inter
    (relaxation.mono Set.inter_subset_left)
    (relaxation.mono Set.inter_subset_right)

/-- The union of two relaxations is contained in the relaxation of their
union. -/
theorem union_subset (relaxation : Relaxation Phi)
    (left right : Specification Phi) :
    relaxation left ∪ relaxation right ⊆ relaxation (left ∪ right) :=
  Set.union_subset
    (relaxation.mono Set.subset_union_left)
    (relaxation.mono Set.subset_union_right)

/-- Pointwise relaxation preserves specification union.

Jost--Maurer 2020, Proposition 3.4 (printed p. 10):
“`(R ∪ S)^φ = R^φ ∪ S^φ`.” -/
theorem ofPointwise_union {relaxation : Phi → Specification Phi}
    {self_mem : ∀ resource, resource ∈ relaxation resource}
    (left right : Specification Phi) :
    ofPointwise relaxation self_mem (left ∪ right) =
      ofPointwise relaxation self_mem left ∪
        ofPointwise relaxation self_mem right := by
  simp only [ofPointwise, Set.biUnion_union]

/-- Composition of relaxations, applying `inner` before `outer`. -/
def comp (outer inner : Relaxation Phi) : Relaxation Phi where
  toFun source := outer (inner source)
  le_toFun source := (inner.le_toFun source).trans (outer.le_toFun _)
  mono _ _ included := outer.mono (inner.mono included)

@[simp]
theorem comp_apply (outer inner : Relaxation Phi)
    (source : Specification Phi) :
    outer.comp inner source = outer (inner source) :=
  rfl

/-- A relaxation is determined by its map on specifications. -/
theorem toFun_injective :
    Function.Injective
      (Relaxation.toFun : Relaxation Phi →
        Specification Phi → Specification Phi) := by
  rintro ⟨left, _, _⟩ ⟨right, _, _⟩ equal
  cases equal
  rfl

end Relaxation

end AbstractCryptography
