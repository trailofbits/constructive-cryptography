import ConstructiveCryptography.Specification.Relaxation.Defs

set_option autoImplicit false

/-!
# Composition and set laws of relaxations

Identity is the singleton relation. `comp outer inner` applies `inner` then
`outer`. Union and empty-specification preservation use `map_iSup`, `map_sup`
and `map_bot`; intersection inclusion uses monotonicity.
-/

namespace ConstructiveCryptography.Relaxation

universe u
variable {X : Type u}

/-- Relaxation of an intersection is included in both relaxations.

Jost, Proposition 2.2.7.3 (printed p. 21): “(R ∩ S)φ ⊆ Rφ ∩ Sφ”. -/
theorem inter_subset (relaxation : Relaxation X) (left right : Specification X) :
    relaxation (left ∩ right) ⊆ relaxation left ∩ relaxation right :=
  Set.subset_inter (relaxation.mono Set.inter_subset_left)
    (relaxation.mono Set.inter_subset_right)

/-- The identity pointwise relaxation admits exactly the original resource. -/
protected def id (X : Type u) : Relaxation X :=
  ofPointwise (fun resource => {resource}) Set.mem_singleton

@[simp] theorem id_apply (source : Specification X) :
    Relaxation.id X source = source :=
  Set.biUnion_of_singleton source

/-- Ordered composition of pointwise relaxations.

Jost, Definition 2.2.6 (printed p. 20): “Rφ := ⋃R∈R φ(R)”.
The pointwise composite admits resources reachable through an intermediate
resource, and its specification lift applies the two relaxations in order. -/
def comp (outer inner : Relaxation X) : Relaxation X where
  toPointwise resource := outer (inner.toPointwise resource)
  self_mem resource := outer.subset_apply _ (inner.self_mem resource)

@[simp] theorem comp_apply (outer inner : Relaxation X) (source : Specification X) :
    outer.comp inner source = outer (inner source) :=
  congrArg (fun f : sSupHom (Specification X) (Specification X) => f source)
    (Specification.lift_comp outer.toPointwise inner.toPointwise)

@[simp] theorem comp_id (relaxation : Relaxation X) :
    relaxation.comp (Relaxation.id X) = relaxation := by
  ext source
  simp only [comp_apply, id_apply]

@[simp] theorem id_comp (relaxation : Relaxation X) :
    (Relaxation.id X).comp relaxation = relaxation := by
  ext source
  simp only [comp_apply, id_apply]

theorem comp_assoc (outer middle inner : Relaxation X) :
    (outer.comp middle).comp inner = outer.comp (middle.comp inner) := by
  ext source
  simp only [comp_apply]

end ConstructiveCryptography.Relaxation
