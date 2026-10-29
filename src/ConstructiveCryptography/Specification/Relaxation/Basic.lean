import ConstructiveCryptography.Specification.Relaxation.Defs

set_option autoImplicit false

/-!
# Composition and set laws of relaxations

Identity is the singleton relation. `comp outer inner` applies `inner` then
`outer`. Union and empty-specification preservation use `map_iSup`, `map_sup`
and `map_bot`; intersection inclusion uses monotonicity.

`comp` satisfies the monoid laws with
unit `Relaxation.id X` (`comp_id`, `id_comp`, `comp_assoc`; no `Monoid` instance is declared).
On specifications,

```text
(outer.comp inner) R = outer (inner R)        Relaxation.id X R = R
```
-/

namespace ConstructiveCryptography.Relaxation

universe u
-- `X` is the one arbitrary type of resources on which all relaxations here act.
variable {X : Type u}

/-- Relaxation of an intersection is included in both relaxations.

Jost, Proposition 2.2.7.3 (printed p. 21): “(R ∩ S)φ ⊆ Rφ ∩ Sφ”.

Only inclusion holds in general: a resource may be close to a center in `left` and to a
different center in `right` without being close to any center in both. -/
theorem inter_subset
    -- `relaxation` is the source's φ (phi); `left` and `right` are R and S on `X`.
    (relaxation : Relaxation X) (left right : Specification X) :
    relaxation (left ∩ right) ⊆ relaxation left ∩ relaxation right :=
  Set.subset_inter (relaxation.mono Set.inter_subset_left)
    (relaxation.mono Set.inter_subset_right)

/-- The identity pointwise relaxation admits exactly the original resource:
`(Relaxation.id X).toPointwise resource = {resource}` on the carrier `X`. -/
protected def id (X : Type u) : Relaxation X :=
  ofPointwise (fun resource => {resource}) Set.mem_singleton

/-- The identity relaxation leaves every specification unchanged. -/
@[simp] lemma id_apply (source : Specification X) :
    Relaxation.id X source = source :=
  Set.biUnion_of_singleton source

/-- Ordered composition of pointwise relaxations.

Jost, Definition 2.2.6 (printed p. 20): “Rφ := ⋃R∈R φ(R)”.
The pointwise composite admits resources reachable through an intermediate
resource, and its specification lift applies the two relaxations in order:

```text
(outer.comp inner).toPointwise r = outer (inner.toPointwise r)
                                 = {s | ∃ m ∈ inner.toPointwise r, s ∈ outer.toPointwise m},
```

so `s` is admitted for `r` through some intermediate resource `m`. Reflexivity of the
composite follows from reflexivity of `inner` and `outer`. -/
def comp
    -- `inner : Relaxation X` is applied first and `outer : Relaxation X` second.
    (outer inner : Relaxation X) : Relaxation X where
  toPointwise resource := outer (inner.toPointwise resource)
  self_mem resource := outer.subset_apply _ (inner.self_mem resource)

/-- On specifications the composite applies `inner` first:
`outer.comp inner source = outer (inner source)`, by `Specification.lift_comp`. -/
@[simp] lemma comp_apply (outer inner : Relaxation X) (source : Specification X) :
    outer.comp inner source = outer (inner source) :=
  congrArg (fun f : sSupHom (Specification X) (Specification X) => f source)
    (Specification.lift_comp outer.toPointwise inner.toPointwise)

/-- Composing with the identity relaxation applied first changes nothing. -/
@[simp] lemma comp_id (relaxation : Relaxation X) :
    relaxation.comp (Relaxation.id X) = relaxation := by
  ext source
  simp only [comp_apply, id_apply]

/-- Composing with the identity relaxation applied last changes nothing. -/
@[simp] lemma id_comp (relaxation : Relaxation X) :
    (Relaxation.id X).comp relaxation = relaxation := by
  ext source
  simp only [comp_apply, id_apply]

/-- Composition of relaxations is associative: both sides apply `inner`, then `middle`, then
`outer`. -/
lemma comp_assoc (outer middle inner : Relaxation X) :
    (outer.comp middle).comp inner = outer.comp (middle.comp inner) := by
  ext source
  simp only [comp_apply]

end ConstructiveCryptography.Relaxation
