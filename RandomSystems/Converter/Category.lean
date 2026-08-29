/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Parallel
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Types.Basic

set_option autoImplicit false

/-!
# Category of interfaces and DDCs

This module packages the proved DDC identity and serial laws as a category and
the deterministic DDS attachment as a contravariant functor.
-/

namespace RandomSystems.Ambient

universe u v

open CategoryTheory

namespace Interface

/-- Interfaces and DDCs form a category.

Maurer--Renner 2016, Section 3.3 (printed p. 7), states
“`(β ◦ α)ⁱR = βⁱ(αⁱR)`” and says that the identity converter induces the
identity. Jost defines sequential converter composition and identity but does
not state a category. This declaration packages the proved DDC laws. -/
@[reducible] noncomputable def category :
    LargeCategory Interface.{u, v} where
  Hom outer inner := DDC outer inner
  id boundary := DDC.forwarding boundary
  comp outer inner := DDC.serial outer inner
  id_comp converter := DDC.forwarding_serial_eq converter
  comp_id converter := DDC.serial_forwarding_eq converter
  assoc first second third := DDC.serial_assoc first second third

noncomputable instance instCategory :
    LargeCategory Interface.{u, v} :=
  category

/-- DDS attachment defines a contravariant functor.

Maurer--Renner 2016, Section 3.3 (printed p. 7), states both that a converter
“induces a function `Φ → Φ`” and that “`(β ◦ α)ⁱR = βⁱ(αⁱR)`.” -/
noncomputable def ddsFunctor :
    CategoryTheory.Functor
      (Opposite Interface.{u, v}) (Type (max u v)) where
  obj boundary := DDS boundary.unop
  map converter := applySystem converter.unop
  map_id boundary := by
    -- Forwarding attachment is the identity on DDSs.
    funext system
    exact applySystem_forwarding_eq boundary.unop system
  map_comp outer inner := by
    -- Serial DDC attachment is nested attachment.
    funext system
    exact DDC.applySystem_serial_eq inner.unop outer.unop system

end Interface

namespace Interface.Equiv

/-- The categorical isomorphism induced by an interface equivalence. -/
noncomputable def toIso {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    A ≅ B where
  hom := equivalence.symm.toDDC
  inv := equivalence.toDDC
  hom_inv_id := DDC.toDDC_symm_serial_eq equivalence
  inv_hom_id := DDC.toDDC_serial_symm_eq equivalence

end Interface.Equiv


open CategoryTheory
open CategoryTheory.MonoidalCategory

namespace DDC

/-- Precomposing by the DDC induced by an interface equivalence is outer
interface relabeling. -/
private theorem toDDC_serial_eq_relabel
    {A A' B : Interface.{u, v}} (outer : A.Equiv A')
    (converter : DDC A B) :
    serial outer.toDDC converter =
      relabel outer (.refl B) converter := by
  have natural := relabel_serial_eq outer (.refl A) (.refl B)
    (forwarding A) converter
  simpa only [Interface.Equiv.toDDC, relabel_refl,
    forwarding_serial_eq] using natural

private theorem serial_cancel_right
    {A B C : Interface.{u, v}}
    (left right : DDC A B) (forward : DDC B C) (back : DDC C B)
    (inverse : serial forward back = forwarding B)
    (equal : serial left forward = serial right forward) :
    left = right := by
  calc
    left = serial left (forwarding B) := (serial_forwarding_eq left).symm
    _ = serial left (serial forward back) := congrArg (serial left) inverse.symm
    _ = serial (serial left forward) back :=
      (serial_assoc left forward back).symm
    _ = serial (serial right forward) back := congrArg (fun c => serial c back) equal
    _ = serial right (serial forward back) := serial_assoc right forward back
    _ = serial right (forwarding B) := congrArg (serial right) inverse
    _ = right := serial_forwarding_eq right

/-- Postcomposing by the inverse interface-equivalence DDC is inner
interface relabeling. -/
private theorem serial_toDDC_symm_eq_relabel
    {A B B' : Interface.{u, v}} (inner : B.Equiv B')
    (converter : DDC A B) :
    serial converter inner.symm.toDDC =
      relabel (.refl A) inner converter := by
  apply serial_cancel_right _ _ inner.toDDC inner.symm.toDDC
    (toDDC_serial_symm_eq inner)
  have leftEqual :
      serial (serial converter inner.symm.toDDC) inner.toDDC = converter := by
    rw [serial_assoc, toDDC_symm_serial_eq, serial_forwarding_eq]
  have natural := relabel_serial_eq (.refl A) inner (.refl B)
    converter (forwarding B)
  have rightEqual :
      serial (relabel (.refl A) inner converter) inner.toDDC =
        converter := by
    simpa only [Interface.Equiv.toDDC, relabel_refl,
      serial_forwarding_eq] using natural
  exact leftEqual.trans rightEqual.symm

/-- Every simultaneous DDC relabeling gives the commuting square of the
induced interface isomorphisms. -/
theorem relabel_naturality
    {A B A' B' : Interface.{u, v}}
    (outer : A.Equiv A') (inner : B.Equiv B')
    (converter : DDC A B) :
    serial outer.symm.toDDC (relabel outer inner converter) =
      serial converter inner.symm.toDDC := by
  rw [toDDC_serial_eq_relabel, relabel_trans,
    Interface.Equiv.trans_symm, Interface.Equiv.trans_refl,
    serial_toDDC_symm_eq_relabel]

/-- Simultaneously relabeling both sides of forwarding gives forwarding at
the relabeled interface. -/
@[simp]
theorem relabel_forwarding_eq
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    relabel equivalence equivalence (forwarding A) = forwarding B := by
  -- Cancel the routing isomorphism on the left.
  let iso := equivalence.toIso
  apply (cancel_epi iso.hom).1
  change serial equivalence.symm.toDDC
      (relabel equivalence equivalence (forwarding A)) =
    serial equivalence.symm.toDDC (forwarding B)
  -- Naturality reduces both sides to forwarding identities.
  rw [relabel_naturality]
  simp only [forwarding_serial_eq, serial_forwarding_eq]


end DDC

namespace Interface.Equiv

@[simp]
private theorem toIso_hom
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    equivalence.toIso.hom = equivalence.symm.toDDC := rfl

@[simp]
private theorem toIso_inv
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    equivalence.toIso.inv = equivalence.toDDC := rfl

end Interface.Equiv

open CategoryTheory.MonoidalCategory

namespace Interface.Equiv

private theorem parallel_refl
    (A B : Interface.{u, v}) :
    Interface.Equiv.parallel (.refl A) (.refl B) =
      .refl (Interface.parallel A B) := by
  apply RandomSystems.Ambient.Interface.Equiv.ext_apply
  · intro query
    cases query <;> rfl
  · intro query
    cases query <;> rfl

private theorem symm_refl (A : Interface.{u, v}) :
    (Interface.Equiv.refl A).symm = .refl A := by
  apply RandomSystems.Ambient.Interface.Equiv.ext_queries_replies
  · rfl
  · rw [RandomSystems.Ambient.Interface.Equiv.replies_symm]
    rfl

private theorem parallel_symm
    {A B C D : Interface.{u, v}}
    (left : A.Equiv C) (right : B.Equiv D) :
    (Interface.Equiv.parallel left right).symm =
      Interface.Equiv.parallel left.symm right.symm := by
  apply RandomSystems.Ambient.Interface.Equiv.ext_apply
  · intro query
    cases query <;> rfl
  · intro query
    cases query <;> rfl

private theorem trans_symm_reverse
    {A B C : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) :
    (first.trans second).symm = second.symm.trans first.symm := by
  apply RandomSystems.Ambient.Interface.Equiv.ext_queries_replies
  · rfl
  · rw [RandomSystems.Ambient.Interface.Equiv.replies_symm,
      RandomSystems.Ambient.Interface.Equiv.replies_trans,
      RandomSystems.Ambient.Interface.Equiv.replies_trans,
      RandomSystems.Ambient.Interface.Equiv.replies_symm,
      RandomSystems.Ambient.Interface.Equiv.replies_symm]
    rfl

private theorem trans_assoc
    {A B C D : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) (third : C.Equiv D) :
    (first.trans second).trans third = first.trans (second.trans third) := by
  apply RandomSystems.Ambient.Interface.Equiv.ext_queries_replies
  · rfl
  · rw [RandomSystems.Ambient.Interface.Equiv.replies_trans,
      RandomSystems.Ambient.Interface.Equiv.replies_trans,
      RandomSystems.Ambient.Interface.Equiv.replies_trans,
      RandomSystems.Ambient.Interface.Equiv.replies_trans]
    rfl

end Interface.Equiv

namespace DDC

private theorem parallel_toDDC
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (left : A₁.Equiv B₁) (right : A₂.Equiv B₂) :
    parallel left.toDDC right.toDDC =
      (Interface.Equiv.parallel left right).toDDC := by
  unfold RandomSystems.Ambient.Interface.Equiv.toDDC
  rw [← relabel_parallel_eq]
  rw [parallel_forwarding_eq]
  rw [Interface.Equiv.parallel_refl]

private theorem parallel_toIso_hom
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (left : A₁.Equiv B₁) (right : A₂.Equiv B₂) :
    parallel left.toIso.hom right.toIso.hom =
      (Interface.Equiv.parallel left right).toIso.hom := by
  rw [Interface.Equiv.toIso_hom, Interface.Equiv.toIso_hom,
    Interface.Equiv.toIso_hom, parallel_toDDC,
    Interface.Equiv.parallel_symm]

private theorem serial_toIso_hom
    {A B C : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) :
    serial first.toIso.hom second.toIso.hom =
      (first.trans second).toIso.hom := by
  rw [Interface.Equiv.toIso_hom, Interface.Equiv.toIso_hom,
    Interface.Equiv.toIso_hom, toDDC_trans,
    Interface.Equiv.trans_symm_reverse]

private theorem parallel_toIso_hom_id_right
    {A B : Interface.{u, v}} (equivalence : A.Equiv B)
    (right : Interface.{u, v}) :
    parallel equivalence.toIso.hom (forwarding right) =
      (Interface.Equiv.parallel equivalence (.refl right)).toIso.hom := by
  have reflHom : (Interface.Equiv.refl right).toIso.hom = forwarding right := by
    rw [Interface.Equiv.toIso_hom, Interface.Equiv.symm_refl, toDDC_refl]
  rw [← reflHom]
  exact parallel_toIso_hom equivalence (.refl right)

private theorem parallel_toIso_hom_id_left
    (left : Interface.{u, v}) {A B : Interface.{u, v}}
    (equivalence : A.Equiv B) :
    parallel (forwarding left) equivalence.toIso.hom =
      (Interface.Equiv.parallel (.refl left) equivalence).toIso.hom := by
  have reflHom : (Interface.Equiv.refl left).toIso.hom = forwarding left := by
    rw [Interface.Equiv.toIso_hom, Interface.Equiv.symm_refl, toDDC_refl]
  rw [← reflHom]
  exact parallel_toIso_hom (.refl left) equivalence

end DDC

namespace Interface

@[reducible] private noncomputable def monoidalStruct :
    CategoryTheory.MonoidalCategoryStruct Interface.{u, v} where
  tensorObj := Interface.parallel
  whiskerLeft := fun left {_ _} converter =>
    DDC.parallel (DDC.forwarding left) converter
  whiskerRight := fun {_ _} converter right =>
    DDC.parallel converter (DDC.forwarding right)
  tensorHom := fun first second => DDC.parallel first second
  tensorUnit := Interface.empty
  associator first second third :=
    (Interface.Equiv.parallelAssoc first second third).toIso
  leftUnitor boundary :=
    (Interface.Equiv.parallelEmptyLeft boundary).toIso
  rightUnitor boundary :=
    (Interface.Equiv.parallelEmptyRight boundary).toIso

attribute [local instance] monoidalStruct

private theorem tensor_identity (first second : Interface.{u, v}) :
    DDC.parallel (DDC.forwarding first) (DDC.forwarding second) =
      DDC.forwarding (Interface.parallel first second) :=
  DDC.parallel_forwarding_eq first second

private theorem tensor_serial
    {A₁ B₁ C₁ A₂ B₂ C₂ : Interface.{u, v}}
    (firstOuter : DDC A₁ B₁) (secondOuter : DDC B₁ C₁)
    (firstInner : DDC A₂ B₂) (secondInner : DDC B₂ C₂) :
    DDC.serial (DDC.parallel firstOuter firstInner)
        (DDC.parallel secondOuter secondInner) =
      DDC.parallel (DDC.serial firstOuter secondOuter)
        (DDC.serial firstInner secondInner) :=
  (DDC.parallel_serial_eq firstOuter firstInner secondOuter secondInner).symm

private theorem associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Interface.{u, v}}
    (first : DDC X₁ Y₁) (second : DDC X₂ Y₂)
    (third : DDC X₃ Y₃) :
    DDC.serial (DDC.parallel (DDC.parallel first second) third)
        (Interface.Equiv.parallelAssoc Y₁ Y₂ Y₃).toIso.hom =
      DDC.serial (Interface.Equiv.parallelAssoc X₁ X₂ X₃).toIso.hom
        (DDC.parallel first (DDC.parallel second third)) := by
  -- Start from naturality of simultaneous outer and inner relabeling.
  have natural := DDC.relabel_naturality
    (Interface.Equiv.parallelAssoc X₁ X₂ X₃)
    (Interface.Equiv.parallelAssoc Y₁ Y₂ Y₃)
    (DDC.parallel (DDC.parallel first second) third)
  -- Parallel reassociation is exactly that relabeling.
  rw [DDC.relabel_parallel_assoc_eq] at natural
  exact natural.symm

private theorem leftUnitor_naturality
    (router : ∀ {A B : Interface.{u, v}} (converter : DDC A B),
      DDC.relabel (Interface.Equiv.parallelEmptyLeft A)
          (Interface.Equiv.parallelEmptyLeft B)
          (DDC.parallel (DDC.forwarding Interface.empty) converter) = converter)
    {X Y : Interface.{u, v}} (converter : DDC X Y) :
    DDC.serial (DDC.parallel (DDC.forwarding Interface.empty) converter)
        (Interface.Equiv.parallelEmptyLeft Y).toIso.hom =
      DDC.serial (Interface.Equiv.parallelEmptyLeft X).toIso.hom converter := by
  -- Start from naturality of the left-unit relabeling.
  have natural := DDC.relabel_naturality
    (Interface.Equiv.parallelEmptyLeft X)
    (Interface.Equiv.parallelEmptyLeft Y)
    (DDC.parallel (DDC.forwarding Interface.empty) converter)
  -- The supplied left-unit router identifies the relabeled DDC with the component.
  rw [router] at natural
  exact natural.symm

private theorem rightUnitor_naturality
    (router : ∀ {A B : Interface.{u, v}} (converter : DDC A B),
      DDC.relabel (Interface.Equiv.parallelEmptyRight A)
          (Interface.Equiv.parallelEmptyRight B)
          (DDC.parallel converter (DDC.forwarding Interface.empty)) = converter)
    {X Y : Interface.{u, v}} (converter : DDC X Y) :
    DDC.serial (DDC.parallel converter (DDC.forwarding Interface.empty))
        (Interface.Equiv.parallelEmptyRight Y).toIso.hom =
      DDC.serial (Interface.Equiv.parallelEmptyRight X).toIso.hom converter := by
  -- Start from naturality of the right-unit relabeling.
  have natural := DDC.relabel_naturality
    (Interface.Equiv.parallelEmptyRight X)
    (Interface.Equiv.parallelEmptyRight Y)
    (DDC.parallel converter (DDC.forwarding Interface.empty))
  -- The supplied right-unit router identifies the relabeled DDC with the component.
  rw [router] at natural
  exact natural.symm

private theorem pentagon (W X Y Z : Interface.{u, v}) :
    DDC.serial
        (DDC.serial
          (DDC.parallel
            (Interface.Equiv.parallelAssoc W X Y).toIso.hom
            (DDC.forwarding Z))
          (Interface.Equiv.parallelAssoc W (Interface.parallel X Y) Z).toIso.hom)
        (DDC.parallel (DDC.forwarding W)
          (Interface.Equiv.parallelAssoc X Y Z).toIso.hom) =
      DDC.serial
        (Interface.Equiv.parallelAssoc (Interface.parallel W X) Y Z).toIso.hom
        (Interface.Equiv.parallelAssoc W X (Interface.parallel Y Z)).toIso.hom := by
  -- Name the three equivalences along the long route and the two along the short route.
  let first := Interface.Equiv.parallel
    (Interface.Equiv.parallelAssoc W X Y) (.refl Z)
  let second := Interface.Equiv.parallelAssoc W (Interface.parallel X Y) Z
  let third := Interface.Equiv.parallel
    (.refl W) (Interface.Equiv.parallelAssoc X Y Z)
  let rightFirst :=
    Interface.Equiv.parallelAssoc (Interface.parallel W X) Y Z
  let rightSecond :=
    Interface.Equiv.parallelAssoc W X (Interface.parallel Y Z)
  -- Serial and parallel interface DDCs collapse to composition of equivalences.
  have leftPath :
      DDC.serial
          (DDC.serial
            (DDC.parallel
              (Interface.Equiv.parallelAssoc W X Y).toIso.hom
              (DDC.forwarding Z))
            (Interface.Equiv.parallelAssoc W (Interface.parallel X Y) Z).toIso.hom)
          (DDC.parallel (DDC.forwarding W)
            (Interface.Equiv.parallelAssoc X Y Z).toIso.hom) =
        (first.trans (second.trans third)).toIso.hom := by
    rw [DDC.parallel_toIso_hom_id_right,
      DDC.parallel_toIso_hom_id_left,
      DDC.serial_toIso_hom, DDC.serial_toIso_hom,
      Interface.Equiv.trans_assoc]
  have rightPath :
      DDC.serial
          (Interface.Equiv.parallelAssoc (Interface.parallel W X) Y Z).toIso.hom
          (Interface.Equiv.parallelAssoc W X (Interface.parallel Y Z)).toIso.hom =
        (rightFirst.trans rightSecond).toIso.hom := by
    exact DDC.serial_toIso_hom rightFirst rightSecond
  -- Reduce the DDC equation to the object-level pentagon for interface equivalences.
  rw [leftPath, rightPath]
  exact congrArg (fun equivalence => equivalence.toIso.hom)
    (Interface.Equiv.parallelAssoc_pentagon W X Y Z)

private theorem triangle (X Y : Interface.{u, v}) :
    DDC.serial
        (Interface.Equiv.parallelAssoc X Interface.empty Y).toIso.hom
        (DDC.parallel (DDC.forwarding X)
          (Interface.Equiv.parallelEmptyLeft Y).toIso.hom) =
      DDC.parallel (Interface.Equiv.parallelEmptyRight X).toIso.hom
        (DDC.forwarding Y) := by
  -- Name the two equivalences along the left path and the one along the right path.
  let first := Interface.Equiv.parallelAssoc X Interface.empty Y
  let second := Interface.Equiv.parallel
    (.refl X) (Interface.Equiv.parallelEmptyLeft Y)
  let right := Interface.Equiv.parallel
    (Interface.Equiv.parallelEmptyRight X) (.refl Y)
  -- Serial and parallel interface DDCs collapse to the named equivalence paths.
  have leftPath :
      DDC.serial
          (Interface.Equiv.parallelAssoc X Interface.empty Y).toIso.hom
          (DDC.parallel (DDC.forwarding X)
            (Interface.Equiv.parallelEmptyLeft Y).toIso.hom) =
        (first.trans second).toIso.hom := by
    rw [DDC.parallel_toIso_hom_id_left]
    exact DDC.serial_toIso_hom first second
  have rightPath :
      DDC.parallel (Interface.Equiv.parallelEmptyRight X).toIso.hom
          (DDC.forwarding Y) = right.toIso.hom := by
    exact DDC.parallel_toIso_hom_id_right
      (Interface.Equiv.parallelEmptyRight X) Y
  -- Reduce the DDC equation to the object-level triangle for interface equivalences.
  rw [leftPath, rightPath]
  exact congrArg (fun equivalence => equivalence.toIso.hom)
    (Interface.Equiv.parallel_triangle X Y)

/-- The ordered monoidal category whose objects are interfaces, whose
morphisms are DDCs, whose tensor is routed parallel, and whose unit is the
empty interface.

Jost, Section 2.2.2 (printed p. 17), says: “A finite set of resources with
disjoint interface sets can be viewed as a single one.” Proposition 2.2.3
(printed p. 18) proves attachment locality. This declaration packages the
already proved routed laws; Jost does not state a monoidal category, and no
symmetry is asserted. -/
@[reducible] noncomputable def monoidalCategory :
    CategoryTheory.MonoidalCategory Interface.{u, v} :=
  @CategoryTheory.MonoidalCategory.ofTensorHom
    Interface.{u, v} Interface.category monoidalStruct
    -- Parallel forwarding is forwarding on the parallel interface.
    (id_tensorHom_id := tensor_identity)
    (id_tensorHom := by
      -- Left whiskering is definitionally tensoring by an identity DDC.
      intro X Y₁ Y₂ converter
      rfl)
    (tensorHom_id := by
      -- Right whiskering is definitionally tensoring by an identity DDC.
      intro X₁ X₂ converter Y
      rfl)
    -- Ordered parallel preserves serial composition componentwise.
    (tensorHom_comp_tensorHom := fun firstOuter firstInner secondOuter
      secondInner => tensor_serial firstOuter secondOuter firstInner secondInner)
    -- Reassociation is natural with respect to all three component DDCs.
    (associator_naturality := associator_naturality)
    -- The two empty-interface relabelings are natural.
    (leftUnitor_naturality :=
      leftUnitor_naturality DDC.relabel_parallel_empty_left_eq)
    (rightUnitor_naturality :=
      rightUnitor_naturality DDC.relabel_parallel_empty_right_eq)
    (pentagon := by
      -- Match Mathlib's bracketing to the previously proved pentagon equation.
      intro W X Y Z
      change DDC.serial
          (DDC.parallel
            (Interface.Equiv.parallelAssoc W X Y).toIso.hom
            (DDC.forwarding Z))
          (DDC.serial
            (Interface.Equiv.parallelAssoc W (Interface.parallel X Y) Z).toIso.hom
            (DDC.parallel (DDC.forwarding W)
              (Interface.Equiv.parallelAssoc X Y Z).toIso.hom)) =
        DDC.serial
          (Interface.Equiv.parallelAssoc (Interface.parallel W X) Y Z).toIso.hom
          (Interface.Equiv.parallelAssoc W X (Interface.parallel Y Z)).toIso.hom
      rw [← DDC.serial_assoc]
      exact pentagon W X Y Z)
    (triangle := by
      -- Match Mathlib's unitors to the previously proved triangle equation.
      intro X Y
      change DDC.serial
          (Interface.Equiv.parallelAssoc X Interface.empty Y).toIso.hom
          (DDC.parallel (DDC.forwarding X)
            (Interface.Equiv.parallelEmptyLeft Y).toIso.hom) =
        DDC.parallel (Interface.Equiv.parallelEmptyRight X).toIso.hom
          (DDC.forwarding Y)
      exact triangle X Y)

noncomputable instance instMonoidalCategory :
    CategoryTheory.MonoidalCategory Interface.{u, v} :=
  monoidalCategory

end Interface

end RandomSystems.Ambient
