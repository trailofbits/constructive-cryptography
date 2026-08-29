/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical.ResourceAlgebra.ConverterTuple
import AbstractCryptography.Categorical.ResourceAlgebra.Star
import RandomSystemsCC.ResourceAlgebra
import Mathlib.Algebra.Group.Submonoid.Basic

set_option autoImplicit false

/-!
# Multiparty random-system converters

This module supplies the concrete query-indexed DDC realization of the
multiparty interface decomposition used by the carrier-independent
`ResourceAlgebra` layer.  For a set `Z` of dishonest parties, the ordered party
interface is routed to the parallel composition of the merged `Z` interface
and the merged `P \ Z` interface.  Honest converter tuples and arbitrary DDCs
on the dishonest interface then occupy disjoint parallel components.

Liu--Maurer 2020, Section 2.5 (printed p. 7): “If we consider a set Z of
potentially dishonest parties, we can consider the set of interfaces in Z as
being merged to a single interface with several sub-interfaces, and applying
the above relaxation to this interface.”

Jost, Proposition 2.2.3 (printed p. 18): “Converter attachment satisfies the
natural property of composition order independence, stating that on the term
algebra level the composition order does not matter—only the final system.”

The routing uses only ordered parallel, associators, unitors, and the explicit
sum-tag exchange equivalence.  It assumes no symmetric monoidal structure.
-/

namespace RandomSystemsCC.Multiparty

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open RandomSystems.Ambient

universe u v

def dishonestTail {n : Nat} (dishonest : Set (Fin (n + 1))) : Set (Fin n) :=
  {i | i.succ ∈ dishonest}

@[simp]
theorem mem_dishonestTail_iff {n : Nat}
    (dishonest : Set (Fin (n + 1))) (i : Fin n) :
    i ∈ dishonestTail dishonest ↔ i.succ ∈ dishonest :=
  Iff.rfl

/-- The merged dishonest interface, the merged honest interface, and the
explicit routing from the ordered party interface. -/
structure PartyInterfaces {n : Nat} (interfaces : Fin n → Interface.{u, v})
    (dishonest : Set (Fin n)) where
  dishonestInterface : Interface.{u, v}
  honestInterface : Interface.{u, v}
  routing : (Finite.interface n interfaces).Equiv
    (Interface.parallel dishonestInterface honestInterface)

/-- Recursively route an ordered party family into its dishonest and honest
interfaces.

Liu--Maurer 2020, Section 2.5 (printed p. 7): “we can consider the set of
interfaces in Z as being merged to a single interface with several
sub-interfaces.” -/
noncomputable def partyInterfaces :
    (n : Nat) → (interfaces : Fin n → Interface.{u, v}) →
      (dishonest : Set (Fin n)) → PartyInterfaces interfaces dishonest
  | 0, _, _ =>
      { dishonestInterface := Interface.empty
        honestInterface := Interface.empty
        routing := (Interface.Equiv.parallelEmptyLeft Interface.empty).symm }
  | n + 1, interfaces, dishonest => by
      classical
      let tail := partyInterfaces n (fun i => interfaces i.succ) (dishonestTail dishonest)
      by_cases zeroDishonest : (0 : Fin (n + 1)) ∈ dishonest
      · exact
          { dishonestInterface := Interface.parallel (interfaces 0) tail.dishonestInterface
            honestInterface := tail.honestInterface
            routing := (Interface.Equiv.parallel (.refl (interfaces 0))
              tail.routing).trans
                (Interface.Equiv.parallelAssoc (interfaces 0)
                  tail.dishonestInterface tail.honestInterface).symm }
      · exact
          { dishonestInterface := tail.dishonestInterface
            honestInterface := Interface.parallel (interfaces 0) tail.honestInterface
            routing := (((Interface.Equiv.parallel (.refl (interfaces 0))
              tail.routing).trans
                (Interface.Equiv.parallelAssoc (interfaces 0)
                  tail.dishonestInterface tail.honestInterface).symm).trans
                    (Interface.Equiv.parallel
                      (Interface.Equiv.parallelSwap (interfaces 0) tail.dishonestInterface)
                      (.refl tail.honestInterface))).trans
                        (Interface.Equiv.parallelAssoc tail.dishonestInterface
                          (interfaces 0) tail.honestInterface) }

@[simp]
private theorem partyInterfaces_succ_of_mem {n : Nat}
    (interfaces : Fin (n + 1) → Interface.{u, v})
    (dishonest : Set (Fin (n + 1)))
    (zeroDishonest : (0 : Fin (n + 1)) ∈ dishonest) :
    partyInterfaces (n + 1) interfaces dishonest =
      let tail := partyInterfaces n (fun i => interfaces i.succ) (dishonestTail dishonest)
      { dishonestInterface := Interface.parallel (interfaces 0) tail.dishonestInterface
        honestInterface := tail.honestInterface
        routing := (Interface.Equiv.parallel (.refl (interfaces 0))
          tail.routing).trans
            (Interface.Equiv.parallelAssoc (interfaces 0)
              tail.dishonestInterface tail.honestInterface).symm } := by
  simp [partyInterfaces, zeroDishonest]

@[simp]
private theorem partyInterfaces_succ_of_not_mem {n : Nat}
    (interfaces : Fin (n + 1) → Interface.{u, v})
    (dishonest : Set (Fin (n + 1))) (excluded : (0 : Fin (n + 1)) ∉ dishonest) :
    partyInterfaces (n + 1) interfaces dishonest =
      let tail := partyInterfaces n (fun i => interfaces i.succ) (dishonestTail dishonest)
      { dishonestInterface := tail.dishonestInterface
        honestInterface := Interface.parallel (interfaces 0) tail.honestInterface
        routing := (((Interface.Equiv.parallel (.refl (interfaces 0))
          tail.routing).trans
            (Interface.Equiv.parallelAssoc (interfaces 0)
              tail.dishonestInterface tail.honestInterface).symm).trans
                (Interface.Equiv.parallel
                  (Interface.Equiv.parallelSwap (interfaces 0) tail.dishonestInterface)
                  (.refl tail.honestInterface))).trans
                    (Interface.Equiv.parallelAssoc tail.dishonestInterface
                      (interfaces 0) tail.honestInterface) } := by
  simp [partyInterfaces, excluded]

noncomputable abbrev dishonestInterface {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n)) :=
  (partyInterfaces n interfaces dishonest).dishonestInterface

noncomputable abbrev honestInterface {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n)) :=
  (partyInterfaces n interfaces dishonest).honestInterface

noncomputable abbrev partyRouting {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n)) :=
  (partyInterfaces n interfaces dishonest).routing

private theorem relabel_parallel_assoc_symm_eq
    {A₁ B₁ A₂ B₂ A₃ B₃ : Interface.{u, v}}
    (first : DDC A₁ B₁) (second : DDC A₂ B₂) (third : DDC A₃ B₃) :
    DDC.relabel (Interface.Equiv.parallelAssoc A₁ A₂ A₃).symm
        (Interface.Equiv.parallelAssoc B₁ B₂ B₃).symm
        (DDC.parallel first (DDC.parallel second third)) =
      DDC.parallel (DDC.parallel first second) third := by
  let outer := Interface.Equiv.parallelAssoc A₁ A₂ A₃
  let inner := Interface.Equiv.parallelAssoc B₁ B₂ B₃
  have equal := congrArg (DDC.relabel outer.symm inner.symm)
    (DDC.relabel_parallel_assoc_eq first second third)
  simpa only [outer, inner, DDC.relabel_trans, Interface.Equiv.trans_symm,
    DDC.relabel_refl] using equal.symm

private theorem relabel_parallel_swap_assoc_eq
    {A₁ B₁ S₁ T₁ C₁ D₁ : Interface.{u, v}}
    (head : DDC A₁ B₁) (dishonest : DDC S₁ T₁)
    (honest : DDC C₁ D₁) :
    let outer :=
      (((Interface.Equiv.parallelAssoc A₁ S₁ C₁).symm.trans
        (Interface.Equiv.parallel (Interface.Equiv.parallelSwap A₁ S₁)
          (.refl C₁))).trans
            (Interface.Equiv.parallelAssoc S₁ A₁ C₁))
    let inner :=
      (((Interface.Equiv.parallelAssoc B₁ T₁ D₁).symm.trans
        (Interface.Equiv.parallel (Interface.Equiv.parallelSwap B₁ T₁)
          (.refl D₁))).trans
            (Interface.Equiv.parallelAssoc T₁ B₁ D₁))
    DDC.relabel outer inner
        (DDC.parallel head (DDC.parallel dishonest honest)) =
      DDC.parallel dishonest (DDC.parallel head honest) := by
  dsimp only
  rw [← DDC.relabel_trans
      ((Interface.Equiv.parallelAssoc A₁ S₁ C₁).symm.trans
        (Interface.Equiv.parallel (Interface.Equiv.parallelSwap A₁ S₁)
          (.refl C₁)))
      ((Interface.Equiv.parallelAssoc B₁ T₁ D₁).symm.trans
        (Interface.Equiv.parallel (Interface.Equiv.parallelSwap B₁ T₁)
          (.refl D₁)))
      (Interface.Equiv.parallelAssoc S₁ A₁ C₁)
      (Interface.Equiv.parallelAssoc T₁ B₁ D₁)]
  rw [← DDC.relabel_trans
      (Interface.Equiv.parallelAssoc A₁ S₁ C₁).symm
      (Interface.Equiv.parallelAssoc B₁ T₁ D₁).symm
      (Interface.Equiv.parallel (Interface.Equiv.parallelSwap A₁ S₁)
        (.refl C₁))
      (Interface.Equiv.parallel (Interface.Equiv.parallelSwap B₁ T₁)
        (.refl D₁))]
  rw [relabel_parallel_assoc_symm_eq]
  rw [DDC.relabel_parallel_eq]
  rw [DDC.relabel_parallel_swap_eq, DDC.relabel_refl]
  rw [DDC.relabel_parallel_assoc_eq]

private structure HonestFactorization {n : Nat}
    {interfaces : Fin n → Interface.{u, v}}
    (tuple : Finite.ConverterTuple interfaces) (dishonest : Set (Fin n))
    (partition : PartyInterfaces interfaces dishonest) where
  converter : DDC partition.honestInterface partition.honestInterface
  factorization :
    DDC.relabel partition.routing partition.routing
        (Finite.ConverterTuple.honestConverter tuple dishonest) =
      DDC.parallel (DDC.forwarding partition.dishonestInterface) converter

private theorem honestConverter_succ_eq {n : Nat}
    {interfaces : Fin (n + 1) → Interface.{u, v}}
    (tuple : Finite.ConverterTuple interfaces) (dishonest : Set (Fin (n + 1))) :
    Finite.ConverterTuple.honestConverter tuple dishonest =
      DDC.parallel (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
        (Finite.ConverterTuple.honestConverter (fun i => tuple i.succ)
          (dishonestTail dishonest)) := by
  rfl

private noncomputable def honestFactorization :
    {n : Nat} → {interfaces : Fin n → Interface.{u, v}} →
      (tuple : Finite.ConverterTuple interfaces) → (dishonest : Set (Fin n)) →
      HonestFactorization tuple dishonest (partyInterfaces _ interfaces dishonest)
  | 0, interfaces, tuple, dishonest => by
      refine { converter := DDC.forwarding Interface.empty, factorization := ?_ }
      rw [show Finite.ConverterTuple.honestConverter tuple dishonest =
        DDC.forwarding (Finite.interface 0 interfaces) by rfl]
      rw [DDC.relabel_forwarding_eq]
      exact (DDC.parallel_forwarding_eq Interface.empty Interface.empty).symm
  | n + 1, interfaces, tuple, dishonest => by
      classical
      let tailInterfaces : Fin n → Interface.{u, v} := fun i => interfaces i.succ
      let tailTuple : Finite.ConverterTuple tailInterfaces := fun i => tuple i.succ
      let dishonestTail : Set (Fin n) := dishonestTail dishonest
      let tailFactorization := honestFactorization tailTuple dishonestTail
      let tail := partyInterfaces n tailInterfaces dishonestTail
      let routeTail := Interface.Equiv.parallel (.refl (interfaces 0)) tail.routing
      have routeTailEqual :
          DDC.relabel routeTail routeTail
              (DDC.parallel
                (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                (Finite.ConverterTuple.honestConverter tailTuple dishonestTail)) =
            DDC.parallel
              (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
              (DDC.parallel (DDC.forwarding tail.dishonestInterface)
                tailFactorization.converter) := by
        rw [DDC.relabel_parallel_eq, DDC.relabel_refl,
          tailFactorization.factorization]
      by_cases zeroDishonest : (0 : Fin (n + 1)) ∈ dishonest
      · have headIdentity :
            Finite.ConverterTuple.«partial» tuple dishonestᶜ 0 =
              DDC.forwarding (interfaces 0) := by
          calc
            _ = 𝟙 (interfaces 0) :=
              Finite.ConverterTuple.partial_apply_of_not_mem tuple dishonestᶜ 0
                (by simpa using zeroDishonest)
            _ = DDC.forwarding (interfaces 0) := rfl
        let regroup := (Interface.Equiv.parallelAssoc
          (interfaces 0) tail.dishonestInterface tail.honestInterface).symm
        let targetConverter := tailFactorization.converter
        have branchEqual :
            DDC.relabel (routeTail.trans regroup) (routeTail.trans regroup)
                (DDC.parallel
                  (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                  (Finite.ConverterTuple.honestConverter tailTuple dishonestTail)) =
              DDC.parallel
                (DDC.forwarding (Interface.parallel (interfaces 0) tail.dishonestInterface))
                targetConverter := by
          calc
            _ = DDC.relabel regroup regroup
                (DDC.relabel routeTail routeTail
                  (DDC.parallel
                    (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                    (Finite.ConverterTuple.honestConverter tailTuple dishonestTail))) := by
                      rw [DDC.relabel_trans]
            _ = DDC.relabel regroup regroup
                (DDC.parallel
                  (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                  (DDC.parallel (DDC.forwarding tail.dishonestInterface)
                    targetConverter)) := by
                      rw [routeTailEqual]
            _ = DDC.parallel
                (DDC.parallel
                  (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                  (DDC.forwarding tail.dishonestInterface)) targetConverter :=
                    relabel_parallel_assoc_symm_eq _ _ _
            _ = DDC.parallel
                (DDC.forwarding (Interface.parallel (interfaces 0) tail.dishonestInterface))
                targetConverter := by rw [headIdentity, DDC.parallel_forwarding_eq]
        let branchPartition : PartyInterfaces interfaces dishonest :=
          { dishonestInterface := Interface.parallel (interfaces 0) tail.dishonestInterface
            honestInterface := tail.honestInterface
            routing := routeTail.trans regroup }
        have partitionEqual :
            partyInterfaces (n + 1) interfaces dishonest = branchPartition := by
          simpa [branchPartition, tail, tailInterfaces, dishonestTail,
            routeTail, regroup] using
              partyInterfaces_succ_of_mem interfaces dishonest zeroDishonest
        let branchFactorization :
            HonestFactorization tuple dishonest branchPartition :=
          { converter := targetConverter
            factorization := by
              rw [honestConverter_succ_eq]
              exact branchEqual }
        exact partitionEqual.symm ▸ branchFactorization
      · have headHonest :
            Finite.ConverterTuple.«partial» tuple dishonestᶜ 0 = tuple 0 := by
          exact Finite.ConverterTuple.partial_apply_of_mem tuple dishonestᶜ 0
            (by simpa using zeroDishonest)
        let regroup :=
          ((((Interface.Equiv.parallelAssoc
            (interfaces 0) tail.dishonestInterface tail.honestInterface).symm.trans
              (Interface.Equiv.parallel
                (Interface.Equiv.parallelSwap (interfaces 0) tail.dishonestInterface)
                (.refl tail.honestInterface))).trans
                  (Interface.Equiv.parallelAssoc tail.dishonestInterface
                    (interfaces 0) tail.honestInterface)))
        let targetConverter := DDC.parallel (tuple 0) tailFactorization.converter
        have branchEqual :
            DDC.relabel (routeTail.trans regroup) (routeTail.trans regroup)
                (DDC.parallel
                  (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                  (Finite.ConverterTuple.honestConverter tailTuple dishonestTail)) =
              DDC.parallel (DDC.forwarding tail.dishonestInterface) targetConverter := by
          calc
            _ = DDC.relabel regroup regroup
                (DDC.relabel routeTail routeTail
                  (DDC.parallel
                    (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                    (Finite.ConverterTuple.honestConverter tailTuple dishonestTail))) := by
                      rw [DDC.relabel_trans]
            _ = DDC.relabel regroup regroup
                (DDC.parallel
                  (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                  (DDC.parallel (DDC.forwarding tail.dishonestInterface)
                    tailFactorization.converter)) := by
                      rw [routeTailEqual]
            _ = DDC.parallel (DDC.forwarding tail.dishonestInterface)
                (DDC.parallel
                  (Finite.ConverterTuple.«partial» tuple dishonestᶜ 0)
                  tailFactorization.converter) :=
                    relabel_parallel_swap_assoc_eq _ _ _
            _ = DDC.parallel (DDC.forwarding tail.dishonestInterface)
                targetConverter := by rw [headHonest]
        let branchPartition : PartyInterfaces interfaces dishonest :=
          { dishonestInterface := tail.dishonestInterface
            honestInterface := Interface.parallel (interfaces 0) tail.honestInterface
            routing := routeTail.trans regroup }
        have partitionEqual :
            partyInterfaces (n + 1) interfaces dishonest = branchPartition := by
          simpa [branchPartition, tail, tailInterfaces, dishonestTail,
            routeTail, regroup] using
              partyInterfaces_succ_of_not_mem interfaces dishonest zeroDishonest
        let branchFactorization :
            HonestFactorization tuple dishonest branchPartition :=
          { converter := targetConverter
            factorization := by
              rw [honestConverter_succ_eq]
              exact branchEqual }
        exact partitionEqual.symm ▸ branchFactorization

/-- After routing, the converters at `P \ Z` are forwarding on the dishonest
interface in parallel with a converter on the honest interface.

Liu--Maurer 2020, Definition 1 (printed p. 7): “if all parties in P \ Z apply
their converter, the resulting resource satisfies specification S_Z.” -/
theorem relabel_honestConverter_eq {n : Nat}
    {interfaces : Fin n → Interface.{u, v}}
    (tuple : Finite.ConverterTuple interfaces) (dishonest : Set (Fin n)) :
    ∃ converter : DDC (honestInterface interfaces dishonest)
        (honestInterface interfaces dishonest),
      DDC.relabel (partyRouting interfaces dishonest) (partyRouting interfaces dishonest)
          (Finite.ConverterTuple.honestConverter tuple dishonest) =
        DDC.parallel (DDC.forwarding (dishonestInterface interfaces dishonest))
          converter :=
  ⟨(honestFactorization tuple dishonest).converter,
    (honestFactorization tuple dishonest).factorization⟩

/-- Route an arbitrary converter on the merged dishonest interface, in parallel
with forwarding on the honest interface, back to the assembled party
interface.

Liu--Maurer 2020, Section 2.4 (printed p. 7): “a dishonest party may apply an
arbitrary converter to its interface, including the identity converter that
gives direct access to the interface.”  Section 2.5 treats the interfaces in
`Z` as one merged interface. -/
noncomputable def jointConverter {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n))
    (converter : CategoryTheory.End (dishonestInterface interfaces dishonest)) :
    CategoryTheory.End (Finite.interface n interfaces) :=
  DDC.relabel (partyRouting interfaces dishonest).symm
    (partyRouting interfaces dishonest).symm
    (DDC.parallel converter
      (DDC.forwarding (honestInterface interfaces dishonest)))

/-- Routing a joint converter to the dishonest and honest interfaces recovers
the original converter beside forwarding. -/
@[simp]
theorem relabel_jointConverter_eq {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n))
    (converter : CategoryTheory.End (dishonestInterface interfaces dishonest)) :
    DDC.relabel (partyRouting interfaces dishonest)
        (partyRouting interfaces dishonest)
        (jointConverter interfaces dishonest converter) =
      DDC.parallel converter
        (DDC.forwarding (honestInterface interfaces dishonest)) := by
  rw [jointConverter, DDC.relabel_trans,
    Interface.Equiv.symm_trans, DDC.relabel_refl]

/-- The joint converter induced by identity is identity. -/
@[simp]
theorem jointConverter_forwarding_eq {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n)) :
    jointConverter interfaces dishonest
        (DDC.forwarding (dishonestInterface interfaces dishonest)) =
      DDC.forwarding (Finite.interface n interfaces) := by
  rw [jointConverter]
  rw [DDC.parallel_forwarding_eq, DDC.relabel_forwarding_eq]

/-- Joint-converter extension preserves serial composition. -/
theorem jointConverter_serial_eq {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n))
    (first second : CategoryTheory.End
      (dishonestInterface interfaces dishonest)) :
    jointConverter interfaces dishonest (first ≫ second) =
      jointConverter interfaces dishonest first ≫
        jointConverter interfaces dishonest second := by
  change jointConverter interfaces dishonest (DDC.serial first second) =
    DDC.serial (jointConverter interfaces dishonest first)
      (jointConverter interfaces dishonest second)
  rw [jointConverter, jointConverter, jointConverter]
  calc
    DDC.relabel (partyRouting interfaces dishonest).symm
        (partyRouting interfaces dishonest).symm
        (DDC.parallel (DDC.serial first second)
          (DDC.forwarding (honestInterface interfaces dishonest))) =
      DDC.relabel (partyRouting interfaces dishonest).symm
        (partyRouting interfaces dishonest).symm
        (DDC.parallel (DDC.serial first second)
          (DDC.serial
            (DDC.forwarding (honestInterface interfaces dishonest))
            (DDC.forwarding (honestInterface interfaces dishonest)))) := by
              rw [DDC.forwarding_serial_eq]
    _ = DDC.relabel (partyRouting interfaces dishonest).symm
        (partyRouting interfaces dishonest).symm
        (DDC.serial
          (DDC.parallel first
            (DDC.forwarding (honestInterface interfaces dishonest)))
          (DDC.parallel second
            (DDC.forwarding (honestInterface interfaces dishonest)))) := by
              rw [DDC.parallel_serial_eq]
    _ = DDC.serial
        (DDC.relabel (partyRouting interfaces dishonest).symm
          (partyRouting interfaces dishonest).symm
          (DDC.parallel first
            (DDC.forwarding (honestInterface interfaces dishonest))))
        (DDC.relabel (partyRouting interfaces dishonest).symm
          (partyRouting interfaces dishonest).symm
          (DDC.parallel second
            (DDC.forwarding (honestInterface interfaces dishonest)))) := by
              rw [DDC.relabel_serial_eq]

private noncomputable def jointConverterHom {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n)) :
    CategoryTheory.End
        (Opposite.op (dishonestInterface interfaces dishonest)) →*
      CategoryTheory.End
        (Opposite.op (Finite.interface n interfaces)) where
  toFun converter := (jointConverter interfaces dishonest converter.unop).op
  map_one' := by
    change (jointConverter interfaces dishonest (𝟙 _)).op = 𝟙 _
    rw [show (𝟙 (dishonestInterface interfaces dishonest) :
        CategoryTheory.End (dishonestInterface interfaces dishonest)) =
          DDC.forwarding (dishonestInterface interfaces dishonest) by rfl]
    rw [jointConverter_forwarding_eq]
    rfl
  map_mul' first second := by
    change (jointConverter interfaces dishonest
      (first.unop ≫ second.unop)).op = _
    rw [jointConverter_serial_eq]
    rfl

/-- The composition-closed family of arbitrary converters on the merged
dishonest interface.

Liu--Maurer 2020, Section 2.5 (printed p. 7): “we can consider the set of
interfaces in Z as being merged to a single interface with several
sub-interfaces, and applying the above relaxation to this interface.” -/
noncomputable def jointConverters {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n)) :
    EndoFamily (Opposite.op (Finite.interface n interfaces)) :=
  Submonoid.map (jointConverterHom interfaces dishonest) ⊤

/-- Membership in the joint-converter family is exactly extension from the
merged dishonest interface. -/
theorem mem_jointConverters_iff {n : Nat}
    (interfaces : Fin n → Interface.{u, v}) (dishonest : Set (Fin n))
    (converter : CategoryTheory.End (Finite.interface n interfaces)) :
    converter.op ∈ jointConverters interfaces dishonest ↔
      ∃ joint : CategoryTheory.End (dishonestInterface interfaces dishonest),
        jointConverter interfaces dishonest joint = converter := by
  constructor
  · rintro ⟨joint, _, equal⟩
    exact ⟨joint.unop, Quiver.Hom.op_inj equal⟩
  · rintro ⟨joint, rfl⟩
    exact ⟨joint.op, Set.mem_univ _, rfl⟩

private theorem relabel_injective
    {A B A' B' : Interface.{u, v}}
    (outer : A.Equiv A') (inner : B.Equiv B') :
    Function.Injective (DDC.relabel outer inner) := by
  intro left right equal
  have inverseEqual := congrArg
    (DDC.relabel outer.symm inner.symm) equal
  simpa only [DDC.relabel_trans, Interface.Equiv.trans_symm,
    DDC.relabel_refl] using inverseEqual

private theorem honestConverter_jointConverter_serial_eq {n : Nat}
    {interfaces : Fin n → Interface.{u, v}}
    (tuple : Finite.ConverterTuple interfaces)
    (dishonest : Set (Fin n))
    (joint : CategoryTheory.End (dishonestInterface interfaces dishonest)) :
    DDC.serial (Finite.ConverterTuple.honestConverter tuple dishonest)
        (jointConverter interfaces dishonest joint) =
      DDC.serial (jointConverter interfaces dishonest joint)
        (Finite.ConverterTuple.honestConverter tuple dishonest) := by
  obtain ⟨honest, honestEqual⟩ :=
    relabel_honestConverter_eq tuple dishonest
  apply relabel_injective (partyRouting interfaces dishonest)
    (partyRouting interfaces dishonest)
  rw [← DDC.relabel_serial_eq, ← DDC.relabel_serial_eq]
  rw [honestEqual, relabel_jointConverter_eq]
  rw [← DDC.parallel_serial_eq, ← DDC.parallel_serial_eq]
  simp only [DDC.forwarding_serial_eq, DDC.serial_forwarding_eq]

/-- Honest-party attachment is independent of the application order of every
converter admitted at the merged dishonest interface.

Jost, Proposition 2.2.3 (printed p. 18): “Converter attachment satisfies the
natural property of composition order independence.”  This is the concrete
DDC specialization to the disjoint honest and dishonest components; it does
not assert equality for arbitrary overlapping converters. -/
theorem honestConverter_attach_commute {n : Nat}
    {interfaces : Fin n → Interface.{u, v}}
    (tuple : Finite.ConverterTuple interfaces)
    (dishonest : Set (Fin n)) :
    ∀ converter : CategoryTheory.End (Finite.interface n interfaces),
      converter.op ∈ jointConverters interfaces dishonest →
        Function.Commute
          (attach (Phi := Interface.randomSystems)
            (Finite.ConverterTuple.honestConverter tuple dishonest))
          (attach (Phi := Interface.randomSystems) converter) := by
  intro converter converterMember resource
  obtain ⟨joint, rfl⟩ :=
    (mem_jointConverters_iff interfaces dishonest converter).mp converterMember
  rw [← attach_serial, ← attach_serial]
  exact congrArg
    (fun applied => attach (Phi := Interface.randomSystems) applied resource)
    (honestConverter_jointConverter_serial_eq tuple dishonest joint)

end

end RandomSystemsCC.Multiparty
