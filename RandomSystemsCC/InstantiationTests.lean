/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical.ResourceAlgebra.Finite
import AbstractCryptography.Categorical.ResourceAlgebra.ConverterTuple
import AbstractCryptography.Categorical.ResourceAlgebra.CostBounded
import AbstractCryptography.Categorical.ResourceAlgebra.Epsilon
import AbstractCryptography.Categorical.ResourceAlgebra.Endomorphism
import AbstractCryptography.Categorical.ResourceAlgebra.Filtered
import AbstractCryptography.Categorical.ResourceAlgebra.Outbound
import AbstractCryptography.Categorical.ResourceAlgebra.Star
import RandomSystems.Converter.CommonDomain
import RandomSystemsCC
import RandomSystemsCC.Multiparty

set_option autoImplicit false

/-!
# Random-systems instantiation tests

These examples check the query-indexed random-system carrier against the
carrier-independent categorical resource algebra. They exercise one selected
category, one ordered parallel operation, and one selected fibre distance.
-/

namespace RandomSystemsCC.InstantiationTests

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open RandomSystems.Ambient
open RandomSystemsCC.Multiparty

universe u v

example : ResourceAlgebra
    RandomSystems.Ambient.Interface.{u, v}
    RandomSystems.Ambient.Interface.randomSystems :=
  inferInstance

/-! ## Attachment -/

example {A : Interface.{u, v}} (system : RandomSystem A) :
    attach (Phi := Interface.randomSystems) (𝟙 A) system = system :=
  ResourceAlgebra.attach_identity
    (Phi := Interface.randomSystems) system

example {A B C : Interface.{u, v}}
    (outer : DDC A B) (inner : DDC B C) (system : RandomSystem C) :
    attach (Phi := Interface.randomSystems) (outer ≫ inner) system =
      attach (Phi := Interface.randomSystems) outer
        (attach (Phi := Interface.randomSystems) inner system) :=
  ResourceAlgebra.attach_serial
    (Phi := Interface.randomSystems) outer inner system

example {A : Interface.{u, v}} (converter : CategoryTheory.End A)
    (system : RandomSystem A) :
    letI : MulAction (MulOpposite (CategoryTheory.End A)) (RandomSystem A) :=
      ResourceAlgebra.endoMulAction Interface.randomSystems A
    MulOpposite.op converter • system =
      attach (Phi := Interface.randomSystems) converter system := by
  -- The derived fixed-fibre action is definitionally converter attachment.
  rfl

/-! ## Specifications and constructions -/

example {A B : Interface.{u, v}} (converter : DDC A B)
    (source : ResourceAlgebra.Specification Interface.randomSystems B)
    (target : ResourceAlgebra.Specification Interface.randomSystems A) : Prop :=
  ResourceAlgebra.Specification.Constructs
    (Phi := Interface.randomSystems) converter source target

example {A : Interface.{u, v}}
    (source : ResourceAlgebra.Specification Interface.randomSystems A) :
    ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) (𝟙 A) source source :=
  ResourceAlgebra.Specification.constructs_identity source

example {A B C : Interface.{u, v}}
    {outer : A ⟶ B} {inner : B ⟶ C}
    {source : ResourceAlgebra.Specification Interface.randomSystems C}
    {middle : ResourceAlgebra.Specification Interface.randomSystems B}
    {target : ResourceAlgebra.Specification Interface.randomSystems A}
    (innerConstruction : ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) inner source middle)
    (outerConstruction : ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) outer middle target) :
    ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) (outer ≫ inner) source target :=
  innerConstruction.serial outerConstruction

example {A B : Interface.{u, v}} {converter : A ⟶ B}
    {source : RandomSystem B} {target : RandomSystem A} :
    ResourceAlgebra.Specification.Constructs
        (Phi := Interface.randomSystems) converter {source} {target} ↔
      attach (Phi := Interface.randomSystems) converter source = target :=
  ResourceAlgebra.Specification.constructs_singleton_iff

example {A B : Interface.{u, v}} {left right : A ⟶ B}
    (equal : left = right)
    {source : ResourceAlgebra.Specification Interface.randomSystems B}
    {target : ResourceAlgebra.Specification Interface.randomSystems A} :
    ResourceAlgebra.Specification.Constructs
        (Phi := Interface.randomSystems) left source target ↔
      ResourceAlgebra.Specification.Constructs
        (Phi := Interface.randomSystems) right source target :=
  ResourceAlgebra.Specification.constructs_iff_of_converter_eq equal

example {A B : Interface.{u, v}} {converter : A ⟶ B}
    {source : ResourceAlgebra.Specification Interface.randomSystems B}
    {target : ResourceAlgebra.Specification Interface.randomSystems A}
    (construction : ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) converter source target) :
    ResourceAlgebra.Specification.Constructible
      (Phi := Interface.randomSystems) {converter} source target :=
  construction.constructible (Set.mem_singleton converter)

example {A B C : Interface.{u, v}}
    {source : ResourceAlgebra.Specification Interface.randomSystems C}
    {middle : ResourceAlgebra.Specification Interface.randomSystems B}
    {target : ResourceAlgebra.Specification Interface.randomSystems A}
    (inner : ResourceAlgebra.Specification.Constructible
      (Phi := Interface.randomSystems) Set.univ source middle)
    (outer : ResourceAlgebra.Specification.Constructible
      (Phi := Interface.randomSystems) Set.univ middle target) :
    ResourceAlgebra.Specification.Constructible
      (Phi := Interface.randomSystems) Set.univ source target :=
  ResourceAlgebra.Specification.Constructible.serial
    (fun _ _ _ _ => Set.mem_univ _) inner outer

example {A B : Interface.{u, v}} {cost : (A ⟶ B) → ℕ∞}
    {budget budget' : ℕ∞} (included : budget ≤ budget')
    {source : ResourceAlgebra.Specification Interface.randomSystems B}
    {target : ResourceAlgebra.Specification Interface.randomSystems A}
    (construction : ResourceAlgebra.Specification.Constructible
      (Phi := Interface.randomSystems)
      (ResourceAlgebra.Specification.costBounded cost budget) source target) :
    ResourceAlgebra.Specification.Constructible
      (Phi := Interface.randomSystems)
      (ResourceAlgebra.Specification.costBounded cost budget') source target :=
  construction.mono_costBounded included

/-! ## Ordered parallel -/

example {A B : Interface.{u, v}}
    (left : RandomSystem A) (right : RandomSystem B) :
    ResourceAlgebra.parallel (Phi := Interface.randomSystems) left right =
      RandomSystem.parallel left right :=
  rfl

example {A A' B B' : Interface.{u, v}}
    (leftConverter : A' ⟶ A) (rightConverter : B' ⟶ B)
    (left : RandomSystem A) (right : RandomSystem B) :
    attach (Phi := Interface.randomSystems)
        (leftConverter ⊗ₘ rightConverter)
        (ResourceAlgebra.parallel (Phi := Interface.randomSystems) left right) =
      ResourceAlgebra.parallel (Phi := Interface.randomSystems)
        (attach (Phi := Interface.randomSystems) leftConverter left)
        (attach (Phi := Interface.randomSystems) rightConverter right) :=
  ResourceAlgebra.attach_parallel
    (Phi := Interface.randomSystems)
    leftConverter rightConverter left right

example (n : Nat) (outer inner : Fin n → Interface.{u, v})
    (family : (i : Fin n) → (outer i ⟶ inner i))
    (systems : (i : Fin n) → RandomSystem (inner i)) :
    attach (Phi := Interface.randomSystems)
        (ResourceAlgebra.Finite.converters n outer inner family)
        (ResourceAlgebra.Finite.resources
          (Phi := Interface.randomSystems) n inner systems) =
      ResourceAlgebra.Finite.resources
        (Phi := Interface.randomSystems) n outer
        (fun i => attach (Phi := Interface.randomSystems)
          (family i) (systems i)) :=
  ResourceAlgebra.Finite.attach_resources
    (Phi := Interface.randomSystems) n outer inner family systems

example {n : Nat} {interfaces : Fin n → Interface.{u, v}}
    (tuple : ResourceAlgebra.Finite.ConverterTuple interfaces)
    (parties : Set (Fin n)) (i : Fin n) (admitted : i ∈ parties) :
    ResourceAlgebra.Finite.ConverterTuple.partial tuple parties i = tuple i :=
  ResourceAlgebra.Finite.ConverterTuple.partial_apply_of_mem
    tuple parties i admitted

example {n : Nat} {interfaces : Fin n → Interface.{u, v}}
    (left right : ResourceAlgebra.Finite.ConverterTuple interfaces)
    (leftParties rightParties : Set (Fin n))
    (disjoint : Disjoint leftParties rightParties) :
    ResourceAlgebra.Finite.ConverterTuple.converter
        (ResourceAlgebra.Finite.ConverterTuple.partial left leftParties) ≫
      ResourceAlgebra.Finite.ConverterTuple.converter
        (ResourceAlgebra.Finite.ConverterTuple.partial right rightParties) =
    ResourceAlgebra.Finite.ConverterTuple.converter
        (ResourceAlgebra.Finite.ConverterTuple.partial right rightParties) ≫
      ResourceAlgebra.Finite.ConverterTuple.converter
        (ResourceAlgebra.Finite.ConverterTuple.partial left leftParties) :=
  ResourceAlgebra.Finite.ConverterTuple.converter_partial_commute_of_disjoint
    left right leftParties rightParties disjoint

/-! ## Multiparty routing -/

example (interfaces : Fin 0 → Interface.{u, v}) :
    dishonestInterface interfaces (∅ : Set (Fin 0)) = Interface.empty := by
  rfl

example (interfaces : Fin 0 → Interface.{u, v}) :
    honestInterface interfaces (∅ : Set (Fin 0)) = Interface.empty := by
  rfl

example (interfaces : Fin 1 → Interface.{u, v}) :
    dishonestInterface interfaces (Set.univ : Set (Fin 1)) =
      Interface.parallel (interfaces 0) Interface.empty := by
  simp [dishonestInterface, partyInterfaces]

example (interfaces : Fin 1 → Interface.{u, v}) :
    honestInterface interfaces (Set.univ : Set (Fin 1)) =
      Interface.empty := by
  simp [honestInterface, partyInterfaces]

/-- With only the second party dishonest, recursive routing uses the explicit
sum-tag exchange and places that party on the dishonest side. -/
example (interfaces : Fin 2 → Interface.{u, v}) :
    dishonestInterface interfaces ({1} : Set (Fin 2)) =
      Interface.parallel (interfaces 1) Interface.empty := by
  simp [dishonestInterface, partyInterfaces]

example (interfaces : Fin 2 → Interface.{u, v}) :
    honestInterface interfaces ({1} : Set (Fin 2)) =
      Interface.parallel (interfaces 0) Interface.empty := by
  simp [honestInterface, partyInterfaces]

example (interfaces : Fin 2 → Interface.{u, v})
    (tuple : Finite.ConverterTuple interfaces) :
    ∃ converter : DDC (honestInterface interfaces ({1} : Set (Fin 2)))
        (honestInterface interfaces ({1} : Set (Fin 2))),
      DDC.relabel (partyRouting interfaces ({1} : Set (Fin 2)))
          (partyRouting interfaces ({1} : Set (Fin 2)))
          (Finite.ConverterTuple.honestConverter tuple ({1} : Set (Fin 2))) =
        DDC.parallel
          (DDC.forwarding
            (dishonestInterface interfaces ({1} : Set (Fin 2))))
          converter :=
  relabel_honestConverter_eq tuple ({1} : Set (Fin 2))

example {n : Nat} (interfaces : Fin n → Interface.{u, v})
    (dishonest : Set (Fin n)) :
    jointConverter interfaces dishonest
        (DDC.forwarding (dishonestInterface interfaces dishonest)) =
      DDC.forwarding (Finite.interface n interfaces) :=
  jointConverter_forwarding_eq interfaces dishonest

example {n : Nat} (interfaces : Fin n → Interface.{u, v})
    (dishonest : Set (Fin n))
    (first second : CategoryTheory.End
      (dishonestInterface interfaces dishonest)) :
    jointConverter interfaces dishonest (first ≫ second) =
      jointConverter interfaces dishonest first ≫
        jointConverter interfaces dishonest second :=
  jointConverter_serial_eq interfaces dishonest first second

example {n : Nat} (interfaces : Fin n → Interface.{u, v})
    (dishonest : Set (Fin n))
    (converter : CategoryTheory.End (Finite.interface n interfaces)) :
    converter.op ∈ jointConverters interfaces dishonest ↔
      ∃ joint : CategoryTheory.End (dishonestInterface interfaces dishonest),
        jointConverter interfaces dishonest joint = converter :=
  mem_jointConverters_iff interfaces dishonest converter

example {n : Nat} {interfaces : Fin n → Interface.{u, v}}
    (tuple : Finite.ConverterTuple interfaces)
    (dishonest : Set (Fin n))
    (converter : CategoryTheory.End (Finite.interface n interfaces))
    (converterMember : converter.op ∈ jointConverters interfaces dishonest) :
    Function.Commute
      (attach (Phi := Interface.randomSystems)
        (Finite.ConverterTuple.honestConverter tuple dishonest))
      (attach (Phi := Interface.randomSystems) converter) :=
  honestConverter_attach_commute tuple dishonest converter converterMember

/-! ## Distance -/

example {A B : Interface.{u, v}} (converter : A ⟶ B)
    (left right : RandomSystem B) :
    ResourceAlgebra.distance (Phi := Interface.randomSystems)
        (attach (Phi := Interface.randomSystems) converter left)
        (attach (Phi := Interface.randomSystems) converter right) ≤
      ResourceAlgebra.distance (Phi := Interface.randomSystems) left right :=
  ResourceAlgebra.distance_attach_le
    (Phi := Interface.randomSystems) converter left right

example {A B : Interface.{u, v}}
    (left left' : RandomSystem A) (right : RandomSystem B) :
    ResourceAlgebra.distance (Phi := Interface.randomSystems)
        (ResourceAlgebra.parallel (Phi := Interface.randomSystems) left right)
        (ResourceAlgebra.parallel (Phi := Interface.randomSystems) left' right) ≤
      ResourceAlgebra.distance (Phi := Interface.randomSystems) left left' :=
  ResourceAlgebra.distance_parallel_left_le
    (Phi := Interface.randomSystems) left left' right

example {A B : Interface.{u, v}}
    (left : RandomSystem A) (right right' : RandomSystem B) :
    ResourceAlgebra.distance (Phi := Interface.randomSystems)
        (ResourceAlgebra.parallel (Phi := Interface.randomSystems) left right)
        (ResourceAlgebra.parallel (Phi := Interface.randomSystems) left right') ≤
      ResourceAlgebra.distance (Phi := Interface.randomSystems) right right' :=
  ResourceAlgebra.distance_parallel_right_le
    (Phi := Interface.randomSystems) left right right'

example {A B : Interface.{u, v}} {converter : A ⟶ B}
    {source : RandomSystem B} {target : RandomSystem A} {error : ENNReal} :
    ResourceAlgebra.Specification.ConstructsWithin
        (Phi := Interface.randomSystems) converter {source} {target} error ↔
      ResourceAlgebra.distance (Phi := Interface.randomSystems)
        (attach (Phi := Interface.randomSystems) converter source) target ≤ error :=
  ResourceAlgebra.Specification.constructsWithin_singleton_iff

example {A B : Interface.{u, v}} {converter : A ⟶ B}
    {source : ResourceAlgebra.Specification Interface.randomSystems B}
    {target : ResourceAlgebra.Specification Interface.randomSystems A}
    {error : ENNReal} :
    ResourceAlgebra.Specification.Constructs
        (Phi := Interface.randomSystems) converter source
        (ResourceAlgebra.Specification.epsilonRelaxation
          (Phi := Interface.randomSystems) error target) ↔
      ResourceAlgebra.Specification.ConstructsWithin
        (Phi := Interface.randomSystems) converter source target error :=
  ResourceAlgebra.Specification.constructs_epsilonRelaxation_iff

/-! ## Converter-class relaxation -/

example {A : Interface.{u, v}}
    (converters : EndoFamily (Opposite.op A))
    (source : ResourceAlgebra.Specification Interface.randomSystems A) :
    ResourceAlgebra.Specification Interface.randomSystems A :=
  ResourceAlgebra.Specification.star
    (Phi := Interface.randomSystems) converters source

example {A B : Interface.{u, v}} {converter : A ⟶ B}
    {converters : EndoFamily (Opposite.op A)}
    {real : RandomSystem B} {ideal : RandomSystem A}
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    (equation : attach (Phi := Interface.randomSystems) converter real =
      attach (Phi := Interface.randomSystems) simulator ideal) :
    ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) converter {real}
      (ResourceAlgebra.Specification.star
        (Phi := Interface.randomSystems) converters {ideal}) :=
  ResourceAlgebra.Specification.constructs_star_of_simulator
    simulator admitted equation

example {A : Interface.{u, v}} {converter : CategoryTheory.End A}
    {converters : EndoFamily (Opposite.op A)}
    {source target : ResourceAlgebra.Specification Interface.randomSystems A}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : RandomSystem A,
          attach (Phi := Interface.randomSystems) converter
              (attach (Phi := Interface.randomSystems) classConverter resource) =
            attach (Phi := Interface.randomSystems) classConverter
              (attach (Phi := Interface.randomSystems) converter resource))
    (construction : ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) converter source target) :
    ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) converter
      (ResourceAlgebra.Specification.star
        (Phi := Interface.randomSystems) converters source)
      (ResourceAlgebra.Specification.star
        (Phi := Interface.randomSystems) converters target) :=
  construction.star commutes

example {A : Interface.{u, v}}
    {converters : EndoFamily (Opposite.op A)}
    {converter sourceFilter targetFilter simulator : CategoryTheory.End A}
    {real ideal : RandomSystem A}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : RandomSystem A,
          attach (Phi := Interface.randomSystems) converter
              (attach (Phi := Interface.randomSystems) classConverter resource) =
            attach (Phi := Interface.randomSystems) classConverter
              (attach (Phi := Interface.randomSystems) converter resource))
    (simulatorAdmitted : simulator.op ∈ converters)
    (equation :
      attach (Phi := Interface.randomSystems) converter
          (attach (Phi := Interface.randomSystems) sourceFilter real) =
        attach (Phi := Interface.randomSystems) simulator
          (attach (Phi := Interface.randomSystems) targetFilter ideal)) :
    ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) converter
      (ResourceAlgebra.Specification.filteredAt
        (Phi := Interface.randomSystems) converters sourceFilter real)
      (ResourceAlgebra.Specification.filteredAt
        (Phi := Interface.randomSystems) converters targetFilter ideal) :=
  ResourceAlgebra.Specification.filteredAt_constructs_of_eq
    commutes simulatorAdmitted equation

example {A B : Interface.{u, v}} {converter : A ⟶ B}
    {converters : EndoFamily (Opposite.op A)}
    {real : RandomSystem B} {ideal : RandomSystem A} {error : ENNReal}
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    (close : ResourceAlgebra.distance (Phi := Interface.randomSystems)
      (attach (Phi := Interface.randomSystems) converter real)
      (attach (Phi := Interface.randomSystems) simulator ideal) ≤ error) :
    ResourceAlgebra.Specification.Constructs
      (Phi := Interface.randomSystems) converter {real}
      (ResourceAlgebra.Specification.epsilonRelaxation
        (Phi := Interface.randomSystems) error
        (ResourceAlgebra.Specification.star
          (Phi := Interface.randomSystems) converters {ideal})) :=
  ResourceAlgebra.Specification.constructs_of_simulator
    simulator admitted close

/-! ## Common-domain restriction -/

attribute [local instance]
  RandomSystems.CommonDomain.Interface.category

example : AbstractCryptography.Categorical.IsNonexpanding
    RandomSystems.CommonDomain.Interface.randomSystems :=
  inferInstance

end

end RandomSystemsCC.InstantiationTests
