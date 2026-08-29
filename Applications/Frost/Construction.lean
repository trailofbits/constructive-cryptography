/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import ConstructiveCryptography.MultipartyComputation

/-!
# FROST as a two-stage construction

This module states the carrier-independent Constructive Cryptography shape of
FROST. Distributed key generation constructs the ideal threshold-key
resource; signing from those keys constructs the ideal threshold-signing
resource. The two constructions compose for every dishonest set.

The concrete random-system carrier must later prove the simulator equations
and the ideal unforgeability bound. This file assumes neither a concrete
carrier nor independently factorized dishonest converters. For each
dishonest set `Z`, `converters Z` is one composition-closed family of joint
converters on the assembled party interface, as required by the merged
interface reading of Liu--Maurer 2020, Section 2.5 (printed pp. 7--8).
-/

open scoped ENNReal

namespace AbstractCryptography
namespace Frost

open CategoryTheory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open ConstructiveCryptography.Multiparty

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-! ## Exact construction leaves -/

omit [ResourceAlgebra C Phi] in
/-- FROST signing constructs the joint-converter relaxation of the ideal
threshold-signing resource from the threshold-key specification.

The hypotheses are the carrier's per-resource simulator equations. The
deterministic signing equations are proved in `Applications.Frost.Protocol`;
the probability argument belongs to the concrete carrier. -/
theorem constructs_tss_from_keys_of_simulators
    {n : Nat} {interfaces : Fin n → C}
    (adversaryStructure : AdversaryStructure (Fin n))
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (πsign : Finite.ConverterTuple interfaces)
    (keysSpec : Set (Fin n) →
      ResourceAlgebra.Specification Phi (Finite.interface n interfaces))
    (tss : Resource Phi (Finite.interface n interfaces))
    (simulates : ∀ dishonest ∈ adversaryStructure.sets,
      ∀ resource ∈ keysSpec dishonest,
        ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
          simulator.op ∈ converters dishonest ∧
            attach (Phi := Phi)
                (Finite.ConverterTuple.honestConverter πsign dishonest)
                resource =
              attach (Phi := Phi) simulator tss) :
    ConstructsForAdversaryStructure (Phi := Phi) adversaryStructure πsign
      keysSpec
      (fun dishonest => zStar (Phi := Phi) converters dishonest
        ({tss} : ResourceAlgebra.Specification Phi
          (Finite.interface n interfaces))) :=
  ConstructsForAdversaryStructure.zStar_of_simulators
    adversaryStructure πsign converters keysSpec tss simulates

omit [ResourceAlgebra C Phi] in
/-- FROST distributed key generation constructs the joint-converter
relaxation of the ideal threshold-key resource from the assumed resources.

The hypotheses are the carrier's per-resource simulator equations. The
deterministic key-generation equations are proved in
`Applications.Frost.Protocol`; the probability argument belongs to the
concrete carrier. -/
theorem constructs_keys_of_simulators
    {n : Nat} {interfaces : Fin n → C}
    (adversaryStructure : AdversaryStructure (Fin n))
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (πdkg : Finite.ConverterTuple interfaces)
    (netSpec : Set (Fin n) →
      ResourceAlgebra.Specification Phi (Finite.interface n interfaces))
    (keys : Resource Phi (Finite.interface n interfaces))
    (simulates : ∀ dishonest ∈ adversaryStructure.sets,
      ∀ resource ∈ netSpec dishonest,
        ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
          simulator.op ∈ converters dishonest ∧
            attach (Phi := Phi)
                (Finite.ConverterTuple.honestConverter πdkg dishonest)
                resource =
              attach (Phi := Phi) simulator keys) :
    ConstructsForAdversaryStructure (Phi := Phi) adversaryStructure πdkg
      netSpec
      (fun dishonest => zStar (Phi := Phi) converters dishonest
        ({keys} : ResourceAlgebra.Specification Phi
          (Finite.interface n interfaces))) :=
  ConstructsForAdversaryStructure.zStar_of_simulators
    adversaryStructure πdkg converters netSpec keys simulates

/-! ## Two-stage construction -/

omit [ResourceAlgebra C Phi] in
/-- The FROST construction is the serial composition of distributed key
generation and signing. A game bound on the ideal threshold-signing resource
is inherited by every constructed real resource when the test family is
closed under the admitted joint converter class. -/
theorem constructs_and_gameSpec_of_stages
    {n : Nat} {interfaces : Fin n → C}
    (adversaryStructure : AdversaryStructure (Fin n))
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (assumed dkgSpec : Set (Fin n) →
      ResourceAlgebra.Specification Phi (Finite.interface n interfaces))
    (tss : Resource Phi (Finite.interface n interfaces))
    (πdkg πsign : Finite.ConverterTuple interfaces)
    (tests : Set (Fin n) →
      Set (Resource Phi (Finite.interface n interfaces) → ENNReal))
    (error : ENNReal)
    (dkgConstruction : ConstructsForAdversaryStructure (Phi := Phi)
      adversaryStructure πdkg assumed dkgSpec)
    (signingConstruction : ConstructsForAdversaryStructure (Phi := Phi)
      adversaryStructure πsign dkgSpec
        (fun dishonest => zStar (Phi := Phi) converters dishonest
          ({tss} : ResourceAlgebra.Specification Phi
            (Finite.interface n interfaces))))
    (closed : ∀ dishonest ∈ adversaryStructure.sets,
      ClosedUnderConverterClass (Phi := Phi)
        (converters dishonest) (tests dishonest))
    (idealBound : ∀ dishonest ∈ adversaryStructure.sets,
      tss ∈ gameSpec (Phi := Phi) (tests dishonest) error) :
    ConstructsForAdversaryStructure (Phi := Phi) adversaryStructure
        (fun i => πsign i ≫ πdkg i) assumed
        (fun dishonest => zStar (Phi := Phi) converters dishonest
          ({tss} : ResourceAlgebra.Specification Phi
            (Finite.interface n interfaces))) ∧
      ∀ dishonest ∈ adversaryStructure.sets,
        ∀ resource ∈ assumed dishonest,
          attach (Phi := Phi)
              (Finite.ConverterTuple.honestConverter
                (fun i => πsign i ≫ πdkg i) dishonest)
              resource ∈
            gameSpec (Phi := Phi) (tests dishonest) error := by
  -- Compose distributed key generation and signing at every dishonest set.
  have construction := dkgConstruction.serial signingConstruction
  refine ⟨construction, ?_⟩
  -- Fix an admitted dishonest set and an admitted real resource.
  intro dishonest dishonestAdmitted resource resourceAdmitted
  simp only [ConstructsForAdversaryStructure, ConstructsForAll] at construction
  have relaxed := ResourceAlgebra.Specification.constructs_iff.mp
    (construction dishonest) resource resourceAdmitted
  simp only [if_pos dishonestAdmitted] at relaxed
  -- Closed tests carry the ideal game bound through the joint simulator.
  exact zStar_subset_gameSpec
    (closed dishonest dishonestAdmitted)
    (idealBound dishonest dishonestAdmitted) relaxed

omit [ResourceAlgebra C Phi] in
/-- From the two families of exact simulator equations, FROST constructs the
joint-converter relaxation of the ideal threshold-signing resource and
inherits its game bound. -/
theorem constructs_and_gameSpec_of_simulators
    {n : Nat} {interfaces : Fin n → C}
    (adversaryStructure : AdversaryStructure (Fin n))
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (πdkg πsign : Finite.ConverterTuple interfaces)
    (netSpec : Set (Fin n) →
      ResourceAlgebra.Specification Phi (Finite.interface n interfaces))
    (keys tss : Resource Phi (Finite.interface n interfaces))
    (tests : Set (Fin n) →
      Set (Resource Phi (Finite.interface n interfaces) → ENNReal))
    (error : ENNReal)
    (dkgSimulates : ∀ dishonest ∈ adversaryStructure.sets,
      ∀ resource ∈ netSpec dishonest,
        ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
          simulator.op ∈ converters dishonest ∧
            attach (Phi := Phi)
                (Finite.ConverterTuple.honestConverter πdkg dishonest)
                resource =
              attach (Phi := Phi) simulator keys)
    (signingSimulates : ∀ dishonest ∈ adversaryStructure.sets,
      ∀ resource ∈ zStar (Phi := Phi) converters dishonest
          ({keys} : ResourceAlgebra.Specification Phi
            (Finite.interface n interfaces)),
        ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
          simulator.op ∈ converters dishonest ∧
            attach (Phi := Phi)
                (Finite.ConverterTuple.honestConverter πsign dishonest)
                resource =
              attach (Phi := Phi) simulator tss)
    (closed : ∀ dishonest ∈ adversaryStructure.sets,
      ClosedUnderConverterClass (Phi := Phi)
        (converters dishonest) (tests dishonest))
    (idealBound : ∀ dishonest ∈ adversaryStructure.sets,
      tss ∈ gameSpec (Phi := Phi) (tests dishonest) error) :
    ConstructsForAdversaryStructure (Phi := Phi) adversaryStructure
        (fun i => πsign i ≫ πdkg i) netSpec
        (fun dishonest => zStar (Phi := Phi) converters dishonest
          ({tss} : ResourceAlgebra.Specification Phi
            (Finite.interface n interfaces))) ∧
      ∀ dishonest ∈ adversaryStructure.sets,
        ∀ resource ∈ netSpec dishonest,
          attach (Phi := Phi)
              (Finite.ConverterTuple.honestConverter
                (fun i => πsign i ≫ πdkg i) dishonest)
              resource ∈
            gameSpec (Phi := Phi) (tests dishonest) error :=
  constructs_and_gameSpec_of_stages adversaryStructure converters netSpec
    (fun dishonest => zStar (Phi := Phi) converters dishonest
      ({keys} : ResourceAlgebra.Specification Phi
        (Finite.interface n interfaces)))
    tss πdkg πsign tests error
    (constructs_keys_of_simulators adversaryStructure converters πdkg netSpec keys
      dkgSimulates)
    (constructs_tss_from_keys_of_simulators adversaryStructure converters πsign
      (fun dishonest => zStar (Phi := Phi) converters dishonest
        ({keys} : ResourceAlgebra.Specification Phi
          (Finite.interface n interfaces)))
      tss signingSimulates)
    closed idealBound

/-! ## Threshold specialization -/

omit [ResourceAlgebra C Phi] in
/-- At threshold `t`, the two-stage FROST construction additionally exposes
the `Q3` condition when `3 * t < n`. Closing the supplied base-test family
under the admitted joint converters discharges the closure premise. -/
theorem threshold_constructs_and_gameSpec
    {n t : Nat} {interfaces : Fin n → C}
    (bound : 3 * t < n)
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (πdkg πsign : Finite.ConverterTuple interfaces)
    (netSpec : Set (Fin n) →
      ResourceAlgebra.Specification Phi (Finite.interface n interfaces))
    (keys tss : Resource Phi (Finite.interface n interfaces))
    (baseTests : Set (Fin n) →
      Set (Resource Phi (Finite.interface n interfaces) → ENNReal))
    (error : ENNReal)
    (dkgSimulates : ∀ dishonest ∈ (AdversaryStructure.threshold n t).sets,
      ∀ resource ∈ netSpec dishonest,
        ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
          simulator.op ∈ converters dishonest ∧
            attach (Phi := Phi)
                (Finite.ConverterTuple.honestConverter πdkg dishonest)
                resource =
              attach (Phi := Phi) simulator keys)
    (signingSimulates :
      ∀ dishonest ∈ (AdversaryStructure.threshold n t).sets,
        ∀ resource ∈ zStar (Phi := Phi) converters dishonest
            ({keys} : ResourceAlgebra.Specification Phi
              (Finite.interface n interfaces)),
          ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
            simulator.op ∈ converters dishonest ∧
              attach (Phi := Phi)
                  (Finite.ConverterTuple.honestConverter πsign dishonest)
                  resource =
                attach (Phi := Phi) simulator tss)
    (idealBound : ∀ dishonest ∈ (AdversaryStructure.threshold n t).sets,
      tss ∈ gameSpec (Phi := Phi)
        (testClosure (Phi := Phi) (converters dishonest)
          (baseTests dishonest)) error) :
    (AdversaryStructure.threshold n t).Q3 Set.univ ∧
      ConstructsForAdversaryStructure (Phi := Phi)
        (AdversaryStructure.threshold n t)
        (fun i => πsign i ≫ πdkg i) netSpec
        (fun dishonest => zStar (Phi := Phi) converters dishonest
          ({tss} : ResourceAlgebra.Specification Phi
            (Finite.interface n interfaces))) ∧
      ∀ dishonest ∈ (AdversaryStructure.threshold n t).sets,
        ∀ resource ∈ netSpec dishonest,
          attach (Phi := Phi)
              (Finite.ConverterTuple.honestConverter
                (fun i => πsign i ≫ πdkg i) dishonest)
              resource ∈
            gameSpec (Phi := Phi)
              (testClosure (Phi := Phi) (converters dishonest)
                (baseTests dishonest)) error := by
  -- The cardinality hypothesis gives Liu--Maurer's `Q3` condition.
  refine ⟨AdversaryStructure.threshold_Q3 bound, ?_⟩
  -- Converter closure supplies the closure hypothesis of the exact theorem.
  exact constructs_and_gameSpec_of_simulators (Phi := Phi)
    (AdversaryStructure.threshold n t) converters πdkg πsign
    netSpec keys tss
    (fun dishonest => testClosure (Phi := Phi)
      (converters dishonest) (baseTests dishonest)) error
    dkgSimulates signingSimulates
    (fun dishonest _ =>
      closedUnderConverterClass_testClosure
        (Phi := Phi) (converters dishonest) (baseTests dishonest))
    idealBound

omit [ResourceAlgebra C Phi] in
/-- Without the `Q3` conclusion, the exact FROST construction only requires
the admitted threshold sets and the two simulator families. This is the
endpoint for applications that assume broadcast rather than construct it. -/
theorem threshold_unforgeability
    {n t : Nat} {interfaces : Fin n → C}
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (πdkg πsign : Finite.ConverterTuple interfaces)
    (netSpec : Set (Fin n) →
      ResourceAlgebra.Specification Phi (Finite.interface n interfaces))
    (keys tss : Resource Phi (Finite.interface n interfaces))
    (baseTests : Set (Fin n) →
      Set (Resource Phi (Finite.interface n interfaces) → ENNReal))
    (error : ENNReal)
    (dkgSimulates : ∀ dishonest ∈ (AdversaryStructure.threshold n t).sets,
      ∀ resource ∈ netSpec dishonest,
        ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
          simulator.op ∈ converters dishonest ∧
            attach (Phi := Phi)
                (Finite.ConverterTuple.honestConverter πdkg dishonest)
                resource =
              attach (Phi := Phi) simulator keys)
    (signingSimulates :
      ∀ dishonest ∈ (AdversaryStructure.threshold n t).sets,
        ∀ resource ∈ zStar (Phi := Phi) converters dishonest
            ({keys} : ResourceAlgebra.Specification Phi
              (Finite.interface n interfaces)),
          ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
            simulator.op ∈ converters dishonest ∧
              attach (Phi := Phi)
                  (Finite.ConverterTuple.honestConverter πsign dishonest)
                  resource =
                attach (Phi := Phi) simulator tss)
    (idealBound : ∀ dishonest ∈ (AdversaryStructure.threshold n t).sets,
      tss ∈ gameSpec (Phi := Phi)
        (testClosure (Phi := Phi) (converters dishonest)
          (baseTests dishonest)) error) :
    ConstructsForAdversaryStructure (Phi := Phi)
        (AdversaryStructure.threshold n t)
        (fun i => πsign i ≫ πdkg i) netSpec
        (fun dishonest => zStar (Phi := Phi) converters dishonest
          ({tss} : ResourceAlgebra.Specification Phi
            (Finite.interface n interfaces))) ∧
      ∀ dishonest ∈ (AdversaryStructure.threshold n t).sets,
        ∀ resource ∈ netSpec dishonest,
          attach (Phi := Phi)
              (Finite.ConverterTuple.honestConverter
                (fun i => πsign i ≫ πdkg i) dishonest)
              resource ∈
            gameSpec (Phi := Phi)
              (testClosure (Phi := Phi) (converters dishonest)
                (baseTests dishonest)) error :=
  constructs_and_gameSpec_of_simulators (Phi := Phi)
    (AdversaryStructure.threshold n t) converters πdkg πsign
    netSpec keys tss
    (fun dishonest => testClosure (Phi := Phi)
      (converters dishonest) (baseTests dishonest)) error
    dkgSimulates signingSimulates
    (fun dishonest _ =>
      closedUnderConverterClass_testClosure
        (Phi := Phi) (converters dishonest) (baseTests dishonest))
    idealBound

end Frost
end AbstractCryptography
