/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import ConstructiveCryptography.MultipartyComputation

set_option autoImplicit false

/-!
# Multiparty computation tests

These tests import only the public multiparty root and use its selected
`ResourceAlgebra`. They check the converter tuple, joint dishonest
converter closure, approximate construction, and adversary-structure assembly
without installing another resource model.
-/

namespace ConstructiveCryptography.Tests.MultipartyComputation

open CategoryTheory
open ConstructiveCryptography.Categorical
open ConstructiveCryptography.Categorical.ResourceAlgebra
open ConstructiveCryptography.Multiparty

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

/-! ## Ordered converter tuples -/

/-- Honest-party restriction preserves the paper's serial application order.

Liu--Maurer 2020, Definition 1 (printed p. 7), applies the protocol tuple at
`P \ Z`; the ordered tuple assembly retains that restriction under serial
composition. -/
example {n : Nat} {interfaces : Fin n → C}
    (outer inner : Finite.ConverterTuple interfaces)
    (dishonest : Set (Fin n)) :
    Finite.ConverterTuple.honestConverter
        (fun i ↦ outer i ≫ inner i) dishonest =
      Finite.ConverterTuple.honestConverter outer dishonest ≫
        Finite.ConverterTuple.honestConverter inner dishonest := by
  -- Restrict each tuple to the honest positions, then assemble in order.
  exact Finite.ConverterTuple.honestConverter_serial
    outer inner dishonest

/-- Disjoint partial tuples commute after ordered assembly, without a symmetry
law for the ambient tensor. -/
example {n : Nat} {interfaces : Fin n → C}
    (left right : Finite.ConverterTuple interfaces)
    (leftParties rightParties : Set (Fin n))
    (disjoint : Disjoint leftParties rightParties) :
    Finite.ConverterTuple.converter
          (Finite.ConverterTuple.partial left leftParties) ≫
        Finite.ConverterTuple.converter
          (Finite.ConverterTuple.partial right rightParties) =
      Finite.ConverterTuple.converter
          (Finite.ConverterTuple.partial right rightParties) ≫
        Finite.ConverterTuple.converter
          (Finite.ConverterTuple.partial left leftParties) := by
  -- At every ordered position, disjointness makes one component identity.
  exact Finite.ConverterTuple.converter_partial_commute_of_disjoint
    left right leftParties rightParties disjoint

/-! ## Joint dishonest-interface closure -/

/-- Per-resource approximate simulators construct between the two `*Z`
closures with the same scalar error.

Liu--Maurer 2020, Section 2.5 (printed pp. 7--8), merges the interfaces in
`Z`; the simulator is therefore one joint endomorphism, not a tuple of
independent dishonest-party converters. -/
example {I : Type*} {A : C}
    (converters : Set I → EndoFamily (Opposite.op A))
    {dishonest : Set I} {converter : CategoryTheory.End A}
    {source : ResourceAlgebra.Specification Phi A} {ideal : Resource Phi A}
    {error : ENNReal}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters dishonest →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (simulates : ∀ resource ∈ source,
      ∃ simulator : CategoryTheory.End A,
        simulator.op ∈ converters dishonest ∧
          distance (Phi := Phi) (attach (Phi := Phi) converter resource)
            (attach (Phi := Phi) simulator ideal) ≤ error) :
    ResourceAlgebra.Specification.ConstructsWithin (Phi := Phi) converter
      (zStar (Phi := Phi) converters dishonest source)
      (zStar (Phi := Phi) converters dishonest
        ({ideal} : ResourceAlgebra.Specification Phi A)) error := by
  -- First use the simulator bounds, then move the converter through `*Z`.
  exact constructsWithin_zStar_of_simulators converters commutes simulates

/-- One joint simulator per admitted source resource assembles every
adversary-structure construction.

Liu--Maurer 2020, Section 2.5 (printed p. 8), chooses the converter after the
resource `U`; Section 2.4 (printed p. 7) gives the trivial target outside the
adversary structure. -/
example {n : Nat} {interfaces : Fin n → C}
    (adversaryStructure : AdversaryStructure (Fin n))
    (tuple : Finite.ConverterTuple interfaces)
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (source : Set (Fin n) →
      ResourceAlgebra.Specification Phi (Finite.interface n interfaces))
    (ideal : Resource Phi (Finite.interface n interfaces))
    (simulates : ∀ dishonest ∈ adversaryStructure.sets,
      ∀ resource ∈ source dishonest,
        ∃ simulator : CategoryTheory.End (Finite.interface n interfaces),
          simulator.op ∈ converters dishonest ∧
            attach (Phi := Phi)
                (Finite.ConverterTuple.honestConverter tuple dishonest)
                resource =
              attach (Phi := Phi) simulator ideal) :
    ConstructsForAdversaryStructure (Phi := Phi) adversaryStructure tuple source
      (fun dishonest ↦ zStar (Phi := Phi) converters dishonest
        ({ideal} : ResourceAlgebra.Specification Phi (Finite.interface n interfaces))) := by
  -- Assemble the honest tuple and the explicit joint simulator at every `Z`.
  exact ConstructsForAdversaryStructure.zStar_of_simulators
    adversaryStructure tuple converters source ideal simulates

/-! ## Threshold adversary structures -/

/-- The threshold condition supplies `Q3` and hence the two-set consequence
used in the Liu--Maurer MPC assembly. -/
example {n t : Nat} (bound : 3 * t < n)
    {first second : Set (Fin n)}
    (firstAdmitted : first ∈ (AdversaryStructure.threshold n t).sets)
    (secondAdmitted : second ∈ (AdversaryStructure.threshold n t).sets) :
    ¬ (Set.univ : Set (Fin n)) ⊆ first ∪ second := by
  -- Three threshold-admitted sets cannot cover all parties.
  have q3 := AdversaryStructure.threshold_Q3 (n := n) (t := t) bound
  -- Repeating one admitted set yields the required two-set consequence.
  exact q3.two_not_cover firstAdmitted secondAdmitted

#print axioms Finite.ConverterTuple.honestConverter_serial
#print axioms Finite.ConverterTuple.converter_partial_commute_of_disjoint
#print axioms constructsWithin_zStar_of_simulators
#print axioms ConstructsForAdversaryStructure.zStar_of_simulators
#print axioms AdversaryStructure.threshold_Q3

end ConstructiveCryptography.Tests.MultipartyComputation
