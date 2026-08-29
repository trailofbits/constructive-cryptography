/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Data.Set.Card
import ConstructiveCryptography
import AbstractCryptography.SemanticRegistry

set_option autoImplicit false

/-!
# Multiparty constructions

This module formalizes Liu--Maurer 2020, Sections 2.4--2.5 and its Section 8
adversary-structure condition, over the single typed `ResourceAlgebra`
presentation.

For an ordered family of party interfaces, an honest converter tuple is
restricted to `P \ Z` and assembled by ordered tensor. The dishonest parties
are represented separately by one explicit composition-closed family of joint
endomorphisms at the assembled interface. This distinction is essential:
Liu--Maurer, Section 2.5 (printed pp. 7--8), treats the interfaces in `Z` as one
merged interface under a central adversary, so the joint converter need not
factor into independent party converters.

Jost, Section 2.2.2 (printed p. 18), defines a protocol as “a (partial) tuple
of converter-connection pairs.” `Finite.ConverterTuple` is the
canonical-connection, interface-preserving specialization. Jost's
composition-order independence is an equality of the resulting resource
attachments; star lifting below assumes exactly that functional equality, not
equality of raw converter arrows. Jost does not require the `*Z`
specialization and does not require symmetry of parallel composition.
-/

namespace ConstructiveCryptography.Multiparty

open CategoryTheory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-! ## Construction for every dishonest set -/

/-- A converter tuple constructs one specification family from another when
the converters at every honest set `P \ Z` establish the corresponding
construction.

Liu--Maurer 2020, Definition 1 (printed p. 7): “The protocol
`pi = (pi_1, ..., pi_n)` constructs specifications `S_Z` from `R_Z` if
`forall Z subseteq P, R_Z --pi^{P\Z}--> S_Z`.” -/
@[crypto_rule "cc.mpc.constructs_for_all" mpc_construction constructive_crypto]
noncomputable def ConstructsForAll {n : Nat} {interfaces : Fin n → C}
    (tuple : Finite.ConverterTuple interfaces)
    (source target : Set (Fin n) →
      Specification Phi (Finite.interface n interfaces)) : Prop :=
  ∀ dishonest : Set (Fin n),
    Specification.Constructs (Phi := Phi)
      (Finite.ConverterTuple.honestConverter tuple dishonest)
      (source dishonest) (target dishonest)

omit [ResourceAlgebra C Phi] in
/-- Multiparty constructions compose pointwise in every dishonest set. -/
@[crypto_rule "cc.mpc.constructs_for_all.serial" mpc_construction constructive_crypto]
theorem ConstructsForAll.serial {n : Nat} {interfaces : Fin n → C}
    {innerTuple outerTuple : Finite.ConverterTuple interfaces}
    {source middle target : Set (Fin n) →
      Specification Phi (Finite.interface n interfaces)}
    (inner : ConstructsForAll (Phi := Phi) innerTuple source middle)
    (outer : ConstructsForAll (Phi := Phi) outerTuple middle target) :
    ConstructsForAll (Phi := Phi)
      (fun i => outerTuple i ≫ innerTuple i) source target := by
  intro dishonest
  -- Compose the two construction statements for this dishonest set.
  have composed := (inner dishonest).serial (outer dishonest)
  -- Honest selection and ordered assembly preserve serial composition.
  simpa only [Finite.ConverterTuple.honestConverter_serial] using composed

omit [ResourceAlgebra C Phi] in
/-- Multiparty construction admits ordinary `calc` chaining in serial order. -/
instance instTransConstructsForAll {n : Nat} {interfaces : Fin n → C}
    {innerTuple outerTuple : Finite.ConverterTuple interfaces} :
    Trans (ConstructsForAll (Phi := Phi) innerTuple)
      (ConstructsForAll (Phi := Phi) outerTuple)
      (ConstructsForAll (Phi := Phi)
        (fun i => outerTuple i ≫ innerTuple i)) where
  trans := ConstructsForAll.serial

omit [ResourceAlgebra C Phi] in
/-- Every converter tuple constructs the trivial specification family. -/
theorem constructsForAll_univ {n : Nat} {interfaces : Fin n → C}
    (tuple : Finite.ConverterTuple interfaces)
    (source : Set (Fin n) →
      Specification Phi (Finite.interface n interfaces)) :
    ConstructsForAll (Phi := Phi) tuple source (fun _ => Set.univ) := by
  intro dishonest
  -- The target admits every attached resource.
  exact fun _ _ => Set.mem_univ _

omit [ResourceAlgebra C Phi] in
/-- Filtered multiparty endpoints follow from one joint simulator at each
dishonest set.

Liu--Maurer 2020, Section 2.5 (printed p. 8): “If the same α works for every
U, then one can think of α as corresponding to a (joint) simulator.” Lean
keeps that joint simulator and its admitted converter family explicit. -/
theorem ConstructsForAll.filteredAt_of_simulators
    {n : Nat} {interfaces : Fin n → C}
    {tuple sourceFilter targetFilter : Finite.ConverterTuple interfaces}
    {real ideal : Resource Phi (Finite.interface n interfaces)}
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (simulator : ∀ _dishonest : Set (Fin n),
      CategoryTheory.End (Finite.interface n interfaces))
    (commutes : ∀ dishonest classConverter,
      classConverter.op ∈ converters dishonest →
        ∀ resource : Resource Phi (Finite.interface n interfaces),
          attach (Phi := Phi)
              (Finite.ConverterTuple.honestConverter tuple dishonest)
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi)
                (Finite.ConverterTuple.honestConverter tuple dishonest)
                resource))
    (simulatorAdmitted : ∀ dishonest,
      (simulator dishonest).op ∈ converters dishonest)
    (equation : ∀ dishonest,
      attach (Phi := Phi)
          (Finite.ConverterTuple.honestConverter tuple dishonest)
          (attach (Phi := Phi)
            (Finite.ConverterTuple.honestConverter sourceFilter dishonest)
            real) =
        attach (Phi := Phi) (simulator dishonest)
          (attach (Phi := Phi)
            (Finite.ConverterTuple.honestConverter targetFilter dishonest)
            ideal)) :
    ConstructsForAll (Phi := Phi) tuple
      (fun dishonest => Specification.filteredAt (Phi := Phi)
        (converters dishonest)
        (Finite.ConverterTuple.honestConverter sourceFilter dishonest) real)
      (fun dishonest => Specification.filteredAt (Phi := Phi)
        (converters dishonest)
        (Finite.ConverterTuple.honestConverter targetFilter dishonest) ideal) := by
  intro dishonest
  -- Apply the generic filtered-endpoint theorem at this dishonest set.
  exact Specification.filteredAt_constructs_of_eq
    (commutes dishonest) (simulatorAdmitted dishonest) (equation dishonest)

/-! ## The `*Z` relaxation -/

/-- Closure under the admitted joint converter class for a dishonest set.

Liu--Maurer 2020, Section 2.5 (printed pp. 7--8): “If we consider a set `Z`
of potentially dishonest parties, we can consider the set of interfaces in
`Z` as being merged to a single interface with several sub-interfaces, and
applying the above relaxation to this interface.”

The abstract category cannot inspect ports. Consequently, the supplied family
at `Z` must be realized by the concrete carrier as converters supported on the
merged `Z` interface. An arbitrary endomorphism family on the assembled
interface does not establish that support property by typing alone. -/
noncomputable def zStar {I : Type*} {A : C}
    (converters : Set I → EndoFamily (Opposite.op A))
    (dishonest : Set I) (source : Specification Phi A) :
    Specification Phi A :=
  Specification.star (Phi := Phi) (converters dishonest) source

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Joint-converter closure at one dishonest set is idempotent. -/
theorem zStar_idem {I : Type*} {A : C}
    (converters : Set I → EndoFamily (Opposite.op A))
    (dishonest : Set I) (source : Specification Phi A) :
    zStar (Phi := Phi) converters dishonest
        (zStar (Phi := Phi) converters dishonest source) =
      zStar (Phi := Phi) converters dishonest source :=
  Specification.star_idem (Phi := Phi) (converters dishonest) source

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Inclusion of joint converter classes gives inclusion of their closures. -/
theorem zStar_mono {I : Type*} {A : C}
    {converters : Set I → EndoFamily (Opposite.op A)}
    {dishonest dishonest' : Set I}
    (included : converters dishonest ≤ converters dishonest')
    (source : Specification Phi A) :
    zStar (Phi := Phi) converters dishonest source ⊆
      zStar (Phi := Phi) converters dishonest' source :=
  Specification.star_mono (Phi := Phi) included source

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Functional composition-order independence moves a converter through a
`*Z`-relaxed source. -/
theorem attach_zStar_subset {I : Type*} {A : C}
    {converters : Set I → EndoFamily (Opposite.op A)}
    {dishonest : Set I} {converter : CategoryTheory.End A}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters dishonest →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (source : Specification Phi A) :
    Specification.map (Phi := Phi) converter
        (zStar (Phi := Phi) converters dishonest source) ⊆
      zStar (Phi := Phi) converters dishonest
        (Specification.map (Phi := Phi) converter source) :=
  Specification.map_star_subset (Phi := Phi) commutes source

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Exact simulator equations lift a construction through `*Z` on both
endpoint specifications. -/
theorem constructs_zStar_of_simulators {I : Type*} {A : C}
    (converters : Set I → EndoFamily (Opposite.op A))
    {dishonest : Set I} {converter : CategoryTheory.End A}
    {source : Specification Phi A} {ideal : Resource Phi A}
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
          attach (Phi := Phi) converter resource =
            attach (Phi := Phi) simulator ideal) :
    Specification.Constructs (Phi := Phi) converter
      (zStar (Phi := Phi) converters dishonest source)
      (zStar (Phi := Phi) converters dishonest
        ({ideal} : Specification Phi A)) := by
  -- Simulator equations construct the star-relaxed ideal from the base source.
  have base := Specification.constructs_star_of_simulators
    (Phi := Phi) simulates
  -- Functional order independence star-relaxes the source as well.
  simpa only [zStar,
    AbstractCryptography.Categorical.ResourceAlgebra.Specification.star_idem]
    using base.star commutes

/-- Approximate simulator equations lift a construction through `*Z` on both
endpoint specifications. -/
theorem constructsWithin_zStar_of_simulators {I : Type*} {A : C}
    (converters : Set I → EndoFamily (Opposite.op A))
    {dishonest : Set I} {converter : CategoryTheory.End A}
    {source : Specification Phi A} {ideal : Resource Phi A}
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
    Specification.ConstructsWithin (Phi := Phi) converter
      (zStar (Phi := Phi) converters dishonest source)
      (zStar (Phi := Phi) converters dishonest
        ({ideal} : Specification Phi A)) error := by
  -- Distance-bounded simulators construct within error from the base source.
  have base := Specification.constructsWithin_star_of_simulators
    (Phi := Phi) simulates
  -- Functional order independence star-relaxes the source as well.
  simpa only [zStar,
    AbstractCryptography.Categorical.ResourceAlgebra.Specification.star_idem]
    using base.star commutes

/-- Approximate simulator equations give exact construction into the scalar
relaxation of the `*Z`-relaxed ideal. -/
theorem constructs_zStar_epsilonRelaxation_of_simulators
    {I : Type*} {A : C}
    (converters : Set I → EndoFamily (Opposite.op A))
    {dishonest : Set I} {converter : CategoryTheory.End A}
    {source : Specification Phi A} {ideal : Resource Phi A}
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
    Specification.Constructs (Phi := Phi) converter
      (zStar (Phi := Phi) converters dishonest source)
      (Specification.epsilonRelaxation (Phi := Phi) error
        (zStar (Phi := Phi) converters dishonest
          ({ideal} : Specification Phi A))) := by
  -- Scalar relaxation is the exact presentation of approximate construction.
  rw [Specification.constructs_epsilonRelaxation_iff]
  exact constructsWithin_zStar_of_simulators converters commutes simulates

/-! ## Adversary structures -/

/-- A monotone family of possible dishonest-party sets.

Liu--Maurer 2020, Section 8 (printed p. 18): “an adversary structure `Z`,
which is a monotone set of subsets of parties, where each subset indicates a
possible set of dishonest parties.” -/
structure AdversaryStructure (I : Type*) where
  /-- The possible dishonest-party sets. -/
  sets : Set (Set I)
  /-- Every subset of a possible dishonest-party set is possible. -/
  mono : ∀ {dishonest dishonest' : Set I},
    dishonest' ⊆ dishonest → dishonest ∈ sets → dishonest' ∈ sets

namespace AdversaryStructure

variable {I : Type*}

/-- No three possible dishonest-party sets cover the protected party set.

Liu--Maurer 2020, Section 8 (printed p. 18): “no three sets in `Z` cover
`[n - 1]`, also known as `Q^3([n - 1], Z)`.” -/
def Q3 (adversaryStructure : AdversaryStructure I) (parties : Set I) : Prop :=
  ∀ first ∈ adversaryStructure.sets,
    ∀ second ∈ adversaryStructure.sets,
      ∀ third ∈ adversaryStructure.sets,
        ¬ parties ⊆ first ∪ second ∪ third

/-- Under `Q3`, two possible dishonest-party sets do not cover the protected
party set. -/
theorem Q3.two_not_cover {adversaryStructure : AdversaryStructure I}
    {parties : Set I} (q3 : adversaryStructure.Q3 parties)
    {first second : Set I}
    (firstAdmitted : first ∈ adversaryStructure.sets)
    (secondAdmitted : second ∈ adversaryStructure.sets) :
    ¬ parties ⊆ first ∪ second := by
  intro covers
  -- Repeating the second set would give three admitted sets covering `parties`.
  exact q3 first firstAdmitted second secondAdmitted second secondAdmitted
    (by simpa [Set.union_assoc] using covers)

/-- The threshold adversary structure contains the sets of at most `t`
dishonest parties.

Liu--Maurer 2020, Section 2.4 (printed p. 7): “for example that there are at
most `t` dishonest parties.” -/
def threshold (n t : Nat) : AdversaryStructure (Fin n) where
  sets := {dishonest | dishonest.ncard ≤ t}
  mono included admitted :=
    le_trans (Set.ncard_le_ncard included (Set.toFinite _)) admitted

/-- Three threshold-admitted dishonest sets cannot cover `Fin n` when
`3 * t < n`. -/
theorem threshold_Q3 {n t : Nat} (bound : 3 * t < n) :
    (threshold n t).Q3 Set.univ := by
  intro first firstAdmitted second secondAdmitted third thirdAdmitted covers
  -- Three admitted sets have total cardinality at most `3 * t`.
  have cardinalityBound : (first ∪ second ∪ third).ncard ≤ 3 * t := by
    calc
      (first ∪ second ∪ third).ncard
          ≤ (first ∪ second).ncard + third.ncard :=
        Set.ncard_union_le _ _
      _ ≤ (first.ncard + second.ncard) + third.ncard := by
        gcongr
        exact Set.ncard_union_le _ _
      _ ≤ t + t + t := by gcongr <;> assumption
      _ = 3 * t := by ring
  -- Covering `Fin n` would force `n ≤ 3 * t`.
  have univCardinality : (Set.univ : Set (Fin n)).ncard = n := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have coversAll : first ∪ second ∪ third = Set.univ :=
    Set.eq_univ_of_univ_subset covers
  rw [coversAll, univCardinality] at cardinalityBound
  omega

end AdversaryStructure

/-- Multiparty construction restricted to an adversary structure; outside the
structure the target is the trivial specification.

Liu--Maurer 2020, Section 2.4 (printed p. 7): “if `Z` is not in the adversary
structure, then the resource is only known to satisfy the trivial
specification `Phi`.” -/
noncomputable def ConstructsForAdversaryStructure
    {n : Nat} {interfaces : Fin n → C}
    (adversaryStructure : AdversaryStructure (Fin n))
    (tuple : Finite.ConverterTuple interfaces)
    (source target : Set (Fin n) →
      Specification Phi (Finite.interface n interfaces)) : Prop := by
  classical
  exact ConstructsForAll (Phi := Phi) tuple source
    (fun dishonest =>
      if dishonest ∈ adversaryStructure.sets then
        target dishonest
      else
        Set.univ)

omit [ResourceAlgebra C Phi] in
/-- Adversary-structure constructions compose serially. -/
theorem ConstructsForAdversaryStructure.serial
    {n : Nat} {interfaces : Fin n → C}
    {adversaryStructure : AdversaryStructure (Fin n)}
    {innerTuple outerTuple : Finite.ConverterTuple interfaces}
    {source middle target : Set (Fin n) →
      Specification Phi (Finite.interface n interfaces)}
    (inner : ConstructsForAdversaryStructure (Phi := Phi)
      adversaryStructure innerTuple source middle)
    (outer : ConstructsForAdversaryStructure (Phi := Phi)
      adversaryStructure outerTuple middle target) :
    ConstructsForAdversaryStructure (Phi := Phi) adversaryStructure
      (fun i => outerTuple i ≫ innerTuple i) source target := by
  classical
  simp only [ConstructsForAdversaryStructure, ConstructsForAll] at inner outer ⊢
  intro dishonest
  by_cases admitted : dishonest ∈ adversaryStructure.sets
  · -- Inside the structure, compose the two genuine construction rungs.
    have innerConstruction := by
      simpa only [if_pos admitted] using inner dishonest
    have outerConstruction := by
      simpa only [if_pos admitted] using outer dishonest
    have composed := innerConstruction.serial outerConstruction
    simpa only [if_pos admitted,
      Finite.ConverterTuple.honestConverter_serial] using composed
  · -- Outside the structure, the target remains trivial.
    simp only [if_neg admitted]
    exact fun _ _ => Set.mem_univ _

omit [ResourceAlgebra C Phi] in
/-- Adversary-structure construction admits ordinary `calc` chaining. -/
instance instTransConstructsForAdversaryStructure
    {n : Nat} {interfaces : Fin n → C}
    {adversaryStructure : AdversaryStructure (Fin n)}
    {innerTuple outerTuple : Finite.ConverterTuple interfaces} :
    Trans (ConstructsForAdversaryStructure (Phi := Phi)
      adversaryStructure innerTuple)
      (ConstructsForAdversaryStructure (Phi := Phi)
        adversaryStructure outerTuple)
      (ConstructsForAdversaryStructure (Phi := Phi) adversaryStructure
        (fun i => outerTuple i ≫ innerTuple i)) where
  trans := ConstructsForAdversaryStructure.serial

omit [ResourceAlgebra C Phi] in
/-- Per-resource joint simulator equations establish every construction in an
adversary structure.

Liu--Maurer 2020, Section 2.5 (printed p. 8): “one can exhibit for every
element `U in U` a converter `alpha` such that `U = alpha^Z S`.” The
simulator is therefore selected after both `Z` and the admitted source
resource. -/
theorem ConstructsForAdversaryStructure.zStar_of_simulators
    {n : Nat} {interfaces : Fin n → C}
    (adversaryStructure : AdversaryStructure (Fin n))
    (tuple : Finite.ConverterTuple interfaces)
    (converters : Set (Fin n) →
      EndoFamily (Opposite.op (Finite.interface n interfaces)))
    (source : Set (Fin n) →
      Specification Phi (Finite.interface n interfaces))
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
      (fun dishonest => zStar (Phi := Phi) converters dishonest
        ({ideal} : Specification Phi (Finite.interface n interfaces))) := by
  classical
  simp only [ConstructsForAdversaryStructure, ConstructsForAll]
  intro dishonest
  by_cases admitted : dishonest ∈ adversaryStructure.sets
  · -- The supplied joint simulator witnesses target-star membership.
    simp only [if_pos admitted]
    exact Specification.constructs_star_of_simulators
      (Phi := Phi) (simulates dishonest admitted)
  · -- Outside the structure, construction into the trivial target is automatic.
    simp only [if_neg admitted]
    exact fun _ _ => Set.mem_univ _

end ConstructiveCryptography.Multiparty
