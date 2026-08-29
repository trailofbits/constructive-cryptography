/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical.ResourceAlgebra.Star

set_option autoImplicit false

/-!
# Filtered endpoint specifications

`filteredAt` is the choice-free endpoint specialization obtained by attaching
one explicit filter and then closing the resulting singleton specification
under one explicit joint converter class.  The party selection and ordered
assembly of a filter tuple are supplied separately by `ConverterTuple.partial`
and `ConverterTuple.converter`.

Liu--Maurer 2020, Section 2.4 (printed p. 7): “While an honest party applies
its converter, there is no such guarantee for a dishonest party.”  Section 2.5
(printed pp. 7--8) defines `S^{*Z}` by merging the interfaces in `Z` and applying
the star relaxation at that single interface.  Therefore the converter class
below is joint; it is not assumed to factor into independent party converters.

This is not Maurer--Renner 2011's choice-setting construction.  Jost's basic
construction theory does not require filtered endpoints, but its addressed
partial converter tuples and attachment locality support this optional
specialization without adding an axiom to `ResourceAlgebra`.
-/

namespace AbstractCryptography.Categorical.ResourceAlgebra.Specification

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-- Attach an explicit filter and close the resulting singleton specification
under the admitted joint converter class. -/
noncomputable def filteredAt {A : C}
    (converters : EndoFamily (Opposite.op A))
    (filter : CategoryTheory.End A) (resource : Resource Phi A) :
    Specification Phi A :=
  star (Phi := Phi) converters
    ({attach (Phi := Phi) filter resource} : Specification Phi A)

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Membership in a filtered endpoint is witnessed by one admitted joint
converter attached after the filter. -/
theorem mem_filteredAt_iff {A : C}
    {converters : EndoFamily (Opposite.op A)}
    {filter : CategoryTheory.End A} {original resource : Resource Phi A} :
    resource ∈ filteredAt (Phi := Phi) converters filter original ↔
      ∃ converter : CategoryTheory.End A,
        converter.op ∈ converters ∧
          attach (Phi := Phi) converter
            (attach (Phi := Phi) filter original) = resource := by
  constructor
  · intro admitted
    rcases mem_star_iff.mp admitted with
      ⟨converter, converterAdmitted, filtered,
        filteredAdmitted, equation⟩
    -- Singleton membership fixes the resource before joint conversion.
    have filteredEquation :
        filtered = attach (Phi := Phi) filter original :=
      Set.mem_singleton_iff.mp filteredAdmitted
    subst filtered
    exact ⟨converter, converterAdmitted, equation⟩
  · rintro ⟨converter, converterAdmitted, equation⟩
    -- The filtered resource itself is the singleton star witness.
    exact mem_star_iff.mpr
      ⟨converter, converterAdmitted,
        attach (Phi := Phi) filter original,
        Set.mem_singleton _, equation⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A simulator equation proves construction between filtered endpoints when
the constructing converter commutes with the admitted joint class. -/
theorem filteredAt_constructs_of_eq {A : C}
    {converters : EndoFamily (Opposite.op A)}
    {converter sourceFilter targetFilter simulator : CategoryTheory.End A}
    {real ideal : Resource Phi A}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (simulatorAdmitted : simulator.op ∈ converters)
    (equation :
      attach (Phi := Phi) converter
          (attach (Phi := Phi) sourceFilter real) =
        attach (Phi := Phi) simulator
          (attach (Phi := Phi) targetFilter ideal)) :
    Constructs (Phi := Phi) converter
      (filteredAt (Phi := Phi) converters sourceFilter real)
      (filteredAt (Phi := Phi) converters targetFilter ideal) := by
  change Constructs (Phi := Phi) converter
    (star (Phi := Phi) converters
      ({attach (Phi := Phi) sourceFilter real} : Specification Phi A))
    (star (Phi := Phi) converters
      ({attach (Phi := Phi) targetFilter ideal} : Specification Phi A))
  -- The supplied simulator proves the singleton construction into star.
  have singletonConstruction := constructs_star_of_simulator
    (Phi := Phi) simulator simulatorAdmitted equation
  -- Star both endpoints; commutation moves the converter through the class.
  have relaxedConstruction := singletonConstruction.star commutes
  -- Idempotence removes the second star at the target.
  simpa only [star_idem] using relaxedConstruction

/-- A simulator distance bound proves construction into the scalar relaxation
of a filtered endpoint when the constructing converter commutes with the
admitted joint class. -/
theorem filteredAt_constructs_epsilonRelaxation_of_distance_le {A : C}
    {converters : EndoFamily (Opposite.op A)}
    {converter sourceFilter targetFilter simulator : CategoryTheory.End A}
    {real ideal : Resource Phi A} {error : ENNReal}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (simulatorAdmitted : simulator.op ∈ converters)
    (close : distance (Phi := Phi)
      (attach (Phi := Phi) converter
        (attach (Phi := Phi) sourceFilter real))
      (attach (Phi := Phi) simulator
        (attach (Phi := Phi) targetFilter ideal)) ≤ error) :
    Constructs (Phi := Phi) converter
      (filteredAt (Phi := Phi) converters sourceFilter real)
      (epsilonRelaxation (Phi := Phi) error
        (filteredAt (Phi := Phi) converters targetFilter ideal)) := by
  rw [constructs_epsilonRelaxation_iff]
  change ConstructsWithin (Phi := Phi) converter
    (star (Phi := Phi) converters
      ({attach (Phi := Phi) sourceFilter real} : Specification Phi A))
    (star (Phi := Phi) converters
      ({attach (Phi := Phi) targetFilter ideal} : Specification Phi A))
    error
  -- The distance witness proves the singleton construction into star.
  have singletonConstruction := constructsWithin_star_of_simulator
    (Phi := Phi) simulator simulatorAdmitted close
  -- Star both endpoints and remove the duplicate target star.
  have relaxedConstruction := singletonConstruction.star commutes
  simpa only [star_idem] using relaxedConstruction

end AbstractCryptography.Categorical.ResourceAlgebra.Specification
