/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ConstructiveCryptography.Categorical.ResourceAlgebra.Finite
import Mathlib.CategoryTheory.Endomorphism

set_option autoImplicit false

/-!
# Finite converter tuples

A converter tuple assigns one interface-preserving converter to each member of
an ordered finite interface family.  Selecting a set of tuple positions replaces
every unselected converter by the identity.  The resulting tuple is assembled
with the ordered finite tensor already derived from `ResourceAlgebra`.

Maurer--Renner 2016, Section 7 (printed p. 19): “A protocol is a tuple of
converters, one for each potentially honest party.”  Jost, Section 2.2.2
(printed p. 18): “We define a protocol to be a (partial) tuple of
converter-connection pairs.”  The definitions here are the
canonical-connection, interface-preserving Lean specialization.

Liu--Maurer 2020 (printed p. 7) likewise writes
`π = (π₁, …, πₙ)` and restricts it to selected parties.  Its joint dishonest
converter class is more general than independently selected component tuples;
that class remains an explicit endomorphism family at the construction site.
-/

namespace ConstructiveCryptography.Categorical.ResourceAlgebra.Finite

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-- One interface-preserving converter for each member of an ordered finite
interface family.

Liu--Maurer 2020, Section 2.4 (printed p. 7): “A protocol consists of a tuple
`π = (π₁, …, πₙ)` of converters, one for each party.” -/
abbrev ConverterTuple {n : Nat} (interfaces : Fin n → C) :=
  (i : Fin n) → CategoryTheory.End (interfaces i)

namespace ConverterTuple

/-- Keep the converters at the selected positions and use identity converters
at every other position.

Jost, Section 2.2.2 (printed p. 18): “We define a protocol to be a (partial)
tuple of converter-connection pairs.”  Lean represents every omitted component
by the identity converter so that the tuple can be assembled by ordered tensor. -/
noncomputable def «partial» {n : Nat} {interfaces : Fin n → C}
    (tuple : ConverterTuple interfaces) (parties : Set (Fin n)) :
    ConverterTuple interfaces := by
  classical
  exact fun i => if i ∈ parties then tuple i else 𝟙 (interfaces i)

/-- Assemble a converter tuple with ordered finite parallel composition. -/
def converter {n : Nat} {interfaces : Fin n → C}
    (tuple : ConverterTuple interfaces) :
    CategoryTheory.End (Finite.interface n interfaces) :=
  Finite.converters n interfaces interfaces tuple

/-- Assemble the converters at the honest parties and use the identity at the
dishonest parties.

Liu--Maurer 2020, Definition 1 (printed p. 7): “if all parties in `P \ Z`
apply their converter, the resulting resource satisfies specification
`S_Z`.” -/
noncomputable abbrev honestConverter {n : Nat} {interfaces : Fin n → C}
    (tuple : ConverterTuple interfaces) (dishonest : Set (Fin n)) :
    CategoryTheory.End (Finite.interface n interfaces) :=
  converter («partial» tuple dishonestᶜ)

omit [MonoidalCategory C] in
@[simp]
theorem partial_apply_of_mem {n : Nat} {interfaces : Fin n → C}
    (tuple : ConverterTuple interfaces) (parties : Set (Fin n))
    (i : Fin n) (admitted : i ∈ parties) :
    «partial» tuple parties i = tuple i := by
  -- Selection keeps the converter at an admitted party.
  simp [«partial», admitted]

omit [MonoidalCategory C] in
@[simp]
theorem partial_apply_of_not_mem {n : Nat} {interfaces : Fin n → C}
    (tuple : ConverterTuple interfaces) (parties : Set (Fin n))
    (i : Fin n) (excluded : i ∉ parties) :
    «partial» tuple parties i = 𝟙 (interfaces i) := by
  -- Selection replaces an excluded party's converter by identity.
  simp [«partial», excluded]

omit [MonoidalCategory C] in
@[simp]
theorem partial_identity {n : Nat} {interfaces : Fin n → C}
    (parties : Set (Fin n)) :
    «partial» (fun i => 𝟙 (interfaces i)) parties =
      (fun i => 𝟙 (interfaces i)) := by
  -- Each selected or unselected component is identity.
  funext i
  simp [«partial»]

omit [MonoidalCategory C] in
/-- Restriction to selected parties preserves pointwise serial composition. -/
theorem partial_serial {n : Nat} {interfaces : Fin n → C}
    (first second : ConverterTuple interfaces) (parties : Set (Fin n)) :
    «partial» (fun i => first i ≫ second i) parties =
      (fun i => «partial» first parties i ≫ «partial» second parties i) := by
  -- At each party either both converters remain or both become identities.
  funext i
  by_cases admitted : i ∈ parties <;> simp [«partial», admitted]

@[simp]
theorem converter_identity {n : Nat} (interfaces : Fin n → C) :
    converter (fun i => 𝟙 (interfaces i)) =
      𝟙 (Finite.interface n interfaces) := by
  -- Finite ordered tensor preserves the component identities.
  exact Finite.converters_identity n interfaces

/-- Assembly preserves pointwise serial converter composition. -/
theorem converter_serial {n : Nat} {interfaces : Fin n → C}
    (first second : ConverterTuple interfaces) :
    converter (fun i => first i ≫ second i) =
      converter first ≫ converter second := by
  -- This is finite ordered tensor bifunctoriality.
  exact Finite.converters_serial n interfaces interfaces interfaces first second

@[simp]
theorem honestConverter_identity {n : Nat} (interfaces : Fin n → C)
    (dishonest : Set (Fin n)) :
    honestConverter (fun i => 𝟙 (interfaces i)) dishonest =
      𝟙 (Finite.interface n interfaces) := by
  -- Selection leaves an identity converter at every party.
  rw [honestConverter, partial_identity, converter_identity]

/-- Honest-party selection preserves serial composition in attachment order. -/
theorem honestConverter_serial {n : Nat} {interfaces : Fin n → C}
    (outer inner : ConverterTuple interfaces) (dishonest : Set (Fin n)) :
    honestConverter (fun i => outer i ≫ inner i) dishonest =
      honestConverter outer dishonest ≫ honestConverter inner dishonest := by
  -- Restrict pointwise, then assemble the pointwise serial composites.
  rw [honestConverter, partial_serial, converter_serial]

/-- Partial tuples selected at disjoint party sets commute after assembly.

Jost, Proposition 2.2.3 (printed p. 18): “Converter attachment satisfies the
natural property of composition order independence.”  Here this property is
derived from ordered tensor bifunctoriality and identity outside the selected
sets; it is not an additional axiom. -/
theorem converter_partial_commute_of_disjoint {n : Nat}
    {interfaces : Fin n → C}
    (left right : ConverterTuple interfaces)
    (leftParties rightParties : Set (Fin n))
    (disjoint : Disjoint leftParties rightParties) :
    converter («partial» left leftParties) ≫
        converter («partial» right rightParties) =
      converter («partial» right rightParties) ≫
        converter («partial» left leftParties) := by
  -- Rewrite both serial composites as assembly of pointwise composites.
  rw [← converter_serial, ← converter_serial]
  -- At each party, disjointness makes at least one converter the identity.
  apply congrArg converter
  funext i
  by_cases leftAdmitted : i ∈ leftParties
  · have rightExcluded : i ∉ rightParties :=
      Set.disjoint_left.mp disjoint leftAdmitted
    simp [«partial», leftAdmitted, rightExcluded]
  · simp [«partial», leftAdmitted]

end ConverterTuple

end ConstructiveCryptography.Categorical.ResourceAlgebra.Finite
