/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical.ResourceAlgebra.Epsilon
import AbstractCryptography.Categorical.Star

set_option autoImplicit false

/-!
# Converter-class relaxation for a resource algebra

The converter class at a base interface `A` is the existing
`EndoFamily (Opposite.op A)`.  This is the one endomorphism monoid on which the
contravariant resource functor acts covariantly.  The declarations below are
only base-interface wrappers around `Categorical.Specification.star`; they do
not introduce another star carrier, action, or multiplication.

For base endomorphisms `β α : End A`, the opposite-category multiplication
satisfies `β.op * α.op = (β ≫ α).op`.  Functoriality therefore gives

`Phi.map (β.op * α.op) R = attach β (attach α R)`,

which is Maurer--Renner's function-composition order.  A submonoid of
`End A` itself would have the reverse multiplication and is not used here.
-/

namespace AbstractCryptography.Categorical.ResourceAlgebra.Specification

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-- Closure of a specification under an interface-preserving converter class.

Maurer--Renner 2016, Section 3.4 (printed p. 8):
“`R* := RΣ = {Rβ | R ∈ R, β ∈ Σ}`.” -/
noncomputable abbrev star {A : C}
    (converters : EndoFamily (Opposite.op A))
    (source : Specification Phi A) : Specification Phi A :=
  Categorical.Specification.star Phi converters source

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Membership in converter-class closure, expressed with ordinary base
converters. -/
theorem mem_star_iff {A : C}
    {converters : EndoFamily (Opposite.op A)}
    {source : Specification Phi A} {resource : Resource Phi A} :
    resource ∈ star (Phi := Phi) converters source ↔
      ∃ converter : CategoryTheory.End A, converter.op ∈ converters ∧
        ∃ original ∈ source,
          attach (Phi := Phi) converter original = resource := by
  constructor
  · -- Read the opposite-category converter as its ordinary base converter.
    rintro ⟨converter, admitted, original, sourceAdmitted, equation⟩
    exact ⟨converter.unop, admitted, original, sourceAdmitted, equation⟩
  · -- Send the ordinary base converter to the acting opposite category.
    rintro ⟨converter, admitted, original, sourceAdmitted, equation⟩
    exact ⟨converter.op, admitted, original, sourceAdmitted, equation⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Every specification is contained in its converter-class closure. -/
theorem subset_star {A : C}
    (converters : EndoFamily (Opposite.op A))
    (source : Specification Phi A) :
    source ⊆ star (Phi := Phi) converters source := by
  -- The generic categorical proof uses the admitted identity converter.
  exact Categorical.Specification.subset_star Phi converters source

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Converter-class closure is idempotent. -/
theorem star_idem {A : C}
    (converters : EndoFamily (Opposite.op A))
    (source : Specification Phi A) :
    star (Phi := Phi) converters
        (star (Phi := Phi) converters source) =
      star (Phi := Phi) converters source := by
  -- Closure follows from multiplication in the one acting endomorphism family.
  exact Categorical.Specification.star_idem Phi converters source

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A larger admitted converter class gives a larger star relaxation. -/
theorem star_mono {A : C}
    {converters converters' : EndoFamily (Opposite.op A)}
    (included : converters ≤ converters') (source : Specification Phi A) :
    star (Phi := Phi) converters source ⊆
      star (Phi := Phi) converters' source := by
  intro resource relaxed
  -- Keep the converter and resource witnesses while enlarging the class.
  rcases mem_star_iff.mp relaxed with
    ⟨converter, admitted, original, sourceAdmitted, equation⟩
  exact mem_star_iff.mpr
    ⟨converter, included admitted, original, sourceAdmitted, equation⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Converter attachment carries a star-relaxed source into the star closure
of its direct image when the converter commutes with the admitted class. -/
theorem map_star_subset {A : C} {converter : CategoryTheory.End A}
    {converters : EndoFamily (Opposite.op A)}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (source : Specification Phi A) :
    map (Phi := Phi) converter (star (Phi := Phi) converters source) ⊆
      star (Phi := Phi) converters
        (map (Phi := Phi) converter source) := by
  rintro resource ⟨relaxed, relaxedAdmitted, rfl⟩
  -- Decompose the source star witness.
  rcases mem_star_iff.mp relaxedAdmitted with
    ⟨classConverter, classAdmitted, original, sourceAdmitted, rfl⟩
  -- Reuse the same class converter around the direct-image resource.
  refine mem_star_iff.mpr
    ⟨classConverter, classAdmitted,
      attach (Phi := Phi) converter original,
      ⟨original, sourceAdmitted, rfl⟩, ?_⟩
  -- Composition-order independence exchanges the two attachment functions.
  exact (commutes classConverter classAdmitted original).symm

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Exact construction remains valid after star-relaxing both endpoints.

Maurer--Renner 2016, Lemma 3 (printed p. 12):
“`R —π→ S  ⟹  R* —π→ S*`.” -/
theorem Constructs.star {A : C} {converter : CategoryTheory.End A}
    {converters : EndoFamily (Opposite.op A)}
    {source target : Specification Phi A}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) converter
      (star (Phi := Phi) converters source)
      (star (Phi := Phi) converters target) := by
  -- The direct image of the relaxed source enters the relaxed direct image.
  refine (map_star_subset (Phi := Phi) commutes source).trans ?_
  -- Enlarge the centers from the direct image into the target specification.
  intro resource relaxed
  rcases mem_star_iff.mp relaxed with
    ⟨classConverter, classAdmitted, original,
      ⟨sourceResource, sourceAdmitted, rfl⟩, equation⟩
  exact mem_star_iff.mpr
    ⟨classConverter, classAdmitted,
      attach (Phi := Phi) converter sourceResource,
      constructs_iff.mp construction sourceResource sourceAdmitted, equation⟩

/-- Approximate construction remains valid after star-relaxing both endpoints
when the constructing converter commutes with the admitted class. -/
theorem ConstructsWithin.star {A : C}
    {converter : CategoryTheory.End A}
    {converters : EndoFamily (Opposite.op A)}
    {source target : Specification Phi A} {error : ENNReal}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (construction : ConstructsWithin (Phi := Phi) converter source target error) :
    ConstructsWithin (Phi := Phi) converter
      (star (Phi := Phi) converters source)
      (star (Phi := Phi) converters target) error := by
  rw [constructsWithin_iff] at construction ⊢
  intro resource relaxed
  -- Decompose the source star witness and apply the base construction.
  rcases mem_star_iff.mp relaxed with
    ⟨classConverter, classAdmitted, original, sourceAdmitted, rfl⟩
  obtain ⟨ideal, targetAdmitted, close⟩ :=
    construction original sourceAdmitted
  -- Attach the same class converter to the selected nearby target.
  refine ⟨attach (Phi := Phi) classConverter ideal,
    mem_star_iff.mpr
      ⟨classConverter, classAdmitted, ideal, targetAdmitted, rfl⟩, ?_⟩
  -- Commute the constructor through, then use attachment non-expansion.
  rw [commutes classConverter classAdmitted original]
  exact (distance_attach_le classConverter
    (attach (Phi := Phi) converter original) ideal).trans close

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- An explicit exact simulator equation proves construction into the
converter-class-relaxed ideal.

Maurer--Renner 2016, Section 4.3 (printed p. 13): an equality of the form
“`πR = Tσ`” is read as membership of `πR` in `TΣ = T*`. -/
theorem constructs_star_of_simulator {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily (Opposite.op A)}
    {real : Resource Phi B} {ideal : Resource Phi A}
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    (equation : attach (Phi := Phi) converter real =
      attach (Phi := Phi) simulator ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (star (Phi := Phi) converters ({ideal} : Specification Phi A)) := by
  -- Re-express base attachment as the resource functor's opposite map.
  change Phi.map converter.op real = Phi.map simulator.op ideal at equation
  -- The generic star theorem inserts the admitted simulator witness.
  exact Categorical.Specification.constructs_star_of_simulator
    Phi simulator.op admitted equation

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Pointwise exact simulator witnesses prove construction into a star-relaxed
singleton ideal.

Maurer--Renner 2016, Section 4.2 (printed p. 12): a simulator is exhibited to
prove the required construction; it is not part of the construction notion. -/
theorem constructs_star_of_simulators {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily (Opposite.op A)}
    {real : Specification Phi B} {ideal : Resource Phi A}
    (simulates : ∀ resource ∈ real,
      ∃ simulator : CategoryTheory.End A, simulator.op ∈ converters ∧
        attach (Phi := Phi) converter resource =
          attach (Phi := Phi) simulator ideal) :
    Constructs (Phi := Phi) converter real
      (star (Phi := Phi) converters ({ideal} : Specification Phi A)) := by
  rw [constructs_iff]
  intro resource admitted
  -- Choose the supplied simulator for this admitted source resource.
  obtain ⟨simulator, simulatorAdmitted, equation⟩ :=
    simulates resource admitted
  -- The equation is precisely membership in the star-relaxed singleton.
  exact mem_star_iff.mpr
    ⟨simulator, simulatorAdmitted, ideal, Set.mem_singleton ideal,
      equation.symm⟩

/-- An explicit simulator distance bound proves approximate construction into
the converter-class-relaxed ideal. -/
theorem constructsWithin_star_of_simulator {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily (Opposite.op A)}
    {real : Resource Phi B} {ideal : Resource Phi A} {error : ENNReal}
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    (close : distance (Phi := Phi) (attach (Phi := Phi) converter real)
      (attach (Phi := Phi) simulator ideal) ≤ error) :
    ConstructsWithin (Phi := Phi) converter ({real} : Specification Phi B)
      (star (Phi := Phi) converters ({ideal} : Specification Phi A))
      error := by
  -- Re-express the selected fibre distance and attachments categorically.
  change Categorical.distance (F := Phi) (Phi.map converter.op real)
      (Phi.map simulator.op ideal) ≤ error at close
  -- The generic approximate theorem inserts the admitted simulator witness.
  exact Categorical.Specification.constructsWithin_star_of_simulator
    Phi simulator.op admitted close

/-- Pointwise simulator distance witnesses prove approximate construction into
a star-relaxed singleton ideal. -/
theorem constructsWithin_star_of_simulators {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily (Opposite.op A)}
    {real : Specification Phi B} {ideal : Resource Phi A} {error : ENNReal}
    (simulates : ∀ resource ∈ real,
      ∃ simulator : CategoryTheory.End A, simulator.op ∈ converters ∧
        distance (Phi := Phi) (attach (Phi := Phi) converter resource)
          (attach (Phi := Phi) simulator ideal) ≤ error) :
    ConstructsWithin (Phi := Phi) converter real
      (star (Phi := Phi) converters ({ideal} : Specification Phi A))
      error := by
  rw [constructsWithin_iff]
  intro resource admitted
  -- Choose the supplied simulator and its distance bound.
  obtain ⟨simulator, simulatorAdmitted, close⟩ :=
    simulates resource admitted
  -- Its action on the ideal is an admitted star member.
  exact ⟨attach (Phi := Phi) simulator ideal,
    mem_star_iff.mpr
      ⟨simulator, simulatorAdmitted, ideal, Set.mem_singleton ideal, rfl⟩,
    close⟩

/-- Maurer--Renner's simulator proof step as exact construction into an error
relaxation of the converter-class-relaxed ideal.

Maurer--Renner 2016, Lemma 5 (printed p. 12):
“`∃σ ∈ Σ : πR ≈ᵋ Sσ  ⟹  R —π→ (S*)ᵋ`.” -/
theorem constructs_of_simulator {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily (Opposite.op A)}
    {real : Resource Phi B} {ideal : Resource Phi A} {error : ENNReal}
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    (close : distance (Phi := Phi) (attach (Phi := Phi) converter real)
      (attach (Phi := Phi) simulator ideal) ≤ error) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        (star (Phi := Phi) converters
          ({ideal} : Specification Phi A))) := by
  -- Convert the relaxed target to the canonical approximate judgment.
  rw [constructs_epsilonRelaxation_iff]
  -- Insert the admitted simulator as the nearby star member.
  exact constructsWithin_star_of_simulator simulator admitted close

end AbstractCryptography.Categorical.ResourceAlgebra.Specification
