import ConstructiveCryptography.CryptographicAlgebra.Epsilon
import ConstructiveCryptography.Specification.Star.Metric
import Mathlib.CategoryTheory.Endomorphism

set_option autoImplicit false

/-!
# Star relaxation

For a class of converters from an interface to itself, closed under composition, the star
relaxation of a specification is the set of resources obtained by attaching a converter of
the class (MR16, §3.4, printed p. 8: `R* := RΣ = {Rβ | R ∈ R, β ∈ Σ}`). It is extensive,
idempotent, monotone in the class, and preserved by constructions that commute with the
class. A simulator equation or distance bound proves construction into the star-relaxed
ideal (MR16, §§4.2–4.3, Lemma 5, printed pp. 12–13).

## Main definitions

* `CryptographicAlgebra.EndoFamily A`: composition-closed classes of converters on `A`
* `CryptographicAlgebra.Specification.star`

## Main results

* `CryptographicAlgebra.Specification.subset_star`, `CryptographicAlgebra.Specification.star_idem`
* `CryptographicAlgebra.Specification.Constructs.star`,
  `CryptographicAlgebra.Specification.ConstructsWithin.star`: MR16, Lemma 3
* `CryptographicAlgebra.Specification.constructs_of_simulator`: MR16, Lemma 5
-/

namespace ConstructiveCryptography.CryptographicAlgebra

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi]

/-- A composition-closed class of converters from `A` to itself. Converters act on
resources contravariantly, so the class is a submonoid of the endomorphisms of `A` in the
opposite category, whose multiplication is attachment order. -/
abbrev EndoFamily (A : C) := Submonoid (CategoryTheory.End (Opposite.op A))

/-- Attachment as an action of the endomorphisms of `A` in the opposite category.

MR16, §3.3 (printed p. 7): “(β ◦ α)ⁱR = βⁱ(αⁱR)”. -/
@[reducible] def endoMulAction (Phi : C → Type w) [ResourceTheory C Phi] (A : C) :
    MulAction (CategoryTheory.End (Opposite.op A)) (Phi A) where
  smul converter resource := attach converter.unop resource
  one_smul resource := attach_identity resource
  mul_smul outer inner resource := attach_serial outer.unop inner.unop resource

namespace Specification

/-- Closure of a specification under an interface-preserving converter class.

Maurer--Renner 2016, Section 3.4 (printed p. 8):
“`R* := RΣ = {Rβ | R ∈ R, β ∈ Σ}`.” -/
noncomputable abbrev star {A : C}
    (converters : EndoFamily A)
    (source : Specification (Phi A)) : Specification (Phi A) :=
  letI := endoMulAction Phi A
  ConstructiveCryptography.Specification.star converters source

omit [MonoidalCategory C] in
/-- Membership in converter-class closure, expressed with ordinary base
converters. -/
theorem mem_star_iff {A : C}
    {converters : EndoFamily A}
    {source : Specification (Phi A)} {resource : Phi A} :
    resource ∈ star converters source ↔
      ∃ converter : CategoryTheory.End A, converter.op ∈ converters ∧
        ∃ original ∈ source,
          attach converter original = resource := by
  constructor
  · -- Read the opposite-category converter as its ordinary base converter.
    rintro ⟨converter, admitted, original, sourceAdmitted, equation⟩
    exact ⟨converter.unop, admitted, original, sourceAdmitted, equation⟩
  · -- Send the ordinary base converter to the acting opposite category.
    rintro ⟨converter, admitted, original, sourceAdmitted, equation⟩
    exact ⟨converter.op, admitted, original, sourceAdmitted, equation⟩

omit [MonoidalCategory C] in
/-- Every specification is contained in its converter-class closure. -/
theorem subset_star {A : C}
    (converters : EndoFamily A)
    (source : Specification (Phi A)) :
    source ⊆ star converters source := by
  let := endoMulAction Phi A
  exact ConstructiveCryptography.Specification.subset_star converters source

omit [MonoidalCategory C] in
/-- Converter-class closure is idempotent. -/
theorem star_idem {A : C}
    (converters : EndoFamily A)
    (source : Specification (Phi A)) :
    star converters
        (star converters source) =
      star converters source := by
  let := endoMulAction Phi A
  exact ConstructiveCryptography.Specification.star_idem converters source

omit [MonoidalCategory C] in
/-- A larger admitted converter class gives a larger star relaxation. -/
theorem star_mono {A : C}
    {converters converters' : EndoFamily A}
    (included : converters ≤ converters') (source : Specification (Phi A)) :
    star converters source ⊆
      star converters' source := by
  intro resource relaxed
  -- Keep the converter and resource witnesses while enlarging the class.
  rcases mem_star_iff.mp relaxed with
    ⟨converter, admitted, original, sourceAdmitted, equation⟩
  exact mem_star_iff.mpr
    ⟨converter, included admitted, original, sourceAdmitted, equation⟩

omit [MonoidalCategory C] in
/-- Converter attachment carries a star-relaxed source into the star closure
of its direct image when the converter commutes with the admitted class. -/
theorem map_star_subset {A : C} {converter : CategoryTheory.End A}
    {converters : EndoFamily A}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Phi A,
          attach converter
              (attach classConverter resource) =
            attach classConverter
              (attach converter resource))
    (source : Specification (Phi A)) :
    map converter (star converters source) ⊆
      star converters
        (map converter source) := by
  let := endoMulAction Phi A
  -- Apply image compatibility to the induced endomorphism action.
  exact ConstructiveCryptography.Specification.image_star_subset
    (f := attach converter)
    (fun classConverter admitted resource => commutes classConverter.unop admitted resource)
    source

omit [MonoidalCategory C] in
/-- Exact construction remains valid after star-relaxing both endpoints.

Maurer--Renner 2016, Lemma 3 (printed p. 11):
“`R —π→ S  ⟹  R* —π→ S*`.” -/
theorem Constructs.star {A : C} {converter : CategoryTheory.End A}
    {converters : EndoFamily A}
    {source target : Specification (Phi A)}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Phi A,
          attach converter
              (attach classConverter resource) =
            attach classConverter
              (attach converter resource))
    (construction : Constructs converter source target) :
    Constructs converter
      (star converters source)
      (star converters target) := by
  let := endoMulAction Phi A
  -- Specialize exact star compatibility to the induced endomorphism action.
  exact ConstructiveCryptography.Specification.Constructs.star construction
    (fun classConverter admitted resource => commutes classConverter.unop admitted resource)

/-- Approximate construction remains valid after star-relaxing both endpoints
when the constructing converter commutes with the admitted class. -/
theorem ConstructsWithin.star [CompatiblePseudoMetric C Phi] {A : C}
    {converter : CategoryTheory.End A}
    {converters : EndoFamily A}
    {source target : Specification (Phi A)} {error : ENNReal}
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Phi A,
          attach converter
              (attach classConverter resource) =
            attach classConverter
              (attach converter resource))
    (construction : ConstructsWithin converter source target error) :
    ConstructsWithin converter
      (star converters source)
      (star converters target) error := by
  let := endoMulAction Phi A
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  -- Apply scalar compatibility to the same class and its non-expanding action.
  exact ConstructiveCryptography.Specification.ConstructsWithin.star construction
    (fun classConverter admitted resource => commutes classConverter.unop admitted resource)
    (fun classConverter _ R S => distance_attach_le classConverter.unop R S)

omit [MonoidalCategory C] in
/-- An explicit exact simulator equation proves construction into the
converter-class-relaxed ideal.

Maurer--Renner 2016, Section 4.3 (printed p. 13): an equality of the form
“`πR = Tσ`” is read as membership of `πR` in `TΣ = T*`. -/
theorem constructs_star_of_simulator {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily A}
    {real : Phi B} {ideal : Phi A}
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    (equation : attach converter real =
      attach simulator ideal) :
    Constructs converter ({real} : Specification (Phi B))
      (star converters ({ideal} : Specification (Phi A))) := by
  let := endoMulAction Phi A
  exact ConstructiveCryptography.Specification.constructs_star_of_simulator
    simulator.op admitted equation

omit [MonoidalCategory C] in
/-- Pointwise exact simulator witnesses prove construction into a star-relaxed
singleton ideal.

Maurer--Renner 2016, Section 4.2 (printed p. 12): a simulator is exhibited to
prove the required construction; it is not part of the construction notion. -/
theorem constructs_star_of_simulators {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily A}
    {real : Specification (Phi B)} {ideal : Phi A}
    (simulates : ∀ resource ∈ real,
      ∃ simulator : CategoryTheory.End A, simulator.op ∈ converters ∧
        attach converter resource =
          attach simulator ideal) :
    Constructs converter real
      (star converters ({ideal} : Specification (Phi A))) := by
  let := endoMulAction Phi A
  -- Reuse each selected simulator in the ordinary action calculus.
  apply ConstructiveCryptography.Specification.constructs_star_of_simulators
  intro resource admitted
  obtain ⟨simulator, simulatorAdmitted, equation⟩ := simulates resource admitted
  exact ⟨simulator.op, simulatorAdmitted, equation⟩

/-- An explicit simulator distance bound proves approximate construction into
the converter-class-relaxed ideal. -/
theorem constructsWithin_star_of_simulator [CompatiblePseudoMetric C Phi] {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily A}
    {real : Phi B} {ideal : Phi A} {error : ENNReal}
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    (close : distance (attach converter real)
      (attach simulator ideal) ≤ error) :
    ConstructsWithin converter ({real} : Specification (Phi B))
      (star converters ({ideal} : Specification (Phi A)))
      error := by
  let := endoMulAction Phi A
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  exact ConstructiveCryptography.Specification.constructsWithin_star_of_simulator
    simulator.op admitted close

/-- Pointwise simulator distance witnesses prove approximate construction into
a star-relaxed singleton ideal. -/
theorem constructsWithin_star_of_simulators [CompatiblePseudoMetric C Phi] {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily A}
    {real : Specification (Phi B)} {ideal : Phi A} {error : ENNReal}
    (simulates : ∀ resource ∈ real,
      ∃ simulator : CategoryTheory.End A, simulator.op ∈ converters ∧
        distance (attach converter resource)
          (attach simulator ideal) ≤ error) :
    ConstructsWithin converter real
      (star converters ({ideal} : Specification (Phi A)))
      error := by
  let := endoMulAction Phi A
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  -- Reuse the simulator and scalar bound in the selected target fibre.
  apply ConstructiveCryptography.Specification.constructsWithin_star_of_simulators
  intro resource admitted
  obtain ⟨simulator, simulatorAdmitted, close⟩ := simulates resource admitted
  exact ⟨simulator.op, simulatorAdmitted, close⟩

/-- Maurer--Renner's simulator proof step as exact construction into an error
relaxation of the converter-class-relaxed ideal.

Maurer--Renner 2016, Lemma 5 (printed p. 12):
“`∃σ ∈ Σ : πR ≈ᵋ Sσ  ⟹  R —π→ (S*)ᵋ`.” -/
theorem constructs_of_simulator [CompatiblePseudoMetric C Phi] {A B : C}
    {converter : A ⟶ B} {converters : EndoFamily A}
    {real : Phi B} {ideal : Phi A} {error : ENNReal}
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    (close : distance (attach converter real)
      (attach simulator ideal) ≤ error) :
    Constructs converter ({real} : Specification (Phi B))
      (epsilonRelaxation error
        (star converters
          ({ideal} : Specification (Phi A)))) := by
  -- Convert the relaxed target to the canonical approximate judgment.
  rw [constructs_epsilonRelaxation_iff]
  -- Insert the admitted simulator as the nearby star member.
  exact constructsWithin_star_of_simulator simulator admitted close

end Specification

end ConstructiveCryptography.CryptographicAlgebra
