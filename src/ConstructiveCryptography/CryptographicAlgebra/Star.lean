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

## Notation

Class converters are endomorphisms `β : A ⟶ A` of one fixed interface. MR16 writes `Rβ`,
attaching `β` on the other side from a protocol `π` in `πR`; here a class member acts on the
whole typed interface `A`, and acting on only part of it is up to the chosen category. A
`simulator` is a chosen admitted `β` exhibited to prove membership in `star`; it is a
witness, not part of the construction notion.

```text
outside A ──[ β ]── A ── R ∈ S        β • R ∈ star converters S
```

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

-- Objects `A : C` are interfaces; `α : A ⟶ B` is a converter with outside `A` and inside `B`;
-- `A ⊗ B` places two interfaces side by side.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
-- `Phi A` is the type of resources on `A`; attaching `β : A ⟶ A` maps `Phi A` to itself.
variable {Phi : C → Type w} [ResourceTheory C Phi]

/-- A composition-closed class of converters from `A` to itself. Converters act on
resources contravariantly, so the class is a submonoid of the endomorphisms of `A` in the
opposite category, whose multiplication is attachment order.

An element is `β.op` for a converter `β : A ⟶ A` of `C`. In the opposite endomorphism
monoid `End (op A)`, the product `outer * inner` corresponds to `outer.unop ≫ inner.unop`
in `C`, with `outer` outside, so `(outer * inner) • R = outer • (inner • R)`. Being a
submonoid means `𝟙 A` is admitted and admitted converters compose; no inverses are required,
and nothing bounds the class's size or efficiency. This is MR16's `Σ`. -/
abbrev EndoFamily (A : C) := Submonoid (CategoryTheory.End (Opposite.op A))

/-- Attachment as an action of the endomorphisms of `A` in the opposite category:
`β • R = attach β.unop R` for `β : End (op A)` and `R : Phi A`. The identity law is
`attach_identity`; the multiplication law `(outer * inner) • R = outer • (inner • R)` is
`attach_serial`. Callers install this action locally to reuse the generic star calculus.

MR16, §3.3 (printed p. 7): “(β ◦ α)ⁱR = βⁱ(αⁱR)”. -/
@[reducible] def endoMulAction (Phi : C → Type w) [ResourceTheory C Phi] (A : C) :
    MulAction (CategoryTheory.End (Opposite.op A)) (Phi A) where
  smul converter resource := attach converter.unop resource
  one_smul resource := attach_identity resource
  mul_smul outer inner resource := attach_serial outer.unop inner.unop resource

namespace Specification

/-- Closure of a specification under an interface-preserving converter class:
for `converters : EndoFamily A` and `source` on `A`,
`star converters source = {β • R | β.op ∈ converters, R ∈ source}`, again on `A`.

Maurer--Renner 2016, Section 3.4 (printed p. 8):
“`R* := RΣ = {Rβ | R ∈ R, β ∈ Σ}`.” -/
noncomputable abbrev star {A : C}
    -- MR16's `Σ`, storing opposite morphisms: `β` is admitted when `β.op ∈ converters`.
    (converters : EndoFamily A)
    (source : Specification (Phi A)) : Specification (Phi A) :=
  letI := endoMulAction Phi A
  ConstructiveCryptography.Specification.star converters source

omit [MonoidalCategory C] in
/-- Membership in converter-class closure, expressed with ordinary base
converters: `resource ∈ star converters source` iff `resource = converter • original` for
some `converter : A ⟶ A` with `converter.op ∈ converters` and some `original ∈ source`. -/
lemma mem_star_iff {A : C}
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
/-- Every specification is contained in its converter-class closure, using the admitted
identity converter `𝟙 A`. -/
lemma subset_star {A : C}
    (converters : EndoFamily A)
    (source : Specification (Phi A)) :
    source ⊆ star converters source := by
  let := endoMulAction Phi A
  exact ConstructiveCryptography.Specification.subset_star converters source

omit [MonoidalCategory C] in
/-- Converter-class closure is idempotent, `(S*)* = S*`: attaching two admitted converters
in turn is attaching their admitted composite, and the identity gives the other inclusion. -/
lemma star_idem {A : C}
    (converters : EndoFamily A)
    (source : Specification (Phi A)) :
    star converters
        (star converters source) =
      star converters source := by
  let := endoMulAction Phi A
  exact ConstructiveCryptography.Specification.star_idem converters source

omit [MonoidalCategory C] in
/-- A larger admitted converter class gives a larger star relaxation: if
`converters ≤ converters'` (inclusion of submonoids), then
`star converters source ⊆ star converters' source`. -/
lemma star_mono {A : C}
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
of its direct image when the converter commutes with the admitted class, since
`converter • (β • R) = β • (converter • R)` with the same admitted `β`. -/
lemma map_star_subset {A : C}
    -- `converter : End A` is a converter from `A` to itself, not necessarily admitted.
    {converter : CategoryTheory.End A}
    -- `converters` is the admitted class; `β` is admitted when `β.op ∈ converters`.
    {converters : EndoFamily A}
    -- `commutes`: `converter • (classConverter • R) = classConverter • (converter • R)` for
    -- every `classConverter` with `classConverter.op ∈ converters` and every `R : Phi A`.
    -- This stands in for MR16's composition-order invariance; it is assumed, not derived.
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Phi A,
          attach converter
              (attach classConverter resource) =
            attach classConverter
              (attach converter resource))
    -- `source` is the specification on `A` that is star-relaxed, then attached.
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
/-- Exact construction remains valid after star-relaxing both endpoints: `converter`
constructs `star converters target` from `star converters source`.

Maurer--Renner 2016, Lemma 3 (printed p. 11):
“`R —π→ S  ⟹  R* —π→ S*`.” MR16's setting already supplies composition-order invariance
for `π` attached as `πR` and `β ∈ Σ` as `Rβ` (§3.3, printed p. 8). Here `converter` is an
endomorphism on the whole interface `A`, so the corresponding commutation is an explicit
hypothesis. -/
theorem Constructs.star {A : C}
    -- `converter : End A` is MR16's protocol `π`, here a converter from `A` to itself.
    {converter : CategoryTheory.End A}
    -- `converters` is MR16's `Σ`; `β` is admitted when `β.op ∈ converters`.
    {converters : EndoFamily A}
    -- `source` and `target` are specifications on `A`.
    {source target : Specification (Phi A)}
    -- `commutes`: `converter` commutes with every admitted `classConverter` on every
    -- `resource : Phi A`; MR16 gets this from its two-side setting, here it is a premise.
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Phi A,
          attach converter
              (attach classConverter resource) =
            attach classConverter
              (attach converter resource))
    -- `construction`: `converter` constructs `target` from `source` exactly.
    (construction : Constructs converter source target) :
    Constructs converter
      (star converters source)
      (star converters target) := by
  let := endoMulAction Phi A
  -- Specialize exact star compatibility to the induced endomorphism action.
  exact ConstructiveCryptography.Specification.Constructs.star construction
    (fun classConverter admitted resource => commutes classConverter.unop admitted resource)

/-- Approximate construction remains valid after star-relaxing both endpoints
when the constructing converter commutes with the admitted class: `converter` constructs
`star converters target` from `star converters source` within the same `error`. For
`R ∈ source` with witness `T ∈ target` and admitted `β`,

```text
d(converter • (β • R), β • T) = d(β • (converter • R), β • T)   commutes
                              ≤ d(converter • R, T) ≤ error      non-expansion of β
``` -/
lemma ConstructsWithin.star [CompatiblePseudoMetric C Phi] {A : C}
    -- `converter : End A` is a converter from `A` to itself, not necessarily admitted.
    {converter : CategoryTheory.End A}
    -- `converters` is the admitted class; `β` is admitted when `β.op ∈ converters`.
    {converters : EndoFamily A}
    -- `source` and `target` are specifications on `A`; `error : ENNReal` is the budget.
    {source target : Specification (Phi A)} {error : ENNReal}
    -- `commutes`: `converter` commutes with every admitted `classConverter` on every
    -- `resource : Phi A`.
    (commutes : ∀ classConverter : CategoryTheory.End A,
      classConverter.op ∈ converters →
        ∀ resource : Phi A,
          attach converter
              (attach classConverter resource) =
            attach classConverter
              (attach converter resource))
    -- `construction`: `converter` constructs `target` from `source` within `error`.
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
converter-class-relaxed ideal:

```text
A ──[ converter ]── B ── real   =   A ──[ simulator ]── A ── ideal
```

Maurer--Renner 2016, Section 4.3 (printed p. 13): an equality of the form
“`πR = Tσ`” is read as membership of `πR` in `TΣ = T*`. -/
lemma constructs_star_of_simulator {A B : C}
    -- `converter : A ⟶ B` is the protocol; `converters` is the admitted class on its
    -- outside interface `A`.
    {converter : A ⟶ B} {converters : EndoFamily A}
    -- `real : Phi B` is the real resource inside; `ideal : Phi A` the ideal one outside.
    {real : Phi B} {ideal : Phi A}
    -- `simulator : End A` is admitted, as `admitted : simulator.op ∈ converters` records.
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    -- `equation`: `converter • real = simulator • ideal`.
    (equation : attach converter real =
      attach simulator ideal) :
    Constructs converter ({real} : Specification (Phi B))
      (star converters ({ideal} : Specification (Phi A))) := by
  let := endoMulAction Phi A
  exact ConstructiveCryptography.Specification.constructs_star_of_simulator
    simulator.op admitted equation

omit [MonoidalCategory C] in
/-- Pointwise exact simulator witnesses prove construction into a star-relaxed
singleton ideal: `converter` constructs `star converters {ideal}` from `real`.

Maurer--Renner 2016, Section 4.2 (printed p. 12): a simulator is exhibited to
prove the required construction; it is not part of the construction notion. -/
lemma constructs_star_of_simulators {A B : C}
    -- `converter` exposes interface A using B; `converters` is the admitted simulator class on A.
    {converter : A ⟶ B} {converters : EndoFamily A}
    -- Here `real` is a specification on `B`; `ideal : Phi A` is one resource on `A`.
    {real : Specification (Phi B)} {ideal : Phi A}
    -- `simulates`: each `resource ∈ real` has an admitted `simulator`, possibly depending on
    -- `resource`, with `converter • resource = simulator • ideal`.
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
the converter-class-relaxed ideal: `converter` constructs `star converters {ideal}` from
`{real}` within `error`, the witness being `simulator • ideal`. -/
lemma constructsWithin_star_of_simulator [CompatiblePseudoMetric C Phi] {A B : C}
    -- `converter` exposes interface A using B; `converters` is the admitted simulator class on A.
    {converter : A ⟶ B} {converters : EndoFamily A}
    -- `real : Phi B` is the resource used inside; `ideal : Phi A` is the desired outside resource.
    {real : Phi B} {ideal : Phi A}
    -- `error` bounds the distance in Phi A; ENNReal permits infinity and untruncated addition.
    {error : ENNReal}
    -- `simulator : End A` is admitted, as `admitted : simulator.op ∈ converters` records.
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    -- `close`: `simulator • ideal` is within `error` of `converter • real` in `Phi A`.
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
a star-relaxed singleton ideal: `converter` constructs `star converters {ideal}` from `real`
within `error`. -/
lemma constructsWithin_star_of_simulators [CompatiblePseudoMetric C Phi] {A B : C}
    -- `converter` exposes interface A using B; `converters` is the admitted simulator class on A.
    {converter : A ⟶ B} {converters : EndoFamily A}
    -- `real` is a set of resources on B; `ideal : Phi A` is the fixed desired outside resource.
    {real : Specification (Phi B)} {ideal : Phi A}
    -- `error` is one ENNReal distance budget for all members of real, possibly infinite.
    {error : ENNReal}
    -- `simulates`: each `resource ∈ real` has an admitted `simulator`, possibly depending on
    -- `resource`, with `simulator • ideal` within the one budget `error` of
    -- `converter • resource`.
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
relaxation of the converter-class-relaxed ideal: `converter` constructs
`epsilonRelaxation error (star converters {ideal})` (MR16's `(S*)ᵋ`) from `{real}`. The
relaxation is closed (`≤ error`) and `error : ENNReal` may be `∞` or `0`.

Maurer--Renner 2016, Lemma 5 (printed p. 12):
“`∃σ ∈ Σ : πR ≈ᵋ Sσ  ⟹  R —π→ (S*)ᵋ`.” -/
theorem constructs_of_simulator [CompatiblePseudoMetric C Phi] {A B : C}
    -- `converter : A ⟶ B` is MR16's protocol `π`; `converters` is its class `Σ` on `A`.
    {converter : A ⟶ B} {converters : EndoFamily A}
    -- `real : Phi B` is MR16's `R`, `ideal : Phi A` its `S`, and `error : ENNReal` its `ε`.
    {real : Phi B} {ideal : Phi A} {error : ENNReal}
    -- `simulator : End A` is MR16's `σ`; `admitted : simulator.op ∈ converters` is `σ ∈ Σ`.
    (simulator : CategoryTheory.End A) (admitted : simulator.op ∈ converters)
    -- `close` is `πR ≈ᵋ Sσ`: `converter • real` lies within `error` of `simulator • ideal`.
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
