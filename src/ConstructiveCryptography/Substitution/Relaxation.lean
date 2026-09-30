import ConstructiveCryptography.CryptographicAlgebra.Relaxation
import ConstructiveCryptography.Substitution.Implication

set_option autoImplicit false

/-!
# Substitution relaxations

The substitution image of a specification under a class of transformations collects the
transformed endpoints of a one-use substitution (Banfi, §4.1.4). A reflexive substitution
relation turns a specification into its substitution relaxation, the resources substituting
for one of its members; the relaxation is compatible with converters and idempotent, so
constructions into relaxed specifications compose with simulators.

## Main definitions

* `Specification.substitutionImage`, `Specification.singleSubstitutionRelaxation`
* `Specification.substitutionRelaxation`

## Main results

* `Specification.singleSubstitutionRelaxation_compatible`,
  `Specification.substitutionRelaxation_compatible`: compatibility with converters
* `Specification.substitutionRelaxation_idem`: idempotence
* `Specification.Constructs.substitutionRelaxation_serial_simulators`: serial composition

Source: Banfi 2023, Definition 2.3.1 and §4.1.4; Jost, Definition 2.2.6.
-/

namespace ConstructiveCryptography.CryptographicAlgebra.Specification

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]
variable {Phi : C → Type w} [ResourceTheory C Phi]

/-- The specification image obtained by one oriented use of a substitution,
with its admitted transformations explicit.

Banfi, Section 4.1.4 (printed p. 76), specifies "`S ≡ ρ_S(X₀) ≃ ρ_S(X₁) ≡ R`"
and unions over `R` in the source specification. This is exactly that image;
it does not add reversed uses, transitive closure, or diagonal elements. -/
def substitutionImage {A B : C} (transformations : Set (A ⟶ B))
    (left right : Phi B) (source : Specification (Phi A)) :
    Specification (Phi A) :=
  {resource | ∃ transformation ∈ transformations,
    resource = attach transformation left ∧
      attach transformation right ∈ source}

/-- The literal one-use image is a relaxation when its admitted
transformations provide every required diagonal witness.

Jost, Definition 2.2.6 (printed p. 20), requires "`R ∈ φ(R)` for all `R ∈ Θ`".
For Banfi's one-transformation image (Section 4.1.4, printed p. 76), the
`diagonal` argument states precisely the missing obligation. Neither
transitivity nor idempotence is imposed or concluded. -/
def singleSubstitutionRelaxation {A B : C}
    (transformations : Set (A ⟶ B)) (left right : Phi B)
    (diagonal : ∀ resource : Phi A,
      ∃ transformation ∈ transformations,
        attach transformation left = resource ∧
        attach transformation right = resource) :
    ConstructiveCryptography.Relaxation (Phi A) :=
  ConstructiveCryptography.Relaxation.ofPointwise
    (fun center => substitutionImage transformations left right {center}) (by
      intro resource
      obtain ⟨transformation, allowed, leftEq, rightEq⟩ := diagonal resource
      exact ⟨transformation, allowed, leftEq.symm, rightEq⟩)

/-- The pointwise relaxation lifts to exactly Banfi's one-use image. -/
@[simp] theorem singleSubstitutionRelaxation_apply {A B : C}
    (transformations : Set (A ⟶ B)) (left right : Phi B)
    (diagonal : ∀ resource : Phi A,
      ∃ transformation ∈ transformations,
        attach transformation left = resource ∧
        attach transformation right = resource)
    (source : Specification (Phi A)) :
    singleSubstitutionRelaxation transformations left right diagonal source =
      substitutionImage transformations left right source := by
  ext resource
  simp only [singleSubstitutionRelaxation,
    ConstructiveCryptography.Relaxation.mem_ofPointwise_iff,
    substitutionImage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨center, hc, transformation, allowed, leftEq, rfl⟩
    exact ⟨transformation, allowed, leftEq, hc⟩
  · rintro ⟨transformation, allowed, leftEq, hc⟩
    exact ⟨_, hc, transformation, allowed, leftEq, rfl⟩

/-- Converter attachment preserves the one-use image when it preserves the
explicit class of admitted transformations by serial composition.

Banfi, Section 4.1.4 (printed p. 76), requires an "(efficient) transformation";
the admitted-class closure here is explicit. The attachment equation is
the existing categorical law, not an additional system-specific axiom. -/
theorem map_substitutionImage_subset {A B D : C} (converter : A ⟶ B)
    (sourceTransformations : Set (B ⟶ D)) (targetTransformations : Set (A ⟶ D))
    (closed : ∀ transformation ∈ sourceTransformations,
      converter ≫ transformation ∈ targetTransformations)
    (left right : Phi D) (source : Specification (Phi B)) :
    map converter (substitutionImage sourceTransformations left right source) ⊆
      substitutionImage targetTransformations left right (map converter source) := by
  rintro _ ⟨resource, ⟨transformation, allowed, leftEq, center⟩, rfl⟩
  -- Compose the named outer converter with the single substitution transformation.
  refine ⟨converter ≫ transformation, closed transformation allowed, ?_, ?_⟩
  · rw [leftEq, attach_serial]
  · -- The same converter maps the right endpoint into the image specification.
    exact ⟨attach transformation right, center,
      (attach_serial converter transformation right).symm⟩

/-- The one-use image with its supplied diagonal witnesses is compatible
under exactly the supplied transformation-closure hypothesis.

This is the converter compatibility of Banfi's Section 4.1.4 image
(printed p. 76), with the "(efficient) transformation" requirement kept as
explicit data and closure, rather than inferred from a generic category. -/
theorem singleSubstitutionRelaxation_compatible {B : C}
    (transformations : ∀ A : C, Set (A ⟶ B)) (left right : Phi B)
    (diagonal : ∀ A (resource : Phi A),
      ∃ transformation ∈ transformations A,
        attach transformation left = resource ∧
        attach transformation right = resource)
    (closed : ∀ {A D : C} (converter : A ⟶ D) transformation,
      transformation ∈ transformations D → converter ≫ transformation ∈ transformations A) :
    Relaxation.Compatible (fun A =>
      singleSubstitutionRelaxation (transformations A) left right (diagonal A)) := by
  intro A D converter source
  simp only [singleSubstitutionRelaxation_apply]
  exact map_substitutionImage_subset converter (transformations D) (transformations A)
    (closed converter) left right source

/-- Banfi's single-use construction statement is exactly the existence of
one admitted transformation with the displayed real and simulated-ideal
endpoint equations.

Banfi, Equation (4.2) (printed p. 76): "`π REAL ∈ (σ IDEAL)^s`". The
singleton specification interpretation uses the existing `Constructs` and
does not require an unsupported extensivity or idempotence claim. -/
theorem constructs_singleton_substitutionImage_iff {A B D E : C}
    (transformations : Set (A ⟶ B)) (left right : Phi B)
    (protocol : A ⟶ D) (simulator : A ⟶ E)
    (real : Phi D) (ideal : Phi E) :
    Constructs protocol {real}
        (substitutionImage transformations left right {attach simulator ideal}) ↔
      ∃ transformation ∈ transformations,
        attach protocol real = attach transformation left ∧
        attach transformation right = attach simulator ideal := by
  -- Singleton membership fixes the real resource and the simulated ideal center.
  rw [constructs_iff]
  simp only [Set.mem_singleton_iff, forall_eq, substitutionImage, Set.mem_ofPred_eq]

/-- The pointwise specification of resources substitutable for an admitted
center under one selected reflexive substitution relation.

Banfi 2023, Section 4.1.4 (printed p. 76) defines
`S^s = {S | ∃ R ∈ S : s implies S substitutes R}`. To represent implication
by finite assumption chains, select `SubstitutionRelation.generatedRelation`.
An arbitrary supplied relation has only its explicitly provided semantics;
it is not automatically implication under any chosen assumptions. The
reflexivity proof supplies the extensivity required by Jost, Definition 2.2.6
(printed p. 20): "`R ∈ φ(R)` for all `R ∈ Θ`". -/
noncomputable def substitutionRelaxation
    (relation : SubstitutionRelation C)
    (reflexive : ∀ A, Std.Refl (relation.substitutes A))
    {A : C} : ConstructiveCryptography.Relaxation (Phi A) :=
  ConstructiveCryptography.Relaxation.ofPointwise
    (fun center => {resource | relation.substitutes A resource center})
    ((reflexive A).refl)

@[simp]
theorem mem_substitutionRelaxation_iff
    (relation : SubstitutionRelation C)
    (reflexive : ∀ A, Std.Refl (relation.substitutes A))
    {A : C} {source : Specification (Phi A)} {resource : Phi A} :
    resource ∈ substitutionRelaxation relation reflexive source ↔
      ∃ center ∈ source, relation.substitutes A resource center :=
  ConstructiveCryptography.Relaxation.mem_ofPointwise_iff

/-- Substitution relaxation is compatible with converter attachment. -/
theorem substitutionRelaxation_compatible
    (relation : SubstitutionRelation C)
    (reflexive : ∀ A, Std.Refl (relation.substitutes A)) :
    Relaxation.Compatible
      (fun A => substitutionRelaxation relation reflexive (A := A)) := by
  intro A B converter source
  rintro resource ⟨original, originalRelaxed, rfl⟩
  rw [mem_substitutionRelaxation_iff] at originalRelaxed ⊢
  obtain ⟨center, admitted, close⟩ := originalRelaxed
  -- Transform the selected center and preserve its substitution witness.
  exact ⟨attach converter center, ⟨center, admitted, rfl⟩,
    relation.preserved converter close⟩

/-- Substitution relaxation is idempotent.

Banfi, Definition 2.3.1 (printed p. 13): "Transitivity".
For the finite-chain implication of Banfi, Section 2.3.1 (printed pp. 14--15),
transitivity concatenates the chains to an admitted center. The theorem uses
that explicit transitivity hypothesis; it is not an idempotence claim for
the single-use description in Section 4.1.4 (printed p. 76). -/
theorem substitutionRelaxation_idem
    (relation : SubstitutionRelation C)
    (reflexive : ∀ A, Std.Refl (relation.substitutes A))
    {A : C} (source : Specification (Phi A)) :
    substitutionRelaxation relation reflexive
        (substitutionRelaxation relation reflexive source) =
      substitutionRelaxation relation reflexive source := by
  apply Set.Subset.antisymm
  · intro resource relaxed
    rw [mem_substitutionRelaxation_iff] at relaxed ⊢
    obtain ⟨middle, middleRelaxed, resourceClose⟩ := relaxed
    rw [mem_substitutionRelaxation_iff] at middleRelaxed
    obtain ⟨center, admitted, middleClose⟩ := middleRelaxed
    -- Transitivity collapses resource-to-middle and middle-to-center.
    exact ⟨center, admitted,
      (relation.transitive A).trans resource middle center
        resourceClose middleClose⟩
  · -- Extensivity supplies the reverse inclusion.
    exact (substitutionRelaxation relation reflexive).subset_apply _

/-- Banfi's relation-based construction is exact construction into the
substitution relaxation of an explicitly simulated ideal resource.

Banfi 2023, Definition 2.4.3 (printed p. 28) requires a simulator `σ` and the
substitution `π REAL` versus `σ IDEAL`; Equation (4.2), printed p. 76, writes
the same statement as `π REAL ∈ (σ IDEAL)^s`. -/
theorem constructs_singleton_substitutionRelaxation_iff
    (relation : SubstitutionRelation C)
    (reflexive : ∀ A, Std.Refl (relation.substitutes A))
    {A B : C} {protocol : A ⟶ B} {simulator : A ⟶ A}
    {real : Phi B} {ideal : Phi A} :
    Constructs protocol ({real} : Specification (Phi B))
        (substitutionRelaxation relation reflexive
          ({attach simulator ideal} : Specification (Phi A))) ↔
      relation.substitutes A (attach protocol real)
        (attach simulator ideal) := by
  rw [constructs_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [mem_substitutionRelaxation_iff]
  simp

/-- Relation-based constructions with explicit simulators compose serially.

Banfi 2023, Theorem 2.4.4 (printed pp. 28--29) transforms the first
substitution by the outer protocol, commutes honest protocol and adversarial
simulator attachment, transforms the second substitution by the transported
simulator, and composes the simulators. The commuting converter equation is
explicit here; the generic categorical layer does not infer interface
disjointness. -/
theorem Constructs.substitutionRelaxation_serial_simulators
    (relation : SubstitutionRelation C)
    (reflexive : ∀ A, Std.Refl (relation.substitutes A))
    {A B D : C} {outerProtocol : A ⟶ B} {innerProtocol : B ⟶ D}
    {innerSimulator : B ⟶ B}
    {transportedSimulator outerSimulator : A ⟶ A}
    {real : Phi D} {middle : Phi B} {ideal : Phi A}
    (inner : Constructs innerProtocol
      ({real} : Specification (Phi D))
      (substitutionRelaxation relation reflexive
        ({attach innerSimulator middle} : Specification (Phi B))))
    (outer : Constructs outerProtocol
      ({middle} : Specification (Phi B))
      (substitutionRelaxation relation reflexive
        ({attach outerSimulator ideal} : Specification (Phi A))))
    (commutes : outerProtocol ≫ innerSimulator =
      transportedSimulator ≫ outerProtocol) :
    Constructs (outerProtocol ≫ innerProtocol)
      ({real} : Specification (Phi D))
      (substitutionRelaxation relation reflexive
        ({attach (transportedSimulator ≫ outerSimulator) ideal} :
          Specification (Phi A))) := by
  rw [constructs_singleton_substitutionRelaxation_iff] at inner outer ⊢
  -- Transform the inner construction by the outer protocol.
  have innerTransported := relation.preserved outerProtocol inner
  -- Transform the outer construction by the transported inner simulator.
  have outerTransported := relation.preserved transportedSimulator outer
  -- Expose each serial converter exactly in the paper's attachment order.
  rw [← attach_serial outerProtocol innerProtocol real,
    ← attach_serial outerProtocol innerSimulator middle] at innerTransported
  rw [← attach_serial transportedSimulator outerProtocol middle,
    ← attach_serial transportedSimulator outerSimulator ideal] at outerTransported
  -- The supplied locality equation identifies the two middle resources.
  rw [commutes] at innerTransported
  -- Transitivity composes the two transformed substitutions.
  exact (relation.transitive A).trans _ _ _ innerTransported outerTransported

end ConstructiveCryptography.CryptographicAlgebra.Specification
