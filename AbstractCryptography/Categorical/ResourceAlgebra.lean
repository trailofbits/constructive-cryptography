/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Types.Basic

set_option autoImplicit false

/-!
# Resource algebra

The interface category and contravariant resource functor are explicit.  A
`ResourceAlgebra` selects ordered parallel composition, the dummy resource,
one pseudo-emetric on each resource fibre, and the corresponding
non-expansion laws.  It assumes no symmetry.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “A converter α, when applied
as an interface i of a resource, induces a function Φ → Φ : R → αⁱR.”  The
same paragraph states “(β ◦ α)ⁱR = βⁱ(αⁱR).”

Jost, Section 2.2.2 (printed pp. 17--18): “A finite set of resources with
disjoint interface sets can be viewed as a single one.”  The same section
defines “the (canonical) dummy resource.”  Proposition 2.2.3 gives attachment
locality, and Section 4.2.2 (printed p. 51) says “the parallel composition
property is just associativity.”

Liu--Maurer's synchronous systems give one concrete resource/converter
specialization of these operations. Lanzenberger supplies a possible
fixed-interface random-system fibre and distance, not additional axioms for
this carrier-independent class.

The class extends the selected fibre metrics and converter non-expansion from
`Categorical.IsNonexpanding`.  Its fields are installed only inside the
operations below; no global fibre metric or lax-monoidal instance is added.
-/

namespace AbstractCryptography.Categorical

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory

universe u v w

private def resourceParallel
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (Phi : Opposite C ⥤ Type w) (lax : Phi.LaxMonoidal)
    {A B : Opposite C} (left : Phi.obj A) (right : Phi.obj B) :
    Phi.obj (A ⊗ B) := by
  letI := lax
  exact LaxMonoidal.μ Phi A B (left, right)

private def dummyResource
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (Phi : Opposite C ⥤ Type w) (lax : Phi.LaxMonoidal) :
    Phi.obj (𝟙_ (Opposite C)) := by
  letI := lax
  exact LaxMonoidal.ε Phi PUnit.unit

/-- Compatible ordered parallel composition and distance on the fibres of one
explicit contravariant resource functor.

Maurer--Renner 2016, Definition 2 (printed p. 11): “A metric `d` on `Φ` is
called non-expanding if `d(αR, αS) ≤ d(R, S)` for all `α`.” Jost, Section
2.2.2 (printed p. 17), states: “A finite set of resources with disjoint
interface sets can be viewed as a single one.” The remaining fields are the
interface-indexed functorial and ordered-parallel laws relating those two operations. -/
class ResourceAlgebra
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (Phi : Opposite C ⥤ Type w)
    extends IsNonexpanding Phi where
  laxMonoidal : Phi.LaxMonoidal
  parallel_nonexpanding : ∀ (A B : Opposite C)
      (left left' : Phi.obj A) (right right' : Phi.obj B),
    @edist (Phi.obj (A ⊗ B)) (fibreMetric (A ⊗ B)).toEDist
        (resourceParallel Phi laxMonoidal left right)
        (resourceParallel Phi laxMonoidal left' right') ≤
      @edist (Phi.obj A) (fibreMetric A).toEDist left left' +
        @edist (Phi.obj B) (fibreMetric B).toEDist right right'

namespace ResourceAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}

/-- Resources in the fibre selected by an interface. -/
abbrev Resource (Phi : Opposite C ⥤ Type w) (A : C) :=
  Phi.obj (Opposite.op A)

/-- Converters between two interfaces. -/
abbrev Converter (C : Type u) [Category.{v} C] (A B : C) := A ⟶ B

/-- A specification in one resource fibre. -/
abbrev Specification (Phi : Opposite C ⥤ Type w) (A : C) :=
  AbstractCryptography.Specification (Resource Phi A)

/-- Converter attachment is the contravariant resource-functor map.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “Application of a converter at
interface i transforms a resource R into another resource which we denote by
αⁱR.” -/
def attach {A B : C} (converter : A ⟶ B) :
    Resource Phi B → Resource Phi A :=
  Phi.map converter.op

/-- Ordered parallel composition of two resources.

Jost, Section 2.2.2 (printed p. 17): “A finite set of resources with disjoint
interface sets can be viewed as a single one.” -/
def parallel [ResourceAlgebra C Phi] {A B : C}
    (left : Resource Phi A) (right : Resource Phi B) :
    Resource Phi (A ⊗ B) :=
  resourceParallel Phi ResourceAlgebra.laxMonoidal left right

/-- Jost's canonical dummy resource at the monoidal unit interface.

Jost, Section 2.2.2 (printed p. 18): “The resource consisting of the dummy
interface only is called the (canonical) dummy resource.” -/
def dummy [ResourceAlgebra C Phi] : Resource Phi (𝟙_ C) :=
  dummyResource Phi ResourceAlgebra.laxMonoidal

/-- Distance in the selected resource fibre. -/
noncomputable def distance [ResourceAlgebra C Phi] {A : C}
    (left right : Resource Phi A) : ENNReal :=
  Categorical.distance (F := Phi) left right

omit [MonoidalCategory C] in
@[simp]
theorem attach_identity {A : C} (resource : Resource Phi A) :
    attach (Phi := Phi) (𝟙 A) resource = resource := by
  -- The resource functor maps the identity converter to the identity function.
  simp [attach]

omit [MonoidalCategory C] in
/-- Serial converter attachment is nested attachment.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “`(β ◦ α)ⁱR =
βⁱ(αⁱR)`.” -/
theorem attach_serial {A B D : C} (first : A ⟶ B) (second : B ⟶ D)
    (resource : Resource Phi D) :
    attach (Phi := Phi) (first ≫ second) resource =
      attach (Phi := Phi) first (attach (Phi := Phi) second resource) := by
  -- Contravariance reverses the functor map back into attachment order.
  simp [attach]

@[simp]
theorem converter_parallel_identity (A B : C) :
    (𝟙 A) ⊗ₘ (𝟙 B) = 𝟙 (A ⊗ B) := by
  -- The ordered tensor bifunctor preserves identities.
  simp

/-- Ordered converter parallel preserves serial composition. -/
theorem converter_parallel_serial
    {A B D E G H : C}
    (leftFirst : A ⟶ B) (leftSecond : B ⟶ D)
    (rightFirst : E ⟶ G) (rightSecond : G ⟶ H) :
    (leftFirst ≫ leftSecond) ⊗ₘ (rightFirst ≫ rightSecond) =
      (leftFirst ⊗ₘ rightFirst) ≫
        (leftSecond ⊗ₘ rightSecond) := by
  -- Bifunctoriality distributes ordered parallel over serial composition.
  simp

/-- Attachment distributes over ordered resource parallel.

Jost, Proposition 2.2.3 (printed p. 18): “if `S` is another resource such
that the interface sets of `R` and `S` are disjoint,” then attachment to `R`
commutes with adjoining `S` in parallel. -/
theorem attach_parallel [ResourceAlgebra C Phi]
    {A A' B B' : C}
    (leftConverter : A' ⟶ A) (rightConverter : B' ⟶ B)
    (left : Resource Phi A) (right : Resource Phi B) :
    attach (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
        (parallel (Phi := Phi) left right) =
      parallel (Phi := Phi)
        (attach (Phi := Phi) leftConverter left)
        (attach (Phi := Phi) rightConverter right) := by
  -- Select this algebra's ordered resource parallel.
  letI := ResourceAlgebra.laxMonoidal (C := C) (Phi := Phi)
  -- Lax-monoidal naturality moves both attachments through parallel.
  have naturality := LaxMonoidal.μ_natural Phi
    leftConverter.op rightConverter.op
  exact congrFun naturality (left, right) |>.symm

/-- Ordered resource parallel is associative through the routed associator.

Jost, Section 4.2.2 (printed p. 51): “the parallel composition property is
just associativity.” -/
theorem parallel_assoc [ResourceAlgebra C Phi] {A B D : C}
    (left : Resource Phi A) (middle : Resource Phi B)
    (right : Resource Phi D) :
    attach (Phi := Phi) (α_ A B D).inv
        (parallel (Phi := Phi) (parallel (Phi := Phi) left middle) right) =
      parallel (Phi := Phi) left (parallel (Phi := Phi) middle right) := by
  -- Select this algebra's ordered resource parallel.
  letI := ResourceAlgebra.laxMonoidal (C := C) (Phi := Phi)
  -- Lax-monoidal associativity identifies the routed bracketings.
  have associativity := LaxMonoidal.associativity Phi
    (Opposite.op A) (Opposite.op B) (Opposite.op D)
  simpa [attach, parallel, resourceParallel] using
    congrFun associativity ((left, middle), right)

@[simp]
theorem parallel_dummy_left [ResourceAlgebra C Phi] {A : C}
    (resource : Resource Phi A) :
    attach (Phi := Phi) (λ_ A).inv
        (parallel (Phi := Phi) (dummy (C := C) (Phi := Phi)) resource) =
      resource := by
  -- Select this algebra's ordered resource parallel and dummy resource.
  letI := ResourceAlgebra.laxMonoidal (C := C) (Phi := Phi)
  -- Lax-monoidal left unitality removes the dummy component.
  have unitality := LaxMonoidal.left_unitality Phi (Opposite.op A)
  change Phi.map (λ_ (Opposite.op A)).hom
      (LaxMonoidal.μ Phi (𝟙_ (Opposite C)) (Opposite.op A)
        (LaxMonoidal.ε Phi PUnit.unit, resource)) = resource
  exact congrFun unitality (PUnit.unit, resource) |>.symm

@[simp]
theorem parallel_dummy_right [ResourceAlgebra C Phi] {A : C}
    (resource : Resource Phi A) :
    attach (Phi := Phi) (ρ_ A).inv
        (parallel (Phi := Phi) resource (dummy (C := C) (Phi := Phi))) =
      resource := by
  -- Select this algebra's ordered resource parallel and dummy resource.
  letI := ResourceAlgebra.laxMonoidal (C := C) (Phi := Phi)
  -- Lax-monoidal right unitality removes the dummy component.
  have unitality := LaxMonoidal.right_unitality Phi (Opposite.op A)
  change Phi.map (ρ_ (Opposite.op A)).hom
      (LaxMonoidal.μ Phi (Opposite.op A) (𝟙_ (Opposite C))
        (resource, LaxMonoidal.ε Phi PUnit.unit)) = resource
  exact congrFun unitality (resource, PUnit.unit) |>.symm

@[simp]
theorem distance_self [ResourceAlgebra C Phi] {A : C}
    (resource : Resource Phi A) :
    distance (Phi := Phi) resource resource = 0 :=
  Categorical.distance_self resource

theorem distance_triangle [ResourceAlgebra C Phi] {A : C}
    (left middle right : Resource Phi A) :
    distance (Phi := Phi) left right ≤
      distance (Phi := Phi) left middle +
        distance (Phi := Phi) middle right :=
  Categorical.distance_triangle left middle right

/-- Converter attachment is non-expanding in the selected fibre distances. -/
theorem distance_attach_le [ResourceAlgebra C Phi] {A B : C}
    (converter : A ⟶ B) (left right : Resource Phi B) :
    distance (Phi := Phi) (attach (Phi := Phi) converter left)
        (attach (Phi := Phi) converter right) ≤
      distance (Phi := Phi) left right :=
  Categorical.distance_map_le converter.op left right

/-- Attachment along an interface isomorphism preserves the selected fibre
distance exactly. -/
theorem distance_attach_iso [ResourceAlgebra C Phi] {A B : C}
    (relabel : A ≅ B) (left right : Resource Phi B) :
    distance (Phi := Phi) (attach (Phi := Phi) relabel.hom left)
        (attach (Phi := Phi) relabel.hom right) =
      distance (Phi := Phi) left right := by
  apply le_antisymm
  · -- Non-expansion gives the forward inequality.
    exact distance_attach_le relabel.hom left right
  · -- Apply the inverse isomorphism to obtain the reverse inequality.
    calc
      distance (Phi := Phi) left right =
          distance (Phi := Phi)
            (attach (Phi := Phi) relabel.inv
              (attach (Phi := Phi) relabel.hom left))
            (attach (Phi := Phi) relabel.inv
              (attach (Phi := Phi) relabel.hom right)) := by
                rw [← attach_serial relabel.inv relabel.hom,
                  ← attach_serial relabel.inv relabel.hom]
                simp
      _ ≤ distance (Phi := Phi)
            (attach (Phi := Phi) relabel.hom left)
            (attach (Phi := Phi) relabel.hom right) :=
          distance_attach_le relabel.inv _ _

/-- Ordered resource parallel is jointly non-expanding. -/
theorem distance_parallel_le [ResourceAlgebra C Phi] {A B : C}
    (left left' : Resource Phi A) (right right' : Resource Phi B) :
    distance (Phi := Phi) (parallel (Phi := Phi) left right)
        (parallel (Phi := Phi) left' right') ≤
      distance (Phi := Phi) left left' +
        distance (Phi := Phi) right right' :=
  ResourceAlgebra.parallel_nonexpanding
    (Opposite.op A) (Opposite.op B) left left' right right'

/-- Ordered parallel with an unchanged right component is non-expanding in
the left component. -/
theorem distance_parallel_left_le [ResourceAlgebra C Phi] {A B : C}
    (left left' : Resource Phi A) (right : Resource Phi B) :
    distance (Phi := Phi) (parallel (Phi := Phi) left right)
        (parallel (Phi := Phi) left' right) ≤
      distance (Phi := Phi) left left' := by
  -- Apply joint non-expansion with identical right components.
  exact (distance_parallel_le left left' right right).trans_eq
    (by rw [distance_self, add_zero])

/-- Ordered parallel with an unchanged left component is non-expanding in
the right component. -/
theorem distance_parallel_right_le [ResourceAlgebra C Phi] {A B : C}
    (left : Resource Phi A) (right right' : Resource Phi B) :
    distance (Phi := Phi) (parallel (Phi := Phi) left right)
        (parallel (Phi := Phi) left right') ≤
      distance (Phi := Phi) right right' := by
  -- Apply joint non-expansion with identical left components.
  exact (distance_parallel_le left left right right').trans_eq
    (by rw [distance_self, zero_add])

namespace Specification

/-- Direct image of a specification under converter attachment.  This is the
existing categorical direct image at the corresponding opposite objects. -/
abbrev map {A B : C} (converter : A ⟶ B)
    (source : Specification Phi B) : Specification Phi A :=
  Categorical.Specification.map Phi converter.op source

/-- Ordered parallel composition of specifications.

Jost, Section 2.2.2 (printed p. 17): “A finite set of resources with disjoint
interface sets can be viewed as a single one.” -/
def parallel [ResourceAlgebra C Phi] {A B : C}
    (left : Specification Phi A) (right : Specification Phi B) :
    Specification Phi (A ⊗ B) :=
  Set.image2 (ResourceAlgebra.parallel (Phi := Phi)) left right

/-- Ordered parallel of singleton specifications is the singleton containing
the ordered parallel resource. -/
@[simp]
theorem parallel_singleton [ResourceAlgebra C Phi] {A B : C}
    (left : Resource Phi A) (right : Resource Phi B) :
    parallel (Phi := Phi) ({left} : Specification Phi A)
        ({right} : Specification Phi B) =
      ({ResourceAlgebra.parallel (Phi := Phi) left right} :
        Specification Phi (A ⊗ B)) := by
  -- Singleton membership fixes both components of the image.
  ext resource
  simp [parallel]

/-- The singleton specification of Jost's canonical dummy resource.

Jost, Section 2.2.2 (printed p. 18): “The resource consisting of the dummy
interface only is called the (canonical) dummy resource.” -/
def dummy [ResourceAlgebra C Phi] : Specification Phi (𝟙_ C) :=
  {ResourceAlgebra.dummy (C := C) (Phi := Phi)}

/-- Ordered specification parallel is associative through the routed
associator. -/
theorem parallel_assoc [ResourceAlgebra C Phi] {A B D : C}
    (left : Specification Phi A) (middle : Specification Phi B)
    (right : Specification Phi D) :
    map (Phi := Phi) (α_ A B D).inv
        (parallel (Phi := Phi) (parallel (Phi := Phi) left middle) right) =
      parallel (Phi := Phi) left (parallel (Phi := Phi) middle right) := by
  ext resource
  constructor
  · -- Decompose a left-associated admitted resource into three components.
    rintro ⟨combined, ⟨leftMiddle, ⟨leftResource, leftAdmitted,
        middleResource, middleAdmitted, rfl⟩, rightResource,
        rightAdmitted, rfl⟩, rfl⟩
    -- Reassociate the same three components to the right.
    refine ⟨leftResource, leftAdmitted,
      ResourceAlgebra.parallel (Phi := Phi) middleResource rightResource,
      ⟨middleResource, middleAdmitted, rightResource, rightAdmitted, rfl⟩, ?_⟩
    exact (ResourceAlgebra.parallel_assoc
      (Phi := Phi) leftResource middleResource rightResource).symm
  · -- Decompose a right-associated admitted resource into three components.
    rintro ⟨leftResource, leftAdmitted, middleRight,
        ⟨middleResource, middleAdmitted, rightResource, rightAdmitted, rfl⟩,
        rfl⟩
    -- Reassociate the same three components to the left before attachment.
    refine ⟨ResourceAlgebra.parallel (Phi := Phi)
        (ResourceAlgebra.parallel (Phi := Phi) leftResource middleResource)
        rightResource,
      ⟨ResourceAlgebra.parallel (Phi := Phi) leftResource middleResource,
        ⟨leftResource, leftAdmitted, middleResource, middleAdmitted, rfl⟩,
        rightResource, rightAdmitted, rfl⟩, ?_⟩
    exact ResourceAlgebra.parallel_assoc
      (Phi := Phi) leftResource middleResource rightResource

@[simp]
theorem parallel_dummy_left [ResourceAlgebra C Phi] {A : C}
    (source : Specification Phi A) :
    map (Phi := Phi) (λ_ A).inv
        (parallel (Phi := Phi) (dummy (C := C) (Phi := Phi)) source) =
      source := by
  ext resource
  constructor
  · -- The dummy component is uniquely the canonical dummy resource.
    rintro ⟨combined, ⟨dummyResource, dummyAdmitted,
        original, admitted, rfl⟩, rfl⟩
    have dummyEqual : dummyResource =
        ResourceAlgebra.dummy (C := C) (Phi := Phi) :=
      Set.mem_singleton_iff.mp dummyAdmitted
    subst dummyResource
    change attach (Phi := Phi) (λ_ A).inv
      (ResourceAlgebra.parallel (Phi := Phi)
        (ResourceAlgebra.dummy (C := C) (Phi := Phi)) original) ∈ source
    simpa using admitted
  · -- Pair the admitted resource with the canonical dummy resource.
    intro admitted
    refine ⟨ResourceAlgebra.parallel (Phi := Phi)
        (ResourceAlgebra.dummy (C := C) (Phi := Phi)) resource,
      ⟨ResourceAlgebra.dummy (C := C) (Phi := Phi), Set.mem_singleton _,
        resource, admitted, rfl⟩, ?_⟩
    exact ResourceAlgebra.parallel_dummy_left (Phi := Phi) resource

@[simp]
theorem parallel_dummy_right [ResourceAlgebra C Phi] {A : C}
    (source : Specification Phi A) :
    map (Phi := Phi) (ρ_ A).inv
        (parallel (Phi := Phi) source (dummy (C := C) (Phi := Phi))) =
      source := by
  ext resource
  constructor
  · -- The dummy component is uniquely the canonical dummy resource.
    rintro ⟨combined, ⟨original, admitted,
        dummyResource, dummyAdmitted, rfl⟩, rfl⟩
    have dummyEqual : dummyResource =
        ResourceAlgebra.dummy (C := C) (Phi := Phi) :=
      Set.mem_singleton_iff.mp dummyAdmitted
    subst dummyResource
    change attach (Phi := Phi) (ρ_ A).inv
      (ResourceAlgebra.parallel (Phi := Phi) original
        (ResourceAlgebra.dummy (C := C) (Phi := Phi))) ∈ source
    simpa using admitted
  · -- Pair the admitted resource with the canonical dummy resource.
    intro admitted
    refine ⟨ResourceAlgebra.parallel (Phi := Phi) resource
        (ResourceAlgebra.dummy (C := C) (Phi := Phi)),
      ⟨resource, admitted,
        ResourceAlgebra.dummy (C := C) (Phi := Phi),
        Set.mem_singleton _, rfl⟩, ?_⟩
    exact ResourceAlgebra.parallel_dummy_right (Phi := Phi) resource

/-- Exact construction is the existing categorical direct-image inclusion.

Maurer--Renner 2016, Definition 1 (printed p. 11):
“R —π→ S :⇐⇒ πR ⊆ S.” -/
abbrev Constructs {A B : C} (converter : A ⟶ B)
    (source : Specification Phi B) (target : Specification Phi A) : Prop :=
  Categorical.Specification.Constructs Phi converter.op source target

omit [MonoidalCategory C] in
/-- Exact construction holds exactly when every admitted resource is carried
into the target specification. -/
theorem constructs_iff {A B : C} {converter : A ⟶ B}
    {source : Specification Phi B} {target : Specification Phi A} :
    Constructs (Phi := Phi) converter source target ↔
      ∀ resource ∈ source,
        attach (Phi := Phi) converter resource ∈ target := by
  constructor
  · intro construction resource admitted
    exact construction ⟨resource, admitted, rfl⟩
  · rintro construction result ⟨resource, admitted, rfl⟩
    exact construction resource admitted

omit [MonoidalCategory C] in
/-- Exact construction is contravariant in its source specification and
covariant in its target specification.

Maurer--Renner 2016, Section 2.3 (printed p. 5):
“`R —γ→ S =⇒ R′ —γ→ S′` if `R′ ⊆ R` and `S ⊆ S′`.” -/
theorem Constructs.mono {A B : C} {converter : A ⟶ B}
    {source source' : Specification Phi B}
    {target target' : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source target)
    (sourceIncluded : source' ⊆ source)
    (targetIncluded : target ⊆ target') :
    Constructs (Phi := Phi) converter source' target' := by
  rw [constructs_iff] at construction ⊢
  intro resource admitted
  -- Weaken the source premise and then the target conclusion.
  exact targetIncluded (construction resource (sourceIncluded admitted))

omit [MonoidalCategory C] in
/-- Singleton exact construction is equality after converter attachment.

Jost--Maurer 2020, Definition 1 (printed p. 9): “In slight abuse of notation,
we write `R —π→ S` in lieu of `{R} —π→ {S}`.” -/
theorem constructs_singleton_iff {A B : C} {converter : A ⟶ B}
    {source : Resource Phi B} {target : Resource Phi A} :
    Constructs (Phi := Phi) converter
        ({source} : Specification Phi B) ({target} : Specification Phi A) ↔
      attach (Phi := Phi) converter source = target := by
  -- Reduce singleton construction to singleton target membership.
  rw [constructs_iff]
  simp only [Set.mem_singleton_iff, forall_eq]

omit [MonoidalCategory C] in
/-- Equal converters between the same interfaces have equal attachment on every resource. -/
theorem attach_eq_of_converter_eq {A B : C} {left right : A ⟶ B}
    (equal : left = right) (resource : Resource Phi B) :
    attach (Phi := Phi) left resource = attach (Phi := Phi) right resource := by
  -- Substitute the converter equality in the functor map.
  subst right
  rfl

omit [MonoidalCategory C] in
/-- Exact construction is invariant under equality of converters between the same interfaces. -/
theorem constructs_iff_of_converter_eq {A B : C} {left right : A ⟶ B}
    (equal : left = right) {source : Specification Phi B}
    {target : Specification Phi A} :
    Constructs (Phi := Phi) left source target ↔
      Constructs (Phi := Phi) right source target := by
  -- Substitute the converter equality in the construction relation.
  subst right
  rfl

omit [MonoidalCategory C] in
@[simp]
theorem constructs_identity {A : C} (source : Specification Phi A) :
    Constructs (Phi := Phi) (𝟙 A) source source := by
  -- Check direct-image inclusion pointwise.
  rw [constructs_iff]
  intro resource admitted
  -- Identity attachment leaves the admitted resource unchanged.
  simpa using admitted

omit [MonoidalCategory C] in
/-- Exact constructions compose serially.

Maurer--Renner 2016, Lemma 1 (printed p. 11): “This construction notion is
composable.” -/
theorem Constructs.serial {A B D : C}
    {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source middle)
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source target := by
  -- Rewrite both premises and the conclusion as pointwise membership.
  rw [constructs_iff] at inner outer ⊢
  intro resource admitted
  -- Serial attachment first reaches the middle, then the target.
  rw [attach_serial]
  exact outer _ (inner resource admitted)

omit [MonoidalCategory C] in
/-- Serial composition of constructions whose intermediate and target
specifications are images of explicit simulators.

Jost--Maurer 2020, Proposition 2.1 (printed p. 10): “By composition order
invariance we have `π'σR = σπ'R ⊆ σσ'T`.”  The commutation equality is
an explicit premise here; addressed disjointness is one way to prove it. -/
theorem Constructs.serial_simulators {A B D : C}
    {first : A ⟶ B} {second : B ⟶ D}
    {innerSimulator : B ⟶ B}
    {transportedSimulator outerSimulator : A ⟶ A}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source
      (map (Phi := Phi) innerSimulator middle))
    (outer : Constructs (Phi := Phi) first middle
      (map (Phi := Phi) outerSimulator target))
    (commutes : first ≫ innerSimulator = transportedSimulator ≫ first) :
    Constructs (Phi := Phi) (first ≫ second) source
      (map (Phi := Phi) (transportedSimulator ≫ outerSimulator) target) := by
  rw [constructs_iff] at inner outer ⊢
  intro resource admitted
  -- The inner construction selects an admitted intermediate resource.
  obtain ⟨middleResource, middleAdmitted, innerEquation⟩ :=
    inner resource admitted
  -- The outer construction selects an admitted target resource.
  obtain ⟨targetResource, targetAdmitted, outerEquation⟩ :=
    outer middleResource middleAdmitted
  change attach (Phi := Phi) innerSimulator middleResource =
    attach (Phi := Phi) second resource at innerEquation
  change attach (Phi := Phi) outerSimulator targetResource =
    attach (Phi := Phi) first middleResource at outerEquation
  -- The composite simulator applied to that target is the required image.
  refine ⟨targetResource, targetAdmitted, ?_⟩
  -- Serial attachment and the crossing equality give the paper's equation.
  calc
    attach (Phi := Phi) (transportedSimulator ≫ outerSimulator)
        targetResource =
        attach (Phi := Phi) transportedSimulator
          (attach (Phi := Phi) outerSimulator targetResource) :=
      attach_serial transportedSimulator outerSimulator targetResource
    _ = attach (Phi := Phi) transportedSimulator
          (attach (Phi := Phi) first middleResource) := by
      rw [outerEquation]
    _ = attach (Phi := Phi) (transportedSimulator ≫ first)
          middleResource :=
      (attach_serial transportedSimulator first middleResource).symm
    _ = attach (Phi := Phi) (first ≫ innerSimulator)
          middleResource := by
      rw [commutes]
    _ = attach (Phi := Phi) first
          (attach (Phi := Phi) innerSimulator middleResource) :=
      attach_serial first innerSimulator middleResource
    _ = attach (Phi := Phi) first
          (attach (Phi := Phi) second resource) := by
      rw [innerEquation]
    _ = attach (Phi := Phi) (first ≫ second) resource :=
      (attach_serial first second resource).symm

/-- Exact constructions compose in ordered parallel.

Jost, Section 4.2.2 (printed p. 51): “the parallel composition property is
just associativity.” -/
theorem Constructs.parallel [ResourceAlgebra C Phi]
    {A A' B B' : C}
    {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : Specification Phi A'} {leftTarget : Specification Phi A}
    {rightSource : Specification Phi B'} {rightTarget : Specification Phi B}
    (leftConstruction : Constructs (Phi := Phi) leftConverter
      leftSource leftTarget)
    (rightConstruction : Constructs (Phi := Phi) rightConverter
      rightSource rightTarget) :
    Constructs (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
      (parallel (Phi := Phi) leftSource rightSource)
      (parallel (Phi := Phi) leftTarget rightTarget) := by
  -- Rewrite both premises and the conclusion as pointwise membership.
  rw [constructs_iff] at leftConstruction rightConstruction ⊢
  -- Decompose an admitted parallel resource into its two components.
  rintro resource ⟨leftResource, leftAdmitted,
    rightResource, rightAdmitted, rfl⟩
  -- Attachment distributes over ordered parallel.
  rw [attach_parallel]
  -- The component constructions witness target parallel membership.
  exact ⟨attach (Phi := Phi) leftConverter leftResource,
    leftConstruction leftResource leftAdmitted,
    attach (Phi := Phi) rightConverter rightResource,
    rightConstruction rightResource rightAdmitted, rfl⟩

/-- Left context-insensitivity: an exact construction remains valid beside an
unchanged right-hand resource specification. -/
theorem Constructs.left_context [ResourceAlgebra C Phi]
    {A A' B : C} {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source target)
    (context : Specification Phi B) :
    Constructs (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) := by
  -- Pair the construction with identity construction of the right context.
  exact construction.parallel (constructs_identity context)

/-- Right context-insensitivity: an exact construction remains valid beside
an unchanged left-hand resource specification. -/
theorem Constructs.right_context [ResourceAlgebra C Phi]
    {A B B' : C} {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    (context : Specification Phi A)
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) := by
  -- Pair identity construction of the left context with the construction.
  exact (constructs_identity context).parallel construction

/-- Approximate construction is the existing categorical construction in the
selected fibre distance. -/
abbrev ConstructsWithin [ResourceAlgebra C Phi] {A B : C}
    (converter : A ⟶ B)
    (source : Specification Phi B) (target : Specification Phi A)
    (error : ENNReal) : Prop :=
  Categorical.Specification.ConstructsWithin
    Phi converter.op source target error

/-- Approximate construction holds exactly when every admitted source
resource attaches within the error bound of an admitted target resource. -/
theorem constructsWithin_iff [ResourceAlgebra C Phi] {A B : C}
    {converter : A ⟶ B} {source : Specification Phi B}
    {target : Specification Phi A} {error : ENNReal} :
    ConstructsWithin (Phi := Phi) converter source target error ↔
      ∀ resource ∈ source, ∃ ideal ∈ target,
        distance (Phi := Phi) (attach (Phi := Phi) converter resource) ideal ≤
          error := by
  -- Expose the resource-algebra names for the underlying functorial relation.
  rfl

/-- Singleton approximate construction is exactly the selected fibre-distance
bound after converter attachment. -/
theorem constructsWithin_singleton_iff [ResourceAlgebra C Phi] {A B : C}
    {converter : A ⟶ B} {source : Resource Phi B}
    {target : Resource Phi A} {error : ENNReal} :
    ConstructsWithin (Phi := Phi) converter
        ({source} : Specification Phi B) ({target} : Specification Phi A)
        error ↔
      distance (Phi := Phi) (attach (Phi := Phi) converter source) target ≤
        error := by
  -- Singleton membership fixes both source and target witnesses.
  rw [constructsWithin_iff]
  simp only [Set.mem_singleton_iff, forall_eq, exists_eq_left]

/-- Approximate construction is invariant under equality of converters
between the same interfaces. -/
theorem constructsWithin_iff_of_converter_eq [ResourceAlgebra C Phi]
    {A B : C} {left right : A ⟶ B} (equal : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    {error : ENNReal} :
    ConstructsWithin (Phi := Phi) left source target error ↔
      ConstructsWithin (Phi := Phi) right source target error := by
  -- Substitute the converter equality in the construction relation.
  subst right
  rfl

@[simp]
theorem constructsWithin_identity [ResourceAlgebra C Phi] {A : C}
    (source : Specification Phi A) :
    ConstructsWithin (Phi := Phi) (𝟙 A) source source 0 :=
  Categorical.Specification.constructsWithin_identity Phi source

/-- Approximate constructions compose serially with additive error. -/
theorem ConstructsWithin.serial [ResourceAlgebra C Phi]
    {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : ConstructsWithin (Phi := Phi) second source middle innerError)
    (outer : ConstructsWithin (Phi := Phi) first middle target outerError) :
    ConstructsWithin (Phi := Phi) (first ≫ second) source target
      (innerError + outerError) := by
  -- Opposite composition is the serial converter in resource-map order.
  change Categorical.Specification.ConstructsWithin Phi
    (second.op ≫ first.op) source target (innerError + outerError)
  -- Apply the existing functorial serial-construction theorem.
  exact Categorical.Specification.ConstructsWithin.serial Phi inner outer

/-- Approximate constructions compose in ordered parallel with additive
error. -/
theorem ConstructsWithin.parallel [ResourceAlgebra C Phi]
    {A A' B B' : C}
    {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : Specification Phi A'} {leftTarget : Specification Phi A}
    {rightSource : Specification Phi B'} {rightTarget : Specification Phi B}
    {leftError rightError : ENNReal}
    (leftConstruction : ConstructsWithin (Phi := Phi) leftConverter
      leftSource leftTarget leftError)
    (rightConstruction : ConstructsWithin (Phi := Phi) rightConverter
      rightSource rightTarget rightError) :
    ConstructsWithin (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
      (parallel (Phi := Phi) leftSource rightSource)
      (parallel (Phi := Phi) leftTarget rightTarget)
      (leftError + rightError) := by
  -- Decompose an admitted parallel resource into its two components.
  rintro resource ⟨leftResource, leftAdmitted,
    rightResource, rightAdmitted, rfl⟩
  -- Choose one nearby target resource from each component construction.
  obtain ⟨leftIdeal, leftIdealAdmitted, leftClose⟩ :=
    leftConstruction leftResource leftAdmitted
  obtain ⟨rightIdeal, rightIdealAdmitted, rightClose⟩ :=
    rightConstruction rightResource rightAdmitted
  -- Their ordered parallel belongs to the parallel target specification.
  refine ⟨ResourceAlgebra.parallel (Phi := Phi) leftIdeal rightIdeal,
    ⟨leftIdeal, leftIdealAdmitted, rightIdeal, rightIdealAdmitted, rfl⟩, ?_⟩
  -- Attachment distributes, and joint non-expansion adds both errors.
  change ResourceAlgebra.distance (Phi := Phi)
      (attach (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
        (ResourceAlgebra.parallel (Phi := Phi) leftResource rightResource))
      (ResourceAlgebra.parallel (Phi := Phi) leftIdeal rightIdeal) ≤
    leftError + rightError
  rw [attach_parallel]
  exact (distance_parallel_le _ _ _ _).trans
    (add_le_add leftClose rightClose)

/-- Left context-insensitivity for approximate construction. -/
theorem ConstructsWithin.left_context [ResourceAlgebra C Phi]
    {A A' B : C} {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    {error : ENNReal}
    (construction : ConstructsWithin (Phi := Phi) converter source target error)
    (context : Specification Phi B) :
    ConstructsWithin (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) error := by
  -- Pair the construction with zero-error identity construction of the context.
  simpa using construction.parallel (constructsWithin_identity context)

/-- Right context-insensitivity for approximate construction. -/
theorem ConstructsWithin.right_context [ResourceAlgebra C Phi]
    {A B B' : C} {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    {error : ENNReal}
    (context : Specification Phi A)
    (construction : ConstructsWithin (Phi := Phi) converter source target error) :
    ConstructsWithin (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) error := by
  -- Pair zero-error identity construction of the context with the construction.
  simpa using (constructsWithin_identity context).parallel construction

end Specification

end ResourceAlgebra

end AbstractCryptography.Categorical
