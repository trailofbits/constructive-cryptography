import ConstructiveCryptography.Specification.Parallel
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Types.Basic

set_option autoImplicit false

/-!
# Cryptographic algebras

A resource theory on a category `C` of interfaces and converters assigns to each interface
`A` its resources `Φ A`, on which converters act by attachment, contravariantly in serial
composition. Attachment makes `Φ` a functor `Cᵒᵖ ⥤ Type`. A cryptographic algebra is a
resource theory on a monoidal category whose resource functor is lax monoidal: parallel
composition of resources, with the dummy resource as unit. Specifications are sets of
resources; a converter constructs `T` from `S` when it maps `S` into `T`. Exact
constructions compose serially and in parallel, and are insensitive to unchanged context.

Sources: Maurer–Renner 2016 (MR16), §3 (printed pp. 6–8) and Definition 1 (printed p. 11);
Jost, §2.2 (printed pp. 16–19).

## Main definitions

* `ResourceTheory C Φ`: resources and converter attachment
* `ResourceTheory.functor C Φ`: the resource functor
* `CryptographicAlgebra C Φ`: the lax monoidal structure of the resource functor
* `CryptographicAlgebra.parallel`, `CryptographicAlgebra.dummy`
* `CryptographicAlgebra.Specification.Constructs`: exact construction

## Main results

* `ResourceTheory.attach_serial`, `CryptographicAlgebra.attach_parallel`: attachment is
  functorial and local
* `CryptographicAlgebra.parallel_assoc`, `CryptographicAlgebra.parallel_dummy_left`,
  `CryptographicAlgebra.parallel_dummy_right`: parallel composition of resources
* `CryptographicAlgebra.Specification.Constructs.serial`,
  `CryptographicAlgebra.Specification.Constructs.parallel`: composition of constructions
-/

namespace ConstructiveCryptography

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory

universe u v w

/-- **A resource theory** on a category of interfaces and converters (MR16, §3.3, printed
p. 7): the resources `Phi A` on each interface `A`, and attachment of converters,
contravariant in serial composition. The category determines its resources. -/
class ResourceTheory (C : Type u) [Category.{v} C] (Phi : outParam (C → Type w)) where
  /-- Converter attachment.

  MR16, §3.3 (printed p. 7): “Application of a converter at interface i transforms a
  resource R into another resource which we denote by αⁱR.” -/
  attach : ∀ {A B : C}, (A ⟶ B) → Phi B → Phi A
  /-- Attaching the identity converter leaves a resource unchanged. -/
  attach_identity : ∀ {A : C} (resource : Phi A), attach (𝟙 A) resource = resource
  /-- Serial converter attachment is nested attachment.

  MR16, §3.3 (printed p. 7): “`(β ◦ α)ⁱR = βⁱ(αⁱR)`.” -/
  attach_serial : ∀ {A B D : C} (first : A ⟶ B) (second : B ⟶ D) (resource : Phi D),
    attach (first ≫ second) resource = attach first (attach second resource)

namespace ResourceTheory

attribute [simp] attach_identity

/-- The resource functor: an interface goes to its resources, a converter to attachment. -/
def functor (C : Type u) [Category.{v} C] (Phi : C → Type w) [ResourceTheory C Phi] :
    Cᵒᵖ ⥤ Type w where
  obj A := Phi A.unop
  map converter := TypeCat.ofHom (attach converter.unop)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro resource
    exact attach_identity resource
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro resource
    exact attach_serial second.unop first.unop resource

end ResourceTheory

/-- Parallel composition of resources, from a lax monoidal structure on the resource
functor. -/
def resourceParallel
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {Phi : C → Type w} [ResourceTheory C Phi]
    (lax : (ResourceTheory.functor C Phi).LaxMonoidal)
    {A B : C} (left : Phi A) (right : Phi B) : Phi (A ⊗ B) :=
  letI := lax
  LaxMonoidal.μ (ResourceTheory.functor C Phi) (Opposite.op A) (Opposite.op B) (left, right)

/-- **A cryptographic algebra** (MR16, §3): interfaces and converters form the monoidal
category `C`, with a resource theory whose resource functor is lax monoidal: parallel
composition of resources, with the dummy resource as unit. -/
class CryptographicAlgebra
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (Phi : C → Type w) [ResourceTheory C Phi] where
  laxMonoidal : (ResourceTheory.functor C Phi).LaxMonoidal

namespace CryptographicAlgebra

export ResourceTheory (attach attach_identity attach_serial)

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi]

/-- Converters from `A` to `B`. -/
abbrev Converter (C : Type u) [Category.{v} C] (A B : C) := A ⟶ B

/-- Converter attachment uses the standard heterogeneous action notation. -/
instance instHSMulConverterResource {A B : C} : HSMul (A ⟶ B) (Phi B) (Phi A) where
  hSMul := attach

omit [MonoidalCategory C] in
@[simp]
theorem smul_eq_attach {A B : C} (converter : A ⟶ B) (resource : Phi B) :
    (converter • resource : Phi A) = attach converter resource :=
  rfl

/-- Parallel composition of two resources.

Jost, §2.2.2 (printed p. 17): “A finite set of resources with disjoint interface sets can
be viewed as a single one.” -/
def parallel [CryptographicAlgebra C Phi] {A B : C} (left : Phi A) (right : Phi B) :
    Phi (A ⊗ B) :=
  resourceParallel CryptographicAlgebra.laxMonoidal left right

/-- Jost's canonical dummy resource at the monoidal unit interface.

Jost, §2.2.2 (printed p. 17), defines the dummy resource as one “where every party has an
empty interface set.” -/
def dummy [CryptographicAlgebra C Phi] : Phi (𝟙_ C) :=
  letI := CryptographicAlgebra.laxMonoidal (C := C) (Phi := Phi)
  LaxMonoidal.ε (ResourceTheory.functor C Phi) PUnit.unit

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
theorem attach_parallel [CryptographicAlgebra C Phi]
    {A A' B B' : C}
    (leftConverter : A' ⟶ A) (rightConverter : B' ⟶ B)
    (left : Phi A) (right : Phi B) :
    attach (leftConverter ⊗ₘ rightConverter)
        (parallel left right) =
      parallel
        (attach leftConverter left)
        (attach rightConverter right) := by
  -- Select this algebra's ordered resource parallel.
  let := CryptographicAlgebra.laxMonoidal (C := C) (Phi := Phi)
  -- Lax-monoidal naturality moves both attachments through parallel.
  have naturality := LaxMonoidal.μ_natural (ResourceTheory.functor C Phi)
    leftConverter.op rightConverter.op
  exact types_congr_hom naturality (left, right) |>.symm

/-- Ordered resource parallel is associative through the routed associator.

Jost, Section 2.2.2 (printed p. 17): “A finite set of resources with disjoint
interface sets can be viewed as a single one.” The equation below is the
associativity law of this library's selected binary packaging; Jost does not
postulate a monoidal category. -/
theorem parallel_assoc [CryptographicAlgebra C Phi] {A B D : C}
    (left : Phi A) (middle : Phi B)
    (right : Phi D) :
    attach (α_ A B D).inv
        (parallel (parallel left middle) right) =
      parallel left (parallel middle right) := by
  -- Select this algebra's ordered resource parallel.
  let := CryptographicAlgebra.laxMonoidal (C := C) (Phi := Phi)
  -- Lax-monoidal associativity identifies the routed bracketings.
  have associativity := LaxMonoidal.associativity (ResourceTheory.functor C Phi)
    (Opposite.op A) (Opposite.op B) (Opposite.op D)
  exact types_congr_hom associativity ((left, middle), right)

@[simp]
theorem parallel_dummy_left [CryptographicAlgebra C Phi] {A : C}
    (resource : Phi A) :
    attach (λ_ A).inv
        (parallel (dummy (C := C)) resource) =
      resource := by
  -- Select this algebra's ordered resource parallel and dummy resource.
  let := CryptographicAlgebra.laxMonoidal (C := C) (Phi := Phi)
  -- Lax-monoidal left unitality removes the dummy component.
  have unitality := LaxMonoidal.left_unitality (ResourceTheory.functor C Phi) (Opposite.op A)
  change (ResourceTheory.functor C Phi).map (λ_ (Opposite.op A)).hom
      (LaxMonoidal.μ (ResourceTheory.functor C Phi) (𝟙_ (Opposite C)) (Opposite.op A)
        (LaxMonoidal.ε (ResourceTheory.functor C Phi) PUnit.unit, resource)) = resource
  exact types_congr_hom unitality (PUnit.unit, resource) |>.symm

@[simp]
theorem parallel_dummy_right [CryptographicAlgebra C Phi] {A : C}
    (resource : Phi A) :
    attach (ρ_ A).inv
        (parallel resource (dummy (C := C))) =
      resource := by
  -- Select this algebra's ordered resource parallel and dummy resource.
  let := CryptographicAlgebra.laxMonoidal (C := C) (Phi := Phi)
  -- Lax-monoidal right unitality removes the dummy component.
  have unitality := LaxMonoidal.right_unitality (ResourceTheory.functor C Phi) (Opposite.op A)
  change (ResourceTheory.functor C Phi).map (ρ_ (Opposite.op A)).hom
      (LaxMonoidal.μ (ResourceTheory.functor C Phi) (Opposite.op A) (𝟙_ (Opposite C))
        (resource, LaxMonoidal.ε (ResourceTheory.functor C Phi) PUnit.unit)) = resource
  exact types_congr_hom unitality (resource, PUnit.unit) |>.symm

namespace Specification

/-- Direct image of a specification under converter attachment. -/
abbrev map {A B : C} (converter : A ⟶ B)
    (source : Specification (Phi B)) : Specification (Phi A) :=
  attach converter '' source

omit [MonoidalCategory C] in
@[simp]
theorem map_identity {A : C} (source : Specification (Phi A)) :
    map (𝟙 A) source = source := by
  simp [map, attach_identity]

omit [MonoidalCategory C] in
theorem map_serial {A B D : C} (first : A ⟶ B) (second : B ⟶ D)
    (source : Specification (Phi D)) :
    map (first ≫ second) source =
      map first (map second source) := by
  simp only [map, attach_serial]
  exact Set.image_comp _ _ _

/-- Ordered parallel composition of specifications.

Jost, Section 2.2.2 (printed p. 17): “A finite set of resources with disjoint
interface sets can be viewed as a single one.” -/
def parallel [CryptographicAlgebra C Phi] {A B : C}
    (left : Specification (Phi A)) (right : Specification (Phi B)) :
    Specification (Phi (A ⊗ B)) :=
  Set.image2 (CryptographicAlgebra.parallel) left right

/-- Ordered parallel of singleton specifications is the singleton containing
the ordered parallel resource. -/
@[simp]
theorem parallel_singleton [CryptographicAlgebra C Phi] {A B : C}
    (left : Phi A) (right : Phi B) :
    parallel ({left} : Specification (Phi A))
        ({right} : Specification (Phi B)) =
      ({CryptographicAlgebra.parallel left right} :
        Specification (Phi (A ⊗ B))) := by
  -- Singleton membership fixes both components of the image.
  ext resource
  simp [parallel]

/-- The singleton specification of Jost's canonical dummy resource.

Jost, Section 2.2.2 (printed p. 17), defines the dummy resource as one “where
every party has an empty interface set.” -/
def dummy [CryptographicAlgebra C Phi] : Specification (Phi (𝟙_ C)) :=
  {CryptographicAlgebra.dummy (C := C)}

/-- Ordered specification parallel is associative through the routed
associator. -/
theorem parallel_assoc [CryptographicAlgebra C Phi] {A B D : C}
    (left : Specification (Phi A)) (middle : Specification (Phi B))
    (right : Specification (Phi D)) :
    map (α_ A B D).inv
        (parallel (parallel left middle) right) =
      parallel left (parallel middle right) := by
  ext resource
  constructor
  · -- Decompose a left-associated admitted resource into three components.
    rintro ⟨combined, ⟨leftMiddle, ⟨leftResource, leftAdmitted,
        middleResource, middleAdmitted, rfl⟩, rightResource,
        rightAdmitted, rfl⟩, rfl⟩
    -- Reassociate the same three components to the right.
    refine ⟨leftResource, leftAdmitted,
      CryptographicAlgebra.parallel middleResource rightResource,
      ⟨middleResource, middleAdmitted, rightResource, rightAdmitted, rfl⟩, ?_⟩
    exact (CryptographicAlgebra.parallel_assoc
      leftResource middleResource rightResource).symm
  · -- Decompose a right-associated admitted resource into three components.
    rintro ⟨leftResource, leftAdmitted, middleRight,
        ⟨middleResource, middleAdmitted, rightResource, rightAdmitted, rfl⟩,
        rfl⟩
    -- Reassociate the same three components to the left before attachment.
    refine ⟨CryptographicAlgebra.parallel
        (CryptographicAlgebra.parallel leftResource middleResource)
        rightResource,
      ⟨CryptographicAlgebra.parallel leftResource middleResource,
        ⟨leftResource, leftAdmitted, middleResource, middleAdmitted, rfl⟩,
        rightResource, rightAdmitted, rfl⟩, ?_⟩
    exact CryptographicAlgebra.parallel_assoc
      leftResource middleResource rightResource

@[simp]
theorem parallel_dummy_left [CryptographicAlgebra C Phi] {A : C}
    (source : Specification (Phi A)) :
    map (λ_ A).inv
        (parallel (dummy (C := C)) source) =
      source := by
  ext resource
  constructor
  · -- The dummy component is uniquely the canonical dummy resource.
    rintro ⟨combined, ⟨dummyResource, dummyAdmitted,
        original, admitted, rfl⟩, rfl⟩
    have dummyEqual : dummyResource =
        CryptographicAlgebra.dummy (C := C) :=
      Set.mem_singleton_iff.mp dummyAdmitted
    subst dummyResource
    change attach (λ_ A).inv
      (CryptographicAlgebra.parallel
        (CryptographicAlgebra.dummy (C := C)) original) ∈ source
    simpa using admitted
  · -- Pair the admitted resource with the canonical dummy resource.
    intro admitted
    refine ⟨CryptographicAlgebra.parallel
        (CryptographicAlgebra.dummy (C := C)) resource,
      ⟨CryptographicAlgebra.dummy (C := C), Set.mem_singleton _,
        resource, admitted, rfl⟩, ?_⟩
    exact CryptographicAlgebra.parallel_dummy_left resource

@[simp]
theorem parallel_dummy_right [CryptographicAlgebra C Phi] {A : C}
    (source : Specification (Phi A)) :
    map (ρ_ A).inv
        (parallel source (dummy (C := C))) =
      source := by
  ext resource
  constructor
  · -- The dummy component is uniquely the canonical dummy resource.
    rintro ⟨combined, ⟨original, admitted,
        dummyResource, dummyAdmitted, rfl⟩, rfl⟩
    have dummyEqual : dummyResource =
        CryptographicAlgebra.dummy (C := C) :=
      Set.mem_singleton_iff.mp dummyAdmitted
    subst dummyResource
    change attach (ρ_ A).inv
      (CryptographicAlgebra.parallel original
        (CryptographicAlgebra.dummy (C := C))) ∈ source
    simpa using admitted
  · -- Pair the admitted resource with the canonical dummy resource.
    intro admitted
    refine ⟨CryptographicAlgebra.parallel resource
        (CryptographicAlgebra.dummy (C := C)),
      ⟨resource, admitted,
        CryptographicAlgebra.dummy (C := C),
        Set.mem_singleton _, rfl⟩, ?_⟩
    exact CryptographicAlgebra.parallel_dummy_right resource

/-- Exact construction under contravariant converter attachment.

Maurer--Renner 2016, Definition 1 (printed p. 11):
“R —π→ S :⇐⇒ πR ⊆ S.” -/
abbrev Constructs {A B : C} (converter : A ⟶ B)
    (source : Specification (Phi B)) (target : Specification (Phi A)) : Prop :=
  ConstructiveCryptography.Specification.Constructs (attach converter) source target

omit [MonoidalCategory C] in
/-- Exact construction holds exactly when every admitted resource is carried
into the target specification. -/
theorem constructs_iff {A B : C} {converter : A ⟶ B}
    {source : Specification (Phi B)} {target : Specification (Phi A)} :
    Constructs converter source target ↔
      ∀ resource ∈ source,
        attach converter resource ∈ target :=
  Iff.rfl

omit [MonoidalCategory C] in
/-- Exact construction is contravariant in its source specification and
covariant in its target specification.

Maurer--Renner 2016, Section 2.3 (printed p. 5):
“`R —γ→ S =⇒ R′ —γ→ S′` if `R′ ⊆ R` and `S ⊆ S′`.” -/
theorem Constructs.mono {A B : C} {converter : A ⟶ B}
    {source source' : Specification (Phi B)}
    {target target' : Specification (Phi A)}
    (construction : Constructs converter source target)
    (sourceIncluded : source' ⊆ source)
    (targetIncluded : target ⊆ target') :
    Constructs converter source' target' :=
  Set.MapsTo.mono construction sourceIncluded targetIncluded

omit [MonoidalCategory C] in
/-- Singleton exact construction is equality after converter attachment.

Jost--Maurer 2020, Definition 1 (printed p. 9): “In slight abuse of notation,
we write `R —π→ S` in lieu of `{R} —π→ {S}`.” -/
theorem constructs_singleton_iff {A B : C} {converter : A ⟶ B}
    {source : Phi B} {target : Phi A} :
    Constructs converter
        ({source} : Specification (Phi B)) ({target} : Specification (Phi A)) ↔
      attach converter source = target := by
  -- Reduce singleton construction to singleton target membership.
  rw [constructs_iff]
  simp only [Set.mem_singleton_iff, forall_eq]

omit [MonoidalCategory C] in
/-- Equal converters between the same interfaces have equal attachment on every resource. -/
theorem attach_eq_of_converter_eq {A B : C} {left right : A ⟶ B}
    (equal : left = right) (resource : Phi B) :
    attach left resource = attach right resource := by
  -- Substitute the converter equality in the functor map.
  subst right
  rfl

omit [MonoidalCategory C] in
/-- Exact construction is invariant under equality of converters between the same interfaces. -/
theorem constructs_iff_of_converter_eq {A B : C} {left right : A ⟶ B}
    (equal : left = right) {source : Specification (Phi B)}
    {target : Specification (Phi A)} :
    Constructs left source target ↔
      Constructs right source target := by
  -- Substitute the converter equality in the construction relation.
  subst right
  rfl

omit [MonoidalCategory C] in
@[simp]
theorem constructs_identity {A : C} (source : Specification (Phi A)) :
    Constructs (𝟙 A) source source := by
  intro resource admitted
  simpa [attach_identity] using admitted

omit [MonoidalCategory C] in
/-- Exact constructions compose serially.

Maurer--Renner 2016, Lemma 1 (printed p. 11): “This construction notion is
composable.” -/
theorem Constructs.serial {A B D : C}
    {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification (Phi D)} {middle : Specification (Phi B)}
    {target : Specification (Phi A)}
    (inner : Constructs second source middle)
    (outer : Constructs first middle target) :
    Constructs (first ≫ second) source target := by
  intro resource admitted
  rw [attach_serial]
  exact outer (inner admitted)

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
    {source : Specification (Phi D)} {middle : Specification (Phi B)}
    {target : Specification (Phi A)}
    (inner : Constructs second source
      (map innerSimulator middle))
    (outer : Constructs first middle
      (map outerSimulator target))
    (commutes : first ≫ innerSimulator = transportedSimulator ≫ first) :
    Constructs (first ≫ second) source
      (map (transportedSimulator ≫ outerSimulator) target) := by
  rw [constructs_iff] at inner outer ⊢
  intro resource admitted
  -- The inner construction selects an admitted intermediate resource.
  obtain ⟨middleResource, middleAdmitted, innerEquation⟩ :=
    inner resource admitted
  -- The outer construction selects an admitted target resource.
  obtain ⟨targetResource, targetAdmitted, outerEquation⟩ :=
    outer middleResource middleAdmitted
  change attach innerSimulator middleResource =
    attach second resource at innerEquation
  change attach outerSimulator targetResource =
    attach first middleResource at outerEquation
  -- The composite simulator applied to that target is the required image.
  refine ⟨targetResource, targetAdmitted, ?_⟩
  -- Serial attachment and the crossing equality give the paper's equation.
  calc
    attach (transportedSimulator ≫ outerSimulator)
        targetResource =
        attach transportedSimulator
          (attach outerSimulator targetResource) :=
      attach_serial transportedSimulator outerSimulator targetResource
    _ = attach transportedSimulator
          (attach first middleResource) := by
      rw [outerEquation]
    _ = attach (transportedSimulator ≫ first)
          middleResource :=
      (attach_serial transportedSimulator first middleResource).symm
    _ = attach (first ≫ innerSimulator)
          middleResource := by
      rw [commutes]
    _ = attach first
          (attach innerSimulator middleResource) :=
      attach_serial first innerSimulator middleResource
    _ = attach first
          (attach second resource) := by
      rw [innerEquation]
    _ = attach (first ≫ second) resource :=
      (attach_serial first second resource).symm

/-- Exact constructions compose in ordered parallel.

Jost, Theorem 2.2.5(2) (printed p. 19):
“R —π→ S implies [R,T] —π→ [S,T].” Applying this locality result in both
components gives the typed equation below. -/
theorem Constructs.parallel [CryptographicAlgebra C Phi]
    {A A' B B' : C}
    {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : Specification (Phi A')} {leftTarget : Specification (Phi A)}
    {rightSource : Specification (Phi B')} {rightTarget : Specification (Phi B)}
    (leftConstruction : Constructs leftConverter
      leftSource leftTarget)
    (rightConstruction : Constructs rightConverter
      rightSource rightTarget) :
    Constructs (leftConverter ⊗ₘ rightConverter)
      (parallel leftSource rightSource)
      (parallel leftTarget rightTarget) := by
  -- The generic parallel theorem needs only the attachment locality equation.
  exact ConstructiveCryptography.Specification.Constructs.parallel
    leftConstruction rightConstruction
    (CryptographicAlgebra.parallel) (CryptographicAlgebra.parallel)
    (attach (leftConverter ⊗ₘ rightConverter))
    (attach_parallel leftConverter rightConverter)

/-- Left context-insensitivity: an exact construction remains valid beside an
unchanged right-hand resource specification. -/
theorem Constructs.left_context [CryptographicAlgebra C Phi]
    {A A' B : C} {converter : A ⟶ A'}
    {source : Specification (Phi A')} {target : Specification (Phi A)}
    (construction : Constructs converter source target)
    (context : Specification (Phi B)) :
    Constructs (converter ⊗ₘ 𝟙 B)
      (Specification.parallel source context)
      (Specification.parallel target context) := by
  -- Pair the construction with identity construction of the right context.
  exact construction.parallel (constructs_identity context)

/-- Right context-insensitivity: an exact construction remains valid beside
an unchanged left-hand resource specification. -/
theorem Constructs.right_context [CryptographicAlgebra C Phi]
    {A B B' : C} {converter : B ⟶ B'}
    {source : Specification (Phi B')} {target : Specification (Phi B)}
    (context : Specification (Phi A))
    (construction : Constructs converter source target) :
    Constructs (𝟙 A ⊗ₘ converter)
      (Specification.parallel context source)
      (Specification.parallel context target) := by
  -- Pair identity construction of the left context with the construction.
  exact (constructs_identity context).parallel construction

end Specification

end CryptographicAlgebra

end ConstructiveCryptography
