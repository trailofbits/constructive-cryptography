/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ConstructiveCryptography.Categorical.ResourceAlgebra.Relaxation

set_option autoImplicit false

/-!
# Scalar error relaxation in one resource fibre

The scalar error relaxation is defined separately in every resource fibre.
Its construction, attachment, and ordered-parallel laws follow from the fibre
pseudo-metrics and the two non-expansion fields of `ResourceAlgebra`; it adds
no action or parallel structure.
-/

namespace ConstructiveCryptography.Categorical.ResourceAlgebra.Specification

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-- The closed scalar-error relaxation of a specification in one resource
fibre.

Maurer--Renner 2016, Section 2.3 (printed p. 5), defines
`R^ε = {R' | ∃ R ∈ R : R' ≈ε R}`. -/
noncomputable def epsilonRelaxation {A : C} (error : ENNReal)
    : ConstructiveCryptography.Relaxation (Resource Phi A) :=
  ConstructiveCryptography.Relaxation.ofPointwise
    (fun center =>
      {resource | distance (Phi := Phi) resource center ≤ error})
    (fun resource =>
      (le_of_eq (distance_self resource)).trans bot_le)

@[simp]
theorem mem_epsilonRelaxation_iff {A : C} {error : ENNReal}
    {source : Specification Phi A} {resource : Resource Phi A} :
    resource ∈ epsilonRelaxation (Phi := Phi) error source ↔
      ∃ center ∈ source,
        distance (Phi := Phi) resource center ≤ error :=
  ConstructiveCryptography.Relaxation.mem_ofPointwise_iff

/-- Every specification is contained in each of its scalar-error
relaxations. -/
theorem subset_epsilonRelaxation {A : C} (error : ENNReal)
    (source : Specification Phi A) :
    source ⊆ epsilonRelaxation (Phi := Phi) error source := by
  -- Extensivity is part of the relaxation object.
  exact (epsilonRelaxation (Phi := Phi) error).le_toFun source

/-- Scalar-error relaxation is monotone in the underlying specification. -/
theorem epsilonRelaxation_mono {A : C} {error : ENNReal}
    {source target : Specification Phi A} (included : source ⊆ target) :
    epsilonRelaxation (Phi := Phi) error source ⊆
      epsilonRelaxation (Phi := Phi) error target := by
  -- Monotonicity is part of the relaxation object.
  exact (epsilonRelaxation (Phi := Phi) error).mono included

/-- Successive scalar-error relaxations add their error bounds.

Jost--Maurer 2020, Theorem 2 (printed p. 11): “the errors just add up.” -/
theorem epsilonRelaxation_epsilonRelaxation_subset {A : C}
    (firstError secondError : ENNReal) (source : Specification Phi A) :
    epsilonRelaxation (Phi := Phi) secondError
        (epsilonRelaxation (Phi := Phi) firstError source) ⊆
      epsilonRelaxation (Phi := Phi) (firstError + secondError) source := by
  intro resource resourceRelaxed
  rw [mem_epsilonRelaxation_iff] at resourceRelaxed ⊢
  rcases resourceRelaxed with ⟨middle, middleRelaxed, resourceClose⟩
  rw [mem_epsilonRelaxation_iff] at middleRelaxed
  rcases middleRelaxed with ⟨center, admitted, middleClose⟩
  -- The triangle inequality joins the two witnesses.
  refine ⟨center, admitted, (distance_triangle resource middle center).trans ?_⟩
  -- Add the two supplied bounds in the paper's order.
  exact (add_le_add resourceClose middleClose).trans_eq
    (add_comm secondError firstError)

/-- Converter attachment carries a relaxed source into the relaxation of its
direct image.

Jost--Maurer 2020, Theorem 3 (printed p. 11): “The ε-relaxation is compatible
with protocol application.”  The scalar bound is unchanged here because every
converter map is non-expanding. -/
theorem map_epsilonRelaxation_subset {A B : C} (converter : A ⟶ B)
    (error : ENNReal) (source : Specification Phi B) :
    map (Phi := Phi) converter
        (epsilonRelaxation (Phi := Phi) error source) ⊆
      epsilonRelaxation (Phi := Phi) error
        (map (Phi := Phi) converter source) := by
  rintro resource ⟨original, originalRelaxed, rfl⟩
  rw [mem_epsilonRelaxation_iff] at originalRelaxed ⊢
  rcases originalRelaxed with ⟨center, admitted, close⟩
  -- Attach the same converter to the center.
  refine ⟨attach (Phi := Phi) converter center,
    ⟨center, admitted, rfl⟩, ?_⟩
  -- Attachment non-expansion preserves the scalar bound.
  exact (distance_attach_le converter original center).trans close

/-- Relaxing the left component before ordered parallel is contained in
relaxing the resulting parallel specification.

Jost--Maurer 2020, Theorem 3 (printed p. 11): the error relaxation “is
compatible with parallel composition.” -/
theorem parallel_epsilonRelaxation_left_subset {A B : C}
    (error : ENNReal) (source : Specification Phi A)
    (context : Specification Phi B) :
    parallel (Phi := Phi) (epsilonRelaxation (Phi := Phi) error source)
        context ⊆
      epsilonRelaxation (Phi := Phi) error
        (parallel (Phi := Phi) source context) := by
  rintro resource ⟨left, leftRelaxed, right, contextAdmitted, rfl⟩
  rw [mem_epsilonRelaxation_iff] at leftRelaxed ⊢
  rcases leftRelaxed with ⟨center, admitted, close⟩
  -- Keep the right component and replace only the relaxed left component.
  refine ⟨ResourceAlgebra.parallel (Phi := Phi) center right,
    ⟨center, admitted, right, contextAdmitted, rfl⟩, ?_⟩
  -- Joint non-expansion reduces to the left distance because the context agrees.
  exact (distance_parallel_le left center right right).trans
    (by simpa using close)

/-- Relaxing the right component before ordered parallel is contained in
relaxing the resulting parallel specification. -/
theorem parallel_epsilonRelaxation_right_subset {A B : C}
    (error : ENNReal) (context : Specification Phi A)
    (source : Specification Phi B) :
    parallel (Phi := Phi) context
        (epsilonRelaxation (Phi := Phi) error source) ⊆
      epsilonRelaxation (Phi := Phi) error
        (parallel (Phi := Phi) context source) := by
  rintro resource ⟨left, contextAdmitted, right, rightRelaxed, rfl⟩
  rw [mem_epsilonRelaxation_iff] at rightRelaxed ⊢
  rcases rightRelaxed with ⟨center, admitted, close⟩
  -- Keep the left component and replace only the relaxed right component.
  refine ⟨ResourceAlgebra.parallel (Phi := Phi) left center,
    ⟨left, contextAdmitted, center, admitted, rfl⟩, ?_⟩
  -- Joint non-expansion reduces to the right distance because the context agrees.
  exact (distance_parallel_le left left right center).trans
    (by simpa using close)

/-- The scalar-error relaxation family is compatible with converter
attachment. -/
theorem epsilonRelaxation_compatible (error : ENNReal) :
    Relaxation.Compatible (Phi := Phi)
      (fun A => epsilonRelaxation (Phi := Phi) (A := A) error) := by
  intro A B converter source
  -- Converter compatibility is precisely attachment non-expansion.
  exact map_epsilonRelaxation_subset converter error source

/-- The scalar-error relaxation family is compatible with ordered parallel
composition. -/
theorem epsilonRelaxation_parallelCompatible (error : ENNReal) :
    Relaxation.ParallelCompatible (Phi := Phi)
      (fun A => epsilonRelaxation (Phi := Phi) (A := A) error) := by
  intro A B left right
  -- The two inclusions are the left and right context non-expansion laws.
  exact ⟨parallel_epsilonRelaxation_left_subset error left right,
    parallel_epsilonRelaxation_right_subset error left right⟩

/-- Exact construction into a scalar-error relaxation is equivalent to
approximate construction in the selected fibre distance. -/
theorem constructs_epsilonRelaxation_iff {A B : C}
    {converter : A ⟶ B} {source : Specification Phi B}
    {target : Specification Phi A} {error : ENNReal} :
    Constructs (Phi := Phi) converter source
        (epsilonRelaxation (Phi := Phi) error target) ↔
      ConstructsWithin (Phi := Phi) converter source target error := by
  rw [constructs_iff]
  constructor
  · intro construction resource admitted
    -- Read target membership as a center and distance witness.
    exact mem_epsilonRelaxation_iff.mp (construction resource admitted)
  · intro construction resource admitted
    -- Package the approximate witness as relaxed-target membership.
    exact mem_epsilonRelaxation_iff.mpr (construction resource admitted)

/-- Exact construction remains valid after relaxing both endpoint
specifications by the same scalar error.

Maurer--Renner 2016, Lemma 2 (printed p. 12): “If the metric on Φ is
non-expanding, then, for any ε > 0, `R —π→ S ⟹ R^ε —π→ S^ε`.”  The proof
also applies at zero. -/
theorem Constructs.epsilonRelaxation {A B : C}
    {converter : A ⟶ B} {source : Specification Phi B}
    {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source target)
    (error : ENNReal) :
    Constructs (Phi := Phi) converter
      (epsilonRelaxation (Phi := Phi) error source)
      (epsilonRelaxation (Phi := Phi) error target) := by
  -- Apply converter compatibility of the scalar-error relaxation family.
  exact (Relaxation.compatible_iff
    (Phi := Phi)
    (fun A =>
      ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.epsilonRelaxation
        (Phi := Phi) (A := A) error)).mp
      (epsilonRelaxation_compatible (Phi := Phi) error)
      converter source target construction

/-- Singleton exact construction into a scalar-error relaxation is exactly a
distance bound between the attached real resource and the ideal resource. -/
theorem constructs_singleton_epsilonRelaxation_iff {A B : C}
    {converter : A ⟶ B} {real : Resource Phi B} {ideal : Resource Phi A}
    {error : ENNReal} :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
        (epsilonRelaxation (Phi := Phi) error
          ({ideal} : Specification Phi A)) ↔
      distance (Phi := Phi) (attach (Phi := Phi) converter real) ideal ≤
        error := by
  -- Replace relaxation membership by approximate construction.
  rw [constructs_epsilonRelaxation_iff]
  -- The singleton approximate-construction law is the desired distance bound.
  exact constructsWithin_singleton_iff

/-- Scalar-error constructions compose serially, and their errors add.

Maurer--Renner 2016, Lemma 1 (printed p. 11): “This construction notion is
composable.”  Jost--Maurer 2020, Corollary 1(1) (printed p. 11) states the
serial construction with the two relaxation budgets added: “The composition
theorem with ϵ-relaxations then follows directly from these compatibility
results.”  Lean specializes its transformed budgets to constant scalar bounds
under non-expansion. -/
theorem Constructs.serial_epsilonRelaxation {A B D : C}
    {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (Specification.epsilonRelaxation (Phi := Phi) innerError middle))
    (outer : Constructs (Phi := Phi) first middle
      (Specification.epsilonRelaxation (Phi := Phi) outerError target)) :
    Constructs (Phi := Phi) (first ≫ second) source
      (Specification.epsilonRelaxation (Phi := Phi)
        (innerError + outerError) target) := by
  -- Read both relaxed-target constructions as approximate constructions.
  rw [constructs_epsilonRelaxation_iff] at inner outer ⊢
  -- Serial approximate construction adds the inner and outer errors.
  exact inner.serial outer

end ConstructiveCryptography.Categorical.ResourceAlgebra.Specification
