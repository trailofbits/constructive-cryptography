import ConstructiveCryptography.CryptographicAlgebra.Relaxation
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import ConstructiveCryptography.Specification.Relaxation.Epsilon

set_option autoImplicit false

/-!
# Error relaxation

The `ε`-relaxation of a specification on an interface is the set of resources within `ε`
of it (MR16, §2.3, printed p. 5: `R^ε = {R′ | ∃R ∈ R : R′ ≈ε R}`). Successive relaxations
add their errors; the relaxation is compatible with attachment and with parallel
composition, and construction into it is approximate construction.

## Main definitions

* `CryptographicAlgebra.Specification.epsilonRelaxation`

## Main results

* `CryptographicAlgebra.Specification.epsilonRelaxation_compatible`,
  `CryptographicAlgebra.Specification.epsilonRelaxation_parallelCompatible`
* `CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff`: construction into
  the relaxation is approximate construction
* `CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation`: errors add
-/

namespace ConstructiveCryptography.CryptographicAlgebra.Specification

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi]
variable [CompatiblePseudoMetric C Phi]

/-- The closed scalar-error relaxation of a specification in one resource
fibre.

Maurer--Renner 2016, Section 2.3 (printed p. 5), defines
`R^ε = {R' | ∃ R ∈ R : R' ≈ε R}`. -/
noncomputable def epsilonRelaxation {A : C} (error : ENNReal)
    : ConstructiveCryptography.Relaxation (Phi A) :=
  @ConstructiveCryptography.Specification.epsilonRelaxation (Phi A)
    (CompatiblePseudoMetric.fibreMetric A) error

@[simp]
theorem mem_epsilonRelaxation_iff {A : C} {error : ENNReal}
    {source : Specification (Phi A)} {resource : Phi A} :
    resource ∈ epsilonRelaxation error source ↔
      ∃ center ∈ source,
        distance resource center ≤ error :=
  ConstructiveCryptography.Relaxation.mem_ofPointwise_iff

/-- Every specification is contained in each of its scalar-error
relaxations. -/
theorem subset_epsilonRelaxation {A : C} (error : ENNReal)
    (source : Specification (Phi A)) :
    source ⊆ epsilonRelaxation error source := by
  -- Extensivity is part of the relaxation object.
  exact (epsilonRelaxation error).subset_apply source

/-- Scalar-error relaxation is monotone in the underlying specification. -/
theorem epsilonRelaxation_mono {A : C} {error : ENNReal}
    {source target : Specification (Phi A)} (included : source ⊆ target) :
    epsilonRelaxation error source ⊆
      epsilonRelaxation error target := by
  -- Monotonicity is part of the relaxation object.
  exact (epsilonRelaxation error).mono included

/-- Successive scalar-error relaxations add their error bounds.

Jost--Maurer 2020, Theorem 2 (printed p. 11): “the errors just add up.” -/
theorem epsilonRelaxation_epsilonRelaxation_subset {A : C}
    (firstError secondError : ENNReal) (source : Specification (Phi A)) :
    epsilonRelaxation secondError
        (epsilonRelaxation firstError source) ⊆
      epsilonRelaxation (firstError + secondError) source := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  -- Apply the triangle-inequality theorem on this carrier.
  exact ConstructiveCryptography.Specification.epsilonRelaxation_epsilonRelaxation_subset
    firstError secondError source

/-- Converter attachment carries a relaxed source into the relaxation of its
direct image.

Jost--Maurer 2020, Theorem 3 (printed p. 11): “The ε-relaxation is compatible
with protocol application.”  The scalar bound is unchanged here because every
converter map is non-expanding. -/
theorem map_epsilonRelaxation_subset {A B : C} (converter : A ⟶ B)
    (error : ENNReal) (source : Specification (Phi B)) :
    map converter
        (epsilonRelaxation error source) ⊆
      epsilonRelaxation error
        (map converter source) := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) B
  -- Attachment is a non-expanding map between the two selected carriers.
  exact ConstructiveCryptography.Specification.image_epsilonRelaxation_subset
    (LipschitzWith.of_edist_le (distance_attach_le converter)) error source

/-- Relaxing the left component before ordered parallel is contained in
relaxing the resulting parallel specification.

Jost--Maurer 2020, Theorem 3 (printed p. 11): the error relaxation “is
compatible with parallel composition.” -/
theorem parallel_epsilonRelaxation_left_subset {A B : C}
    (error : ENNReal) (source : Specification (Phi A))
    (context : Specification (Phi B)) :
    parallel (epsilonRelaxation error source)
        context ⊆
      epsilonRelaxation error
        (parallel source context) := by
  rintro resource ⟨left, leftRelaxed, right, contextAdmitted, rfl⟩
  rw [mem_epsilonRelaxation_iff] at leftRelaxed ⊢
  rcases leftRelaxed with ⟨center, admitted, close⟩
  -- Keep the right component and replace only the relaxed left component.
  refine ⟨CryptographicAlgebra.parallel center right,
    ⟨center, admitted, right, contextAdmitted, rfl⟩, ?_⟩
  -- Joint non-expansion reduces to the left distance because the context agrees.
  exact (distance_parallel_le left center right right).trans
    (by simpa using close)

/-- Relaxing the right component before ordered parallel is contained in
relaxing the resulting parallel specification. -/
theorem parallel_epsilonRelaxation_right_subset {A B : C}
    (error : ENNReal) (context : Specification (Phi A))
    (source : Specification (Phi B)) :
    parallel context
        (epsilonRelaxation error source) ⊆
      epsilonRelaxation error
        (parallel context source) := by
  rintro resource ⟨left, contextAdmitted, right, rightRelaxed, rfl⟩
  rw [mem_epsilonRelaxation_iff] at rightRelaxed ⊢
  rcases rightRelaxed with ⟨center, admitted, close⟩
  -- Keep the left component and replace only the relaxed right component.
  refine ⟨CryptographicAlgebra.parallel left center,
    ⟨left, contextAdmitted, center, admitted, rfl⟩, ?_⟩
  -- Joint non-expansion reduces to the right distance because the context agrees.
  exact (distance_parallel_le left left right center).trans
    (by simpa using close)

/-- The scalar-error relaxation family is compatible with converter
attachment. -/
theorem epsilonRelaxation_compatible (error : ENNReal) :
    Relaxation.Compatible (Phi := Phi)
      (fun A => epsilonRelaxation (A := A) error) := by
  intro A B converter source
  -- Converter compatibility is precisely attachment non-expansion.
  exact map_epsilonRelaxation_subset converter error source

/-- The scalar-error relaxation family is compatible with ordered parallel
composition. -/
theorem epsilonRelaxation_parallelCompatible (error : ENNReal) :
    Relaxation.ParallelCompatible (Phi := Phi)
      (fun A => epsilonRelaxation (A := A) error) := by
  intro A B left right
  -- The two inclusions are the left and right context non-expansion laws.
  exact ⟨parallel_epsilonRelaxation_left_subset error left right,
    parallel_epsilonRelaxation_right_subset error left right⟩

/-- Exact construction into a scalar-error relaxation is equivalent to
approximate construction in the selected fibre distance. -/
theorem constructs_epsilonRelaxation_iff {A B : C}
    {converter : A ⟶ B} {source : Specification (Phi B)}
    {target : Specification (Phi A)} {error : ENNReal} :
    Constructs converter source
        (epsilonRelaxation error target) ↔
      ConstructsWithin converter source target error := by
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
    {converter : A ⟶ B} {source : Specification (Phi B)}
    {target : Specification (Phi A)}
    (construction : Constructs converter source target)
    (error : ENNReal) :
    Constructs converter
      (epsilonRelaxation error source)
      (epsilonRelaxation error target) := by
  -- Apply converter compatibility of the scalar-error relaxation family.
  exact (Relaxation.compatible_iff
    (fun A =>
      ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation
        (A := A) error)).mp
      (epsilonRelaxation_compatible error)
      converter source target construction

/-- Singleton exact construction into a scalar-error relaxation is exactly a
distance bound between the attached real resource and the ideal resource. -/
theorem constructs_singleton_epsilonRelaxation_iff {A B : C}
    {converter : A ⟶ B} {real : Phi B} {ideal : Phi A}
    {error : ENNReal} :
    Constructs converter ({real} : Specification (Phi B))
        (epsilonRelaxation error
          ({ideal} : Specification (Phi A))) ↔
      distance (attach converter real) ideal ≤
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
    {source : Specification (Phi D)} {middle : Specification (Phi B)}
    {target : Specification (Phi A)} {innerError outerError : ENNReal}
    (inner : Constructs second source
      (Specification.epsilonRelaxation innerError middle))
    (outer : Constructs first middle
      (Specification.epsilonRelaxation outerError target)) :
    Constructs (first ≫ second) source
      (Specification.epsilonRelaxation
        (innerError + outerError) target) := by
  -- Read both relaxed-target constructions as approximate constructions.
  rw [constructs_epsilonRelaxation_iff] at inner outer ⊢
  -- Serial approximate construction adds the inner and outer errors.
  exact inner.serial outer

end ConstructiveCryptography.CryptographicAlgebra.Specification
