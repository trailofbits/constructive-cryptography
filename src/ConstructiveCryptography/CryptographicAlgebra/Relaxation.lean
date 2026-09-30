import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.Specification.Relaxation.Basic

set_option autoImplicit false

/-!
# Relaxations of specifications in a cryptographic algebra

A relaxation is chosen on each interface. It is compatible with attachment when attaching
a converter to a relaxed specification stays within the relaxation of the attached one,
and compatible with parallel composition in either position. Compatible relaxations are
preserved by construction, serially and in context.

## Main definitions

* `CryptographicAlgebra.Specification.Relaxation.Compatible`,
  `CryptographicAlgebra.Specification.Relaxation.ParallelCompatible`

## Main results

* `CryptographicAlgebra.Specification.Relaxation.compatible_iff`: compatibility is
  preservation of construction
* `CryptographicAlgebra.Specification.Constructs.relax_serial`,
  `CryptographicAlgebra.Specification.Constructs.relax_left_context`,
  `CryptographicAlgebra.Specification.Constructs.relax_right_context`
-/

namespace ConstructiveCryptography.CryptographicAlgebra.Specification

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi]
variable [CryptographicAlgebra C Phi]

namespace Relaxation

/-- Compatibility of a fibrewise relaxation with every converter map.

Jost--Maurer 2020, Theorem 3 (printed p. 11): “The ε-relaxation is compatible
with protocol application.”  This predicate records the typed inclusion used
by that theorem for a supplied relaxation in every fibre. -/
def Compatible
    (relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)) : Prop :=
  ∀ {A B : C} (converter : A ⟶ B) (source : Specification (Phi B)),
    map converter (relaxation B source) ⊆
      relaxation A (map converter source)

/-- Compatibility of a fibrewise relaxation with ordered parallel in both
component positions.

Jost--Maurer 2020, Theorem 3 (printed p. 11): the ε-relaxation “is compatible
with parallel composition.” -/
def ParallelCompatible
    (relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)) : Prop :=
  ∀ (A B : C) (left : Specification (Phi A)) (right : Specification (Phi B)),
    parallel (relaxation A left) right ⊆
      relaxation (A ⊗ B) (parallel left right) ∧
    parallel left (relaxation B right) ⊆
      relaxation (A ⊗ B) (parallel left right)

omit [MonoidalCategory C] [CryptographicAlgebra C Phi] in
/-- Pointwise composition of compatible relaxation families is compatible. -/
theorem Compatible.comp
    {outer inner : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)}
    (outerCompatible : Compatible outer)
    (innerCompatible : Compatible inner) :
    Compatible (fun A => (outer A).comp (inner A)) := by
  intro A B converter source
  simp only [ConstructiveCryptography.Relaxation.comp_apply]
  -- Pull the outer map through converter attachment.
  exact (outerCompatible converter (inner B source)).trans
    ((outer A).mono (innerCompatible converter source))

omit [MonoidalCategory C] [CryptographicAlgebra C Phi] in
/-- Converter compatibility is equivalent to preservation of exact
construction under the relaxation family. -/
theorem compatible_iff
    (relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)) :
    Compatible relaxation ↔
      ∀ {A B : C} (converter : A ⟶ B)
        (source : Specification (Phi B)) (target : Specification (Phi A)),
        Constructs converter source target →
          Constructs converter
            (relaxation B source) (relaxation A target) := by
  constructor
  · intro compatible A B converter source target construction
    rw [constructs_iff] at construction ⊢
    intro resource admitted
    -- Pull the relaxed source through attachment, then weaken its centers.
    have relaxedImage := compatible converter source
      ⟨resource, admitted, rfl⟩
    have imageIncluded : map converter source ⊆ target := by
      rintro _ ⟨original, sourceAdmitted, rfl⟩
      exact construction original sourceAdmitted
    exact (relaxation A).mono imageIncluded relaxedImage
  · intro preserves A B converter source
    -- Apply preservation to the direct image of the unrelaxed source.
    have preserved := preserves converter source
      (map converter source)
      (constructs_iff.mpr fun resource admitted =>
        ⟨resource, admitted, rfl⟩)
    rintro _ ⟨resource, admitted, rfl⟩
    exact constructs_iff.mp preserved resource admitted

end Relaxation

omit [MonoidalCategory C] [CryptographicAlgebra C Phi] in
/-- A construction respects a supplied change from the source relaxation to
the target relaxation. Jost, Theorem 2.2.11 (printed p. 22), changes `ε` to
`επ` under protocol attachment. The compatibility premise records exactly
that inclusion; the two relaxations need not be the same family. -/
theorem Constructs.relax {A B : C} {converter : A ⟶ B}
    {source : Specification (Phi B)} {target : Specification (Phi A)}
    (construction : Constructs converter source target)
    (sourceRelaxation : ConstructiveCryptography.Relaxation (Phi B))
    (targetRelaxation : ConstructiveCryptography.Relaxation (Phi A))
    (compatible : ∀ specification,
      map converter (sourceRelaxation specification) ⊆
        targetRelaxation (map converter specification)) :
    Constructs converter
      (sourceRelaxation source) (targetRelaxation target) :=
  ConstructiveCryptography.Specification.Constructs.map construction
    sourceRelaxation targetRelaxation targetRelaxation.mono compatible

omit [MonoidalCategory C] [CryptographicAlgebra C Phi] in
/-- Pull a compatible relaxation through the outer leg of a serial
construction. -/
theorem Constructs.relax_serial
    {relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)}
    (compatible : Relaxation.Compatible relaxation)
    {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification (Phi D)} {middle : Specification (Phi B)}
    {target : Specification (Phi A)}
    (inner : Constructs second source (relaxation B middle))
    (outer : Constructs first middle target) :
    Constructs (first ≫ second) source
      (relaxation A target) := by
  rw [constructs_iff] at inner outer ⊢
  intro resource admitted
  -- The inner construction reaches the relaxed middle specification.
  have middleRelaxed := inner resource admitted
  -- Serial attachment exposes the outer converter on that relaxed resource.
  rw [attach_serial]
  -- Compatibility pulls the relaxation through the outer converter.
  have relaxedImage := compatible first middle
    ⟨attach second resource, middleRelaxed, rfl⟩
  have imageIncluded : map first middle ⊆ target := by
    rintro _ ⟨original, middleAdmitted, rfl⟩
    exact outer original middleAdmitted
  exact (relaxation A).mono imageIncluded relaxedImage

/-- Put an exact construction into an unchanged right context and pull a
parallel-compatible relaxation around the result. -/
theorem Constructs.relax_left_context
    {relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)}
    (parallelCompatible :
      Relaxation.ParallelCompatible relaxation)
    {A A' B : C} {converter : A ⟶ A'}
    {source : Specification (Phi A')} {target : Specification (Phi A)}
    (construction : Constructs converter source
      (relaxation A target))
    (context : Specification (Phi B)) :
    Constructs (converter ⊗ₘ 𝟙 B)
      (CryptographicAlgebra.Specification.parallel source context)
      (relaxation (A ⊗ B)
        (CryptographicAlgebra.Specification.parallel target context)) := by
  -- Ordinary context-insensitivity reaches parallel with the relaxed target.
  rw [constructs_iff] at construction ⊢
  rintro resource ⟨left, admitted, right, contextAdmitted, rfl⟩
  rw [attach_parallel]
  simp only [attach_identity]
  -- Parallel compatibility moves the relaxation outside that context.
  exact (parallelCompatible A B target context).1
    ⟨attach converter left, construction left admitted,
      right, contextAdmitted, rfl⟩

/-- Right-context counterpart of `Constructs.relax_left_context`. -/
theorem Constructs.relax_right_context
    {relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)}
    (parallelCompatible :
      Relaxation.ParallelCompatible relaxation)
    {A B B' : C} {converter : B ⟶ B'}
    {source : Specification (Phi B')} {target : Specification (Phi B)}
    (context : Specification (Phi A))
    (construction : Constructs converter source
      (relaxation B target)) :
    Constructs (𝟙 A ⊗ₘ converter)
      (CryptographicAlgebra.Specification.parallel context source)
      (relaxation (A ⊗ B)
        (CryptographicAlgebra.Specification.parallel context target)) := by
  -- Ordinary context-insensitivity reaches parallel with the relaxed target.
  rw [constructs_iff] at construction ⊢
  rintro resource ⟨left, contextAdmitted, right, admitted, rfl⟩
  rw [attach_parallel]
  simp only [attach_identity]
  -- Parallel compatibility moves the relaxation outside that context.
  exact (parallelCompatible A B context target).2
    ⟨left, contextAdmitted,
      attach converter right, construction right admitted, rfl⟩

end ConstructiveCryptography.CryptographicAlgebra.Specification
