import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.Specification.Relaxation.Basic

set_option autoImplicit false

/-!
# Relaxations of specifications in a cryptographic algebra

A relaxation is chosen on each interface. It is compatible with attachment when attaching
a converter to a relaxed specification stays within the relaxation of the attached one,
and compatible with parallel composition in either position. Compatible relaxations are
preserved by construction, serially and in context.

Notation is as in `ConstructiveCryptography.CryptographicAlgebra.Basic`; `α : A ⟶ B` has
outside `A`, inside `B`, and `map α` sends specifications on `B` to specifications on `A`.
A relaxation `φ : ConstructiveCryptography.Relaxation (Phi A)` (Jost's `φ`) assigns to each
resource `R` a set `φ.toPointwise R ∋ R` and acts on a specification `S` by union,
`φ S = ⋃_{R ∈ S} φ.toPointwise R ⊇ S`; it is monotone. No metric is assumed in this file.

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

-- Objects `A : C` are interfaces; `α : A ⟶ B` is a converter with outside `A` and inside `B`;
-- `A ⊗ B` places two interfaces side by side.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
-- `Phi A` is the type of resources on `A`; `map α` sends specifications on `B` to `A`.
variable {Phi : C → Type w} [ResourceTheory C Phi]
-- `CryptographicAlgebra C Phi` selects `parallel` on resources and on specifications.
variable [CryptographicAlgebra C Phi]

namespace Relaxation

/-- Compatibility of a fibrewise relaxation with every converter map. For every
converter `converter : A ⟶ B` and specification `source` on `B`,

```text
map converter (relaxation B source) ⊆ relaxation A (map converter source)
```

attaching the converter to a relaxed resource gives a resource of the relaxed image. The same
family is used on both sides, so the relaxation may not grow under attachment; Jost's
`ε ↦ επ` change of relaxation is handled by `Constructs.relax` instead.

Jost--Maurer 2020, Theorem 3 (printed p. 11): “The ε-relaxation is compatible
with protocol application.”  This predicate records the typed inclusion used
by that theorem for a supplied relaxation in every fibre. -/
def Compatible
    -- `relaxation A` is the relaxation chosen on `Phi A` for each interface `A : C`; nothing
    -- relates the choices on different interfaces except this predicate.
    (relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)) : Prop :=
  ∀ {A B : C} (converter : A ⟶ B) (source : Specification (Phi B)),
    map converter (relaxation B source) ⊆
      relaxation A (map converter source)

/-- Compatibility of a fibrewise relaxation with ordered parallel in both
component positions. For all interfaces `A, B` and specifications `left` on `A`, `right`
on `B`, writing `∥` for specification `parallel`,

```text
relaxation A left ∥ right  ⊆  relaxation (A ⊗ B) (left ∥ right)
left ∥ relaxation B right  ⊆  relaxation (A ⊗ B) (left ∥ right)
```

relaxing one component, with the other unchanged, stays within the relaxation of the
parallel specification. Relaxing both components at once is not covered.

Jost--Maurer 2020, Theorem 3 (printed p. 11): the ε-relaxation “is compatible
with parallel composition.” -/
def ParallelCompatible
    -- `relaxation A` is the relaxation chosen on `Phi A` for each interface `A : C`.
    (relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)) : Prop :=
  ∀ (A B : C) (left : Specification (Phi A)) (right : Specification (Phi B)),
    parallel (relaxation A left) right ⊆
      relaxation (A ⊗ B) (parallel left right) ∧
    parallel left (relaxation B right) ⊆
      relaxation (A ⊗ B) (parallel left right)

omit [MonoidalCategory C] [CryptographicAlgebra C Phi] in
/-- Pointwise composition of compatible relaxation families is compatible. If `outer` and
`inner` are converter-compatible families, so is the family whose relaxation on `A` applies
`inner A` and then `outer A`. For `converter : A ⟶ B`:

```text
map converter (outer B (inner B S)) ⊆ outer A (map converter (inner B S))   outer compatible
                                     ⊆ outer A (inner A (map converter S))   inner, monotone
``` -/
lemma Compatible.comp
    -- `outer A` and `inner A` are two relaxations on `Phi A`; the composite applies `inner A`
    -- first.
    {outer inner : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)}
    -- `outerCompatible` and `innerCompatible`: each family is converter-compatible.
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
construction under the relaxation family: `Compatible relaxation` holds iff, for every
converter `converter : A ⟶ B` and specifications `source` on `B`, `target` on `A`,
`Constructs converter source target` implies
`Constructs converter (relaxation B source) (relaxation A target)`.

The forward direction weakens the relaxed image `relaxation A (map converter source)` to
`relaxation A target` by monotonicity; the backward direction applies preservation to the
trivial construction of `map converter source` from `source`. -/
lemma compatible_iff
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
    -- `construction`: `converter : A ⟶ B` constructs `target` (on `A`) from `source` (on `B`).
    (construction : Constructs converter source target)
    -- `sourceRelaxation` on `Phi B` and `targetRelaxation` on `Phi A` are single relaxations,
    -- not families: Jost's `ε` and `επ`.
    (sourceRelaxation : ConstructiveCryptography.Relaxation (Phi B))
    (targetRelaxation : ConstructiveCryptography.Relaxation (Phi A))
    -- `compatible`, for this `converter` only: attaching it to `sourceRelaxation` of any
    -- `specification` on `B` stays in `targetRelaxation` of the attached specification.
    (compatible : ∀ specification,
      map converter (sourceRelaxation specification) ⊆
        targetRelaxation (map converter specification)) :
    Constructs converter
      (sourceRelaxation source) (targetRelaxation target) :=
  ConstructiveCryptography.Specification.Constructs.map construction
    sourceRelaxation targetRelaxation targetRelaxation.mono compatible

omit [MonoidalCategory C] [CryptographicAlgebra C Phi] in
/-- Pull a compatible relaxation through the outer leg of a serial
construction: `first ≫ second` constructs `relaxation A target` from `source`:

```text
first • (second • R) ∈ map first (relaxation B middle)
                     ⊆ relaxation A (map first middle)   compatible
                     ⊆ relaxation A target               outer, monotonicity
```

The relaxation is applied once; the outer construction must be exact. -/
lemma Constructs.relax_serial
    -- `relaxation A` is the relaxation chosen on `Phi A` for each interface `A : C`.
    {relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)}
    -- `compatible`: `map α (relaxation B S) ⊆ relaxation A (map α S)` for every `α : A ⟶ B`.
    (compatible : Relaxation.Compatible relaxation)
    -- `first : A ⟶ B` is the outer converter and `second : B ⟶ D` the inner one.
    {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    -- `source` lies on the inside `D`, `middle` on `B`, and `target` on the outside `A`.
    {source : Specification (Phi D)} {middle : Specification (Phi B)}
    {target : Specification (Phi A)}
    -- `inner`: `second` constructs only the relaxed `relaxation B middle` from `source`.
    (inner : Constructs second source (relaxation B middle))
    -- `outer`: `first` constructs `target` exactly from `middle`.
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
parallel-compatible relaxation around the result: `converter ⊗ₘ 𝟙 B` constructs
`relaxation (A ⊗ B) (parallel target context)` from `parallel source context`. Only the
first (left-component) inclusion of `parallelCompatible` is used. -/
lemma Constructs.relax_left_context
    -- `relaxation A` is the relaxation chosen on `Phi A` for each interface `A : C`.
    {relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)}
    -- `parallelCompatible`: relaxing one parallel component stays in `relaxation (A ⊗ B)`.
    (parallelCompatible :
      Relaxation.ParallelCompatible relaxation)
    -- `converter` has outside `A` and inside `A'`.
    {A A' B : C} {converter : A ⟶ A'}
    -- `source` lies on the inside `A'` and `target` on the outside `A`.
    {source : Specification (Phi A')} {target : Specification (Phi A)}
    -- `construction`: `converter` constructs `relaxation A target` from `source`.
    (construction : Constructs converter source
      (relaxation A target))
    -- `context` on `B` is the unchanged right-hand specification.
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

/-- Right-context counterpart of `Constructs.relax_left_context`: `𝟙 A ⊗ₘ converter`
constructs `relaxation (A ⊗ B) (parallel context target)` from `parallel context source`,
using the second inclusion of `parallelCompatible`. -/
lemma Constructs.relax_right_context
    -- `relaxation A` is the relaxation chosen on `Phi A` for each interface `A : C`.
    {relaxation : (A : C) →
      ConstructiveCryptography.Relaxation (Phi A)}
    -- `parallelCompatible`: relaxing one parallel component stays in `relaxation (A ⊗ B)`.
    (parallelCompatible :
      Relaxation.ParallelCompatible relaxation)
    -- `converter` has outside `B` and inside `B'`.
    {A B B' : C} {converter : B ⟶ B'}
    -- `source` lies on the inside `B'` and `target` on the outside `B`.
    {source : Specification (Phi B')} {target : Specification (Phi B)}
    -- `context` on `A` is the unchanged left-hand specification.
    (context : Specification (Phi A))
    -- `construction`: `converter` constructs `relaxation B target` from `source`.
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
