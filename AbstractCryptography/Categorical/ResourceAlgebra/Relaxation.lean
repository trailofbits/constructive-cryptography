/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical.ResourceAlgebra
import AbstractCryptography.Specification.Relaxation.Defs

set_option autoImplicit false

/-!
# Relaxations over interface-indexed resource specifications

A relaxation is selected separately in each resource fibre.  Compatibility is
an explicit property of that family with converter attachment or ordered
parallel composition.  These predicates use the operations of
`ResourceAlgebra`; they introduce no action, parallel operation, or instance.

Jost--Maurer 2020 proves the corresponding inclusions for its
distinguisher-indexed error relaxation.  The definitions below retain the same
typed inclusions for an explicit relaxation family; they do not claim that an
arbitrary relaxation satisfies them.
-/

namespace AbstractCryptography.Categorical.ResourceAlgebra.Specification

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

namespace Relaxation

/-- Compatibility of a fibrewise relaxation with every converter map.

Jost--Maurer 2020, Theorem 3 (printed p. 11): “The ε-relaxation is compatible
with protocol application.”  This predicate records the typed inclusion used
by that theorem for a supplied relaxation in every fibre. -/
def Compatible
    (relaxation : (A : C) →
      AbstractCryptography.Relaxation (Resource Phi A)) : Prop :=
  ∀ {A B : C} (converter : A ⟶ B) (source : Specification Phi B),
    map (Phi := Phi) converter (relaxation B source) ⊆
      relaxation A (map (Phi := Phi) converter source)

/-- Compatibility of a fibrewise relaxation with ordered parallel in both
component positions.

Jost--Maurer 2020, Theorem 3 (printed p. 11): the ε-relaxation “is compatible
with parallel composition.” -/
def ParallelCompatible
    (relaxation : (A : C) →
      AbstractCryptography.Relaxation (Resource Phi A)) : Prop :=
  ∀ (A B : C) (left : Specification Phi A) (right : Specification Phi B),
    parallel (Phi := Phi) (relaxation A left) right ⊆
      relaxation (A ⊗ B) (parallel (Phi := Phi) left right) ∧
    parallel (Phi := Phi) left (relaxation B right) ⊆
      relaxation (A ⊗ B) (parallel (Phi := Phi) left right)

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Pointwise composition of compatible relaxation families is compatible. -/
theorem Compatible.comp
    {outer inner : (A : C) →
      AbstractCryptography.Relaxation (Resource Phi A)}
    (outerCompatible : Compatible (Phi := Phi) outer)
    (innerCompatible : Compatible (Phi := Phi) inner) :
    Compatible (Phi := Phi) (fun A => (outer A).comp (inner A)) := by
  intro A B converter source
  -- Pull the outer map through converter attachment.
  exact (outerCompatible converter (inner B source)).trans
    ((outer A).mono (innerCompatible converter source))

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Converter compatibility is equivalent to preservation of exact
construction under the relaxation family. -/
theorem compatible_iff
    (relaxation : (A : C) →
      AbstractCryptography.Relaxation (Resource Phi A)) :
    Compatible (Phi := Phi) relaxation ↔
      ∀ {A B : C} (converter : A ⟶ B)
        (source : Specification Phi B) (target : Specification Phi A),
        Constructs (Phi := Phi) converter source target →
          Constructs (Phi := Phi) converter
            (relaxation B source) (relaxation A target) := by
  constructor
  · intro compatible A B converter source target construction
    rw [constructs_iff] at construction ⊢
    intro resource admitted
    -- Pull the relaxed source through attachment, then weaken its centers.
    have relaxedImage := compatible converter source
      ⟨resource, admitted, rfl⟩
    have imageIncluded : map (Phi := Phi) converter source ⊆ target := by
      rintro _ ⟨original, sourceAdmitted, rfl⟩
      exact construction original sourceAdmitted
    exact (relaxation A).mono imageIncluded relaxedImage
  · intro preserves A B converter source
    -- Apply preservation to the direct image of the unrelaxed source.
    have preserved := preserves converter source
      (map (Phi := Phi) converter source)
      (constructs_iff.mpr fun resource admitted =>
        ⟨resource, admitted, rfl⟩)
    rintro _ ⟨resource, admitted, rfl⟩
    exact constructs_iff.mp preserved resource admitted

end Relaxation

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Pull a compatible relaxation through the outer leg of a serial
construction. -/
theorem Constructs.relax_serial
    {relaxation : (A : C) →
      AbstractCryptography.Relaxation (Resource Phi A)}
    (compatible : Relaxation.Compatible (Phi := Phi) relaxation)
    {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source (relaxation B middle))
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source
      (relaxation A target) := by
  rw [constructs_iff] at inner outer ⊢
  intro resource admitted
  -- The inner construction reaches the relaxed middle specification.
  have middleRelaxed := inner resource admitted
  -- Serial attachment exposes the outer converter on that relaxed resource.
  rw [attach_serial]
  -- Compatibility pulls the relaxation through the outer converter.
  have relaxedImage := compatible first middle
    ⟨attach (Phi := Phi) second resource, middleRelaxed, rfl⟩
  have imageIncluded : map (Phi := Phi) first middle ⊆ target := by
    rintro _ ⟨original, middleAdmitted, rfl⟩
    exact outer original middleAdmitted
  exact (relaxation A).mono imageIncluded relaxedImage

/-- Put an exact construction into an unchanged right context and pull a
parallel-compatible relaxation around the result. -/
theorem Constructs.relax_left_context
    {relaxation : (A : C) →
      AbstractCryptography.Relaxation (Resource Phi A)}
    (parallelCompatible :
      Relaxation.ParallelCompatible (Phi := Phi) relaxation)
    {A A' B : C} {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source
      (relaxation A target))
    (context : Specification Phi B) :
    Constructs (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (ResourceAlgebra.Specification.parallel (Phi := Phi) source context)
      (relaxation (A ⊗ B)
        (ResourceAlgebra.Specification.parallel (Phi := Phi) target context)) := by
  -- Ordinary context-insensitivity reaches parallel with the relaxed target.
  rw [constructs_iff] at construction ⊢
  rintro resource ⟨left, admitted, right, contextAdmitted, rfl⟩
  rw [attach_parallel]
  simp only [attach_identity]
  -- Parallel compatibility moves the relaxation outside that context.
  exact (parallelCompatible A B target context).1
    ⟨attach (Phi := Phi) converter left, construction left admitted,
      right, contextAdmitted, rfl⟩

/-- Right-context counterpart of `Constructs.relax_left_context`. -/
theorem Constructs.relax_right_context
    {relaxation : (A : C) →
      AbstractCryptography.Relaxation (Resource Phi A)}
    (parallelCompatible :
      Relaxation.ParallelCompatible (Phi := Phi) relaxation)
    {A B B' : C} {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    (context : Specification Phi A)
    (construction : Constructs (Phi := Phi) converter source
      (relaxation B target)) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (ResourceAlgebra.Specification.parallel (Phi := Phi) context source)
      (relaxation (A ⊗ B)
        (ResourceAlgebra.Specification.parallel (Phi := Phi) context target)) := by
  -- Ordinary context-insensitivity reaches parallel with the relaxed target.
  rw [constructs_iff] at construction ⊢
  rintro resource ⟨left, contextAdmitted, right, admitted, rfl⟩
  rw [attach_parallel]
  simp only [attach_identity]
  -- Parallel compatibility moves the relaxation outside that context.
  exact (parallelCompatible A B context target).2
    ⟨left, contextAdmitted,
      attach (Phi := Phi) converter right, construction right admitted, rfl⟩

end AbstractCryptography.Categorical.ResourceAlgebra.Specification
