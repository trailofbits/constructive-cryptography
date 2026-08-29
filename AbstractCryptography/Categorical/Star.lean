/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.CategoryTheory.Endomorphism

set_option autoImplicit false

/-!
# Star closure in one interface fibre

For a resource functor `F : C ⥤ Type`, the endomorphisms of one object `A`
are precisely the converters that preserve that interface.  A submonoid of
`End A` is therefore a composition-closed simulator family.  Its star closure
of a specification in `F.obj A` consists of every resource obtained by mapping
an admitted resource through one family member.

The construction relation remains ordinary image inclusion.  The simulator
appears only in the two proof theorems at the end: an explicit exact equation,
or an explicit distance bound, exhibits the constructed resource as a member
of the star-relaxed ideal specification.  This is the heterogeneous form of
Maurer--Renner 2016, Sections 4.2--4.3; simulation is not construction
semantics.
-/

namespace AbstractCryptography.Categorical

open CategoryTheory
open Pointwise

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A composition-closed converter family preserving one interface. -/
abbrev EndoFamily (A : C) := Submonoid (CategoryTheory.End A)

namespace Specification

/-- Star closure of a specification under a composition-closed family of
endomorphisms at the same interface.

Maurer--Renner 2016, Section 3.4 (printed p. 8):
“`R* := RΣ = {Rβ | R ∈ R, β ∈ Σ}`.” -/
noncomputable def star (F : C ⥤ Type w) {A : C}
    (family : EndoFamily A) (source : Specification F A) :
    Specification F A :=
  {resource | ∃ converter ∈ family, ∃ original ∈ source,
    F.map converter original = resource}

theorem mem_star_iff (F : C ⥤ Type w) {A : C}
    {family : EndoFamily A} {source : Specification F A}
    {resource : F.obj A} :
    resource ∈ star F family source ↔
      ∃ converter ∈ family, ∃ original ∈ source,
        F.map converter original = resource :=
  Iff.rfl

/-- Every specification is contained in its star closure, using the identity
endomorphism. -/
theorem subset_star (F : C ⥤ Type w) {A : C}
    (family : EndoFamily A) (source : Specification F A) :
    source ⊆ star F family source := by
  intro resource admitted
  -- The identity endomorphism witnesses the original resource.
  exact ⟨𝟙 A, family.one_mem, resource, admitted, by simp⟩

/-- Star closure is idempotent because the endomorphism family contains the
identity and is closed under categorical composition. -/
theorem star_idem (F : C ⥤ Type w) {A : C}
    (family : EndoFamily A) (source : Specification F A) :
    star F family (star F family source) = star F family source := by
  apply Set.Subset.antisymm
  · -- Compose the two endomorphism witnesses.
    rintro resource ⟨outer, outerAdmitted, middle,
      ⟨inner, innerAdmitted, original, sourceAdmitted, rfl⟩, rfl⟩
    exact ⟨outer * inner, family.mul_mem outerAdmitted innerAdmitted,
      original, sourceAdmitted, by simp⟩
  · -- Extensivity supplies the reverse inclusion.
    exact subset_star F family (star F family source)

/-- An explicit exact simulator equation proves a heterogeneous construction
into the star-relaxed ideal.  The simulator is evidence for this theorem, not
part of `Constructs`. -/
theorem constructs_star_of_simulator (F : C ⥤ Type w)
    {A B : C} {converter : A ⟶ B} {family : EndoFamily B}
    {real : F.obj A} {ideal : F.obj B}
    (simulator : CategoryTheory.End B) (admitted : simulator ∈ family)
    (equation : F.map converter real = F.map simulator ideal) :
    Constructs F converter ({real} : Specification F A)
      (star F family ({ideal} : Specification F B)) := by
  intro result membership
  obtain ⟨resource, sourceMember, rfl⟩ := membership
  have resource_eq : resource = real := Set.mem_singleton_iff.mp sourceMember
  subst resource
  exact (mem_star_iff F).mpr
    ⟨simulator, admitted, ideal, Set.mem_singleton ideal, equation.symm⟩

/-- An explicit approximate simulator bound proves the corresponding
heterogeneous construction.  The distance is measured after the converter and
simulator have both been applied, so the proof uses no further non-expansion
step beyond selecting the ambient fibre distance. -/
theorem constructsWithin_star_of_simulator (F : C ⥤ Type w)
    [IsNonexpanding F]
    {A B : C} {converter : A ⟶ B} {family : EndoFamily B}
    {real : F.obj A} {ideal : F.obj B} {ε : ENNReal}
    (simulator : CategoryTheory.End B) (admitted : simulator ∈ family)
    (close : distance (F := F) (F.map converter real)
      (F.map simulator ideal) ≤ ε) :
    ConstructsWithin F converter ({real} : Specification F A)
      (star F family ({ideal} : Specification F B)) ε := by
  intro resource sourceMember
  have resource_eq : resource = real := Set.mem_singleton_iff.mp sourceMember
  subst resource
  refine ⟨F.map simulator ideal, ?_, close⟩
  exact (mem_star_iff F).mpr
    ⟨simulator, admitted, ideal, Set.mem_singleton ideal, rfl⟩

end Specification

end AbstractCryptography.Categorical
