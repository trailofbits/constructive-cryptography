/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Specification.Defs
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option autoImplicit false

/-!
# Interface-indexed specifications and constructions

For a functor `F : C ⥤ Type`, each object has its own resource carrier
`F.obj A`.  A converter `f : A ⟶ B` maps a specification by direct image,
and constructs a target specification exactly when that image is included in
the target.  Functor identity and composition give the identity and serial
construction laws.

This is the heterogeneous form of Maurer--Renner's specification calculus. It
does not choose a concrete resource model or converter category. Jost's
interface-indexed attachment supplies the same heterogeneous shape but does
not require it to be packaged as a Lean category. Liu--Maurer's homogeneous
presentation is recovered by restricting to one object and its endomorphisms.
-/

namespace AbstractCryptography.Categorical

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The selected pseudo-emetric on each resource fibre, together with
non-expansion of every converter map.

Maurer--Renner 2016, Definition 2 (printed p. 11): “A metric `d` on `Φ` is
called non-expanding if `d(αR, αS) ≤ d(R, S)` for all `α`.”  The metrics are
fields rather than global instances because one resource functor may admit
more than one useful distance. -/
class IsNonexpanding (F : C ⥤ Type w) where
  fibreMetric : ∀ A, PseudoEMetricSpace (F.obj A)
  edist_map_le : ∀ {A B : C} (converter : A ⟶ B)
      (left right : F.obj A),
    @edist (F.obj B) (fibreMetric B).toEDist
        (F.map converter left) (F.map converter right) ≤
      @edist (F.obj A) (fibreMetric A).toEDist left right

variable {F : C ⥤ Type w}

/-- Distance in the selected resource fibre. -/
noncomputable def distance [IsNonexpanding F] {A : C}
    (left right : F.obj A) : ENNReal :=
  @edist (F.obj A) (IsNonexpanding.fibreMetric (F := F) A).toEDist left right

@[simp]
theorem distance_self [IsNonexpanding F] {A : C} (resource : F.obj A) :
    distance (F := F) resource resource = 0 := by
  letI := IsNonexpanding.fibreMetric (F := F) A
  exact edist_self resource

theorem distance_triangle [IsNonexpanding F] {A : C}
    (left middle right : F.obj A) :
    distance (F := F) left right ≤
      distance (F := F) left middle + distance (F := F) middle right := by
  letI := IsNonexpanding.fibreMetric (F := F) A
  exact edist_triangle left middle right

/-- Every converter map is non-expanding for the selected fibre distances. -/
theorem distance_map_le [IsNonexpanding F] {A B : C}
    (converter : A ⟶ B) (left right : F.obj A) :
    distance (F := F) (F.map converter left) (F.map converter right) ≤
      distance (F := F) left right :=
  IsNonexpanding.edist_map_le converter left right

/-- A specification in the resource fibre at `A`. -/
abbrev Specification (F : C ⥤ Type w) (A : C) :=
  AbstractCryptography.Specification (F.obj A)

namespace Specification

variable (F : C ⥤ Type w)

/-- Direct image of a specification under a converter. -/
def map {A B : C} (converter : A ⟶ B) (source : Specification F A) :
    Specification F B :=
  F.map converter '' source

/-- Exact construction is image inclusion in the target fibre.

Maurer--Renner 2016, Definition 1 (printed p. 11):
“`R —π→ S :⇐⇒ πR ⊆ S`.” -/
def Constructs {A B : C} (converter : A ⟶ B)
    (source : Specification F A) (target : Specification F B) : Prop :=
  map F converter source ⊆ target

@[simp]
theorem map_identity {A : C} (source : Specification F A) :
    map F (𝟙 A) source = source := by
  apply Set.ext
  intro resource
  constructor
  · rintro ⟨original, member, equality⟩
    have original_eq : original = resource := by
      simpa using equality
    simpa [original_eq] using member
  · intro member
    exact ⟨resource, member, by simp⟩

theorem map_serial {A B D : C} (first : A ⟶ B) (second : B ⟶ D)
    (source : Specification F A) :
    map F (first ≫ second) source = map F second (map F first source) := by
  apply Set.ext
  intro resource
  constructor
  · rintro ⟨original, member, rfl⟩
    exact ⟨F.map first original, ⟨original, member, rfl⟩, by simp⟩
  · rintro ⟨middle, ⟨original, member, rfl⟩, rfl⟩
    exact ⟨original, member, by simp⟩

@[simp]
theorem constructs_identity {A : C} (source : Specification F A) :
    Constructs F (𝟙 A) source source := by
  rw [Constructs, map_identity]

/-- Serial construction follows from functorial direct image and subset
transitivity. -/
theorem Constructs.serial {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification F A} {middle : Specification F B}
    {target : Specification F D}
    (firstLeg : Constructs F first source middle)
    (secondLeg : Constructs F second middle target) :
    Constructs F (first ≫ second) source target := by
  rw [Constructs, map_serial]
  exact (Set.image_mono firstLeg).trans secondLeg

/-- Approximate construction: every attached source resource is within `ε`
of an admitted target resource for the selected fibre distance. -/
def ConstructsWithin [IsNonexpanding F] {A B : C}
    (converter : A ⟶ B) (source : Specification F A)
    (target : Specification F B) (ε : ENNReal) : Prop :=
  ∀ resource ∈ source, ∃ ideal ∈ target,
    distance (F := F) (F.map converter resource) ideal ≤ ε

@[simp]
theorem constructsWithin_identity [IsNonexpanding F] {A : C}
    (source : Specification F A) :
    ConstructsWithin F (𝟙 A) source source 0 := by
  intro resource member
  exact ⟨resource, member, by simp [distance]⟩

theorem ConstructsWithin.weaken [IsNonexpanding F]
    {A B : C} {converter : A ⟶ B}
    {source : Specification F A} {target : Specification F B}
    {ε δ : ENNReal} (construction : ConstructsWithin F converter source target ε)
    (bound : ε ≤ δ) : ConstructsWithin F converter source target δ := by
  intro resource member
  obtain ⟨ideal, admitted, close⟩ := construction resource member
  exact ⟨ideal, admitted, close.trans bound⟩

/-- Approximate constructions compose serially, adding their error budgets. -/
theorem ConstructsWithin.serial [IsNonexpanding F]
    {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification F A} {middle : Specification F B}
    {target : Specification F D} {ε δ : ENNReal}
    (firstLeg : ConstructsWithin F first source middle ε)
    (secondLeg : ConstructsWithin F second middle target δ) :
    ConstructsWithin F (first ≫ second) source target (ε + δ) := by
  intro resource member
  obtain ⟨middleResource, middleMember, firstClose⟩ := firstLeg resource member
  obtain ⟨idealResource, idealMember, secondClose⟩ :=
    secondLeg middleResource middleMember
  refine ⟨idealResource, idealMember, ?_⟩
  rw [FunctorToTypes.map_comp_apply]
  calc
    distance (F := F) (F.map second (F.map first resource)) idealResource ≤
        distance (F := F) (F.map second (F.map first resource))
            (F.map second middleResource) +
          distance (F := F) (F.map second middleResource) idealResource :=
      distance_triangle _ _ _
    _ ≤ ε + δ := add_le_add
      ((distance_map_le second _ _).trans firstClose) secondClose

end Specification

end AbstractCryptography.Categorical
