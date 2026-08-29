/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical.ResourceAlgebra.ConstructorClass
import Mathlib.Data.ENat.Lattice

set_option autoImplicit false

/-!
# Cost-bounded constructor classes

The cost-bounded class in a typed hom-set contains exactly the converters whose
given cost is at most the given budget.  Cost is an explicit modeling parameter.
Identity, serial, and ordered-parallel closure are hypotheses on that parameter;
they are not fields of `ResourceAlgebra` and are not inferred from a global
converter monoid.

Maurer--Renner 2016, Section 2.1 (printed p. 4) allows the constructor set to be
“possibly restricted in terms of efficiency or implementation cost.”  Section
3.5 (printed p. 10) says that one may take the converter set to be “the set of
efficiently implementable converter systems,” and footnote 6 requires the
chosen class to be closed under converter composition.

Jost makes converters explicit in the basic theory and treats efficient
families only as an optional specialization.  Accordingly, this module supplies
one family of admitted constructor sets; it changes neither Jost's construction
relation nor the ambient resource algebra.  Liu--Maurer's explicit multiparty
converter tuples can be restricted by this family when an application chooses
a cost model.
-/

namespace AbstractCryptography.Categorical.ResourceAlgebra.Specification

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-- The converters whose explicit cost is at most the supplied budget. -/
def costBounded {Converter : Type*} (cost : Converter → ℕ∞)
    (budget : ℕ∞) : Set Converter :=
  {converter | cost converter ≤ budget}

@[simp]
theorem mem_costBounded {Converter : Type*} {cost : Converter → ℕ∞}
    {budget : ℕ∞} {converter : Converter} :
    converter ∈ costBounded cost budget ↔ cost converter ≤ budget :=
  Iff.rfl

/-- A larger budget admits every converter admitted by a smaller budget. -/
theorem costBounded_mono {Converter : Type*} {cost : Converter → ℕ∞}
    {budget budget' : ℕ∞} (included : budget ≤ budget') :
    costBounded cost budget ⊆ costBounded cost budget' :=
  fun _ admitted => admitted.trans included

/-- Cost-bounded converter classes are monotone in their budget. -/
theorem monotone_costBounded {Converter : Type*} (cost : Converter → ℕ∞) :
    Monotone (costBounded cost) :=
  fun _ _ included => costBounded_mono included

/-- The unbounded budget admits every converter. -/
@[simp]
theorem costBounded_top {Converter : Type*} (cost : Converter → ℕ∞) :
    costBounded cost ⊤ = (Set.univ : Set Converter) :=
  Set.eq_univ_of_forall fun _ => mem_costBounded.mpr le_top

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Enlarging the budget preserves constructibility. -/
theorem Constructible.mono_costBounded {A B : C}
    {cost : (A ⟶ B) → ℕ∞} {budget budget' : ℕ∞}
    (included : budget ≤ budget')
    {source : Specification Phi B} {target : Specification Phi A}
    (construction :
      Constructible (Phi := Phi) (costBounded cost budget) source target) :
    Constructible (Phi := Phi) (costBounded cost budget') source target :=
  construction.mono_constructors (costBounded_mono included)

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Non-constructibility against a larger budget implies
non-constructibility against every smaller budget. -/
theorem Unconstructible.mono_costBounded {A B : C}
    {cost : (A ⟶ B) → ℕ∞} {budget budget' : ℕ∞}
    (included : budget ≤ budget')
    {source : Specification Phi B} {target : Specification Phi A}
    (impossible :
      Unconstructible (Phi := Phi) (costBounded cost budget') source target) :
    Unconstructible (Phi := Phi) (costBounded cost budget) source target :=
  impossible.mono_constructors (costBounded_mono included)

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Every cost-bounded construction is admitted by the unbounded class. -/
theorem Constructible.mono_costBounded_top {A B : C}
    {cost : (A ⟶ B) → ℕ∞} {budget : ℕ∞}
    {source : Specification Phi B} {target : Specification Phi A}
    (construction :
      Constructible (Phi := Phi) (costBounded cost budget) source target) :
    Constructible (Phi := Phi) (costBounded cost ⊤) source target :=
  construction.mono_costBounded le_top

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Specification inclusion is cost-bounded constructible when the identity
converter is within budget. -/
theorem constructible_of_subset_costBounded {A : C}
    {cost : CategoryTheory.End A → ℕ∞} {budget : ℕ∞}
    (identityCost : cost (𝟙 A) ≤ budget)
    {source target : Specification Phi A} (included : source ⊆ target) :
    Constructible (Phi := Phi) (costBounded cost budget) source target :=
  constructible_of_subset identityCost included

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Cost-bounded constructions compose serially when the cost of every
admitted composite fits the stated result budget.

Maurer--Renner 2016, footnote 6 (printed p. 10): “converters `α` and `β` from
this particular set `Σ` can be composed to a new converter, say `α ∘ β`, and
this composition is closed.” -/
theorem Constructible.serial_costBounded {A B D : C}
    (cost : ∀ {X Y : C}, (X ⟶ Y) → ℕ∞)
    {firstBudget secondBudget compositeBudget : ℕ∞}
    (serialCost : ∀ (first : A ⟶ B) (second : B ⟶ D),
      cost first ≤ firstBudget → cost second ≤ secondBudget →
        cost (first ≫ second) ≤ compositeBudget)
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructible (Phi := Phi)
      (costBounded cost secondBudget) source middle)
    (outer : Constructible (Phi := Phi)
      (costBounded cost firstBudget) middle target) :
    Constructible (Phi := Phi)
      (costBounded cost compositeBudget) source target :=
  Constructible.serial
    (fun first firstAdmitted second secondAdmitted =>
      serialCost first second firstAdmitted secondAdmitted)
    inner outer

/-- Cost-bounded constructions compose in ordered parallel when the cost of
every admitted tensor fits the stated result budget. -/
theorem Constructible.parallel_costBounded {A A' B B' : C}
    (cost : ∀ {X Y : C}, (X ⟶ Y) → ℕ∞)
    {leftBudget rightBudget parallelBudget : ℕ∞}
    (parallelCost : ∀ (left : A ⟶ A') (right : B ⟶ B'),
      cost left ≤ leftBudget → cost right ≤ rightBudget →
        cost (left ⊗ₘ right) ≤ parallelBudget)
    {leftSource : Specification Phi A'} {leftTarget : Specification Phi A}
    {rightSource : Specification Phi B'} {rightTarget : Specification Phi B}
    (leftConstruction : Constructible (Phi := Phi)
      (costBounded cost leftBudget) leftSource leftTarget)
    (rightConstruction : Constructible (Phi := Phi)
      (costBounded cost rightBudget) rightSource rightTarget) :
    Constructible (Phi := Phi) (costBounded cost parallelBudget)
      (Specification.parallel (Phi := Phi) leftSource rightSource)
      (Specification.parallel (Phi := Phi) leftTarget rightTarget) :=
  Constructible.parallel
    (fun left leftAdmitted right rightAdmitted =>
      parallelCost left right leftAdmitted rightAdmitted)
    leftConstruction rightConstruction

end AbstractCryptography.Categorical.ResourceAlgebra.Specification
