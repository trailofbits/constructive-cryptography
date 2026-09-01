/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ConstructiveCryptography.Categorical.ResourceAlgebra.Star

set_option autoImplicit false

/-!
# Admitted constructor classes

An admitted constructor class is a set in one typed hom-set.  It restricts the
converter witnessing a construction without introducing another action or a
global converter monoid.  Serial and parallel closure are explicit hypotheses
relating the three typed classes that occur in the conclusion.

Maurer--Renner 2016, Section 2.1 (printed p. 4): “Typically one considers a
certain set Γ of constructors, possibly restricted in terms of efficiency or
implementation cost.”  Section 3.5 (printed p. 10) allows different converter
sets for honest and dishonest parties, so the constructor class here is
independent of the converter class used by `star`.

Jost, Section 2.2.2 (printed p. 17): “In this work, we mainly avoid the delicate
task of choosing the class of converters under consideration by making all
converters explicit.”  Thus this layer is an optional restriction of Jost's
typed construction relation, not an axiom required by that relation.  Liu--
Maurer's multiparty construction likewise supplies its honest converter tuple
explicitly; an admitted class may be imposed when an application needs one.
-/

namespace ConstructiveCryptography.Categorical.ResourceAlgebra.Specification

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-- A target specification is constructible from a source within a typed set of
admitted constructors.

Maurer--Renner 2016, Section 2.1 (printed p. 4): “Typically one considers a
certain set `Γ` of constructors, possibly restricted in terms of efficiency or
implementation cost.” Lean records membership in that set explicitly. -/
def Constructible {A B : C} (constructors : Set (A ⟶ B))
    (source : Specification Phi B) (target : Specification Phi A) : Prop :=
  ∃ converter ∈ constructors,
    Constructs (Phi := Phi) converter source target

/-- A target specification is not constructible from a source within the
specified typed constructor class.

Maurer--Renner 2016, Section 2.1 (printed p. 4):
“`R ↛ S :⇐⇒ ¬∃ γ ∈ Γ : R —γ→ S`.” -/
def Unconstructible {A B : C} (constructors : Set (A ⟶ B))
    (source : Specification Phi B) (target : Specification Phi A) : Prop :=
  ¬ Constructible (Phi := Phi) constructors source target

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
@[simp]
theorem unconstructible_iff_not_constructible {A B : C}
    {constructors : Set (A ⟶ B)} {source : Specification Phi B}
    {target : Specification Phi A} :
    Unconstructible (Phi := Phi) constructors source target ↔
      ¬ Constructible (Phi := Phi) constructors source target :=
  Iff.rfl

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A labelled construction whose converter is admitted is constructible
within that class. -/
theorem Constructs.constructible {A B : C} {converter : A ⟶ B}
    {constructors : Set (A ⟶ B)} {source : Specification Phi B}
    {target : Specification Phi A} (admitted : converter ∈ constructors)
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructible (Phi := Phi) constructors source target :=
  ⟨converter, admitted, construction⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Constructibility is contravariant in its source specification and
covariant in its target specification. -/
theorem Constructible.mono {A B : C} {constructors : Set (A ⟶ B)}
    {source source' : Specification Phi B}
    {target target' : Specification Phi A}
    (sourceIncluded : source' ⊆ source)
    (targetIncluded : target ⊆ target')
    (construction : Constructible (Phi := Phi) constructors source target) :
    Constructible (Phi := Phi) constructors source' target' := by
  obtain ⟨converter, admitted, constructs⟩ := construction
  exact ⟨converter, admitted, constructs.mono sourceIncluded targetIncluded⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Enlarging the admitted constructor class preserves constructibility. -/
theorem Constructible.mono_constructors {A B : C}
    {constructors constructors' : Set (A ⟶ B)}
    (included : constructors ⊆ constructors')
    {source : Specification Phi B} {target : Specification Phi A}
    (construction : Constructible (Phi := Phi) constructors source target) :
    Constructible (Phi := Phi) constructors' source target := by
  obtain ⟨converter, admitted, constructs⟩ := construction
  exact ⟨converter, included admitted, constructs⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Non-constructibility is covariant in the source and contravariant in the
target specification. -/
theorem Unconstructible.anti {A B : C} {constructors : Set (A ⟶ B)}
    {source source' : Specification Phi B}
    {target target' : Specification Phi A}
    (sourceIncluded : source ⊆ source')
    (targetIncluded : target' ⊆ target)
    (impossible : Unconstructible (Phi := Phi) constructors source target) :
    Unconstructible (Phi := Phi) constructors source' target' := by
  intro construction
  exact impossible (construction.mono sourceIncluded targetIncluded)

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Non-constructibility against a larger admitted class implies
non-constructibility against each smaller class. -/
theorem Unconstructible.mono_constructors {A B : C}
    {constructors constructors' : Set (A ⟶ B)}
    (included : constructors ⊆ constructors')
    {source : Specification Phi B} {target : Specification Phi A}
    (impossible : Unconstructible (Phi := Phi) constructors' source target) :
    Unconstructible (Phi := Phi) constructors source target := by
  intro construction
  exact impossible (construction.mono_constructors included)

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Admitted converter classes compose serially when their composites
belong to the stated result class.

Maurer--Renner 2016, Lemma 1 (printed p. 11): “This construction notion is
composable.” -/
theorem Constructible.serial {A B D : C}
    {firstConstructors : Set (A ⟶ B)}
    {secondConstructors : Set (B ⟶ D)}
    {compositeConstructors : Set (A ⟶ D)}
    (serialAdmitted : ∀ first ∈ firstConstructors,
      ∀ second ∈ secondConstructors,
        first ≫ second ∈ compositeConstructors)
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructible (Phi := Phi) secondConstructors source middle)
    (outer : Constructible (Phi := Phi) firstConstructors middle target) :
    Constructible (Phi := Phi) compositeConstructors source target := by
  obtain ⟨second, secondAdmitted, innerConstruction⟩ := inner
  obtain ⟨first, firstAdmitted, outerConstruction⟩ := outer
  exact ⟨first ≫ second,
    serialAdmitted first firstAdmitted second secondAdmitted,
    innerConstruction.serial outerConstruction⟩

/-- Admitted converter classes compose in ordered parallel when the
tensor of every admitted pair belongs to the stated result class.

Jost, Theorem 2.2.5 (printed p. 19):
“`R —π→ S =⇒ [R,T] —π→ [S,T]`.” -/
theorem Constructible.parallel {A A' B B' : C}
    {leftConstructors : Set (A ⟶ A')}
    {rightConstructors : Set (B ⟶ B')}
    {parallelConstructors : Set (Quiver.Hom (A ⊗ B) (A' ⊗ B'))}
    (parallelAdmitted : ∀ left ∈ leftConstructors,
      ∀ right ∈ rightConstructors,
        left ⊗ₘ right ∈ parallelConstructors)
    {leftSource : Specification Phi A'} {leftTarget : Specification Phi A}
    {rightSource : Specification Phi B'} {rightTarget : Specification Phi B}
    (leftConstruction :
      Constructible (Phi := Phi) leftConstructors leftSource leftTarget)
    (rightConstruction :
      Constructible (Phi := Phi) rightConstructors rightSource rightTarget) :
    Constructible (Phi := Phi) parallelConstructors
      (Specification.parallel (Phi := Phi) leftSource rightSource)
      (Specification.parallel (Phi := Phi) leftTarget rightTarget) := by
  obtain ⟨left, leftAdmitted, leftConstructs⟩ := leftConstruction
  obtain ⟨right, rightAdmitted, rightConstructs⟩ := rightConstruction
  exact ⟨left ⊗ₘ right,
    parallelAdmitted left leftAdmitted right rightAdmitted,
    leftConstructs.parallel rightConstructs⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Inclusion is constructible whenever the identity converter is admitted. -/
theorem constructible_of_subset {A : C}
    {constructors : Set (CategoryTheory.End A)}
    (identityAdmitted : 𝟙 A ∈ constructors)
    {source target : Specification Phi A} (included : source ⊆ target) :
    Constructible (Phi := Phi) constructors source target := by
  refine ⟨𝟙 A, identityAdmitted, ?_⟩
  exact (constructs_identity (Phi := Phi) source).mono Set.Subset.rfl included

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A specification is constructible from itself whenever the identity
converter is admitted. -/
theorem Constructible.refl {A : C}
    {constructors : Set (CategoryTheory.End A)}
    (identityAdmitted : 𝟙 A ∈ constructors)
    (source : Specification Phi A) :
    Constructible (Phi := Phi) constructors source source :=
  constructible_of_subset identityAdmitted Set.Subset.rfl

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Constructibility within an admitted constructor class is preserved when
both specifications are closed under an independent converter class.

Maurer--Renner 2016, Lemma 3 (printed p. 11):
“`R —π→ S  =⇒  R* —π→ S*`.” -/
theorem Constructible.star {A : C}
    {constructors : Set (CategoryTheory.End A)}
    {converters : EndoFamily (Opposite.op A)}
    (commutes : ∀ constructor ∈ constructors,
      ∀ classConverter : CategoryTheory.End A,
        classConverter.op ∈ converters →
          ∀ resource : Resource Phi A,
            attach (Phi := Phi) constructor
                (attach (Phi := Phi) classConverter resource) =
              attach (Phi := Phi) classConverter
                (attach (Phi := Phi) constructor resource))
    {source target : Specification Phi A}
    (construction : Constructible (Phi := Phi) constructors source target) :
    Constructible (Phi := Phi) constructors
      (star (Phi := Phi) converters source)
      (star (Phi := Phi) converters target) := by
  obtain ⟨constructor, admitted, constructs⟩ := construction
  exact ⟨constructor, admitted, constructs.star (commutes constructor admitted)⟩

/-- Two constructible scalar-error legs compose serially, their errors add,
and the composite remains in the stated admitted constructor class. -/
theorem Constructible.serial_epsilonRelaxation {A B D : C}
    {firstConstructors : Set (A ⟶ B)}
    {secondConstructors : Set (B ⟶ D)}
    {compositeConstructors : Set (A ⟶ D)}
    (serialAdmitted : ∀ first ∈ firstConstructors,
      ∀ second ∈ secondConstructors,
        first ≫ second ∈ compositeConstructors)
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : Constructible (Phi := Phi) secondConstructors source
      (epsilonRelaxation (Phi := Phi) innerError middle))
    (outer : Constructible (Phi := Phi) firstConstructors middle
      (epsilonRelaxation (Phi := Phi) outerError target)) :
    Constructible (Phi := Phi) compositeConstructors source
      (epsilonRelaxation (Phi := Phi) (innerError + outerError) target) := by
  obtain ⟨second, secondAdmitted, innerConstruction⟩ := inner
  obtain ⟨first, firstAdmitted, outerConstruction⟩ := outer
  refine ⟨first ≫ second,
    serialAdmitted first firstAdmitted second secondAdmitted, ?_⟩
  rw [constructs_epsilonRelaxation_iff] at innerConstruction outerConstruction ⊢
  exact innerConstruction.serial outerConstruction

end ConstructiveCryptography.Categorical.ResourceAlgebra.Specification
