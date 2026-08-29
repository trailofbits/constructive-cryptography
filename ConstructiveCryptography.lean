/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Categorical.ResourceAlgebra.ConstructorClass
import AbstractCryptography.Categorical.ResourceAlgebra.ConverterTuple
import AbstractCryptography.Categorical.ResourceAlgebra.CostBounded
import AbstractCryptography.Categorical.ResourceAlgebra.Filtered
import AbstractCryptography.Categorical.ResourceAlgebra.Outbound

/-!
# Constructive Cryptography

This is the public carrier-independent Constructive Cryptography root over the
single typed `ResourceAlgebra` presentation.

Resources at an interface `A` are the objects of the fibre `Phi.obj (op A)`;
typed converters `A ⟶ B` act by the contravariant resource functor;
`Specification.Constructs` is direct-image inclusion.  Serial construction,
ordered parallel construction, scalar-error relaxation, converter-class
relaxation, filtered endpoints, constructor classes, and cost bounds are the
corresponding imported theorem families.  A protocol in the multiparty sense
is an explicit partial converter tuple from `ConverterTuple`; it is not a
second action or resource carrier.

Maurer--Renner 2016 supplies the construction and relaxation calculus.  Jost's
typed attachment and ordered parallel presentation requires no symmetric
parallel axiom.  Liu--Maurer multiparty constructions are layered in
`ConstructiveCryptography.MultipartyComputation`, which depends on this root.
-/

set_option autoImplicit false

namespace AbstractCryptography.Categorical.ResourceAlgebra.Specification

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}

/-- Exact typed construction as a `Trans` relation. This is the paper's serial
construction law exposed to Lean `calc`; it adds no new construction notion. -/
instance instTransConstructs {A B D : C}
    {first : A ⟶ B} {second : B ⟶ D} :
    Trans (Constructs (Phi := Phi) second)
      (Constructs (Phi := Phi) first)
      (Constructs (Phi := Phi) (first ≫ second)) where
  trans := Constructs.serial

/-- Scalar approximate construction is exact construction into the selected
scalar-error relaxation. -/
@[reducible] def ApproximatelyConstructs [ResourceAlgebra C Phi]
    {A B : C} (converter : A ⟶ B) (error : ENNReal)
    (source : Specification Phi B) (target : Specification Phi A) : Prop :=
  Constructs (Phi := Phi) converter source
    (epsilonRelaxation (Phi := Phi) error target)

/-- Scalar approximate construction as a `Trans` relation. Serial composition
uses categorical composition and adds the two error bounds. -/
instance instTransApproximatelyConstructs [ResourceAlgebra C Phi]
    {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {innerError outerError : ENNReal} :
    Trans (ApproximatelyConstructs (Phi := Phi) second innerError)
      (ApproximatelyConstructs (Phi := Phi) first outerError)
      (ApproximatelyConstructs (Phi := Phi) (first ≫ second)
        (innerError + outerError)) where
  trans := Constructs.serial_epsilonRelaxation

end AbstractCryptography.Categorical.ResourceAlgebra.Specification

namespace ConstructiveCryptography

/-- Paper notation for exact typed construction. -/
scoped notation:50 source " —[" converter "]→ " target:51 =>
  AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs
    converter source target

/-- Paper notation for scalar approximate typed construction. -/
scoped notation:50 source " —[" converter "; " error "]→ " target:51 =>
  AbstractCryptography.Categorical.ResourceAlgebra.Specification.ApproximatelyConstructs
    converter error source target

end ConstructiveCryptography
