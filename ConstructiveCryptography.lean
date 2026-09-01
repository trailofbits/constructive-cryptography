/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import ConstructiveCryptography.Categorical.ResourceAlgebra.ConstructorClass
import ConstructiveCryptography.Categorical.ResourceAlgebra.ConverterTuple
import ConstructiveCryptography.Categorical.ResourceAlgebra.CostBounded
import ConstructiveCryptography.Categorical.ResourceAlgebra.Endomorphism
import ConstructiveCryptography.Categorical.ResourceAlgebra.Filtered
import ConstructiveCryptography.Categorical.ResourceAlgebra.Outbound
import ConstructiveCryptography.Tactics.ProofAutomation
import ConstructiveCryptography.Presentation.ControlledNaturalLanguage

/-!
# Constructive Cryptography

This is the MR16/Jost/Liu Constructive Cryptography theory before selecting a
concrete system model. It exports one interface-indexed presentation centered on
`ConstructiveCryptography.Categorical.ResourceAlgebra`.

Resources at an interface `A` are the objects of the fibre `Phi.obj (op A)`;
typed converters `A ⟶ B` act by the contravariant resource functor;
`Specification.Constructs` is direct-image inclusion.  Serial construction,
ordered parallel construction, scalar-error relaxation, converter-class
relaxation, filtered endpoints, constructor classes, and cost bounds are the
corresponding imported theorem families.  A protocol in the multiparty sense
is an explicit partial converter tuple from `ConverterTuple`; it is not a
second action or resource carrier.

For a category `C` of interfaces and converters and a contravariant functor
`Phi : Cᵒᵖ ⥤ Type` of resources, `ResourceAlgebra C Phi` supplies ordered
parallel composition, attachment as `Phi.map`, a pseudo-emetric on every
resource fibre, and non-expansion of attachment and parallel composition.

Maurer--Renner 2016 supplies the construction and relaxation calculus.  Jost's
typed attachment and ordered parallel presentation requires no symmetric
parallel axiom.  Liu--Maurer multiparty constructions are layered in
`ConstructiveCryptography.MultipartyComputation`, which depends on this root.

`RandomSystems` owns fixed-interface DDS, DDE, and PDS mathematics.
`RandomSystems.Converter` owns the concrete PDC category, with DDCs as its
deterministic specialization, and `RandomSystemsCC` installs the selected
`ResourceAlgebra` instance. None of those concrete modules is imported here.

The systematic public setup is:

```lean
import ConstructiveCryptography
open ConstructiveCryptography
open scoped ConstructiveCryptography
```

This makes the scoped notation and the `cc_*` proof commands available.
Controlled-language sentences additionally require:

```lean
open scoped CryptoControlledNaturalLanguage
```
-/

set_option autoImplicit false

namespace ConstructiveCryptography.Categorical.ResourceAlgebra.Specification

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

end ConstructiveCryptography.Categorical.ResourceAlgebra.Specification

namespace ConstructiveCryptography

/-- Paper notation for exact typed construction. -/
scoped notation:50 source " —[" converter "]→ " target:51 =>
  ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs
    converter source target

/-- Paper notation for scalar approximate typed construction. -/
scoped notation:50 source " —[" converter "; " error "]→ " target:51 =>
  ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ApproximatelyConstructs
    converter error source target

end ConstructiveCryptography
