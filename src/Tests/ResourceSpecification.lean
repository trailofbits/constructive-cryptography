import ConstructiveCryptography.Notation
import ConstructiveCryptography.CryptographicAlgebra.Epsilon
import ConstructiveCryptography.CryptographicAlgebra.Star

/-! The abstract construction, relaxation and closure theorems of `CryptographicAlgebra`,
applied to the instance for interfaces. -/

namespace ResourceSpecificationTests

open CategoryTheory MonoidalCategory ConstructiveCryptography
open ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open SystemAlgebra

variable {A B C D : Interface}

/-- Serial construction. -/
example {α : A ⟶ B} {β : B ⟶ C} {R : Specification (Interface.Resource C)}
    {S : Specification (Interface.Resource B)} {T : Specification (Interface.Resource A)}
    (inner : Constructs β R S)
    (outer : Constructs α S T) :
    Constructs (α ≫ β) R T :=
  inner.serial outer

/-- Relaxing both endpoints by the same error. -/
example {α : A ⟶ B} {R : Specification (Interface.Resource B)}
    {S : Specification (Interface.Resource A)}
    (construction : Constructs α R S) (ε : ENNReal) :
    Constructs α (epsilonRelaxation ε R) (epsilonRelaxation ε S) :=
  construction.epsilonRelaxation ε

/-- Approximate serial construction adds the errors. -/
example {α : A ⟶ B} {β : B ⟶ C} {R : Specification (Interface.Resource C)}
    {S : Specification (Interface.Resource B)} {T : Specification (Interface.Resource A)}
    {ε δ : ENNReal}
    (inner : ConstructsWithin β R S ε)
    (outer : ConstructsWithin α S T δ) :
    ConstructsWithin (α ≫ β) R T (ε + δ) :=
  inner.serial outer

/-- Parallel construction. -/
example {α : A ⟶ B} {β : C ⟶ D} {R : Specification (Interface.Resource B)}
    {S : Specification (Interface.Resource A)} {T : Specification (Interface.Resource D)}
    {U : Specification (Interface.Resource C)}
    (left : Constructs α R S)
    (right : Constructs β T U) :
    Constructs (α ⊗ₘ β) (Specification.parallel R T)
      (Specification.parallel S U) :=
  left.parallel right

/-- Approximate parallel construction adds the errors. -/
example {α : A ⟶ B} {β : C ⟶ D} {R : Specification (Interface.Resource B)}
    {S : Specification (Interface.Resource A)} {T : Specification (Interface.Resource D)}
    {U : Specification (Interface.Resource C)} {ε δ : ENNReal}
    (left : ConstructsWithin α R S ε)
    (right : ConstructsWithin β T U δ) :
    ConstructsWithin (α ⊗ₘ β) (Specification.parallel R T)
      (Specification.parallel S U) (ε + δ) :=
  left.parallel right

/-- Closure under a class of converters that commute with the constructing one. -/
example {π : End A} {converters : EndoFamily A} {R S : Specification (Interface.Resource A)}
    (commutes : ∀ σ : End A, σ.op ∈ converters → ∀ T : Interface.Resource A,
      attach π (attach σ T) =
        attach σ (attach π T))
    (construction : Constructs π R S) :
    Constructs π (star converters R) (star converters S) :=
  Constructs.star commutes construction

/-- Approximate construction is preserved by the same closure. -/
example {π : End A} {converters : EndoFamily A} {R S : Specification (Interface.Resource A)}
    {ε : ENNReal}
    (commutes : ∀ σ : End A, σ.op ∈ converters → ∀ T : Interface.Resource A,
      attach π (attach σ T) =
        attach σ (attach π T))
    (construction : ConstructsWithin π R S ε) :
    ConstructsWithin π (star converters R) (star converters S) ε :=
  ConstructsWithin.star commutes construction

end ResourceSpecificationTests
