/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ProofAutomation

/-!
# Typed Abstract Cryptography proof-language tests

These examples exercise the deterministic proof commands solely through
`ResourceAlgebra`: heterogeneous interface objects, ordered parallel
composition, and explicit semantic witnesses.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open AbstractCryptography.Categorical.ResourceAlgebra.Specification

namespace AbstractCryptography.Categorical.ResourceAlgebra.ProofAutomation.Tests

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

section Construction

variable {A B : C}

example (converter : A ⟶ B) (real : Resource Phi B)
    (ideal : Resource Phi A)
    (equation : attach (Phi := Phi) converter real = ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  ac_construct using equation

example (converter : A ⟶ B) (real : Resource Phi B)
    (ideal : Resource Phi A) (error : ENNReal)
    (bound : distance (Phi := Phi) (attach (Phi := Phi) converter real)
      ideal ≤ error) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({ideal} : Specification Phi A)) := by
  ac_construct using bound

example (converter : A ⟶ B) (source : Specification Phi B)
    (target : Specification Phi A) (error : ENNReal)
    (pointwise : ∀ resource ∈ source, ∃ ideal ∈ target,
      distance (Phi := Phi) (attach (Phi := Phi) converter resource)
        ideal ≤ error) :
    Constructs (Phi := Phi) converter source
      (epsilonRelaxation (Phi := Phi) error target) := by
  ac_construct using pointwise

example (converter : A ⟶ B) (real : Resource Phi B)
    (ideal : Resource Phi A) (error : ENNReal)
    (bound : distance (Phi := Phi) (attach (Phi := Phi) converter real)
      ideal ≤ error) :
    ConstructsWithin (Phi := Phi) converter
      ({real} : Specification Phi B) ({ideal} : Specification Phi A)
      error := by
  ac_construct using bound

example {left right : A ⟶ B} (same : left = right)
    (resource : Resource Phi B) :
    attach (Phi := Phi) left resource =
      attach (Phi := Phi) right resource := by
  ac_transport using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A} :
    Constructs (Phi := Phi) left source target ↔
      Constructs (Phi := Phi) right source target := by
  ac_transport using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    {error : ENNReal} :
    ConstructsWithin (Phi := Phi) left source target error ↔
      ConstructsWithin (Phi := Phi) right source target error := by
  ac_transport using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) left source target) :
    Constructs (Phi := Phi) right source target := by
  ac_transport construction using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) right source target) :
    Constructs (Phi := Phi) left source target := by
  ac_transport construction using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    {error : ENNReal}
    (construction : ConstructsWithin (Phi := Phi) left source target error) :
    ConstructsWithin (Phi := Phi) right source target error := by
  ac_transport construction using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    {error : ENNReal}
    (construction : ConstructsWithin (Phi := Phi) right source target error) :
    ConstructsWithin (Phi := Phi) left source target error := by
  ac_transport construction using same

end Construction

section Simulator

variable {A B : C}

example (converter : A ⟶ B) (simulator : A ⟶ A)
    (converters : EndoFamily (Opposite.op A))
    (real : Resource Phi B) (ideal : Resource Phi A) (error : ENNReal)
    (simulatorAdmitted : simulator.op ∈ converters)
    (bound : distance (Phi := Phi)
      (attach (Phi := Phi) converter real)
      (attach (Phi := Phi) simulator ideal) ≤ error) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        (star (Phi := Phi) converters
          ({ideal} : Specification Phi A))) := by
  ac_simulator simulator
  · exact simulatorAdmitted
  · exact bound

example (converters : EndoFamily (Opposite.op A))
    (converter sourceFilter targetFilter simulator : A ⟶ A)
    (real ideal : Resource Phi A)
    (commutes : ∀ classConverter : A ⟶ A,
      classConverter.op ∈ converters →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (simulatorAdmitted : simulator.op ∈ converters)
    (equation :
      attach (Phi := Phi) converter
          (attach (Phi := Phi) sourceFilter real) =
        attach (Phi := Phi) simulator
          (attach (Phi := Phi) targetFilter ideal)) :
    Constructs (Phi := Phi) converter
      (filteredAt (Phi := Phi) converters sourceFilter real)
      (filteredAt (Phi := Phi) converters targetFilter ideal) := by
  ac_filtered using commutes, simulatorAdmitted, equation

example (converters : EndoFamily (Opposite.op A))
    (converter sourceFilter targetFilter simulator : A ⟶ A)
    (real ideal : Resource Phi A) (error : ENNReal)
    (commutes : ∀ classConverter : A ⟶ A,
      classConverter.op ∈ converters →
        ∀ resource : Resource Phi A,
          attach (Phi := Phi) converter
              (attach (Phi := Phi) classConverter resource) =
            attach (Phi := Phi) classConverter
              (attach (Phi := Phi) converter resource))
    (simulatorAdmitted : simulator.op ∈ converters)
    (bound : distance (Phi := Phi)
      (attach (Phi := Phi) converter
        (attach (Phi := Phi) sourceFilter real))
      (attach (Phi := Phi) simulator
        (attach (Phi := Phi) targetFilter ideal)) ≤ error) :
    Constructs (Phi := Phi) converter
      (filteredAt (Phi := Phi) converters sourceFilter real)
      (epsilonRelaxation (Phi := Phi) error
        (filteredAt (Phi := Phi) converters targetFilter ideal)) := by
  ac_filtered using commutes, simulatorAdmitted, bound

end Simulator

section Serial

variable {A B D E : C}

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source middle)
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source target := by
  ac_compose inner, outer

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (epsilonRelaxation (Phi := Phi) innerError middle))
    (outer : Constructs (Phi := Phi) first middle
      (epsilonRelaxation (Phi := Phi) outerError target)) :
    Constructs (Phi := Phi) (first ≫ second) source
      (epsilonRelaxation (Phi := Phi) (innerError + outerError) target) := by
  ac_compose inner, outer

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : ConstructsWithin (Phi := Phi) second source middle innerError)
    (outer : ConstructsWithin (Phi := Phi) first middle target outerError) :
    ConstructsWithin (Phi := Phi) (first ≫ second) source target
      (innerError + outerError) := by
  ac_compose inner, outer

example {first : A ⟶ B} {second : B ⟶ D}
    {innerSimulator : B ⟶ B}
    {transportedSimulator outerSimulator : A ⟶ A}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source
      (map (Phi := Phi) innerSimulator middle))
    (outer : Constructs (Phi := Phi) first middle
      (map (Phi := Phi) outerSimulator target))
    (commutes : first ≫ innerSimulator = transportedSimulator ≫ first) :
    Constructs (Phi := Phi) (first ≫ second) source
      (map (Phi := Phi) (transportedSimulator ≫ outerSimulator) target) := by
  ac_compose_simulators inner, outer using commutes

example {first : A ⟶ B} {second : B ⟶ D} {third : D ⟶ E}
    {source : Specification Phi E} {middleTwo : Specification Phi D}
    {middleOne : Specification Phi B} {target : Specification Phi A}
    (thirdLeg : Constructs (Phi := Phi) third source middleTwo)
    (secondLeg : Constructs (Phi := Phi) second middleTwo middleOne)
    (firstLeg : Constructs (Phi := Phi) first middleOne target) :
    Constructs (Phi := Phi) ((first ≫ second) ≫ third) source target := by
  ac_chain [thirdLeg, secondLeg, firstLeg]

example {first : A ⟶ B} {second : B ⟶ D} {third : D ⟶ E}
    {source : Specification Phi E} {middleTwo : Specification Phi D}
    {middleOne : Specification Phi B} {target : Specification Phi A}
    {thirdError secondError firstError : ENNReal}
    (thirdLeg : Constructs (Phi := Phi) third source
      (epsilonRelaxation (Phi := Phi) thirdError middleTwo))
    (secondLeg : Constructs (Phi := Phi) second middleTwo
      (epsilonRelaxation (Phi := Phi) secondError middleOne))
    (firstLeg : Constructs (Phi := Phi) first middleOne
      (epsilonRelaxation (Phi := Phi) firstError target)) :
    Constructs (Phi := Phi) ((first ≫ second) ≫ third) source
      (epsilonRelaxation (Phi := Phi)
        ((thirdError + secondError) + firstError) target) := by
  ac_chain [thirdLeg, secondLeg, firstLeg]

example {first : A ⟶ B} {second : B ⟶ D} {third : D ⟶ E}
    {source : Specification Phi E} {middleTwo : Specification Phi D}
    {middleOne : Specification Phi B} {target : Specification Phi A}
    {thirdError secondError firstError : ENNReal}
    (thirdLeg : ConstructsWithin (Phi := Phi) third source middleTwo thirdError)
    (secondLeg : ConstructsWithin (Phi := Phi) second middleTwo middleOne secondError)
    (firstLeg : ConstructsWithin (Phi := Phi) first middleOne target firstError) :
    ConstructsWithin (Phi := Phi) ((first ≫ second) ≫ third) source target
      ((thirdError + secondError) + firstError) := by
  ac_chain [thirdLeg, secondLeg, firstLeg]

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {error : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (epsilonRelaxation (Phi := Phi) error middle))
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source
      (epsilonRelaxation (Phi := Phi) error target) := by
  ac_relax using inner, outer with
    epsilonRelaxation_compatible (Phi := Phi) error

end Serial

section Parallel

variable {A A' B B' : C}

example {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : Specification Phi A'} {leftTarget : Specification Phi A}
    {rightSource : Specification Phi B'} {rightTarget : Specification Phi B}
    (leftConstruction : Constructs (Phi := Phi) leftConverter
      leftSource leftTarget)
    (rightConstruction : Constructs (Phi := Phi) rightConverter
      rightSource rightTarget) :
    Constructs (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
      (Specification.parallel (Phi := Phi) leftSource rightSource)
      (Specification.parallel (Phi := Phi) leftTarget rightTarget) := by
  ac_parallel leftConstruction, rightConstruction

example {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : Specification Phi A'} {leftTarget : Specification Phi A}
    {rightSource : Specification Phi B'} {rightTarget : Specification Phi B}
    {leftError rightError : ENNReal}
    (leftConstruction : ConstructsWithin (Phi := Phi) leftConverter
      leftSource leftTarget leftError)
    (rightConstruction : ConstructsWithin (Phi := Phi) rightConverter
      rightSource rightTarget rightError) :
    ConstructsWithin (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
      (Specification.parallel (Phi := Phi) leftSource rightSource)
      (Specification.parallel (Phi := Phi) leftTarget rightTarget)
      (leftError + rightError) := by
  ac_parallel leftConstruction, rightConstruction

example {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source target)
    (context : Specification Phi B) :
    Constructs (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) := by
  ac_context_left context using construction

example {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    {error : ENNReal} (context : Specification Phi A)
    (construction : ConstructsWithin (Phi := Phi) converter source target error) :
    ConstructsWithin (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) error := by
  ac_context_right context using construction

example {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    (context : Specification Phi A)
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) := by
  ac_context_right context using construction

example {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    {error : ENNReal}
    (construction : ConstructsWithin (Phi := Phi) converter source target error)
    (context : Specification Phi B) :
    ConstructsWithin (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) error := by
  ac_context_left context using construction

example {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    {error : ENNReal} (context : Specification Phi A)
    (construction : Constructs (Phi := Phi) converter source
      (epsilonRelaxation (Phi := Phi) error target)) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (epsilonRelaxation (Phi := Phi) error
        (Specification.parallel (Phi := Phi) context target)) := by
  ac_context_right context using construction

example {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    {error : ENNReal}
    (construction : Constructs (Phi := Phi) converter source
      (epsilonRelaxation (Phi := Phi) error target))
    (context : Specification Phi B) :
    Constructs (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (epsilonRelaxation (Phi := Phi) error
        (Specification.parallel (Phi := Phi) target context)) := by
  ac_context_left context using construction

end Parallel

section Distance

variable {A B : C}

example (left middle right : Resource Phi A)
    (firstError secondError : ENNReal)
    (firstBound : distance (Phi := Phi) left middle ≤ firstError)
    (secondBound : distance (Phi := Phi) middle right ≤ secondError) :
    distance (Phi := Phi) left right ≤ firstError + secondError := by
  ac_triangle via middle
  · exact firstBound
  · exact secondBound

example (converter : A ⟶ B) (left right : Resource Phi B) :
    distance (Phi := Phi)
      (attach (Phi := Phi) converter left)
      (attach (Phi := Phi) converter right) ≤
        distance (Phi := Phi) left right := by
  ac_nonexpand

example (left left' : Resource Phi A) (right right' : Resource Phi B) :
    distance (Phi := Phi)
      (ResourceAlgebra.parallel (Phi := Phi) left right)
      (ResourceAlgebra.parallel (Phi := Phi) left' right') ≤
        distance (Phi := Phi) left left' +
          distance (Phi := Phi) right right' := by
  ac_nonexpand

example (left left' : Resource Phi A) (right : Resource Phi B) :
    distance (Phi := Phi)
      (ResourceAlgebra.parallel (Phi := Phi) left right)
      (ResourceAlgebra.parallel (Phi := Phi) left' right) ≤
        distance (Phi := Phi) left left' := by
  ac_nonexpand

example (left : Resource Phi A) (right right' : Resource Phi B) :
    distance (Phi := Phi)
      (ResourceAlgebra.parallel (Phi := Phi) left right)
      (ResourceAlgebra.parallel (Phi := Phi) left right') ≤
        distance (Phi := Phi) right right' := by
  ac_nonexpand

end Distance

section Tuple

open AbstractCryptography.Categorical.ResourceAlgebra.Finite

variable {n : Nat} {interfaces : Fin n → C}

example (left right : ConverterTuple interfaces)
    (leftParties rightParties : Set (Fin n))
    (disjoint : Disjoint leftParties rightParties) :
    ConverterTuple.converter (ConverterTuple.partial left leftParties) ≫
        ConverterTuple.converter (ConverterTuple.partial right rightParties) =
      ConverterTuple.converter (ConverterTuple.partial right rightParties) ≫
        ConverterTuple.converter (ConverterTuple.partial left leftParties) := by
  ac_commute using disjoint

end Tuple

section Normalization

variable {A B D : C}

example (first : A ⟶ B) (second : B ⟶ D)
    (resource : Resource Phi D) :
    attach (Phi := Phi) (first ≫ second) resource =
      attach (Phi := Phi) first
        (attach (Phi := Phi) second resource) := by
  ac_normalize

example (error bound : ENNReal) (included : error ≤ bound) :
    error + 0 ≤ bound := by
  ac_routine

end Normalization

/-! The following checks keep diagnostics bounded and terminology stable. -/

/-- trace: [AbstractCryptography.ProofAutomation.rule] AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial -/
#guard_msgs in
set_option trace.AbstractCryptography.ProofAutomation.rule true in
example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source middle)
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source target := by
  ac_compose inner, outer

/-- trace: [AbstractCryptography.ProofAutomation.rule] AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation -/
#guard_msgs in
set_option trace.AbstractCryptography.ProofAutomation.rule true in
example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (epsilonRelaxation (Phi := Phi) innerError middle))
    (outer : Constructs (Phi := Phi) first middle
      (epsilonRelaxation (Phi := Phi) outerError target)) :
    Constructs (Phi := Phi) (first ≫ second) source
      (epsilonRelaxation (Phi := Phi) (innerError + outerError) target) := by
  ac_compose inner, outer

/-- trace: [AbstractCryptography.ProofAutomation.rule] AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial -/
#guard_msgs in
set_option trace.AbstractCryptography.ProofAutomation.rule true in
example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : ConstructsWithin (Phi := Phi) second source middle innerError)
    (outer : ConstructsWithin (Phi := Phi) first middle target outerError) :
    ConstructsWithin (Phi := Phi) (first ≫ second) source target
      (innerError + outerError) := by
  ac_compose inner, outer

/-- trace: [AbstractCryptography.ProofAutomation.rule] AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel -/
#guard_msgs in
set_option trace.AbstractCryptography.ProofAutomation.rule true in
example {A A' B B' : C}
    {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : Specification Phi A'} {leftTarget : Specification Phi A}
    {rightSource : Specification Phi B'} {rightTarget : Specification Phi B}
    (leftConstruction : Constructs (Phi := Phi) leftConverter
      leftSource leftTarget)
    (rightConstruction : Constructs (Phi := Phi) rightConverter
      rightSource rightTarget) :
    Constructs (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
      (Specification.parallel (Phi := Phi) leftSource rightSource)
      (Specification.parallel (Phi := Phi) leftTarget rightTarget) := by
  ac_parallel leftConstruction, rightConstruction

/-- trace: [AbstractCryptography.ProofAutomation.rule] AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel -/
#guard_msgs in
set_option trace.AbstractCryptography.ProofAutomation.rule true in
example {A A' B B' : C}
    {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : Specification Phi A'} {leftTarget : Specification Phi A}
    {rightSource : Specification Phi B'} {rightTarget : Specification Phi B}
    {leftError rightError : ENNReal}
    (leftConstruction : ConstructsWithin (Phi := Phi) leftConverter
      leftSource leftTarget leftError)
    (rightConstruction : ConstructsWithin (Phi := Phi) rightConverter
      rightSource rightTarget rightError) :
    ConstructsWithin (Phi := Phi) (leftConverter ⊗ₘ rightConverter)
      (Specification.parallel (Phi := Phi) leftSource rightSource)
      (Specification.parallel (Phi := Phi) leftTarget rightTarget)
      (leftError + rightError) := by
  ac_parallel leftConstruction, rightConstruction

/-- info: Categorical AC rule candidates (goal unchanged): -/
#guard_msgs (substring := true) in
set_option linter.unusedTactic false in
example {A B : C} (converter : A ⟶ B)
    (real : Resource Phi B) (ideal : Resource Phi A)
    (equation : attach (Phi := Phi) converter real = ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  ac?
  exact constructs_singleton_iff.mpr equation

/-- trace: [AbstractCryptography.ProofAutomation.rule] AbstractCryptography.Categorical.ResourceAlgebra.Specification.attach_eq_of_converter_eq -/
#guard_msgs in
set_option trace.AbstractCryptography.ProofAutomation.rule true in
example {A B : C} {left right : A ⟶ B} (same : left = right)
    (resource : Resource Phi B) :
    attach (Phi := Phi) left resource =
      attach (Phi := Phi) right resource := by
  ac_transport using same

/-- error: ac_transport expected attachment equality or construction equivalence induced by the supplied converter equality -/
#guard_msgs (substring := true) in
example {A B : C} {left right : A ⟶ B} (same : left = right) : True := by
  ac_transport using same

/-- error: ac_transport could not replace the converter in the supplied construction using the supplied equality -/
#guard_msgs (substring := true) in
example {A B : C} (converter : A ⟶ B)
    {source source' : Specification Phi B} {target : Specification Phi A}
    (sameSource : source = source')
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) converter source' target := by
  ac_transport construction using sameSource

/-- error: ac_nonexpand expected a converter-attachment or ordered-parallel distance goal -/
#guard_msgs (substring := true) in
example : True := by
  ac_nonexpand

/-- error: ac_compose expected two composable typed construction proofs -/
#guard_msgs (substring := true) in
example (firstFact secondFact : True) : True := by
  ac_compose firstFact, secondFact

/-- error: ac_parallel expected two typed constructions for ordered parallel composition -/
#guard_msgs (substring := true) in
example (leftFact rightFact : True) : True := by
  ac_parallel leftFact, rightFact

/-- error: ac_filtered expected a filtered-endpoint construction and matching commutation, simulator-membership, and equality or distance proofs -/
#guard_msgs (substring := true) in
example : True := by
  ac_filtered using True.intro, True.intro, True.intro

/-- error: ac_chain requires at least two named construction proofs -/
#guard_msgs (substring := true) in
example (fact : True) : True := by
  ac_chain [fact]

end AbstractCryptography.Categorical.ResourceAlgebra.ProofAutomation.Tests
