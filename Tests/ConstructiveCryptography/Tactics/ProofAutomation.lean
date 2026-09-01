/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import ConstructiveCryptography.Tactics.ProofAutomation

/-!
# Typed Constructive Cryptography proof-language tests

These examples exercise the deterministic proof commands solely through
`ResourceAlgebra`: heterogeneous interface objects, ordered parallel
composition, and explicit semantic witnesses.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ConstructiveCryptography.Categorical
open ConstructiveCryptography.Categorical.ResourceAlgebra
open ConstructiveCryptography.Categorical.ResourceAlgebra.Specification

namespace ConstructiveCryptography.Categorical.ResourceAlgebra.Tests.ProofAutomation

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
  cc_construct using equation

example (converter : A ⟶ B) (real : Resource Phi B)
    (ideal : Resource Phi A) (error : ENNReal)
    (bound : distance (Phi := Phi) (attach (Phi := Phi) converter real)
      ideal ≤ error) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({ideal} : Specification Phi A)) := by
  cc_construct using bound

example (converter : A ⟶ B) (source : Specification Phi B)
    (target : Specification Phi A) (error : ENNReal)
    (pointwise : ∀ resource ∈ source, ∃ ideal ∈ target,
      distance (Phi := Phi) (attach (Phi := Phi) converter resource)
        ideal ≤ error) :
    Constructs (Phi := Phi) converter source
      (epsilonRelaxation (Phi := Phi) error target) := by
  cc_construct using pointwise

example (converter : A ⟶ B) (real : Resource Phi B)
    (ideal : Resource Phi A) (error : ENNReal)
    (bound : distance (Phi := Phi) (attach (Phi := Phi) converter real)
      ideal ≤ error) :
    ConstructsWithin (Phi := Phi) converter
      ({real} : Specification Phi B) ({ideal} : Specification Phi A)
      error := by
  cc_construct using bound

example {left right : A ⟶ B} (same : left = right)
    (resource : Resource Phi B) :
    attach (Phi := Phi) left resource =
      attach (Phi := Phi) right resource := by
  cc_transport using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A} :
    Constructs (Phi := Phi) left source target ↔
      Constructs (Phi := Phi) right source target := by
  cc_transport using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    {error : ENNReal} :
    ConstructsWithin (Phi := Phi) left source target error ↔
      ConstructsWithin (Phi := Phi) right source target error := by
  cc_transport using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) left source target) :
    Constructs (Phi := Phi) right source target := by
  cc_transport construction using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) right source target) :
    Constructs (Phi := Phi) left source target := by
  cc_transport construction using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    {error : ENNReal}
    (construction : ConstructsWithin (Phi := Phi) left source target error) :
    ConstructsWithin (Phi := Phi) right source target error := by
  cc_transport construction using same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    {error : ENNReal}
    (construction : ConstructsWithin (Phi := Phi) right source target error) :
    ConstructsWithin (Phi := Phi) left source target error := by
  cc_transport construction using same

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
  cc_simulator simulator
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
  cc_filtered using commutes, simulatorAdmitted, equation

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
  cc_filtered using commutes, simulatorAdmitted, bound

end Simulator

section Serial

variable {A B D E : C}

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source middle)
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source target := by
  cc_compose inner, outer

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (epsilonRelaxation (Phi := Phi) innerError middle))
    (outer : Constructs (Phi := Phi) first middle
      (epsilonRelaxation (Phi := Phi) outerError target)) :
    Constructs (Phi := Phi) (first ≫ second) source
      (epsilonRelaxation (Phi := Phi) (innerError + outerError) target) := by
  cc_compose inner, outer

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : ConstructsWithin (Phi := Phi) second source middle innerError)
    (outer : ConstructsWithin (Phi := Phi) first middle target outerError) :
    ConstructsWithin (Phi := Phi) (first ≫ second) source target
      (innerError + outerError) := by
  cc_compose inner, outer

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
  cc_compose_simulators inner, outer using commutes

example {first : A ⟶ B} {second : B ⟶ D} {third : D ⟶ E}
    {source : Specification Phi E} {middleTwo : Specification Phi D}
    {middleOne : Specification Phi B} {target : Specification Phi A}
    (thirdLeg : Constructs (Phi := Phi) third source middleTwo)
    (secondLeg : Constructs (Phi := Phi) second middleTwo middleOne)
    (firstLeg : Constructs (Phi := Phi) first middleOne target) :
    Constructs (Phi := Phi) ((first ≫ second) ≫ third) source target := by
  cc_chain [thirdLeg, secondLeg, firstLeg]

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
  cc_chain [thirdLeg, secondLeg, firstLeg]

example {first : A ⟶ B} {second : B ⟶ D} {third : D ⟶ E}
    {source : Specification Phi E} {middleTwo : Specification Phi D}
    {middleOne : Specification Phi B} {target : Specification Phi A}
    {thirdError secondError firstError : ENNReal}
    (thirdLeg : ConstructsWithin (Phi := Phi) third source middleTwo thirdError)
    (secondLeg : ConstructsWithin (Phi := Phi) second middleTwo middleOne secondError)
    (firstLeg : ConstructsWithin (Phi := Phi) first middleOne target firstError) :
    ConstructsWithin (Phi := Phi) ((first ≫ second) ≫ third) source target
      ((thirdError + secondError) + firstError) := by
  cc_chain [thirdLeg, secondLeg, firstLeg]

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {error : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (epsilonRelaxation (Phi := Phi) error middle))
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source
      (epsilonRelaxation (Phi := Phi) error target) := by
  cc_relax using inner, outer with
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
  cc_parallel leftConstruction, rightConstruction

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
  cc_parallel leftConstruction, rightConstruction

example {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source target)
    (context : Specification Phi B) :
    Constructs (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) := by
  cc_context_left context using construction

example {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    {error : ENNReal} (context : Specification Phi A)
    (construction : ConstructsWithin (Phi := Phi) converter source target error) :
    ConstructsWithin (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) error := by
  cc_context_right context using construction

example {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    (context : Specification Phi A)
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) := by
  cc_context_right context using construction

example {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    {error : ENNReal}
    (construction : ConstructsWithin (Phi := Phi) converter source target error)
    (context : Specification Phi B) :
    ConstructsWithin (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) error := by
  cc_context_left context using construction

example {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    {error : ENNReal} (context : Specification Phi A)
    (construction : Constructs (Phi := Phi) converter source
      (epsilonRelaxation (Phi := Phi) error target)) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (epsilonRelaxation (Phi := Phi) error
        (Specification.parallel (Phi := Phi) context target)) := by
  cc_context_right context using construction

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
  cc_context_left context using construction

end Parallel

section Distance

variable {A B : C}

example (left middle right : Resource Phi A)
    (firstError secondError : ENNReal)
    (firstBound : distance (Phi := Phi) left middle ≤ firstError)
    (secondBound : distance (Phi := Phi) middle right ≤ secondError) :
    distance (Phi := Phi) left right ≤ firstError + secondError := by
  cc_triangle via middle
  · exact firstBound
  · exact secondBound

example (converter : A ⟶ B) (left right : Resource Phi B) :
    distance (Phi := Phi)
      (attach (Phi := Phi) converter left)
      (attach (Phi := Phi) converter right) ≤
        distance (Phi := Phi) left right := by
  cc_nonexpand

example (left left' : Resource Phi A) (right right' : Resource Phi B) :
    distance (Phi := Phi)
      (ResourceAlgebra.parallel (Phi := Phi) left right)
      (ResourceAlgebra.parallel (Phi := Phi) left' right') ≤
        distance (Phi := Phi) left left' +
          distance (Phi := Phi) right right' := by
  cc_nonexpand

example (left left' : Resource Phi A) (right : Resource Phi B) :
    distance (Phi := Phi)
      (ResourceAlgebra.parallel (Phi := Phi) left right)
      (ResourceAlgebra.parallel (Phi := Phi) left' right) ≤
        distance (Phi := Phi) left left' := by
  cc_nonexpand

example (left : Resource Phi A) (right right' : Resource Phi B) :
    distance (Phi := Phi)
      (ResourceAlgebra.parallel (Phi := Phi) left right)
      (ResourceAlgebra.parallel (Phi := Phi) left right') ≤
        distance (Phi := Phi) right right' := by
  cc_nonexpand

end Distance

section Tuple

open ConstructiveCryptography.Categorical.ResourceAlgebra.Finite

variable {n : Nat} {interfaces : Fin n → C}

example (left right : ConverterTuple interfaces)
    (leftParties rightParties : Set (Fin n))
    (disjoint : Disjoint leftParties rightParties) :
    ConverterTuple.converter (ConverterTuple.partial left leftParties) ≫
        ConverterTuple.converter (ConverterTuple.partial right rightParties) =
      ConverterTuple.converter (ConverterTuple.partial right rightParties) ≫
        ConverterTuple.converter (ConverterTuple.partial left leftParties) := by
  cc_commute using disjoint

end Tuple

section Normalization

variable {A B D : C}

example (first : A ⟶ B) (second : B ⟶ D)
    (resource : Resource Phi D) :
    attach (Phi := Phi) (first ≫ second) resource =
      attach (Phi := Phi) first
        (attach (Phi := Phi) second resource) := by
  cc_normalize

example (error bound : ENNReal) (included : error ≤ bound) :
    error + 0 ≤ bound := by
  cc_routine

end Normalization

/-! The following checks keep diagnostics bounded and terminology stable. -/

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source middle)
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source target := by
  cc_compose inner, outer

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (epsilonRelaxation (Phi := Phi) innerError middle))
    (outer : Constructs (Phi := Phi) first middle
      (epsilonRelaxation (Phi := Phi) outerError target)) :
    Constructs (Phi := Phi) (first ≫ second) source
      (epsilonRelaxation (Phi := Phi) (innerError + outerError) target) := by
  cc_compose inner, outer

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {innerError outerError : ENNReal}
    (inner : ConstructsWithin (Phi := Phi) second source middle innerError)
    (outer : ConstructsWithin (Phi := Phi) first middle target outerError) :
    ConstructsWithin (Phi := Phi) (first ≫ second) source target
      (innerError + outerError) := by
  cc_compose inner, outer

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
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
  cc_parallel leftConstruction, rightConstruction

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
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
  cc_parallel leftConstruction, rightConstruction

/-- info: Categorical CC rule candidates (goal unchanged): -/
#guard_msgs (substring := true) in
set_option linter.unusedTactic false in
example {A B : C} (converter : A ⟶ B)
    (real : Resource Phi B) (ideal : Resource Phi A)
    (equation : attach (Phi := Phi) converter real = ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  cc?
  exact constructs_singleton_iff.mpr equation

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.attach_eq_of_converter_eq -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A B : C} {left right : A ⟶ B} (same : left = right)
    (resource : Resource Phi B) :
    attach (Phi := Phi) left resource =
      attach (Phi := Phi) right resource := by
  cc_transport using same

/-- error: cc_transport expected attachment equality or construction equivalence induced by the supplied converter equality -/
#guard_msgs (substring := true) in
example {A B : C} {left right : A ⟶ B} (same : left = right) : True := by
  cc_transport using same

/-- error: cc_transport could not replace the converter in the supplied construction using the supplied equality -/
#guard_msgs (substring := true) in
example {A B : C} (converter : A ⟶ B)
    {source source' : Specification Phi B} {target : Specification Phi A}
    (sameSource : source = source')
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) converter source' target := by
  cc_transport construction using sameSource

/-- error: cc_nonexpand expected a converter-attachment or ordered-parallel distance goal -/
#guard_msgs (substring := true) in
example : True := by
  cc_nonexpand

/-- error: cc_compose expected two composable typed construction proofs -/
#guard_msgs (substring := true) in
example (firstFact secondFact : True) : True := by
  cc_compose firstFact, secondFact

/-- error: cc_parallel expected two typed constructions for ordered parallel composition -/
#guard_msgs (substring := true) in
example (leftFact rightFact : True) : True := by
  cc_parallel leftFact, rightFact

/-- error: cc_filtered expected a filtered-endpoint construction and matching commutation, simulator-membership, and equality or distance proofs -/
#guard_msgs (substring := true) in
example : True := by
  cc_filtered using True.intro, True.intro, True.intro

/-- error: cc_chain requires at least two named construction proofs -/
#guard_msgs (substring := true) in
example (fact : True) : True := by
  cc_chain [fact]

/-! ## Direct command contracts

Every exported command has a successful firing site and a bounded failure
site. Commands that report a selected theorem also have a stable rule trace.
-/

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] direct exact rule -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example (proposition : Prop) (proof : proposition) : proposition := by
  cc_exact_rule "direct exact rule" => proof

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
example (proof : True) : False := by
  cc_exact_rule "ill-typed direct rule" => proof

example {A B : C} (converter : A ⟶ B)
    (real : Resource Phi B) (ideal : Resource Phi A)
    (equation : attach (Phi := Phi) converter real = ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  cc_construct
  exact equation

/-- error: cc_construct expected a typed singleton or scalar-error construction goal -/
#guard_msgs (substring := true) in
example : True := by
  cc_construct

/-- error: cc_construct could not use the supplied equality, distance bound, or pointwise proof -/
#guard_msgs (substring := true) in
example (irrelevantFact : True) : True := by
  cc_construct using irrelevantFact

/-- trace: [Meta.Tactic.simp.rewrite] attach_serial -/
#guard_msgs (substring := true) in
example {A B D : C} (first : A ⟶ B) (second : B ⟶ D)
    (resource : Resource Phi D) (ideal : Resource Phi A)
    (equation : attach (Phi := Phi) (first ≫ second) resource = ideal) :
    attach (Phi := Phi) first (attach (Phi := Phi) second resource) = ideal := by
  cc_normalize? at equation
  exact equation

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example {A : C} (left right : Resource Phi A) : left = right := by
  cc_normalize

/-- error: unsolved goals -/
#guard_msgs (substring := true) in
example {A : C} (left right : Resource Phi A) : left = right := by
  cc_normalize?

/-- error: cc_routine could not close the goal with assumptions or the curated CC registries -/
#guard_msgs (substring := true) in
example : False := by
  cc_routine

/-- error: cc_simulator expected a typed singleton construction into the scalar relaxation of a star specification -/
#guard_msgs (substring := true) in
example {A : C} (simulator : A ⟶ A) : True := by
  cc_simulator simulator

/-- error: cc_relax could not apply the typed serial relaxation theorem to the supplied constructions and compatibility proof -/
#guard_msgs (substring := true) in
example (inner outer compatibility : True) : True := by
  cc_relax using inner, outer with compatibility

/-- error: cc_triangle expected a typed resource-distance goal with an additive bound -/
#guard_msgs (substring := true) in
example {A : C} (intermediate : Resource Phi A) : True := by
  cc_triangle via intermediate

/-- error: cc_commute expected assembled partial converter tuples and explicit disjointness -/
#guard_msgs (substring := true) in
example (disjoint : True) : True := by
  cc_commute using disjoint

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_simulators -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
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
  cc_compose_simulators inner, outer using commutes

/-- error: cc_compose_simulators expected two typed simulator-target constructions and an explicit composition-order commutation equality -/
#guard_msgs (substring := true) in
example (inner outer commutes : True) : True := by
  cc_compose_simulators inner, outer using commutes

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.left_context -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A A' B : C} {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source target)
    (context : Specification Phi B) :
    Constructs (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) := by
  cc_context_left context using construction

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.right_context -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A B B' : C} {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    (construction : Constructs (Phi := Phi) converter source target)
    (context : Specification Phi A) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) := by
  cc_context_right context using construction

/-- error: cc_context_left expected a typed construction and a fixed right specification context -/
#guard_msgs (substring := true) in
example (context construction : True) : True := by
  cc_context_left context using construction

/-- error: cc_context_right expected a typed construction and a fixed left specification context -/
#guard_msgs (substring := true) in
example (context construction : True) : True := by
  cc_context_right context using construction

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] replace converter in exact construction, left-to-right -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A B : C} {left right : A ⟶ B}
    {source : Specification Phi B} {target : Specification Phi A}
    (same : left = right)
    (construction : Constructs (Phi := Phi) left source target) :
    Constructs (Phi := Phi) right source target := by
  cc_transport construction using same

/-- trace: [ConstructiveCryptography.ProofAutomation.rule] ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc -/
#guard_msgs in
set_option trace.ConstructiveCryptography.ProofAutomation.rule true in
example {A B D E : C} {first : A ⟶ B} {second : B ⟶ D}
    {third : D ⟶ E}
    {source : Specification Phi E} {middleTwo : Specification Phi D}
    {middleOne : Specification Phi B} {target : Specification Phi A}
    (thirdLeg : Constructs (Phi := Phi) third source middleTwo)
    (secondLeg : Constructs (Phi := Phi) second middleTwo middleOne)
    (firstLeg : Constructs (Phi := Phi) first middleOne target) :
    Constructs (Phi := Phi) ((first ≫ second) ≫ third) source target := by
  cc_chain [thirdLeg, secondLeg, firstLeg]

/-- error: cc_chain could not compose the supplied typed construction proofs -/
#guard_msgs (substring := true) in
set_option linter.unusedVariables false in
set_option linter.unnecessarySimpa false in
example (firstFact secondFact : True) : False := by
  cc_chain [firstFact, secondFact]

/-- info: No categorical CC rule in the bounded diagnostic table matches this goal. -/
#guard_msgs in
set_option linter.unusedTactic false in
example (proposition : Prop) (proof : proposition) : proposition := by
  cc?
  exact proof

end ConstructiveCryptography.Categorical.ResourceAlgebra.Tests.ProofAutomation
