import Verbose
import Verbose.AbstractCryptography

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open AbstractCryptography.Categorical.ResourceAlgebra.Specification
open scoped CryptoVerbose

namespace CryptoLanguage.Verbose.Tests.AbstractCryptography

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w} [ResourceAlgebra C Phi]

section Construction

variable {A B D : C}

example (converter : A ⟶ B) (real : Resource Phi B)
    (ideal : Resource Phi A)
    (equation : attach (Phi := Phi) converter real = ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  The construction follows from equation

example (converter : A ⟶ B) (real : Resource Phi B)
    (ideal : Resource Phi A) (error : ENNReal)
    (bound : distance (Phi := Phi) (attach (Phi := Phi) converter real)
      ideal ≤ error) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      (epsilonRelaxation (Phi := Phi) error
        ({ideal} : Specification Phi A)) := by
  The construction follows from bound noted "the quantitative leg"

example {left right : A ⟶ B} (same : left = right)
    (resource : Resource Phi B) :
    attach (Phi := Phi) left resource =
      attach (Phi := Phi) right resource := by
  The equality follows from same

example {left right : A ⟶ B} (same : left = right)
    {source : Specification Phi B} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) left source target) :
    Constructs (Phi := Phi) right source target := by
  Replacing the converter in construction using same,
    we obtain the required construction

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A}
    (inner : Constructs (Phi := Phi) second source middle)
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source target := by
  The construction follows by composing inner and outer

example {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification Phi D} {middle : Specification Phi B}
    {target : Specification Phi A} {error : ENNReal}
    (inner : Constructs (Phi := Phi) second source
      (epsilonRelaxation (Phi := Phi) error middle))
    (outer : Constructs (Phi := Phi) first middle target) :
    Constructs (Phi := Phi) (first ≫ second) source
      (epsilonRelaxation (Phi := Phi) error target) := by
  have compatibility : Relaxation.Compatible (C := C) (Phi := Phi)
      (fun (A : C) => epsilonRelaxation (Phi := Phi) (A := A) error) :=
    epsilonRelaxation_compatible (C := C) (Phi := Phi) error
  The construction follows by relaxing inner through outer using compatibility

end Construction

section SimulatorAndFiltering

variable {A B : C}

/-- trace: [CryptoLanguage.Verbose.sentence] ac.construction.simulator -/
#guard_msgs in
set_option trace.CryptoLanguage.Verbose.sentence true in
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
  We use simulator noted "the explicit simulator" to prove the construction
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
  The filtered construction follows from equation using commutes and
    simulatorAdmitted

end SimulatorAndFiltering

section SerialAndParallel

variable {A B D A' B' : C}

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
  The construction follows by composing the simulators in inner and outer
    using commutes

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
  The construction follows in parallel from leftConstruction and
    rightConstruction

example {converter : A ⟶ A'}
    {source : Specification Phi A'} {target : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source target)
    (context : Specification Phi B) :
    Constructs (Phi := Phi) (converter ⊗ₘ 𝟙 B)
      (Specification.parallel (Phi := Phi) source context)
      (Specification.parallel (Phi := Phi) target context) := by
  With context as the right parallel context,
    the construction follows from construction

example {converter : B ⟶ B'}
    {source : Specification Phi B'} {target : Specification Phi B}
    (context : Specification Phi A)
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) (𝟙 A ⊗ₘ converter)
      (Specification.parallel (Phi := Phi) context source)
      (Specification.parallel (Phi := Phi) context target) := by
  With context as the left parallel context,
    the construction follows from construction

end SerialAndParallel

section Distance

variable {A : C}

example (real middle ideal : Resource Phi A) (firstError secondError : ENNReal)
    (first : distance (Phi := Phi) real middle ≤ firstError)
    (second : distance (Phi := Phi) middle ideal ≤ secondError) :
    distance (Phi := Phi) real ideal ≤ firstError + secondError := by
  The distance bound follows through middle using first and second

example (real middle ideal : Resource Phi A)
    (firstError secondError : ENNReal)
    (first : distance (Phi := Phi) real middle ≤ firstError)
    (second : distance (Phi := Phi) middle ideal ≤ secondError) :
    distance (Phi := Phi) real ideal ≤ firstError + secondError := by
  To prove the distance bound, apply the triangle inequality through middle
  · exact first
  · exact second

end Distance

/-- trace: [CryptoLanguage.Verbose.sentence] ac.construction.fromProof -/
#guard_msgs in
set_option trace.CryptoLanguage.Verbose.sentence true in
example {A B : C} (converter : A ⟶ B) (real : Resource Phi B)
    (ideal : Resource Phi A)
    (equation : attach (Phi := Phi) converter real = ideal) :
    Constructs (Phi := Phi) converter ({real} : Specification Phi B)
      ({ideal} : Specification Phi A) := by
  The construction follows from equation

/- error: This sentence cannot establish -/
#guard_msgs (substring := true) in
example (firstFact secondFact : True) : True := by
  The construction follows by composing firstFact and secondFact

end CryptoLanguage.Verbose.Tests.AbstractCryptography
