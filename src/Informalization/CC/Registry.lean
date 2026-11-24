/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import ConstructiveCryptography.Notation.Basic
import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import ConstructiveCryptography.CryptographicAlgebra.Distinguisher
import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction
import ConstructiveCryptography.CryptographicAlgebra.Epsilon
import ConstructiveCryptography.CryptographicAlgebra.Star
import ConstructiveCryptography.CryptographicAlgebra.SimulatorComposition
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
import ConstructiveCryptography.CryptographicAlgebra.Game
import ConstructiveCryptography.Substitution.Basic
import ConstructiveCryptography.Substitution.Implication
import ConstructiveCryptography.Substitution.Reduction
import ConstructiveCryptography.Instances.Algebra
import ConstructiveCryptography.Instances.Game
import ConstructiveCryptography.Instances.Substitution
import RandomSystems.Distance.HCoefficient
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Distance.UntilBad
import RandomSystems.Game.MBO
import RandomSystems.Game.UntilBad
import RandomSystems.Typed.Interface
import RandomSystems.Typed.Parallel
import RandomSystems.Typed.Context
import RandomSystems.Typed.Game
import RandomSystems.Typed.Distinguisher
import RandomSystems.Typed.Solver

/-!
# Compile-Time-Checked Constructive Cryptography Constant Registry

Resolves every core Constructive Cryptography and Random Systems declaration name at
compile time using double-backtick quotations (`` ``FullName ``). Any upstream rename,
namespace change, or deletion fails the build immediately instead of silently degrading
presentation or proof explanation.
-/

namespace Informalization.CC.Registry

open Lean Meta

/-! ## 1. Categorical & Resource-Theory Core -/

def resourceTheoryName : Name := ``ConstructiveCryptography.ResourceTheory
def attachName : Name := ``ConstructiveCryptography.ResourceTheory.attach
def attachIdentityName : Name := ``ConstructiveCryptography.ResourceTheory.attach_identity
def attachSerialName : Name := ``ConstructiveCryptography.ResourceTheory.attach_serial
def cryptographicAlgebraName : Name := ``ConstructiveCryptography.CryptographicAlgebra
def converterName : Name := ``ConstructiveCryptography.CryptographicAlgebra.Converter
def instHSMulConverterResourceName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.instHSMulConverterResource
def parallelName : Name := ``ConstructiveCryptography.CryptographicAlgebra.parallel
def dummyName : Name := ``ConstructiveCryptography.CryptographicAlgebra.dummy
def attachParallelName : Name := ``ConstructiveCryptography.CryptographicAlgebra.attach_parallel
def attachWhiskerLeftName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.attach_whiskerLeft
def attachWhiskerRightName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.attach_whiskerRight
def whiskerAttachCommName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.whisker_attach_comm

def quiverHomName : Name := ``Quiver.Hom
def categoryCompName : Name := ``CategoryTheory.CategoryStruct.comp
def categoryIdName : Name := ``CategoryTheory.CategoryStruct.id
def tensorObjName : Name := ``CategoryTheory.MonoidalCategoryStruct.tensorObj
def tensorHomName : Name := ``CategoryTheory.MonoidalCategoryStruct.tensorHom
def tensorUnitName : Name := ``CategoryTheory.MonoidalCategoryStruct.tensorUnit
def whiskerLeftName : Name := ``CategoryTheory.MonoidalCategoryStruct.whiskerLeft
def whiskerRightName : Name := ``CategoryTheory.MonoidalCategoryStruct.whiskerRight

/-! ## 2. Specifications, Constructions, Metrics & Relaxations -/

def specificationName : Name := ``ConstructiveCryptography.Specification
def relaxationName : Name := ``ConstructiveCryptography.Relaxation
def relaxedByName : Name := ``ConstructiveCryptography.Relaxation.relaxedBy
def specMapName : Name := ``ConstructiveCryptography.CryptographicAlgebra.Specification.map
def specParallelName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.parallel
def specDummyName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.dummy
def constructsName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
def constructsSerialName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial
def constructsParallelName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel
def constructsLeftContextName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context
def constructsRightContextName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context

def compatiblePseudoMetricName : Name := ``ConstructiveCryptography.CompatiblePseudoMetric
def distanceName : Name := ``ConstructiveCryptography.CryptographicAlgebra.distance
def distanceAttachLeName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le
def distanceParallelLeName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le
def constructsWithinName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
def constructsWithinSerialName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
def constructsWithinParallelName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel
def constructsWithinLeftContextName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context
def constructsWithinRightContextName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context

def epsilonRelaxationName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation
def specEpsilonRelaxationName : Name :=
  ``ConstructiveCryptography.Specification.epsilonRelaxation
def endoFamilyName : Name := ``ConstructiveCryptography.CryptographicAlgebra.EndoFamily
def starName : Name := ``ConstructiveCryptography.CryptographicAlgebra.Specification.star
def simulatorImageName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.simulatorImage
def simulatorImageCompName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.simulatorImage_comp
def constructsOfSimulatorName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator
def constructsOfSimulatorImageName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage
def serialSimulatorImageName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage
def mixedApplicationOfIndifferentiabilityName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.Specification.mixed_application_of_indifferentiability

/-! ## 3. Distinguishers, Absorption & Substitution -/

def advantageDistanceName : Name := ``ConstructiveCryptography.advantageDistance
def compatibleDistinguisherClassName : Name :=
  ``ConstructiveCryptography.CompatibleDistinguisherClass
def distinguisherAdvantageName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage
def distinguishersName : Name := ``ConstructiveCryptography.Distinguishers
def distinguisherProbabilityName : Name := ``ConstructiveCryptography.Distinguishers.probability
def distinguisherAdvantageValName : Name := ``ConstructiveCryptography.Distinguishers.advantage
def admissibleDistinguishersName : Name := ``ConstructiveCryptography.AdmissibleDistinguishers
def admissibleName : Name := ``ConstructiveCryptography.AdmissibleDistinguishers.admissible
def distinguisherActionName : Name := ``ConstructiveCryptography.DistinguisherAction
def absorbName : Name := ``ConstructiveCryptography.DistinguisherAction.absorb
def closedUnderName : Name := ``ConstructiveCryptography.AdmissibleDistinguishers.ClosedUnder
def dominatedByDistanceName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.DominatedByDistance
def substitutesWithinName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin
def substitutesWithinTransName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.trans
def substitutesWithinSymmName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.symm
def substitutesWithinAttachName : Name :=
  ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_attach
def substitutesWithinContextName : Name :=
  ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_context
def substitutionRelationName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation
def implicationName : Name :=
  ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication

/-! ## 4. Games, MBOs, Conditional Equivalence & Until-Bad -/

def performanceLeOfReductionName : Name :=
  ``ConstructiveCryptography.Problem.performance_le_of_reduction
def gamesName : Name := ``ConstructiveCryptography.Games
def gameActionName : Name := ``ConstructiveCryptography.GameAction
def attachGameName : Name := ``ConstructiveCryptography.GameAction.attachGame
def instHSMulConverterGameName : Name := ``ConstructiveCryptography.Games.instHSMulConverterGame
def gamesAbsorbName : Name := ``ConstructiveCryptography.Games.absorb
def distinctionGamesName : Name := ``ConstructiveCryptography.DistinctionGames
def distinctionGameActionName : Name := ``ConstructiveCryptography.DistinctionGameAction
def visibleName : Name := ``ConstructiveCryptography.DistinctionGames.visible
def conditionallyEquivalentName : Name :=
  ``ConstructiveCryptography.DistinctionGames.ConditionallyEquivalent

def monotoneMBOName : Name := ``SystemAlgebra.RandomSystem.MonotoneMBO
def rsVisibleName : Name := ``SystemAlgebra.RandomSystem.visible
def rsConditionallyEquivalentName : Name := ``SystemAlgebra.RandomSystem.ConditionallyEquivalent
def rsGameEquivalentName : Name := ``SystemAlgebra.RandomSystem.GameEquivalent
def rsWinProbabilityName : Name := ``SystemAlgebra.RandomSystem.winProbability
def rsWinLeOfTranscriptCostName : Name :=
  ``SystemAlgebra.RandomSystem.winProbability_le_of_transcriptCost_le
def rsTranscriptDistanceOfCostName : Name :=
  ``SystemAlgebra.RandomSystem.transcriptDistance_le_of_transcriptCost_le
def typedGameName : Name := ``SystemAlgebra.TypedGame
def typedGameVisibleName : Name := ``SystemAlgebra.TypedGame.visible
def typedConverterAttachGameName : Name := ``SystemAlgebra.TypedConverter.attachGame

/-! ## 5. Concrete Typed Systems, Interfaces, Converters & H-Coefficient -/

def interfaceName : Name := ``SystemAlgebra.Interface
def interfaceTensorName : Name := ``SystemAlgebra.Interface.tensor
def interfaceQueryBudgetName : Name := ``SystemAlgebra.Interface.queryBudget
def interfacePortBudgetName : Name := ``SystemAlgebra.Interface.portBudget
def typedSystemName : Name := ``SystemAlgebra.TypedSystem
def typedSystemParallelName : Name := ``SystemAlgebra.TypedSystem.parallel
def typedSystemDummyName : Name := ``SystemAlgebra.TypedSystem.dummy
def typedConverterName : Name := ``SystemAlgebra.TypedConverter
def typedConverterAttachName : Name := ``SystemAlgebra.TypedConverter.attach
def instHSMulTypedSystemName : Name := ``SystemAlgebra.TypedConverter.instHSMulTypedSystem
def instHSMulHomTypedSystemName : Name :=
  ``SystemAlgebra.Interface.instHSMulHomTypedSystem_constructiveCryptography
def typedConverterCompName : Name := ``SystemAlgebra.TypedConverter.comp
def typedConverterIdName : Name := ``SystemAlgebra.TypedConverter.id
def typedConverterParallelName : Name := ``SystemAlgebra.TypedConverter.parallel
def typedConverterLeftContextName : Name := ``SystemAlgebra.TypedConverter.leftContext
def typedConverterRightContextName : Name := ``SystemAlgebra.TypedConverter.rightContext
def typedDistinguisherName : Name := ``SystemAlgebra.TypedDistinguisher
def typedDistinguisherAbsorbName : Name := ``SystemAlgebra.TypedDistinguisher.absorb
def typedSolverName : Name := ``SystemAlgebra.TypedSolver
def typedSolverWinProbabilityName : Name := ``SystemAlgebra.TypedSolver.winProbability
def transcriptDistanceName : Name := ``SystemAlgebra.RandomSystem.transcriptDistance
def hCoefficientName : Name := ``SystemAlgebra.RandomSystem.HCoefficient
def hCoefficientBoundName : Name := ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le
def hCoefficientGoodBadName : Name :=
  ``SystemAlgebra.RandomSystem.transcriptDistance_le_add_of_ratio_on_good
def distanceLeOfHCoefficientName : Name :=
  ``SystemAlgebra.Interface.distance_le_of_hCoefficient

/-- Complete list of compile-time-verified CC constant names (useful for audits and tests). -/
def allRegisteredNames : Array Name := #[
  resourceTheoryName, attachName, attachIdentityName, attachSerialName,
  cryptographicAlgebraName, converterName, instHSMulConverterResourceName,
  parallelName, dummyName, attachParallelName, attachWhiskerLeftName,
  attachWhiskerRightName, whiskerAttachCommName,
  quiverHomName, categoryCompName, categoryIdName,
  tensorObjName, tensorHomName, tensorUnitName, whiskerLeftName, whiskerRightName,
  specificationName, relaxationName, relaxedByName,
  specMapName, specParallelName, specDummyName,
  constructsName, constructsSerialName, constructsParallelName,
  constructsLeftContextName, constructsRightContextName,
  compatiblePseudoMetricName, distanceName, distanceAttachLeName, distanceParallelLeName,
  constructsWithinName, constructsWithinSerialName, constructsWithinParallelName,
  constructsWithinLeftContextName, constructsWithinRightContextName,
  epsilonRelaxationName, specEpsilonRelaxationName, endoFamilyName,
  starName, simulatorImageName, simulatorImageCompName,
  constructsOfSimulatorName, constructsOfSimulatorImageName,
  serialSimulatorImageName, mixedApplicationOfIndifferentiabilityName,
  advantageDistanceName, compatibleDistinguisherClassName,
  distinguisherAdvantageName, distinguishersName,
  distinguisherProbabilityName, distinguisherAdvantageValName,
  admissibleDistinguishersName, admissibleName,
  distinguisherActionName, absorbName, closedUnderName, dominatedByDistanceName,
  substitutesWithinName, substitutesWithinTransName, substitutesWithinSymmName,
  substitutesWithinAttachName, substitutesWithinContextName,
  substitutionRelationName, implicationName,
  performanceLeOfReductionName, gamesName, gameActionName, attachGameName,
  instHSMulConverterGameName, gamesAbsorbName,
  distinctionGamesName, distinctionGameActionName, visibleName, conditionallyEquivalentName,
  monotoneMBOName, rsVisibleName, rsConditionallyEquivalentName,
  rsGameEquivalentName, rsWinProbabilityName,
  rsWinLeOfTranscriptCostName, rsTranscriptDistanceOfCostName,
  typedGameName, typedGameVisibleName, typedConverterAttachGameName,
  interfaceName, interfaceTensorName, interfaceQueryBudgetName, interfacePortBudgetName,
  typedSystemName, typedSystemParallelName, typedSystemDummyName,
  typedConverterName, typedConverterAttachName,
  instHSMulTypedSystemName, instHSMulHomTypedSystemName,
  typedConverterCompName, typedConverterIdName, typedConverterParallelName,
  typedConverterLeftContextName, typedConverterRightContextName,
  typedDistinguisherName, typedDistinguisherAbsorbName,
  typedSolverName, typedSolverWinProbabilityName,
  transcriptDistanceName, hCoefficientName, hCoefficientBoundName,
  hCoefficientGoodBadName, distanceLeOfHCoefficientName
]

/-! ## 6. Live Local-Context Semantic Predicates -/

/-- Ambient CC families present in the current local context:
`(categories, resourceFamilies, distinguisherFamilies, gameFamilies)`. -/
structure AmbientFamilies where
  categories : Array Expr := #[]
  resourceFamilies : Array Expr := #[]
  distinguisherFamilies : Array Expr := #[]
  gameFamilies : Array Expr := #[]
  deriving Inhabited

/-- Collect the active CC category, resource, distinguisher, and game families declared in
the current local context (e.g., from `[ResourceTheory C Phi]`, `[Distinguishers C Phi D]`,
`[Games C Game Ω]`). -/
def collectAmbientFamilies : MetaM AmbientFamilies := do
  let mut cats : Array Expr := #[]
  let mut phis : Array Expr := #[]
  let mut dists : Array Expr := #[]
  let mut games : Array Expr := #[]
  for decl in ← getLCtx do
    let ty ← instantiateMVars decl.type
    let fn := ty.getAppFn.consumeMData
    let args := ty.getAppArgs
    if let .const head _ := fn then
      if head == resourceTheoryName && args.size ≥ 3 then
        cats := cats.push args[0]!
        phis := phis.push args[2]!
      else if (head == cryptographicAlgebraName || head == compatiblePseudoMetricName ||
               head == compatibleDistinguisherClassName) && args.size ≥ 4 then
        cats := cats.push args[0]!
        phis := phis.push args[3]!
      else if head == distinguishersName && args.size ≥ 3 then
        cats := cats.push args[0]!
        phis := phis.push args[1]!
        dists := dists.push args[2]!
      else if head == admissibleDistinguishersName && args.size ≥ 2 then
        cats := cats.push args[0]!
        dists := dists.push args[1]!
      else if head == gamesName && args.size ≥ 2 then
        cats := cats.push args[0]!
        games := games.push args[1]!
      else if head == distinctionGamesName && args.size ≥ 3 then
        cats := cats.push args[0]!
        phis := phis.push args[1]!
        games := games.push args[2]!
  return {
    categories := cats
    resourceFamilies := phis
    distinguisherFamilies := dists
    gameFamilies := games
  }

/-- Is `ty` a CC interface carrier (`SystemAlgebra.Interface` or a category `C` carrying a
`ResourceTheory` in the local context)? -/
def isInterfaceType (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  if ty.consumeMData == mkConst interfaceName then
    return true
  let fam ← collectAmbientFamilies
  return fam.categories.any (fun c => c == ty.consumeMData)

/-- If `ty` is a CC resource type (`Phi A` or `TypedSystem A`), return its interface `A`. -/
def resourceInterface? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  let fn := ty.getAppFn.consumeMData
  let args := ty.getAppArgs
  if fn.isConstOf typedSystemName && args.size ≥ 1 then
    return some args.back!
  if let .app f iface := ty.consumeMData then
    let fam ← collectAmbientFamilies
    if fam.resourceFamilies.any (fun phi => phi == f) then
      return some iface
  return none

/-- If `ty` is a CC converter type (`A ⟶ B` in a resource-theory category, `Converter C A B`,
or `TypedConverter A B`), return `(outsideInterface, insideInterface)`. -/
def converterInterfaces? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← instantiateMVars ty
  let fn := ty.getAppFn.consumeMData
  let args := ty.getAppArgs
  if fn.isConstOf typedConverterName && args.size ≥ 2 then
    return some (args[args.size - 2]!, args[args.size - 1]!)
  if fn.isConstOf converterName && args.size ≥ 4 then
    return some (args[args.size - 2]!, args[args.size - 1]!)
  if fn.isConstOf quiverHomName && args.size ≥ 4 then
    let cat := args[0]!
    let outIface := args[args.size - 2]!
    let inIface := args[args.size - 1]!
    if cat.consumeMData == mkConst interfaceName then
      return some (outIface, inIface)
    let fam ← collectAmbientFamilies
    if fam.categories.any (fun c => c == cat.consumeMData) then
      return some (outIface, inIface)
  return none

/-- If `ty` is a CC specification type (`Specification (Phi A)` or `Set (Phi A)` or
`Set (TypedSystem A)`), return the interface `A` of its resources. -/
def specificationInterface? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  let fn := ty.getAppFn.consumeMData
  let args := ty.getAppArgs
  if (fn.isConstOf specificationName || fn.isConstOf ``Set) && args.size ≥ 1 then
    resourceInterface? args.back!
  else
    return none

/-- If `ty` is a CC game type (`Game A` or `TypedGame A`), return its interface `A`. -/
def gameInterface? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  let fn := ty.getAppFn.consumeMData
  let args := ty.getAppArgs
  if fn.isConstOf typedGameName && args.size ≥ 1 then
    return some args.back!
  if let .app f iface := ty.consumeMData then
    let fam ← collectAmbientFamilies
    if fam.gameFamilies.any (fun g => g == f) then
      return some iface
  return none

/-- If `ty` is a CC distinguisher or solver type (`D A`, `TypedDistinguisher A`, `TypedSolver A`),
return its interface `A`. -/
def distinguisherInterface? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  let fn := ty.getAppFn.consumeMData
  let args := ty.getAppArgs
  if (fn.isConstOf typedDistinguisherName || fn.isConstOf typedSolverName) && args.size ≥ 1 then
    return some args.back!
  if let .app f iface := ty.consumeMData then
    let fam ← collectAmbientFamilies
    if fam.distinguisherFamilies.any (fun d => d == f) then
      return some iface
  return none

/-- Is `ty` an `HCoefficient` witness type? -/
def isHCoefficientType (ty : Expr) : Bool :=
  ty.getAppFn.consumeMData.isConstOf hCoefficientName

/-- Is `ty` a `SubstitutionRelation.Implication` witness type? -/
def isImplicationType (ty : Expr) : Bool :=
  ty.getAppFn.consumeMData.isConstOf implicationName

end Informalization.CC.Registry
