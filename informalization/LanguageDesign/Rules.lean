import LanguageDesign.Basic

/-! Stable rule identities shared by authoring and informalization. -/

namespace CryptoLanguage.LanguageDesign.Rules

open CryptoLanguage.LanguageDesign

def structuralConclude := rule `structural `claim `conclude
def structuralGoalReminder := rule `structural `goal `remind
def structuralFix := rule `structural `binder `fix
def structuralAssume := rule `structural `binder `assume
def structuralChoose := rule `structural `elimination `choose
def structuralConjunction := rule `structural `elimination `conjunction
def structuralTheorem := rule `structural `declaration `theorem

def acConstructionFrom := rule `ac `construction `fromProof
def acEqualityFrom := rule `ac `equality `fromProof
def acReplaceProtocol := rule `ac `construction `replaceProtocol
def acCompose := rule `ac `construction `compose
def acSimulator := rule `ac `construction `simulator
def acContextRight := rule `ac `construction `contextRight
def acContextLeft := rule `ac `construction `contextLeft
def acTriangleClose := rule `ac `distance `triangleClose
def acTriangleReduce := rule `ac `distance `triangleReduce
def acRelax := rule `ac `construction `relax
def acFiltered := rule `ac `construction `filtered
def acParallel := rule `ac `construction `parallel
def acComposeSimulators := rule `ac `construction `composeSimulators

def rsConditionalLaw := rule `rs `conditionalEquivalence `fromProof
def rsPdsEquivalent := rule `rs `systemRelation `pdsEquivalent
def rsGameEquivalent := rule `rs `gameRelation `equivalentAsGames
def rsForgetGame := rule `rs `gameRelation `forget
def rsEnhanceWithMBO := rule `rs `gameRelation `enhanceWithMBO
def rsFilterConditionalLaw := rule `rs `conditionalEquivalence `filterDomain
def rsFilterQueriesConditionalLaw := rule `rs `conditionalEquivalence `filterQueries
def rsConditionalBlindBound := rule `rs `conditionalEquivalence `blindBound
def rsConditionalBlindComparison :=
  rule `rs `conditionalEquivalence `blindComparison
def rsBlindUniversal := rule `rs `winning `blindUniversal
def rsBlindWinningBound := rule `rs `winning `blindBound
def rsMassBound := rule `rs `collision `massBound
def rsCommonDomainDataProcessing := rule `rs `distance `commonDomainDataProcessing
def rsHCoefficient := rule `rs `distance `hCoefficient
def rsTransformConditionalLaw := rule `rs `conditionalEquivalence `transform
def rsWinningMassIdentity := rule `rs `winning `fixedScheduleIdentity

/- Random Systems object introductions.  These are definitions, not proof
steps: their checked effect is to add one local mathematical object. -/
def rsBindSystem := rule `rs `declaration `systemBinder
def rsDeclareRestrictedURF := rule `rs `declaration `restrictedURF
def rsDefineCharacterizedMBO := rule `rs `declaration `characterizedMBO
def rsDeclareEnhancedURFGame := rule `rs `declaration `enhancedURFGame
def rsDeclareRestrictedGame := rule `rs `declaration `restrictedGame
def rsDeclareRestrictedURP := rule `rs `declaration `restrictedURP
def rsRestrictedEnhancedURFGameNonnegative :=
  rule `rs `property `restrictedEnhancedURFGameNonnegative

/- Stable proof-rule identities used by the presentation-side semantic IR.
They live here so Verbose and Informalization can agree on meaning without
depending on one another. -/
def proofExactEquivalence := rule `proof `equivalence `exact
def proofConstruction := rule `proof `construction `close
def proofDistanceBound := rule `proof `distance `bound
def proofAdvantageBound := rule `proof `advantage `bound
def proofIgnoreGameMBO := rule `proof `game `ignoreMBO
def proofTriangleHybrid := rule `proof `distance `triangleHybrid
def proofConditionalEquivalenceUnderRestriction :=
  rule `proof `conditionalEquivalence `underRestriction
def proofCollisionConditionalEquivalence :=
  rule `proof `conditionalEquivalence `collision
def proofBlindWinningBound := rule `proof `winning `blindBound
def proofBlindWinningToNonadaptive := rule `proof `winning `toNonadaptive
def proofNonadaptiveQueriesFixed := rule `proof `winning `fixedQueries
def proofCommonDomainDataProcessing := rule `proof `commonDomain `dataProcessing
def proofRestrictionApplicationEquation :=
  rule `proof `converter `restrictionApplicationEquation
def proofConditionalUniformOutputs := rule `proof `collision `uniformOutputs
def proofDistinctTerminalInputs := rule `proof `collision `distinctTerminalInputs
def proofGamePlayingFundamentalLemma := rule `proof `game `fundamentalLemma
def proofCoupling := rule `proof `distance `coupling
def proofRepresentativeSelection := rule `proof `quotient `representativeSelection
def proofWinnability := rule `proof `winning `winnability
def proofSignedExpansion := rule `proof `algebra `signedExpansion
def proofCounting := rule `proof `counting `counting
def proofCollisionProbabilityBound := rule `proof `collision `probabilityBound
def proofCollisionMassBound := rule `proof `collision `massBound
def proofBirthdayBound := rule `proof `counting `birthdayBound
def proofScalarClosure := rule `proof `scalar `closure
def proofArithmetic := rule `proof `routine `arithmetic
def proofRewriting := rule `proof `routine `rewriting
def proofMonotonicity := rule `proof `order `monotonicity

/-- Closed inventory of mathematical and discourse-rule identities currently
recognized by either frontend. The language contract must classify every
entry; a newly introduced rule cannot remain an untyped identifier. -/
def allRules : Array RuleId := #[
  structuralConclude, structuralGoalReminder, structuralFix, structuralAssume,
  structuralChoose, structuralConjunction, structuralTheorem,
  acConstructionFrom, acEqualityFrom, acReplaceProtocol, acCompose,
  acSimulator, acContextRight, acContextLeft, acTriangleClose,
  acTriangleReduce, acRelax, acFiltered, acParallel, acComposeSimulators,
  rsConditionalLaw, rsPdsEquivalent, rsGameEquivalent, rsForgetGame,
  rsEnhanceWithMBO, rsFilterConditionalLaw, rsFilterQueriesConditionalLaw,
  rsConditionalBlindBound, rsConditionalBlindComparison, rsBlindUniversal,
  rsBlindWinningBound, rsMassBound, rsCommonDomainDataProcessing,
  rsHCoefficient, rsTransformConditionalLaw, rsWinningMassIdentity,
  rsBindSystem, rsDeclareRestrictedURF, rsDefineCharacterizedMBO,
  rsDeclareEnhancedURFGame, rsDeclareRestrictedGame, rsDeclareRestrictedURP,
  rsRestrictedEnhancedURFGameNonnegative,
  proofExactEquivalence, proofConstruction, proofDistanceBound,
  proofAdvantageBound, proofIgnoreGameMBO, proofTriangleHybrid,
  proofConditionalEquivalenceUnderRestriction,
  proofCollisionConditionalEquivalence, proofBlindWinningBound,
  proofBlindWinningToNonadaptive, proofNonadaptiveQueriesFixed,
  proofCommonDomainDataProcessing, proofRestrictionApplicationEquation,
  proofConditionalUniformOutputs, proofDistinctTerminalInputs,
  proofGamePlayingFundamentalLemma, proofCoupling,
  proofRepresentativeSelection, proofWinnability, proofSignedExpansion,
  proofCounting, proofCollisionProbabilityBound, proofCollisionMassBound,
  proofBirthdayBound, proofScalarClosure, proofArithmetic, proofRewriting,
  proofMonotonicity]

end CryptoLanguage.LanguageDesign.Rules
