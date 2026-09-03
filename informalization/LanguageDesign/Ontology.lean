import LanguageDesign.Basic

/-!
# Shared mathematical ontology

These stable identifiers classify sentence operands and results. They contain
no surface-language strings and are shared by authoring and informalization.
-/

namespace CryptoLanguage.LanguageDesign.Ontology

open CryptoLanguage.LanguageDesign

def object := concept `object
def naturalNumber := concept `naturalNumber
def alphabet := concept `alphabet
def proposition := concept `proposition
def proof := concept `proof
def protocol := concept `protocol
def construction := concept `construction
def equality := concept `equality
def simulator := concept `simulator
def context := concept `context
def system := concept `system
def deterministicSystem := concept `deterministicSystem
def probabilisticSystem := concept `probabilisticSystem
def probabilisticGame := concept `probabilisticGame
def pdsLaw := concept `pdsLaw
def normalizedPartialSystemLaw := concept `normalizedPartialSystemLaw
def commonDomainPresentation := concept `commonDomainPresentation
def commonDomainProbabilityPresentation := concept `commonDomainProbabilityPresentation
def commonDomainSystem := concept `commonDomainSystem
def commonDomainProbabilitySystem := concept `commonDomainProbabilitySystem
def ambientSystem := concept `ambientSystem
def ambientProbabilityPresentation := concept `ambientProbabilityPresentation
def converter := concept `converter
def systemTransform := concept `systemTransform
def gameTransform := concept `gameTransform
def game := concept `game
def condition := concept `condition
def monotoneCondition := concept `monotoneCondition
def monotoneBinaryOutput := concept `monotoneBinaryOutput
def predicate := concept `predicate
def environment := concept `environment
def horizon := concept `horizon
def bound := concept `bound
def equation := concept `equation
def intermediate := concept `intermediate
def compatibility := concept `compatibility
def support := concept `support
def distinguisherClass := concept `distinguisherClass
def test := concept `test
def realScalar := concept `realScalar
def nonnegativeRealScalar := concept `nonnegativeRealScalar
def extendedNonnegativeRealScalar := concept `extendedNonnegativeRealScalar
def mass := concept `mass
def probabilityLaw := concept `probabilityLaw
def queryList := concept `queryList
def collisionEvent := concept `collisionEvent
def winningProbability := concept `winningProbability
def blindWinningProbability := concept `blindWinningProbability
def statisticalDistance := concept `statisticalDistance
def distinguishingAdvantage := concept `distinguishingAdvantage

/-- Closed inventory of ontology concepts owned by the shared language
design. Contract validation requires every entry to have one typed entity
specification; adding a concept here without one is a test failure. -/
def allConcepts : Array ConceptId := #[
  object, naturalNumber, alphabet, proposition, proof, protocol,
  construction, equality, simulator, context, system, deterministicSystem,
  probabilisticSystem, probabilisticGame, pdsLaw,
  normalizedPartialSystemLaw, commonDomainPresentation,
  commonDomainProbabilityPresentation, commonDomainSystem,
  commonDomainProbabilitySystem, ambientSystem,
  ambientProbabilityPresentation, converter, systemTransform, gameTransform,
  game, condition, monotoneCondition, monotoneBinaryOutput, predicate,
  environment, horizon, bound, equation, intermediate, compatibility, support,
  distinguisherClass, test, realScalar, nonnegativeRealScalar,
  extendedNonnegativeRealScalar, mass, probabilityLaw, queryList,
  collisionEvent, winningProbability, blindWinningProbability,
  statisticalDistance, distinguishingAdvantage]

namespace Relations

def proofState := relation `proofState
def definition := relation `definition
def proposition := relation `proposition
def equality := relation `equality
def construction := relation `construction
def distanceBound := relation `distanceBound
def conditionalEquivalence := relation `conditionalEquivalence
def winningBound := relation `winningBound
def advantageBound := relation `advantageBound
def upperBound := relation `upperBound
def indistinguishability := relation `indistinguishability
def gameEquivalence := relation `gameEquivalence
def reduction := relation `reduction
def eventImplication := relation `eventImplication
def winningProbability := relation `winningProbability
def blindWinningProbability := relation `blindWinningProbability
def badEventProbability := relation `badEventProbability
def nonnegativity := relation `nonnegativity

/-- Closed inventory of relation identities owned by the shared language
design. -/
def allRelations : Array RelationId := #[
  proofState, definition, proposition, equality, construction, distanceBound,
  conditionalEquivalence, winningBound, advantageBound, upperBound,
  indistinguishability, gameEquivalence, reduction, eventImplication,
  winningProbability, blindWinningProbability, badEventProbability,
  nonnegativity]

end Relations
end CryptoLanguage.LanguageDesign.Ontology
