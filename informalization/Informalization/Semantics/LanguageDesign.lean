import LanguageDesign
import Informalization.Semantics.IR

/-!
# Shared language-design adapter

Informalization keeps its richer recovery IR, while exposing a total mapping
to the neutral identifiers also used by Verbose.  This is the only dependency
between the two products: neither frontend imports the other.
-/

namespace Informalization.Semantics.LanguageDesign

open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Ontology
open CryptoLanguage.LanguageDesign.Rules
open Informalization.Semantics

inductive SharedNodeRole
  | concept (id : ConceptId)
  | relation (id : RelationId)
  | rule (id : RuleId)
deriving Inhabited, BEq, Repr

def entityRole : EntityRole → ConceptId
  | .carrier => Ontology.object
  | .randomSystem => Ontology.system
  | .game => Ontology.game
  | .converter => Ontology.converter
  | .distinguisher => concept `distinguisher
  | .environment => Ontology.environment
  | .transcript => concept `transcript
  | .event => concept `event
  | .collisionCondition => Ontology.condition
  | .queryBudget => Ontology.bound
  | .probability => concept `probability
  | .distribution => concept `distribution
  | .errorBound => Ontology.bound
  | .simulator => Ontology.simulator
  | .custom name => concept name

def systemRole : SystemRole → ConceptId
  | .atom => Ontology.system
  | .uniformRandomFunction => concept `uniformRandomFunction
  | .uniformRandomPermutation => concept `uniformRandomPermutation
  | .presentationQuotient => Ontology.ambientSystem
  | .converterApplication => concept `converterApplication
  | .queryRestriction => concept `queryRestrictedSystem
  | .forgetGame => Ontology.probabilisticSystem
  | .transform => concept `transformedSystem
  | .parallelComposition => concept `parallelSystem
  | .serialComposition => concept `serialSystem
  | .idealFunctionality => concept `idealFunctionality
  | .custom name => concept name

def gameRole : GameRole → ConceptId
  | .atom => Ontology.game
  | .enhanceWithMBO => Ontology.probabilisticGame
  | .queryRestriction => concept `queryRestrictedGame
  | .transform => concept `transformedGame
  | .custom name => concept name

def converterRole : ConverterRole → ConceptId
  | .atom => Ontology.converter
  | .queryRestriction => concept `queryRestrictionConverter
  | .blockRestriction => concept `blockRestrictionConverter
  | .serialComposition => concept `serialConverter
  | .parallelComposition => concept `parallelConverter
  | .custom name => concept name

def quantityRole : QuantityRole → ConceptId
  | .distinguishingAdvantage => Ontology.distinguishingAdvantage
  | .statisticalDistance => Ontology.statisticalDistance
  | .winningProbability => Ontology.winningProbability
  | .blindWinningProbability => Ontology.blindWinningProbability
  | .badEventProbability => concept `badEventProbability
  | .systemWeight => concept `systemWeight
  | .custom name => concept name

def relationRole : RelationRole → RelationId
  | .equality => Relations.equality
  | .upperBound => Relations.upperBound
  | .indistinguishability => Relations.indistinguishability
  | .advantageBound => Relations.advantageBound
  | .conditionalEquivalence => Relations.conditionalEquivalence
  | .gameEquivalence => Relations.gameEquivalence
  | .construction => Relations.construction
  | .reduction => Relations.reduction
  | .eventImplication => Relations.eventImplication
  | .custom name => relation name

def proofRuleRole : ProofRuleRole → RuleId
  | .exactEquivalence => proofExactEquivalence
  | .construction => proofConstruction
  | .distanceBound => proofDistanceBound
  | .advantageBound => proofAdvantageBound
  | .ignoreGameMBO => proofIgnoreGameMBO
  | .triangleHybrid => proofTriangleHybrid
  | .hTechnique => rsHCoefficient
  | .conditionalEquivalence => rsConditionalLaw
  | .conditionalEquivalenceUnderRestriction =>
      proofConditionalEquivalenceUnderRestriction
  | .collisionConditionalEquivalence => proofCollisionConditionalEquivalence
  | .conditionalEquivalenceToBlindWinning => rsConditionalBlindBound
  | .blindWinningBound => proofBlindWinningBound
  | .blindWinningToNonadaptive => proofBlindWinningToNonadaptive
  | .nonadaptiveQueriesFixed => proofNonadaptiveQueriesFixed
  | .commonDomainDataProcessing => rsCommonDomainDataProcessing
  | .restrictionApplicationEquation => proofRestrictionApplicationEquation
  | .conditionalUniformOutputs => proofConditionalUniformOutputs
  | .distinctTerminalInputs => proofDistinctTerminalInputs
  | .gamePlayingFundamentalLemma => proofGamePlayingFundamentalLemma
  | .coupling => proofCoupling
  | .representativeSelection => proofRepresentativeSelection
  | .winnability => proofWinnability
  | .signedExpansion => proofSignedExpansion
  | .counting => proofCounting
  | .collisionProbabilityBound => proofCollisionProbabilityBound
  | .collisionMassBound => proofCollisionMassBound
  | .birthdayBound => proofBirthdayBound
  | .scalarClosure => proofScalarClosure
  | .arithmetic => proofArithmetic
  | .rewriting => proofRewriting
  | .monotonicity => proofMonotonicity
  | .custom name => rule `informalization `custom name

def argumentRole : Informalization.Semantics.ArgumentRole →
    CryptoLanguage.LanguageDesign.ArgumentRole
  | .subject => role `subject
  | .inputSpace => role `inputSpace
  | .outputSpace => role `outputSpace
  | .alphabet => role `alphabet
  | .realSystem => role `realSystem
  | .idealSystem => role `idealSystem
  | .sourceSystem => role `sourceSystem
  | .targetSystem => role `targetSystem
  | .transformedSystem => role `transformedSystem
  | .converter => role `converter
  | .game => role `game
  | .condition => role `condition
  | .queryBudget => role `queryBudget
  | .distinguisher => role `distinguisher
  | .environment => role `environment
  | .transcript => role `transcript
  | .event => role `event
  | .badEvent => role `badEvent
  | .bound => role `bound
  | .errorTerm => role `errorTerm
  | .probabilityLaw => role `probabilityLaw
  | .premise index => role (.num `premise index)
  | .conclusion => role `conclusion
  | .custom name => role name

def nodeRole : NodeRole → SharedNodeRole
  | .entity value => .concept (entityRole value)
  | .system value => .concept (systemRole value)
  | .game value => .concept (gameRole value)
  | .converter value => .concept (converterRole value)
  | .quantity value => .concept (quantityRole value)
  | .proposition value => .relation (relationRole value)
  | .proofRule value => .rule (proofRuleRole value)

end Informalization.Semantics.LanguageDesign
