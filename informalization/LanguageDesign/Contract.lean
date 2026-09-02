import LanguageDesign.Grammar
import LanguageDesign.Ontology
import LanguageDesign.Rules
import LanguageDesign.SurfaceContract

/-!
# Executable language-design contract

This module is the normative abstract design shared by Verbose and
Informalization. It records the closed entity families, every currently owned
ontology concept and relation, the compositional expression vocabulary, the
R1--R23 compilation rules, and the implementation/publication state of every
stable `RuleId`.

Markdown documents may explain or project this catalog. They do not add an
entity, relation, rule, surface form, or implementation obligation.
-/

namespace CryptoLanguage.LanguageDesign.Contract

open Lean
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Ontology
open CryptoLanguage.LanguageDesign.Rules

inductive ImplementationStatus
  | implemented
  | specified
  | deferred
  | rejected
  | ordinaryLean
deriving Repr, BEq, Hashable, Inhabited

inductive PublicationStatus
  | published
  | applicationScoped
  | pendingAttestation
  | internal
  | notApplicable
deriving Repr, BEq, Hashable, Inhabited

inductive EvidenceRequirement
  | positiveGrammar
  | negativeGrammar
  | ontologySchema
  | deterministicLowering
  | checkedEffect
  | sentenceTrace
  | canonicalRendering
  | completePassage
  | invariance
  | diagnostic
  | sourceAttestation
deriving Repr, BEq, Hashable, Inhabited

structure EntityFamilySpec where
  kind : EntityKind
  subkinds : Array Name
  distinctions : Array Name
deriving Repr, BEq, Inhabited

structure EntitySpec where
  concept : ConceptId
  kind : EntityKind
  registers : Array Register
  acts : Array DiscourseAct
  definitionModes : Array DefinitionMode := #[]
  requiredDistinctions : Array Name := #[]
deriving Repr, BEq, Inhabited

structure RelationSpec where
  relation : RelationId
  registers : Array Register
  subjectKinds : Array EntityKind
  complementKinds : Array EntityKind := #[]
  permittedActs : Array DiscourseAct
deriving Repr, BEq, Inhabited

structure ExpressionConstructorSpec where
  id : Name
  resultKind : EntityKind
  operandKinds : Array EntityKind
  requiredIndices : Array Name := #[]
  status : ImplementationStatus := .specified
deriving Repr, BEq, Inhabited

structure CompilationRuleSpec where
  number : Nat
  id : Name
  stage : InferenceStage
  requiredInputs : Array Name
  produces : Array Name
  invariants : Array Name
deriving Repr, BEq, Inhabited

structure RuleContract where
  ruleId : RuleId
  implementation : ImplementationStatus
  publication : PublicationStatus
  evidence : Array EvidenceRequirement
deriving Repr, BEq, Inhabited

private def names (values : List String) : Array Name :=
  values.toArray.map Name.mkSimple

def entityFamilies : Array EntityFamilySpec := #[
  {
    kind := .carrier
    subkinds := names ["type", "finiteAlphabet", "nonemptyAlphabet", "subtype",
      "stateSpace"]
    distinctions := names ["finitenessIsProperty", "nonemptinessIsProperty",
      "decidableEqualityIsProperty", "algebraicStructureIsProperty"]
  },
  {
    kind := .interface
    subkinds := names ["inputSignature", "outputSignature", "namedPort",
      "insidePort", "outsidePort", "partyIndexedPort",
      "dependentInterfaceFamily", "routedSubinterface"]
    distinctions := names ["direction", "ownership", "dependency",
      "attachmentSite"]
  },
  {
    kind := .history
    subkinds := names ["query", "answer", "inputHistory", "attemptedHistory",
      "transcript", "prefix", "fixedQueryList", "encodedBlockList",
      "callSite", "schedule"]
    distinctions := names ["queryVsTranscript", "fixedVsAdaptive",
      "acceptedVsAttempted"]
  },
  {
    kind := .system
    subkinds := names ["dds", "signedPds", "normalizedProbDistPresentation",
      "commonDomainPresentation", "ambientPresentation", "behaviouralQuotient",
      "randomSystem", "resource", "realRole", "idealRole"]
    distinctions := names ["presentationVsBehaviour", "signStatus",
      "weightStatus", "commonDomainVsAmbient", "intrinsicKindVsRole"]
  },
  {
    kind := .converter
    subkinds := names ["deterministicConverter", "randomizedConverter",
      "identityConverter", "blockingConverter", "queryRestriction",
      "domainFilter", "blockRestriction", "relabelling", "serialComposite",
      "parallelComposite", "protocolComponent", "simulatorRole"]
    distinctions := names ["outsideSignature", "insideSignature",
      "applicationOrder", "attachmentInterface", "applicability"]
  },
  {
    kind := .game
    subkinds := names ["deterministicGame", "probabilisticGame", "gamesFor",
      "mboEnhancedGame", "restrictedGame", "transformedGame",
      "forgottenMboSystem"]
    distinctions := names ["gameVsForgottenSystem", "interactiveEquivalence",
      "notWonEquivalence", "conditionalEquivalence"]
  },
  {
    kind := .strategy
    subkinds := names ["partialEnvironment", "totalEnvironment",
      "signedPartialPde", "normalizedAmbientTotalPde", "strictDistinguisher",
      "winnerRole", "nonAdaptiveProperty", "fixedQueryEnvironment",
      "fixedSchedule"]
    distinctions := names ["acceptedVsAttempted", "strategyVsStrictTest",
      "unrestrictedVsNonAdaptive"]
  },
  {
    kind := .law
    subkinds := names ["sourceLaw", "transcriptLaw", "outputLaw", "notWonLaw",
      "conditionedLaw", "pushforward", "extendedLaw", "jointLaw", "coupling",
      "marginal", "signedExpansion"]
    distinctions := names ["lawVsSystem", "supportVsDomain",
      "honestJointVsSignedIdentity"]
  },
  {
    kind := .event
    subkinds := names ["predicate", "monotoneCondition", "mbo", "badEvent",
      "goodEvent", "collision", "freshness", "winning", "disagreement",
      "supportEvent", "domainEvent"]
    distinctions := names ["scope", "monotonicity", "complement",
      "temporalBoundary"]
  },
  {
    kind := .quantity
    subkinds := names ["weight", "mass", "probability", "advantage",
      "fullyDefinedAdvantage", "ambientAdvantage", "classDistance",
      "quotientDistance", "adaptiveWinningProbability",
      "blindWinningProbability", "winnability", "cardinality", "errorBudget"]
    distinctions := names ["scalarCarrier", "orientation", "observerClass",
      "normalization", "carrierLevel", "supremumDomain"]
  },
  {
    kind := .specification
    subkinds := names ["resourceProperty", "singleton", "constructorImage",
      "relaxation", "filteredSpecification", "parallelSpecification"]
    distinctions := names ["objectVsSet", "exactVsRelaxedMembership"]
  },
  {
    kind := .construction
    subkinds := names ["constructor", "protocol", "simulatorConstruction",
      "exactConstruction", "approximateConstruction", "composition",
      "contextApplication"]
    distinctions := names ["sourceSpecification", "targetSpecification",
      "protocol", "interfacePattern", "error"]
  },
  {
    kind := .proofObject
    subkinds := names ["theoremApplication", "equalityWitness", "coupling",
      "reduction", "representativeSelection", "simulator", "countingWitness",
      "proofObligation"]
    distinctions := names ["evidenceType", "premiseSlots", "notCertificate"]
  },
  {
    kind := .formalArtifact
    subkinds := names ["declaration", "binder", "proofTerm", "tacticEvent",
      "goal", "infoTreeNode", "coercion", "elaborationWrapper",
      "unsupportedExpression"]
    distinctions := names ["checkedProvenanceOnly", "noDefaultMathNoun"]
  }
]

private def entity (id : ConceptId) (kind : EntityKind)
    (registers : Array Register) (acts : Array DiscourseAct)
    (modes : Array DefinitionMode := #[])
    (distinctions : Array Name := #[]) : EntitySpec :=
  { concept := id, kind, registers, acts, definitionModes := modes,
    requiredDistinctions := distinctions }

private def commonActs : Array DiscourseAct := #[
  .introduce, .define, .describe, .assert, .derive, .refer]

def entities : Array EntitySpec := #[
  entity object .formalArtifact #[.formal] commonActs,
  entity naturalNumber .quantity #[.scalar] commonActs,
  entity alphabet .carrier #[.formal, .system] commonActs,
  entity proposition .formalArtifact #[.formal] #[.assert, .assume, .derive, .refer],
  entity proof .proofObject #[.formal] #[.introduce, .derive, .refer],
  entity protocol .construction #[.construction] commonActs,
  entity construction .construction #[.construction] commonActs,
  entity equality .proofObject #[.formal, .algebra] #[.assert, .derive, .refer],
  entity simulator .converter #[.construction, .system] commonActs
    #[.roleAssignment] #[`roleNotIdentity],
  entity context .converter #[.construction, .system] commonActs,
  entity system .system #[.system] commonActs,
  entity deterministicSystem .system #[.system] commonActs,
  entity probabilisticSystem .system #[.system, .law] commonActs,
  entity probabilisticGame .game #[.game, .law] commonActs,
  entity pdsLaw .system #[.system, .law] commonActs
    #[.representational] #[`presentationVsBehaviour],
  entity normalizedPartialSystemLaw .law #[.law] commonActs,
  entity commonDomainPresentation .system #[.system, .law] commonActs
    #[.representational] #[`commonDomainVsAmbient],
  entity commonDomainProbabilityPresentation .system #[.system, .law] commonActs
    #[.representational] #[`commonDomainVsAmbient, `weightStatus],
  entity commonDomainSystem .system #[.system] commonActs
    #[.representational] #[`presentationVsBehaviour],
  entity commonDomainProbabilitySystem .system #[.system] commonActs
    #[.representational] #[`presentationVsBehaviour, `weightStatus],
  entity ambientSystem .system #[.system] commonActs #[.representational]
    #[`commonDomainVsAmbient],
  entity ambientProbabilityPresentation .system #[.system, .law] commonActs
    #[.representational] #[`commonDomainVsAmbient, `weightStatus],
  entity converter .converter #[.system, .construction] commonActs,
  entity systemTransform .converter #[.system] commonActs,
  entity gameTransform .converter #[.game] commonActs,
  entity game .game #[.game] commonActs,
  entity condition .event #[.game, .law] commonActs #[.predicate],
  entity monotoneCondition .event #[.game, .law] commonActs #[.predicate]
    #[`monotonicity],
  entity monotoneBinaryOutput .event #[.game] commonActs #[.predicate]
    #[`monotonicity, `temporalBoundary],
  entity predicate .event #[.law, .game] commonActs #[.predicate],
  entity environment .strategy #[.game, .law] commonActs,
  entity horizon .quantity #[.game, .scalar] commonActs,
  entity bound .quantity #[.scalar, .construction] commonActs,
  entity equation .proofObject #[.formal, .algebra] #[.assert, .derive, .refer],
  entity intermediate .system #[.system, .game] commonActs #[.roleAssignment]
    #[`roleNotIdentity],
  entity compatibility .proofObject #[.formal] #[.assert, .derive, .refer],
  entity support .event #[.law] commonActs #[.predicate] #[`supportVsDomain],
  entity distinguisherClass .specification #[.construction, .system] commonActs,
  entity test .strategy #[.system, .law] commonActs,
  entity realScalar .quantity #[.scalar, .algebra] commonActs,
  entity nonnegativeRealScalar .quantity #[.scalar, .algebra] commonActs
    #[] #[`scalarCarrier],
  entity extendedNonnegativeRealScalar .quantity #[.scalar, .algebra] commonActs
    #[] #[`scalarCarrier],
  entity mass .quantity #[.law, .scalar] commonActs,
  entity probabilityLaw .law #[.law] commonActs,
  entity queryList .history #[.game, .law] commonActs,
  entity collisionEvent .event #[.game, .law] commonActs #[.predicate]
    #[`scope, `temporalBoundary],
  entity winningProbability .quantity #[.game, .scalar] commonActs
    #[] #[`observerClass, `supremumDomain],
  entity blindWinningProbability .quantity #[.game, .scalar] commonActs
    #[] #[`observerClass, `supremumDomain],
  entity statisticalDistance .quantity #[.system, .scalar] commonActs
    #[] #[`orientation, `carrierLevel],
  entity distinguishingAdvantage .quantity #[.system, .scalar] commonActs
    #[] #[`orientation, `observerClass]
]

private def relationSpec (id : RelationId) (registers : Array Register)
    (subjects : Array EntityKind) (complements : Array EntityKind)
    (acts : Array DiscourseAct) : RelationSpec :=
  { relation := id, registers, subjectKinds := subjects,
    complementKinds := complements, permittedActs := acts }

def relations : Array RelationSpec := #[
  relationSpec Relations.proofState #[.formal] #[.formalArtifact] #[]
    #[.assert, .reduce, .refer],
  relationSpec Relations.definition #[.formal, .system, .game, .law]
    #[.carrier, .system, .converter, .game, .law, .event, .quantity]
    #[.formalArtifact] #[.define, .describe],
  relationSpec Relations.proposition #[.formal] #[.formalArtifact] #[]
    #[.assert, .assume, .derive],
  relationSpec Relations.equality #[.formal, .algebra]
    #[.system, .converter, .game, .law, .quantity, .formalArtifact]
    #[.system, .converter, .game, .law, .quantity, .formalArtifact]
    #[.assert, .derive, .calculate],
  relationSpec Relations.construction #[.construction] #[.construction]
    #[.specification, .converter, .quantity] #[.assert, .derive, .conclude],
  relationSpec Relations.distanceBound #[.system, .scalar] #[.quantity]
    #[.system, .quantity] #[.assert, .derive, .estimate],
  relationSpec Relations.conditionalEquivalence #[.game] #[.game]
    #[.system] #[.assert, .derive, .preserve],
  relationSpec Relations.winningBound #[.game, .scalar] #[.quantity]
    #[.game, .quantity] #[.assert, .derive, .estimate],
  relationSpec Relations.advantageBound #[.system, .scalar] #[.quantity]
    #[.system, .quantity] #[.assert, .derive, .estimate],
  relationSpec Relations.upperBound #[.scalar, .algebra] #[.quantity]
    #[.quantity] #[.assert, .derive, .calculate, .estimate],
  relationSpec Relations.indistinguishability #[.system] #[.system]
    #[.system, .quantity] #[.assert, .derive],
  relationSpec Relations.gameEquivalence #[.game] #[.game] #[.game]
    #[.assert, .derive],
  relationSpec Relations.reduction #[.construction, .game] #[.proofObject]
    #[.construction, .game, .quantity] #[.reduce, .derive],
  relationSpec Relations.eventImplication #[.law, .game] #[.event] #[.event]
    #[.assert, .derive],
  relationSpec Relations.winningProbability #[.game, .scalar] #[.quantity]
    #[.game] #[.assert, .estimate],
  relationSpec Relations.blindWinningProbability #[.game, .scalar] #[.quantity]
    #[.game, .strategy] #[.assert, .estimate],
  relationSpec Relations.badEventProbability #[.law, .scalar] #[.quantity]
    #[.law, .event] #[.assert, .estimate],
  relationSpec Relations.nonnegativity #[.law, .scalar] #[.law, .quantity]
    #[] #[.assert, .derive]
]

private def constructor (id : Name) (result : EntityKind)
    (operands : Array EntityKind) (indices : Array Name := #[])
    (status : ImplementationStatus := .specified) : ExpressionConstructorSpec :=
  { id, resultKind := result, operandKinds := operands,
    requiredIndices := indices, status }

def expressionConstructors : Array ExpressionConstructorSpec := #[
  constructor `systemAtom .system #[.interface] #[`carrierLevel, `signature],
  constructor `uniformRandomFunction .system #[.carrier, .carrier]
    #[`pdsPresentation, `normalized],
  constructor `uniformRandomPermutation .system #[.carrier]
    #[`pdsPresentation, `normalized],
  constructor `idealFunctionality .system #[.interface] #[`signature],
  constructor `presentedBy .system #[.law] #[`presentationVsBehaviour],
  constructor `quotientOf .system #[.system] #[`quotientKind],
  constructor `embedCommonDomain .system #[.system] #[`domainIndex],
  constructor `normalizePresentation .system #[.system] #[`massIndex],
  constructor `applyConverter .system #[.converter, .interface, .system]
    #[`attachmentSite, `actionRegime, `signature],
  constructor `restrictQueries .system #[.system, .quantity] #[`queryBudget],
  constructor `restrictDomain .system #[.system, .event] #[`domainIndex],
  constructor `transformSystem .system #[.converter, .system] #[`signature],
  constructor `parallelSystems .system #[.system, .interface]
    #[`ordered, `router],
  constructor `forgetMbo .system #[.game] #[`presentationEquality],

  constructor `converterAtom .converter #[.interface, .interface]
    #[`outerSignature, `innerSignature],
  constructor `identityConverter .converter #[.interface] #[`signature],
  constructor `blockingConverter .converter #[.interface] #[`attachmentSite],
  constructor `queryRestriction .converter #[.quantity] #[`queryBudget],
  constructor `domainFilter .converter #[.event] #[`domainIndex],
  constructor `blockRestriction .converter #[.formalArtifact, .quantity]
    #[`encoding, `blockBudget],
  constructor `relabelling .converter #[.formalArtifact, .formalArtifact]
    #[`inputMap, `outputMap],
  constructor `serialConverters .converter #[.converter, .converter]
    #[`firstApplied, `secondApplied, `signature],
  constructor `parallelConverters .converter #[.converter]
    #[`ordered, `router],

  constructor `gameAtom .game #[.interface] #[`signature],
  constructor `enhanceWithMbo .game #[.system, .event]
    #[`gamesFor, `monotonicity],
  constructor `restrictGame .game #[.game, .converter] #[`restriction],
  constructor `transformGame .game #[.converter, .game] #[`signature],

  constructor `partialEnvironment .strategy #[.interface]
    #[`acceptedHistory],
  constructor `totalEnvironment .strategy #[.interface]
    #[`attemptedHistory],
  constructor `signedPartialPde .strategy #[.law] #[`signStatus],
  constructor `normalizedAmbientTotalPde .strategy #[.law]
    #[`weightStatus, `attemptedHistory],
  constructor `strictDistinguisher .strategy #[.converter]
    #[`unitToBoolProtocol],
  constructor `explicitSchedule .history #[.history] #[`fixed],
  constructor `inducedSchedule .history #[.strategy, .system, .quantity]
    #[`horizon],
  constructor `admittedSchedule .history #[.history, .event] #[`domainIndex],

  constructor `query .history #[.formalArtifact],
  constructor `answer .history #[.formalArtifact],
  constructor `inputHistory .history #[.history] #[`acceptedHistory],
  constructor `attemptedHistory .history #[.history] #[`attemptedHistory],
  constructor `transcript .history #[.history] #[`queryAnswerPairs],
  constructor `prefix .history #[.history, .quantity] #[`temporalBoundary],
  constructor `inducedQueries .history #[.strategy, .system, .quantity]
    #[`horizon],
  constructor `encodedBlocks .history #[.formalArtifact, .formalArtifact]
    #[`encoding],
  constructor `callSite .history #[.formalArtifact, .quantity]
    #[`blockPosition],

  constructor `sourceLaw .law #[.system] #[`presentation],
  constructor `gameSourceLaw .law #[.game] #[`presentation],
  constructor `transcriptLaw .law #[.system, .strategy, .quantity]
    #[`horizon],
  constructor `outputLaw .law #[.system, .history],
  constructor `notWonLaw .law #[.game, .strategy, .quantity]
    #[`unnormalized, `horizon],
  constructor `conditionedLaw .law #[.law, .event] #[`nonzeroMass],
  constructor `pushforward .law #[.converter, .law],
  constructor `extendedLaw .law #[.law, .formalArtifact] #[`reveal],
  constructor `jointLaw .law #[.law, .law] #[`nonnegative, `marginals],
  constructor `marginal .law #[.law] #[`side],
  constructor `signedExpansion .law #[.law, .law] #[`signedAllowed],

  constructor `eventAtom .event #[.formalArtifact] #[`scope],
  constructor `gameSystemWinnable .event #[.carrier, .carrier]
    #[`queryType, `answerType],
  constructor `holdsBy .event #[.history, .quantity, .event]
    #[`temporalBoundary],
  constructor `eventComplement .event #[.event] #[`complement],
  constructor `eventUnion .event #[.event] #[`scope],
  constructor `eventIntersection .event #[.event] #[`scope],
  constructor `collision .event #[.formalArtifact, .proofObject]
    #[`equalityCriterion],
  constructor `freshness .event #[.history, .history] #[`scope],
  constructor `winning .event #[.game, .strategy, .quantity] #[`horizon],
  constructor `disagreement .event #[.law] #[`jointLaw],

  constructor `weight .quantity #[.law] #[`scalarCarrier],
  constructor `mass .quantity #[.law, .event] #[`scalarCarrier],
  constructor `probability .quantity #[.law, .event]
    #[`normalized, `scalarCarrier],
  constructor `distance .quantity #[.system, .system, .strategy]
    #[`distanceKind, `observerScope, `orientation],
  constructor `advantage .quantity #[.system, .system, .strategy]
    #[`advantageKind, `observerScope, `orientation],
  constructor `winningProbability .quantity #[.game, .strategy]
    #[`winningKind, `winningScope],
  constructor `winnability .quantity #[.game] #[`winnabilityIndex],
  constructor `cardinality .quantity #[.formalArtifact] #[`finite],
  constructor `opaqueQuantity .quantity #[.formalArtifact]
    #[`exactScalarType, `unsupported],

  constructor `specificationAtom .specification #[.formalArtifact] #[`carrier],
  constructor `singletonSpecification .specification #[.system]
    #[`singleton],
  constructor `imageSpecification .specification
    #[.converter, .specification] #[`constructorImage],
  constructor `relaxedSpecification .specification
    #[.specification, .quantity] #[`errorBudget],
  constructor `filteredSpecification .specification
    #[.specification, .event] #[`filter],
  constructor `parallelSpecification .specification #[.specification]
    #[`ordered]
]

private def compilationRule (number : Nat) (id : Name) (stage : InferenceStage)
    (inputs outputs invariants : List String) : CompilationRuleSpec :=
  { number, id, stage, requiredInputs := names inputs,
    produces := names outputs, invariants := names invariants }

def compilationRules : Array CompilationRuleSpec := #[
  compilationRule 1 `registeredGrounding .grounding
    ["checkedHead", "profile", "selectors"] ["semanticObject"]
    ["signatureMatch", "noNameGuessing"],
  compilationRule 2 `structuralComposition .semanticComposition
    ["registeredConstructor", "typedOperands"] ["compositeSemanticObject"]
    ["preserveOpaqueChildren", "preserveOperandOrder"],
  compilationRule 3 `formalEvidenceNormalization .evidenceNormalization
    ["checkedConclusion", "rule", "operands", "obligations"]
    ["semanticApplication"] ["recordEvidenceCoverage", "eraseTacticIdentity"],
  compilationRule 4 `entityIntroduction .clausePlanning
    ["newReferent", "entitySpec", "occurrenceContext"] ["referencePlan"]
    ["dependencySafeAggregation", "agreement"],
  compilationRule 5 `relationToClause .clausePlanning
    ["relationSpec", "typedOperands", "occurrenceContext"] ["clausePlan"]
    ["valency", "selectionalRestrictions"],
  compilationRule 6 `rootForegrounding .discoursePlanning
    ["theoremRoot", "bridgeGraph"] ["rootClause"]
    ["preserveRootRegister"],
  compilationRule 7 `operationalDefinition .clausePlanning
    ["newConverter", "interfaces", "behaviour"] ["definitionClauses"]
    ["outsideInsideRoles", "noEmptyCopula"],
  compilationRule 8 `representationAndRoleAssignment .semanticComposition
    ["checkedBridge", "entity", "role"] ["scopedRoleAssignment"]
    ["presentationNotBehaviour", "roleNotIdentity", "scope"],
  compilationRule 9 `predicateEventDefinition .clausePlanning
    ["event", "checkedIff", "temporalScope"] ["definitionClause"]
    ["preserveIff", "preserveTemporalScope"],
  compilationRule 10 `causalInference .discoursePlanning
    ["premise", "application", "conclusion"] ["causalEdge"]
    ["premiseMarkedSubstantive", "decodedIntermediateClaim"],
  compilationRule 11 `conditioningAndExceptionScope .clausePlanning
    ["law", "eventComplement", "checkedProperties"] ["conditionedClause"]
    ["scopeAllCoordinatedClauses", "noUnlicensedNormalization"],
  compilationRule 12 `precisionElaboration .discoursePlanning
    ["proseClaim", "exactFormula", "sameSemanticAnchor"] ["elaborationEdge"]
    ["noDuplicatePeerClaims"],
  compilationRule 13 `preservationUnderCommonOperation .clausePlanning
    ["preservationRule", "priorRelation", "commonOperation"]
    ["preservationClause"] ["sameOperationBothSides", "safeAnaphora"],
  compilationRule 14 `equalityGuidedSubstitution .discoursePlanning
    ["checkedEquality", "currentClaim", "resultClaim"] ["substitutionEdge"]
    ["tacticIndependent", "operandIdentity"],
  compilationRule 15 `registeredTheoremApplication .clausePlanning
    ["registeredRule", "typedPremises", "conclusion"] ["resultClause"]
    ["stateConsequence", "noLeanDeclarationName"],
  compilationRule 16 `goalShiftReduction .discoursePlanning
    ["reductionApplication", "residualGoal"] ["foregroundShift"]
    ["goalTransformationChecked"],
  compilationRule 17 `nonadaptiveScheduleFixation .discoursePlanning
    ["nonadaptiveStrategy", "inducedSchedule", "budget"] ["scheduleClause"]
    ["scheduleFixedBeforeAnswers"],
  compilationRule 18 `perScheduleEstimate .discoursePlanning
    ["fixedSchedule", "admissibility", "event", "law", "bound"]
    ["estimateClause", "supremumLift"] ["retainAllExperimentOperands"],
  compilationRule 19 `boundChaining .discoursePlanning
    ["compatibleComparisons"] ["boundParagraph"]
    ["checkedRepeatedTerms", "preserveOrientation"],
  compilationRule 20 `constructionClosure .discoursePlanning
    ["rootConstruction", "realizationBridge", "systemBound"]
    ["constructionConclusion"] ["returnToRootRegister"],
  compilationRule 21 `referenceSafety .discoursePlanning
    ["discourseState", "referent", "scope"] ["referencePlan"]
    ["uniqueCompatibleAntecedent", "expansionScope"],
  compilationRule 22 `routineCompression .compression
    ["checkedRegion", "beforeMeaning", "afterMeaning", "routineClass"]
    ["coverageReceipt"] ["semanticEquivalence", "noTacticNameClassification"],
  compilationRule 23 `safeFallback .fallback
    ["exactExpression", "exactType", "failureReason"] ["formalFallback"]
    ["retainExactSource", "markUnsupported", "noInventedProse"]
]

private def ruleContract (id : RuleId) (implementation : ImplementationStatus)
    (publication : PublicationStatus)
    (evidence : Array EvidenceRequirement) : RuleContract :=
  { ruleId := id, implementation, publication, evidence }

private def implementedEvidence : Array EvidenceRequirement := #[
  .positiveGrammar, .negativeGrammar, .ontologySchema, .deterministicLowering,
  .checkedEffect, .sentenceTrace, .canonicalRendering, .sourceAttestation]

private def semanticEvidence : Array EvidenceRequirement := #[
  .ontologySchema, .deterministicLowering, .sentenceTrace, .sourceAttestation]

def ruleContracts : Array RuleContract := #[
  ruleContract structuralConclude .ordinaryLean .notApplicable #[],
  ruleContract structuralGoalReminder .implemented .published implementedEvidence,
  ruleContract structuralFix .implemented .published implementedEvidence,
  ruleContract structuralAssume .implemented .published implementedEvidence,
  ruleContract structuralChoose .implemented .published implementedEvidence,
  ruleContract structuralConjunction .implemented .published implementedEvidence,
  ruleContract structuralTheorem .implemented .published implementedEvidence,

  ruleContract acConstructionFrom .implemented .published implementedEvidence,
  ruleContract acEqualityFrom .implemented .published implementedEvidence,
  ruleContract acReplaceProtocol .implemented .published implementedEvidence,
  ruleContract acCompose .implemented .published implementedEvidence,
  ruleContract acSimulator .implemented .published implementedEvidence,
  ruleContract acContextRight .implemented .published implementedEvidence,
  ruleContract acContextLeft .implemented .published implementedEvidence,
  ruleContract acTriangleClose .implemented .pendingAttestation implementedEvidence,
  ruleContract acTriangleReduce .implemented .pendingAttestation implementedEvidence,
  ruleContract acRelax .implemented .pendingAttestation implementedEvidence,
  ruleContract acFiltered .implemented .pendingAttestation implementedEvidence,
  ruleContract acParallel .implemented .pendingAttestation implementedEvidence,
  ruleContract acComposeSimulators .implemented .pendingAttestation implementedEvidence,

  ruleContract rsConditionalLaw .implemented .applicationScoped implementedEvidence,
  ruleContract rsPdsEquivalent .implemented .pendingAttestation implementedEvidence,
  ruleContract rsGameEquivalent .implemented .published implementedEvidence,
  ruleContract rsForgetGame .implemented .applicationScoped implementedEvidence,
  ruleContract rsEnhanceWithMBO .implemented .pendingAttestation implementedEvidence,
  ruleContract rsFilterConditionalLaw .implemented .pendingAttestation implementedEvidence,
  ruleContract rsFilterQueriesConditionalLaw .implemented .pendingAttestation implementedEvidence,
  ruleContract rsConditionalBlindBound .implemented .pendingAttestation implementedEvidence,
  ruleContract rsConditionalBlindComparison .implemented .applicationScoped implementedEvidence,
  ruleContract rsBlindUniversal .implemented .pendingAttestation implementedEvidence,
  ruleContract rsBlindWinningBound .implemented .applicationScoped implementedEvidence,
  ruleContract rsMassBound .implemented .pendingAttestation implementedEvidence,
  ruleContract rsCommonDomainDataProcessing .implemented .pendingAttestation implementedEvidence,
  ruleContract rsHCoefficient .implemented .pendingAttestation implementedEvidence,
  ruleContract rsTransformConditionalLaw .implemented .pendingAttestation implementedEvidence,
  ruleContract rsWinningMassIdentity .implemented .pendingAttestation implementedEvidence,
  ruleContract rsBindSystem .implemented .published implementedEvidence,
  ruleContract rsDeclareRestrictedURF .rejected .notApplicable #[],
  ruleContract rsDefineCharacterizedMBO .implemented .published implementedEvidence,
  ruleContract rsDeclareEnhancedURFGame .rejected .notApplicable #[],
  ruleContract rsDeclareRestrictedGame .rejected .notApplicable #[],
  ruleContract rsDeclareRestrictedURP .rejected .notApplicable #[],
  ruleContract rsRestrictedEnhancedURFGameNonnegative .rejected .notApplicable #[],

  ruleContract proofExactEquivalence .implemented .internal semanticEvidence,
  ruleContract proofConstruction .implemented .internal semanticEvidence,
  ruleContract proofDistanceBound .implemented .internal semanticEvidence,
  ruleContract proofAdvantageBound .implemented .internal semanticEvidence,
  ruleContract proofIgnoreGameMBO .implemented .internal semanticEvidence,
  ruleContract proofTriangleHybrid .implemented .internal semanticEvidence,
  ruleContract proofConditionalEquivalenceUnderRestriction .implemented .internal semanticEvidence,
  ruleContract proofCollisionConditionalEquivalence .implemented .applicationScoped semanticEvidence,
  ruleContract proofBlindWinningBound .implemented .internal semanticEvidence,
  ruleContract proofBlindWinningToNonadaptive .implemented .internal semanticEvidence,
  ruleContract proofNonadaptiveQueriesFixed .implemented .internal semanticEvidence,
  ruleContract proofCommonDomainDataProcessing .implemented .internal semanticEvidence,
  ruleContract proofRestrictionApplicationEquation .implemented .internal semanticEvidence,
  ruleContract proofConditionalUniformOutputs .implemented .applicationScoped semanticEvidence,
  ruleContract proofDistinctTerminalInputs .implemented .applicationScoped semanticEvidence,
  ruleContract proofGamePlayingFundamentalLemma .implemented .internal semanticEvidence,
  ruleContract proofCoupling .implemented .internal semanticEvidence,
  ruleContract proofRepresentativeSelection .implemented .internal semanticEvidence,
  ruleContract proofWinnability .implemented .internal semanticEvidence,
  ruleContract proofSignedExpansion .implemented .internal semanticEvidence,
  ruleContract proofCounting .implemented .internal semanticEvidence,
  ruleContract proofCollisionProbabilityBound .implemented .internal semanticEvidence,
  ruleContract proofCollisionMassBound .implemented .internal semanticEvidence,
  ruleContract proofBirthdayBound .implemented .internal semanticEvidence,
  ruleContract proofScalarClosure .implemented .internal semanticEvidence,
  ruleContract proofArithmetic .implemented .internal semanticEvidence,
  ruleContract proofRewriting .implemented .internal semanticEvidence,
  ruleContract proofMonotonicity .implemented .internal semanticEvidence
]

def ruleContractFor? (id : RuleId) : Option RuleContract :=
  ruleContracts.find? (·.ruleId == id)

private def duplicateCount {α : Type} [BEq α] (values : Array α) : Nat :=
  values.size - values.toList.eraseDups.length

def missingEntityConcepts : Array ConceptId :=
  Ontology.allConcepts.filter fun id => !entities.any (·.concept == id)

def extraEntityConcepts : Array ConceptId :=
  entities.map (·.concept) |>.filter fun id => !Ontology.allConcepts.contains id

def missingRelations : Array RelationId :=
  Relations.allRelations.filter fun id => !relations.any (·.relation == id)

def extraRelations : Array RelationId :=
  relations.map (·.relation) |>.filter fun id => !Relations.allRelations.contains id

def missingRules : Array RuleId :=
  Rules.allRules.filter fun id => !ruleContracts.any (·.ruleId == id)

def extraRules : Array RuleId :=
  ruleContracts.map (·.ruleId) |>.filter fun id => !Rules.allRules.contains id

def compilationRuleNumbers : Array Nat := compilationRules.map (·.number)

def unknownCanonicalSurfaceRules : Array RuleId :=
  SurfaceContract.canonicalForms.map (·.ruleId) |>.filter fun id =>
    !Rules.allRules.contains id

def duplicateCanonicalSurfaceIds : Nat :=
  duplicateCount (SurfaceContract.canonicalForms.map (·.id))

def publishedAuthoringRulesWithoutCanonicalSurface : Array RuleId :=
  ruleContracts.filterMap fun entry =>
    if entry.publication == .published &&
        entry.ruleId != structuralTheorem &&
        (SurfaceContract.canonicalFormsForRule entry.ruleId).isEmpty then
      some entry.ruleId
    else none

def isValid : Bool :=
  entityFamilies.size == 14 &&
  duplicateCount (entityFamilies.map (·.kind)) == 0 &&
  missingEntityConcepts.isEmpty && extraEntityConcepts.isEmpty &&
  duplicateCount (entities.map (·.concept)) == 0 &&
  missingRelations.isEmpty && extraRelations.isEmpty &&
  duplicateCount (relations.map (·.relation)) == 0 &&
  missingRules.isEmpty && extraRules.isEmpty &&
  duplicateCount (ruleContracts.map (·.ruleId)) == 0 &&
  compilationRules.size == 23 &&
  compilationRuleNumbers == (List.range 23 |>.map (· + 1) |>.toArray) &&
  duplicateCount (expressionConstructors.map (·.id)) == 0 &&
  unknownCanonicalSurfaceRules.isEmpty &&
  duplicateCanonicalSurfaceIds == 0 &&
  publishedAuthoringRulesWithoutCanonicalSurface.isEmpty &&
  SurfaceContract.forms.all (·.witnessComplete)

end CryptoLanguage.LanguageDesign.Contract
