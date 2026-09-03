/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Informalization.Semantics.Canonical
import Informalization.Semantics.Validation
import Informalization.Semantics.Plan
import Informalization.Semantics.Realize

/-!
# Machine-readable semantic reports

This is the diagnostic boundary for exercising semantic recovery.  Alongside
roles, graph edges, proof plans, and checked formal provenance, it includes the
first generic semantic-discourse realization slice.  The latter remains linked
to exact evidence identifiers and is not the legacy manual informalizer.
-/

namespace Informalization.Semantics.Report

open Lean Meta
open Informalization.Semantics
open Informalization.Semantics.Registry
open Informalization.Semantics.Canonical
open Informalization.Semantics.Validation
open Informalization.Semantics.Plan
open Informalization.Semantics.EvidenceCompression

private def optionStringJson : Option String → Json
  | some value => .str value
  | none => .null

private def evidenceKindCode : EvidenceKind → String
  | .declaration => "declaration"
  | .application => "application"
  | .binder => "binder"
  | .proposition => "proposition"
  | .proofTerm => "proof-term"

private def entityRoleCode : EntityRole → String
  | .carrier => "carrier"
  | .randomSystem => "random-system"
  | .game => "game"
  | .converter => "converter"
  | .distinguisher => "distinguisher"
  | .environment => "environment"
  | .transcript => "transcript"
  | .event => "event"
  | .collisionCondition => "collision-condition"
  | .queryBudget => "query-budget"
  | .probability => "probability"
  | .distribution => "distribution"
  | .errorBound => "error-bound"
  | .simulator => "simulator"
  | .custom name => "custom:" ++ name.toString

private def systemRoleCode : SystemRole → String
  | .atom => "atom"
  | .uniformRandomFunction => "uniform-random-function"
  | .uniformRandomPermutation => "uniform-random-permutation"
  | .presentationQuotient => "presentation-quotient"
  | .converterApplication => "converter-application"
  | .queryRestriction => "query-restriction"
  | .forgetGame => "forget-game"
  | .transform => "transform"
  | .parallelComposition => "parallel-composition"
  | .serialComposition => "serial-composition"
  | .idealFunctionality => "ideal-functionality"
  | .custom name => "custom:" ++ name.toString

private def gameRoleCode : GameRole → String
  | .atom => "atom"
  | .enhanceWithMBO => "enhance-with-mbo"
  | .queryRestriction => "query-restriction"
  | .transform => "transform"
  | .custom name => "custom:" ++ name.toString

private def converterRoleCode : ConverterRole → String
  | .atom => "atom"
  | .queryRestriction => "query-restriction"
  | .blockRestriction => "block-restriction"
  | .serialComposition => "serial-composition"
  | .parallelComposition => "parallel-composition"
  | .custom name => "custom:" ++ name.toString

private def quantityRoleCode : QuantityRole → String
  | .distinguishingAdvantage => "distinguishing-advantage"
  | .statisticalDistance => "statistical-distance"
  | .winningProbability => "winning-probability"
  | .blindWinningProbability => "blind-winning-probability"
  | .badEventProbability => "bad-event-probability"
  | .systemWeight => "system-weight"
  | .custom name => "custom:" ++ name.toString

private def relationRoleCode : RelationRole → String
  | .equality => "equality"
  | .upperBound => "upper-bound"
  | .indistinguishability => "indistinguishability"
  | .advantageBound => "advantage-bound"
  | .conditionalEquivalence => "conditional-equivalence"
  | .gameEquivalence => "game-equivalence"
  | .construction => "construction"
  | .reduction => "reduction"
  | .eventImplication => "event-implication"
  | .custom name => "custom:" ++ name.toString

private def proofRuleRoleCode : ProofRuleRole → String
  | .exactEquivalence => "exact-equivalence"
  | .construction => "construction"
  | .distanceBound => "distance-bound"
  | .advantageBound => "advantage-bound"
  | .ignoreGameMBO => "ignore-game-mbo"
  | .triangleHybrid => "triangle-hybrid"
  | .hTechnique => "h-technique"
  | .conditionalEquivalence => "conditional-equivalence"
  | .conditionalEquivalenceUnderRestriction => "conditional-equivalence-under-restriction"
  | .collisionConditionalEquivalence => "collision-conditional-equivalence"
  | .conditionalEquivalenceToBlindWinning => "conditional-equivalence-to-blind-winning"
  | .blindWinningBound => "blind-winning-bound"
  | .blindWinningToNonadaptive => "blind-winning-to-nonadaptive"
  | .nonadaptiveQueriesFixed => "nonadaptive-queries-fixed"
  | .commonDomainDataProcessing => "common-domain-data-processing"
  | .restrictionApplicationEquation => "restriction-application-equation"
  | .conditionalUniformOutputs => "conditional-uniform-outputs"
  | .distinctTerminalInputs => "distinct-terminal-inputs"
  | .gamePlayingFundamentalLemma => "game-playing-fundamental-lemma"
  | .coupling => "coupling"
  | .representativeSelection => "representative-selection"
  | .winnability => "winnability"
  | .signedExpansion => "signed-expansion"
  | .counting => "counting"
  | .collisionProbabilityBound => "collision-probability-bound"
  | .collisionMassBound => "collision-mass-bound"
  | .birthdayBound => "birthday-bound"
  | .scalarClosure => "scalar-closure"
  | .arithmetic => "arithmetic"
  | .rewriting => "rewriting"
  | .monotonicity => "monotonicity"
  | .custom name => "custom:" ++ name.toString

private def nodeRoleCode : NodeRole → String
  | .entity role => "entity/" ++ entityRoleCode role
  | .system role => "system/" ++ systemRoleCode role
  | .game role => "game/" ++ gameRoleCode role
  | .converter role => "converter/" ++ converterRoleCode role
  | .quantity role => "quantity/" ++ quantityRoleCode role
  | .proposition role => "proposition/" ++ relationRoleCode role
  | .proofRule role => "proof-rule/" ++ proofRuleRoleCode role

private def argumentRoleCode : ArgumentRole → String
  | .subject => "subject"
  | .inputSpace => "input-space"
  | .outputSpace => "output-space"
  | .alphabet => "alphabet"
  | .realSystem => "real-system"
  | .idealSystem => "ideal-system"
  | .sourceSystem => "source-system"
  | .targetSystem => "target-system"
  | .transformedSystem => "transformed-system"
  | .converter => "converter"
  | .game => "game"
  | .condition => "condition"
  | .queryBudget => "query-budget"
  | .distinguisher => "distinguisher"
  | .environment => "environment"
  | .transcript => "transcript"
  | .event => "event"
  | .badEvent => "bad-event"
  | .bound => "bound"
  | .errorTerm => "error-term"
  | .probabilityLaw => "probability-law"
  | .premise index => s!"premise:{index}"
  | .conclusion => "conclusion"
  | .custom name => "custom:" ++ name.toString

private def salienceCode : Salience → String
  | .primary => "primary"
  | .supporting => "supporting"
  | .implementation => "implementation"
  | .implicit => "implicit"

private def securityKindCode : SecurityStatementKind → String
  | .advantageBound => "advantage-bound"
  | .distanceBound => "distance-bound"
  | .indistinguishability => "indistinguishability"
  | .winningProbabilityBound => "winning-probability-bound"
  | .badEventProbabilityBound => "bad-event-probability-bound"
  | .construction => "construction"
  | .reduction => "reduction"

private def genreCode : Genre → String
  | .exactEquivalence => "exact-equivalence"
  | .conditionalEquivalence => "conditional-equivalence"
  | .blindWinningBound => "blind-winning-bound"
  | .hTechnique => "h-technique"
  | .hybrid => "hybrid"
  | .gameHop => "game-hop"
  | .counting => "counting"
  | .generic => "generic"

private def planKindCode : Plan.Kind → String
  | .conditionalEquivalenceBlind => "conditional-equivalence/blind-winning"
  | .exactEquivalence => "exact-equivalence"
  | .conditionalEquivalence => "conditional-equivalence"
  | .blindWinningBound => "blind-winning-bound"
  | .hTechnique => "h-technique"
  | .hybrid => "hybrid"
  | .gameHop => "game-hop"
  | .counting => "counting"
  | .generic => "generic"
  | .fallback => "fallback"

private def routineEffectCode : RoutineEffect → String
  | .singletonMembership => "singleton-membership"
  | .singletonEqualityWrapper => "singleton-equality-wrapper"
  | .definitionalOrCoercionNormalization => "definitional-or-coercion-normalization"

private def carrierAssumptionKindCode : CarrierAssumptionKind → String
  | .inhabited => "inhabited"
  | .nontrivial => "nontrivial"

private def argumentJson (argument : SemanticArgument) : Json :=
  Json.mkObj [
    ("role", .str (argumentRoleCode argument.role)),
    ("salience", .str (salienceCode argument.salience)),
    ("formal", .str (reprStr argument.source))
  ]

private def nodeJson (index : Nat) (node : Node) : Json :=
  Json.mkObj [
    ("id", .num index),
    ("role", .str (nodeRoleCode node.role)),
    ("declaration", optionStringJson (node.provenance.declaration?.map Name.toString)),
    ("evidenceKind", .str (evidenceKindCode node.provenance.evidenceKind)),
    ("formal", .str (reprStr node.provenance.expression)),
    ("arguments", .arr (node.arguments.map argumentJson))
  ]

private def edgeJson (edge : Edge) : Json :=
  Json.mkObj [
    ("parent", .num edge.parent.index),
    ("child", .num edge.child.index),
    ("role", .str (argumentRoleCode edge.argument.role))
  ]

private def premiseJson (premise : ProofEvidence.Premise) : Json :=
  Json.mkObj [
    ("role", .str (argumentRoleCode premise.descriptor.role)),
    ("salience", .str (salienceCode premise.descriptor.salience)),
    ("position", .num premise.descriptor.position),
    ("formal", .str (reprStr premise.descriptor.proposition))
  ]

private def stepJson (index : Nat) (step : Plan.Step) : Json :=
  Json.mkObj [
    ("id", .num index),
    ("genre", .str (genreCode step.genre)),
    ("semanticDepth", .num step.semanticDepth),
    ("rule", .str (proofRuleRoleCode step.application.role)),
    ("declaration", optionStringJson
      (step.application.provenance.declaration?.map Name.toString)),
    ("premises", .arr (step.premises.map premiseJson)),
    ("semanticNodes", .arr (step.semanticGraph.nodes.map fun node =>
      .str (nodeRoleCode node.role)))
  ]

private def stepOriginJson : Plan.StepOrigin → Json
  | .root => Json.mkObj [("kind", .str "root")]
  | .macroExpansion parentStepId => Json.mkObj [
      ("kind", .str "macro-expansion"),
      ("parentStep", .num parentStepId)
    ]
  | .premise parentStepId key descriptor => Json.mkObj [
      ("kind", .str "premise"),
      ("parentStep", .num parentStepId),
      ("telescopePosition", .num key.telescopePosition),
      ("proofOrdinal", .num key.proofOrdinal),
      ("role", .str (argumentRoleCode descriptor.role)),
      ("salience", .str (salienceCode descriptor.salience))
    ]

private def proofPathSegmentJson : CanonicalProof.ProofPathSegment → Json
  | .fallbackChild index => Json.mkObj [
      ("kind", .str "fallback-child"),
      ("index", .num index)
    ]
  | .macroExpansion => Json.mkObj [("kind", .str "macro-expansion")]
  | .premise key => Json.mkObj [
      ("kind", .str "premise"),
      ("telescopePosition", .num key.telescopePosition),
      ("proofOrdinal", .num key.proofOrdinal)
    ]

private def expressionShape (expression : Expr) : String :=
  match expression.consumeMData with
  | .bvar _ => "bound-variable"
  | .fvar _ => "local-constant"
  | .mvar _ => "metavariable"
  | .sort _ => "sort"
  | .const _ _ => "constant"
  | .app _ _ => "application"
  | .lam .. => "lambda"
  | .forallE .. => "function-type"
  | .letE .. => "let"
  | .lit _ => "literal"
  | .mdata _ _ => "metadata"
  | .proj _ _ _ => "projection"

private def expressionHeadJson (expression : Expr) : Json :=
  match headDeclaration? expression with
  | some declaration => .str declaration.toString
  | none => .null

private def fallbackRegionJson (region : ProofPlan.FallbackRegion) : Json :=
  Json.mkObj [
    ("path", .arr (region.path.map proofPathSegmentJson)),
    ("proofHash", .str (toString region.payload.proof.hash)),
    ("proofShape", .str (expressionShape region.payload.proof)),
    ("proofHead", expressionHeadJson region.payload.proof),
    ("expectedHash", .str (toString region.payload.expected.hash)),
    ("expectedShape", .str (expressionShape region.payload.expected)),
    ("expectedHead", expressionHeadJson region.payload.expected)
  ]

private def propositionFingerprintJson
    (fingerprint : EvidenceCompression.PropositionFingerprint) : Json :=
  Json.mkObj [
    ("head", optionStringJson (fingerprint.head?.map Name.toString)),
    ("normalizedHash", .str (toString fingerprint.normalizedHash))
  ]

private def carrierAssumptionJson (assumption : CarrierAssumption) : Json :=
  Json.mkObj [
    ("kind", .str (carrierAssumptionKindCode assumption.kind)),
    ("proposition", propositionFingerprintJson assumption.proposition),
    ("occurrences", .arr (assumption.occurrences.map fun path =>
      .arr (path.map proofPathSegmentJson)))
  ]

private def primaryHypothesisJson (hypothesis : PrimaryHypothesis) : Json :=
  Json.mkObj [
    ("declaration", .str hypothesis.declaration.toString),
    ("proposition", propositionFingerprintJson hypothesis.proposition),
    ("occurrences", .arr (hypothesis.occurrences.map fun path =>
      .arr (path.map proofPathSegmentJson)))
  ]

private def compressionJson (compression : EvidenceCompression.Result) : Json :=
  Json.mkObj [
    ("coverageComplete", .bool compression.coverageComplete),
    ("evidenceCount", .num compression.evidenceCount),
    ("coverageEntryCount", .num compression.coverage.size),
    ("rootEffect", optionStringJson (compression.rootEffect?.map routineEffectCode)),
    ("absorbedEffects", .arr (compression.absorbedEffects.map fun effect =>
      .str (routineEffectCode effect))),
    ("carrierAssumptions", .arr
      (compression.carrierAssumptions.map carrierAssumptionJson)),
    ("primaryHypotheses", .arr
      (compression.primaryHypotheses.map primaryHypothesisJson)),
    ("uncoveredRegions", .arr
      (compression.uncoveredRegions.map fallbackRegionJson))
  ]

/-- Recursive registered-rule support graph.  The flat `steps` array remains a
compatibility index; this tree is the source of disclosure ancestry. -/
private partial def supportTreeJson (tree : Plan.SupportTree) : Json :=
  Json.mkObj [
    ("step", .num tree.view.stepId),
    ("parentStep", match tree.view.parentStepId? with
      | some parent => .num parent
      | none => .null),
    ("origin", stepOriginJson tree.view.origin),
    ("children", .arr (tree.children.map supportTreeJson))
  ]

private def planJson (plan : ProofPlan) : Json :=
  Json.mkObj [
    ("kind", .str (planKindCode plan.kind)),
    ("dominantGenre", optionStringJson (plan.dominantGenre?.map genreCode)),
    ("genres", .arr (plan.genres.map fun genre => .str (genreCode genre))),
    ("hasFallback", .bool plan.hasFallback),
    ("fallbackEvidenceCount", .num plan.fallbackEvidence.size),
    ("fallbackRegions", .arr (plan.fallbackRegions.map fallbackRegionJson)),
    ("evidenceCompression", compressionJson plan.compression),
    ("steps", .arr (plan.steps.mapIdx stepJson)),
    ("supportForest", .arr (plan.supportForest.map supportTreeJson))
  ]

/-- Semantic recovery result for one selected declaration. -/
structure DeclarationReport where
  declaration : Name
  securityKind? : Option SecurityStatementKind
  graph? : Option Graph
  proofPlan? : Option ProofPlan := none
  discourse? : Option Realize.Document := none
  deriving Inhabited

def DeclarationReport.toJson (report : DeclarationReport) : Json :=
  Json.mkObj [
    ("declaration", .str report.declaration.toString),
    ("securityKind", optionStringJson (report.securityKind?.map securityKindCode)),
    ("semanticRoot", .bool report.securityKind?.isSome),
    ("proofPlan", report.proofPlan?.map planJson |>.getD .null),
    ("discourse", report.discourse?.map (·.toJson) |>.getD .null),
    ("graph", match report.graph? with
      | none => .null
      | some graph => Json.mkObj [
          ("root", .num graph.root.index),
          ("nodes", .arr (graph.nodes.mapIdx nodeJson)),
          ("edges", .arr (graph.edges.map edgeJson))
        ])
  ]

/-- Recover a statement graph and security-root classification.  This is a
typed diagnostic artifact, not a natural-language explanation. -/
def ofConclusion (environment : Environment) (catalog : Catalog)
    (declaration : Name) (conclusion : Expr)
    (canonicalProfile : DecoderProfile := {}) : MetaM DeclarationReport := do
  let securityKind? := (← securityStatementRootWith? environment catalog conclusion).map (·.kind)
  let graph? ← recoverGraphWith? environment catalog conclusion
  let proofPlan? ← Plan.fromDeclarationWithProfile?
    environment catalog canonicalProfile declaration
  let discourse? : Option Realize.Document ← match graph?, proofPlan? with
    | some graph, some proofPlan => do
        let discourse ← Discourse.ofGraphAndPlan graph proofPlan canonicalProfile
        let discourse := { discourse with rootDeclaration? := some declaration }
        let realized ← Realize.document discourse
        pure (some realized)
    | _, _ => pure none
  return { declaration, securityKind?, graph?, proofPlan?, discourse? }

def documentToJson (reports : Array DeclarationReport) : Json :=
  .arr (reports.map DeclarationReport.toJson)

end Informalization.Semantics.Report
