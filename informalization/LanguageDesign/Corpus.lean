import LanguageDesign.Rules

/-!
# Source-controlled dialect contracts

An ontology rule does not by itself license an English predicate. Each public
sentence form is tied here to one source construction (or, for carrier
plumbing, to an exact checked relation). Verbose and Informalization can
therefore share a mathematical rule without either frontend inventing an
operational gloss.
-/

namespace CryptoLanguage.LanguageDesign.Corpus

open Lean
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules

inductive Source where
  | projectControlled
  | languageDesignMassot
  | primaryMauRen16
  | primaryJost
  | primaryLiuMau20
  | primaryLanzenberger
  | checkedLibrary
  | proposedPendingAttestation
  | cr18Fallback
deriving Repr, BEq, Inhabited

def Source.label : Source → String
  | .projectControlled => "project-controlled composition"
  | .languageDesignMassot => "Massot controlled-language design"
  | .primaryMauRen16 => "Maurer–Renner 2016"
  | .primaryJost => "Jost thesis"
  | .primaryLiuMau20 => "Liu–Maurer 2020"
  | .primaryLanzenberger => "Lanzenberger thesis"
  | .checkedLibrary => "checked library relation"
  | .proposedPendingAttestation => "proposed; source attestation pending"
  | .cr18Fallback => "Coretti–Rösler 2018 fallback"

inductive Strength where
  /-- The source uses this grammatical construction for the same relation. -/
  | attestedConstruction
  /-- The clause composes source-attested constructions without adding a relation. -/
  | compositionalAdaptation
  /-- The wording states only the exact checked formal relation. -/
  | exactFormalRelation
  /-- The sentence names the checked theorem or method and asserts no gloss. -/
  | checkedMethodName
deriving Repr, BEq, Inhabited

def Strength.label : Strength → String
  | .attestedConstruction => "attested construction"
  | .compositionalAdaptation => "compositional adaptation"
  | .exactFormalRelation => "exact formal relation"
  | .checkedMethodName => "checked method name"

structure Attestation where
  source : Source
  work : String
  locator : String
  construction : Name
  strength : Strength
deriving Repr, BEq, Inhabited

def Attestation.isValid (value : Attestation) : Bool :=
  !value.work.trimAscii.isEmpty && !value.locator.trimAscii.isEmpty &&
    !value.construction.isAnonymous

def Attestation.isPubliclyLicensed (value : Attestation) : Bool :=
  value.isValid && value.source != .proposedPendingAttestation &&
    value.source != .checkedLibrary

private def projectControlled (locator : String) (construction : Name) : Attestation :=
  ⟨.projectControlled, "abstract-crypto language design", locator,
    construction, .compositionalAdaptation⟩

private def liuMau20 (locator : String) (construction : Name)
    (strength : Strength := .attestedConstruction) : Attestation :=
  ⟨.primaryLiuMau20, "Liu–Maurer 2020", locator, construction, strength⟩

private def jost (locator : String) (construction : Name)
    (strength : Strength := .attestedConstruction) : Attestation :=
  ⟨.primaryJost, "Jost thesis", locator, construction, strength⟩

private def cr18Fallback (locator : String) (construction : Name)
    (strength : Strength := .attestedConstruction) : Attestation :=
  ⟨.cr18Fallback, "Coretti–Rösler 2018", locator, construction, strength⟩

private def pendingPrimaryAttestation (locator : String)
    (construction : Name) : Attestation :=
  ⟨.proposedPendingAttestation, "MauRen16-or-later source required", locator,
    construction, .compositionalAdaptation⟩

private def lanzenberger (locator : String) (construction : Name) : Attestation :=
  ⟨.primaryLanzenberger, "Lanzenberger thesis", locator, construction,
    .attestedConstruction⟩

private def pending (locator : String) (construction : Name) : Attestation :=
  ⟨.proposedPendingAttestation, "source attestation required", locator,
    construction, .compositionalAdaptation⟩

private def formal (construction : Name) : Attestation :=
  ⟨.checkedLibrary, "live abstract-crypto and Random Systems declarations",
    "exact public declaration signature", construction, .exactFormalRelation⟩

private def methodName (construction : Name) : Attestation :=
  ⟨.checkedLibrary, "live abstract-crypto and Random Systems declarations",
    "exact public theorem name and signature", construction, .checkedMethodName⟩

/-- The unique dialect contract for a shared mathematical rule. Returning
`none` is intentional: a new rule is not renderable until its language source
has been registered here. -/
def attestationFor? (id : RuleId) : Option Attestation :=
  if id == structuralConclude then
    some (pending "ordinary Lean `exact` is the canonical form"
      `structural.claim.conclude)
  else if id == structuralGoalReminder then
    some (projectControlled "VERBOSE_SPEC §8.2: exact goal announcement"
      `project.proof.goalReminder)
  else if id == structuralFix then
    some (projectControlled "VERBOSE_SPEC §8.2: explicit binder introduction"
      `project.proof.fix)
  else if id == structuralAssume then
    some (projectControlled "VERBOSE_SPEC §8.2: explicit assumption introduction"
      `project.proof.assume)
  else if id == structuralChoose then
    some (projectControlled "VERBOSE_SPEC §8.2: explicit existential elimination"
      `project.proof.choose)
  else if id == structuralConjunction then
    some (projectControlled "VERBOSE_SPEC §8.2: explicit conjunction elimination"
      `project.proof.conjunction)
  else if id == structuralTheorem then
    some (projectControlled "Theorem/Given/Conclusion/Proof/QED layout"
      `project.declaration.theorem)

  else if id == acConstructionFrom then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.follows)
  else if id == acEqualityFrom then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.equality.fromEstablishedIdentity)
  else if id == acReplaceProtocol then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.replacement)
  else if id == acCompose then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.compose)
  else if id == acSimulator then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.simulator)
  else if id == acContextRight then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.rightContext)
  else if id == acContextLeft then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.leftContext)
  else if id == acTriangleClose then
    some (projectControlled "abstract-crypto deterministic AC proof language"
      `project.ac.distance.triangle)
  else if id == acTriangleReduce then
    some (projectControlled "abstract-crypto deterministic AC proof language"
      `project.ac.distance.triangleReduction)
  else if id == acRelax then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.relaxation)
  else if id == acFiltered then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.filtered)
  else if id == acParallel then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.construction.parallel)
  else if id == acComposeSimulators then
    some (projectControlled "abstract-crypto AGENTS: controlled-language extensions"
      `project.ac.simulator.compose)

  else if id == rsConditionalLaw then
    some (formal `lean.pdg.conditionalEquivalence)
  else if id == rsFilterConditionalLaw then
    some (formal `lean.pdg.conditionalEquivalence.filterDomain)
  else if id == rsConditionalBlindBound then
    some (formal `lean.pdg.conditionalEquivalence.blindBound)
  else if id == rsConditionalBlindComparison then
    some (formal `lean.pdg.conditionalEquivalence.blindComparison)
  else if id == rsBlindUniversal then
    some (formal `lean.pdg.blindWinning.universal)
  else if id == rsBlindWinningBound then
    some (formal `lean.blindWinning.boundFromNamedTheorem)
  else if id == rsCommonDomainDataProcessing then
    some (formal `lean.commonDomain.edist.dataProcessing)
  else if id == rsPdsEquivalent then some (formal `lean.pds.observationalEquivalence)
  else if id == rsGameEquivalent then
    some (lanzenberger "Chapter 2, Definitions 2.20–2.28"
      `randomSystems.game.equivalence)
  else if id == rsForgetGame then
    some (formal `lean.pdg.forgetMBO)
  else if id == rsEnhanceWithMBO then
    some (formal `lean.pds.adjoinMBO)
  else if id == rsFilterQueriesConditionalLaw then
    some (formal `lean.pdg.conditionalEquivalence.filterQueries)
  else if id == rsTransformConditionalLaw then
    some (formal `lean.pdg.conditionalEquivalence.transform)
  else if id == rsWinningMassIdentity then
    some (formal `lean.pdg.blindWinning.fixedScheduleIdentity)
  else if id == rsMassBound then
    some (formal `lean.probability.collision.massBound)
  else if id == rsHCoefficient then some (methodName `lean.hCoefficient.theorem)
  else if id == rsBindSystem then
    some (projectControlled
      "VERBOSE_SPEC executable surface: typed Random Systems binder"
      `project.randomSystems.declaration.systemBinder)
  else if id == rsDeclareRestrictedURF then
    some (pending "notation-first replacement required"
      `randomSystems.declaration.restrictedUniformRandomFunction)
  else if id == rsDefineCharacterizedMBO then
    some (projectControlled
      "LANGUAGE_REFERENCE_CORPUS §3.2: exact characterized-MBO surface"
      `project.randomSystems.declaration.characterizedMBO)
  else if id == rsDeclareEnhancedURFGame then
    some (pending "source-attested operational definition required"
      `randomSystems.declaration.enhancedUniformRandomFunctionGame)
  else if id == rsDeclareRestrictedGame then
    some (pending "notation-first replacement required"
      `randomSystems.declaration.restrictedGame)
  else if id == rsDeclareRestrictedURP then
    some (pending "notation-first replacement required"
      `randomSystems.declaration.restrictedUniformRandomPermutation)
  else if id == rsRestrictedEnhancedURFGameNonnegative then
    some (pending "rejected by-construction assertion form"
      `randomSystems.property.restrictedEnhancedURFGameNonnegative)

  else if id == proofExactEquivalence then
    some (formal `lean.proof.exactEquivalence)
  else if id == proofConstruction then
    some (pendingPrimaryAttestation "Maurer-style construction calculus" `maurer.construction.conclusion)
  else if id == proofDistanceBound then
    some (formal `lean.proof.distanceBound)
  else if id == proofAdvantageBound then
    some (formal `lean.proof.advantageBound)
  else if id == proofIgnoreGameMBO then
    some (formal `lean.pdg.forgetMBO)
  else if id == proofTriangleHybrid then
    some (pendingPrimaryAttestation "metric hybrid argument" `maurer.distance.triangle)
  else if id == proofConditionalEquivalenceUnderRestriction then
    some (formal `lean.pdg.conditionalEquivalence.restriction)
  else if id == proofCollisionConditionalEquivalence then
    some (formal `lean.proof.collisionConditionalEquivalence)
  else if id == proofBlindWinningBound then
    some (formal `lean.pdg.blindWinning.bound)
  else if id == proofBlindWinningToNonadaptive then
    some (formal `lean.pdg.blindWinning.nonadaptive)
  else if id == proofNonadaptiveQueriesFixed then
    some (formal `lean.pdg.blindWinning.fixedQueries)
  else if id == proofCommonDomainDataProcessing then
    some (formal `lean.commonDomain.dataProcessing)
  else if id == proofRestrictionApplicationEquation then
    some (formal `lean.converter.restrictionApplicationEquation)
  else if id == proofConditionalUniformOutputs then
    some (formal `lean.proof.conditionalUniformOutputs)
  else if id == proofDistinctTerminalInputs then
    some (formal `lean.proof.distinctTerminalInputs)
  else if id == proofGamePlayingFundamentalLemma then
    some (methodName `lean.gamePlaying.fundamentalLemma)
  else if id == proofCoupling then some (methodName `lean.proof.coupling)
  else if id == proofRepresentativeSelection then
    some (methodName `lean.proof.representativeSelection)
  else if id == proofWinnability then some (methodName `lean.proof.winnability)
  else if id == proofSignedExpansion then
    some (methodName `lean.proof.signedExpansion)
  else if id == proofCounting then some (methodName `lean.proof.counting)
  else if id == proofCollisionProbabilityBound then
    some (formal `lean.proof.collisionProbabilityBound)
  else if id == proofCollisionMassBound then
    some (formal `lean.proof.collisionMassBound)
  else if id == proofBirthdayBound then
    some (formal `lean.proof.birthdayBound)
  else if id == proofScalarClosure then some (formal `lean.scalar.monotonicity)
  else if id == proofArithmetic then some (formal `lean.routine.arithmetic)
  else if id == proofRewriting then some (formal `lean.routine.rewriting)
  else if id == proofMonotonicity then some (formal `lean.order.monotonicity)
  else if id == rule `informalization `custom `securityTheorem then
    some (formal `lean.securityTheorem.conclusion)
  else none

/-- Additional sources used by a compositional sentence. The primary
attestation licenses the exact surface; these entries record the independently
attested ontology and discourse pattern that the surface combines. -/
def supportingAttestationsFor (id : RuleId) : Array Attestation :=
  if id == rsDefineCharacterizedMBO then #[
    jost
      "printed pp. 33–34: an MBO is a 0-to-1 monotone output and an event is a named monotone condition"
      `jost.randomSystems.mboEventOntology,
    liuMau20
      "Definition 6, pp. 9–10: definition followed by an equivalent characterization"
      `liuMau.randomSystems.definitionByCharacterization .compositionalAdaptation]
  else #[]

/-- Application-scoped language licenses for Verbose parser backends.  The
profile and exact backend declaration are both part of the key: a switching
occurrence cannot license the same generic rule in a CBC proof. -/
def applicationAttestationFor? (profile : String) (declaration backend : Name)
    (id : RuleId) : Option Attestation :=
  if profile == "switching" && declaration ==
      `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching &&
      backend == `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw &&
      id == rsConditionalLaw then
    some (cr18Fallback "Section 4.11.3: switching collision game and permutation law"
      `switching.conditionalLaw)
  else if profile == "switching" && declaration ==
      `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching &&
      backend == `CryptoLanguage.Verbose.RandomSystems.Relations.Backend.forgetGame &&
      id == rsForgetGame then
    some (cr18Fallback "Sections 4.10–4.11: removal of the switching game's MBO"
      `switching.forgetMBO)
  else if profile == "switching" && declaration ==
      `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching &&
      backend == `CryptoLanguage.Verbose.Backend.replaceInClaim &&
      id == proofRewriting then
    some (projectControlled "LANGUAGE_REFERENCE_CORPUS §3.3: S1 exact rewrite clause"
      `switching.proof.rewriting)
  else if profile == "switching" && declaration ==
      `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching &&
      backend == `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalBlindComparison &&
      id == rsConditionalBlindComparison then
    some (cr18Fallback "Theorem 4.17 as used in the Section 4.11.3 switching argument"
      `switching.conditionalBlindComparison)
  else if profile == "switching" && declaration ==
      `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching &&
      backend == `CryptoLanguage.Verbose.RandomSystems.Backend.blindWinningBound &&
      id == rsBlindWinningBound then
    some (projectControlled
      "LANGUAGE_REFERENCE_CORPUS §3.1/§3.3: checked sharper finite-alphabet bound"
      `switching.blindWinningBound)
  else none

/-- Application-scoped language licenses for computed informalization.  The
selected theorem root, the exact proof declaration, and the semantic rule are
all part of the key.  This prevents a switching fixture from authorizing the
same generic library theorem when it occurs in a CBC or unrelated proof. -/
def informalizationApplicationAttestationFor? (root declaration : Name)
    (id : RuleId) : Option Attestation :=
  if root == `RandomSystems.Switching.urf_urp_switching && declaration ==
      `RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv &&
      id == rsConditionalBlindBound then
    some (cr18Fallback
      "Theorem 4.17 as instantiated in Section 4.11.3: conditional equivalence bounds fully-defined advantage by blind winning"
      `switching.conditionalEquivalenceToBlindWinning)
  else if root == `RandomSystems.Switching.urf_urp_switching && declaration ==
      `RandomSystems.PDG.blindSupWinProb_le_of_forall &&
      id == proofBlindWinningToNonadaptive then
    some (cr18Fallback
      "Theorem 4.17 and Section 4.11.3: blind winning is bounded uniformly over non-adaptive environments and horizons"
      `switching.blindWinningToNonadaptive)
  else if root == `RandomSystems.Switching.urf_urp_switching && declaration ==
      `RandomSystems.System.transcriptInputs_congr_of_nonAdaptive &&
      id == proofNonadaptiveQueriesFixed then
    some (cr18Fallback
      "Section 4.11.3: a non-adaptive environment fixes its query sequence before replies are seen"
      `switching.nonadaptiveQueriesFixed)
  else if root == `CBCMAC.cbc_randomness_expander && declaration ==
      `CBCMAC.cbcCollisionGame_conditionallyEquivalent &&
      id == proofCollisionConditionalEquivalence then
    some (cr18Fallback
      "Section 6.2.3, Theorem 6.1: outside collision, prefix-freeness gives distinct terminal inputs and hence uniform consistent outputs"
      `cbc.collisionConditionalEquivalence)
  else if root == `CBCMAC.cbc_randomness_expander && declaration ==
      `CBCMAC.theta_cbcCollisionGame_conditionallyEquivalent &&
      id == proofConditionalEquivalenceUnderRestriction then
    some (cr18Fallback
      "Section 6.2.3, Theorem 6.1: the total-block restriction is applied to the real and ideal systems"
      `cbc.restrictedConditionalEquivalence)
  else if root == `CBCMAC.cbc_randomness_expander && declaration ==
      `CBCMAC.supWinProb_blind_filterDom_cbc_le &&
      id == proofBlindWinningBound then
    some (cr18Fallback
      "Section 6.2.3, Theorem 6.1: the CBC collision probability is bounded uniformly under the block limit"
      `cbc.blindWinningBound)
  else if root == `CBCMAC.cbc_randomness_expander &&
      (declaration ==
          `RandomSystems.PDS.advantage_le_of_conditionallyEquivalent_of_supWinProb_blind_le ||
        declaration ==
          `RandomSystems.Ambient.RandomSystem.advantage_le_supWinProb_blind_of_conditionallyEquivalent) &&
      id == rsConditionalBlindBound then
    some (cr18Fallback
      "Theorem 4.17 as used in Section 6.2.3: conditional equivalence reduces advantage to blind winning"
      `cbc.conditionalEquivalenceToBlindWinning)
  else if root == `CBCMAC.cbc_randomness_expander && declaration ==
      `RandomSystems.PDG.supWinProb_blind_filterDom_fTransform_le &&
      id == proofBlindWinningToNonadaptive then
    some (cr18Fallback
      "Theorem 4.17 and Section 6.2.3: a blind environment fixes the message list before replies are seen"
      `cbc.blindWinningToFixedMessages)
  else if root == `CBCMAC.cbc_randomness_expander && declaration ==
      `CBCMAC.CBCCombinatorics.mass_cbcBad_le &&
      id == proofCollisionMassBound then
    some (cr18Fallback
      "Section 6.2.3, Theorem 6.1: CBC collision-mass bound for an admitted message list"
      `cbc.collisionMassBound)
  else if root == `CBCMAC.cbc_randomness_expander && declaration ==
      `CBCMAC.CBCCombinatorics.mass_cbc_outputs_and_not_cbcBad_on_list_eq &&
      id == proofConditionalUniformOutputs then
    some (cr18Fallback
      "Section 6.2.3, Theorem 6.1: collision-free CBC outputs have the uniform consistent law"
      `cbc.uniformConsistentOutputs)
  else if root == `CBCMAC.cbc_randomness_expander &&
      (declaration == `CBCMAC.CBCCombinatorics.not_cbcBad_inputs_ne ||
        declaration == `CBCMAC.CBCCombinatorics.cbcLastInput_injOn) &&
      id == proofDistinctTerminalInputs then
    some (cr18Fallback
      "Section 6.2.3, Theorem 6.1: without a collision, distinct messages give distinct terminal round-function inputs"
      `cbc.distinctTerminalInputs)
  else if root == `CBCMAC.cbc_randomness_expander && declaration ==
      `CBCMAC.cbcPDS_advantage_le_restrictedCBCPDS_advantage &&
      id == rsCommonDomainDataProcessing then
    some (projectControlled
      "CBC frontend contract: exact checked common-domain advantage inequality"
      `cbc.commonDomainDataProcessing)
  else if root == `CBCMAC.cbc_randomness_expander &&
      (declaration == `CBCMAC.realPDS_eq ||
        declaration == `CBCMAC.theta_cbc_eq_theta_cbc_queryLimit) &&
      id == proofRestrictionApplicationEquation then
    some (projectControlled
      "CBC frontend contract: exact checked restriction and query-limit equation"
      `cbc.restrictionApplicationEquation)
  else if root == `CBCMAC.cbc_randomness_expander && declaration ==
      `CBCMAC.underlying_restrictedCBCCollisionGame &&
      id == proofIgnoreGameMBO then
    some (cr18Fallback
      "Section 6.2.3, Theorem 6.1: forgetting the collision MBO leaves restricted CBC"
      `cbc.ignoreCollisionMBO)
  else none

/-- Exact declaration-scoped linguistic evidence.  Unlike
`attestationForDeclaration?`, this function never falls back to a generic rule
entry.  Presentation code uses it to decide whether a checked semantic node
may receive domain prose. -/
def exactAttestationForDeclaration? (declaration : Name)
    (id : RuleId) : Option Attestation :=
  if declaration == `RandomSystems.Switching.urf_collision_condEquiv_urp &&
      id == proofCollisionConditionalEquivalence then
    some (cr18Fallback "Section 4.11.3: URF–URP switching conditional equivalence"
      `switching.urfCollisionConditionalEquivalence)
  else if declaration ==
      `RandomSystems.Switching.limit_urf_collision_condEquiv_limit_urp &&
      id == proofConditionalEquivalenceUnderRestriction then
    some (cr18Fallback "Section 4.11.3: query-restricted switching argument"
      `switching.restrictedConditionalEquivalence)
  else if declaration ==
      `RandomSystems.Switching.blindSupWinProb_limit_urf_collision_le &&
      id == proofBlindWinningBound then
    some (projectControlled
      "checked sharper finite-alphabet switching bound; CR18 displays only the coarser form"
      `switching.checkedBlindWinningBound)
  else if declaration == `RandomSystems.Switching.forget_limitGame_adjoin &&
      id == proofIgnoreGameMBO then
    some (cr18Fallback "Sections 4.10–4.11: removal of the switching game's MBO"
      `switching.forgetLimitGame)
  else if declaration ==
      `RandomSystems.Switching.uniform_function_collision_on_finset_le &&
      id == proofCollisionProbabilityBound then
    some (projectControlled "checked finite-set collision bound used by switching"
      `switching.uniformFunctionCollisionBound)
  else if declaration == `Applications.CBCCombinatorics.mass_cbcBad_le &&
      id == proofCollisionMassBound then
    some (cr18Fallback "Section 6.2.3, Theorem 6.1: CBC collision-mass bound"
      `cbc.collisionMassBound)
  else if declaration ==
      `CBCMAC.cbc_conditionallyEquivalent_urf_of_condition_eq_cbcBad &&
      id == proofCollisionConditionalEquivalence then
    some (cr18Fallback
      "Section 6.2.3, Theorem 6.1: collision-free CBC has the transcript law of the ideal random function"
      `cbc.collisionConditionalEquivalence)
  else if declaration ==
      `Applications.CBCCombinatorics.not_cbcBad_implies_uniform_outputs &&
      id == proofConditionalUniformOutputs then
    some (cr18Fallback "Section 6.2.3, Theorem 6.1: CBC output factorization"
      `cbc.uniformConsistentOutputs)
  else if (declaration == `Applications.CBCCombinatorics.not_cbcBad_inputs_ne ||
      declaration == `Applications.CBCCombinatorics.cbcLastInput_injOn) &&
      id == proofDistinctTerminalInputs then
    some (cr18Fallback "Section 6.2.3, Theorem 6.1: distinct CBC terminal inputs"
      `cbc.distinctTerminalInputs)
  else if declaration == `Probability.Counting.birthday_bound &&
      id == proofBirthdayBound then
    some (formal `lean.probability.birthdayBound)
  else none

/-- Source evidence used by registry diagnostics.  Generic evidence is useful
for classifying a rule, but is not by itself a license to narrate an arbitrary
declaration occurrence. -/
def attestationForDeclaration? (declaration : Name)
    (id : RuleId) : Option Attestation :=
  exactAttestationForDeclaration? declaration id <|> attestationFor? id

end CryptoLanguage.LanguageDesign.Corpus
