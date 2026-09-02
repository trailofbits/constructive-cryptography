import Tests.ProofPlan
import Informalization.Semantics.Realize

namespace Tests.Discourse

open Lean Meta Elab Command
open Informalization.Semantics
open Informalization.Semantics.Registry
open Informalization.Semantics.Plan
open Informalization.Semantics.Discourse
open Informalization.Semantics.Realize

theorem conditionalEquivalenceDetailRule (P : Prop) (h : P) : P := h

run_cmd register {
  declaration := ``conditionalEquivalenceDetailRule
  role := .proofRule .conditionalEquivalenceUnderRestriction
  arguments := #[
    { selector := .binder `P, role := .subject },
    { selector := .binder `h, role := .premise 0, salience := .supporting },
    { selector := .result, role := .conclusion }
  ]
}

theorem ceWithExpansionDetail (P : Prop) (h : P) : P :=
  Tests.ProofPlan.ceRule P (conditionalEquivalenceDetailRule P h)

def TestCondEquiv (_game _target : Nat) : Prop := True

theorem baseConditionalEquivalence (game target : Nat) :
    TestCondEquiv game target := by trivial

theorem preserveConditionalEquivalence (game target : Nat)
    (h : TestCondEquiv game target) :
    TestCondEquiv (Nat.succ game) (Nat.succ target) := h

/-- A project wrapper whose body exposes the generic preservation rule.  It
has no registered premise interface and is therefore a bounded semantic macro. -/
theorem wrappedConditionalEquivalence (game target : Nat) :
    TestCondEquiv (Nat.succ game) (Nat.succ target) :=
  preserveConditionalEquivalence game target
    (baseConditionalEquivalence game target)

theorem ceRecursiveDisclosure (game target : Nat) :
    TestCondEquiv (Nat.succ game) (Nat.succ target) :=
  Tests.ProofPlan.ceRule (TestCondEquiv (Nat.succ game) (Nat.succ target))
    (wrappedConditionalEquivalence game target)

/-- Equal claims in two independent proof premises must not be globally
deduplicated merely because they have the same canonical conclusion. -/
theorem pairConditionalEquivalence (game target : Nat)
    (left right : TestCondEquiv (Nat.succ game) (Nat.succ target)) :
    TestCondEquiv (Nat.succ game) (Nat.succ target) ∧
      TestCondEquiv (Nat.succ game) (Nat.succ target) := ⟨left, right⟩

theorem independentEqualBranches (game target : Nat) :
    TestCondEquiv (Nat.succ game) (Nat.succ target) ∧
      TestCondEquiv (Nat.succ game) (Nat.succ target) :=
  pairConditionalEquivalence game target
    (wrappedConditionalEquivalence game target)
    (wrappedConditionalEquivalence game target)

run_cmd register {
  declaration := ``baseConditionalEquivalence
  role := .proofRule .collisionConditionalEquivalence
  arguments := #[
    { selector := .binder `game, role := .game },
    { selector := .binder `target, role := .targetSystem },
    { selector := .result, role := .conclusion }
  ]
}

run_cmd register {
  declaration := ``preserveConditionalEquivalence
  role := .proofRule .conditionalEquivalenceUnderRestriction
  arguments := #[
    { selector := .binder `game, role := .game },
    { selector := .binder `target, role := .targetSystem },
    { selector := .binder `h, role := .premise 0, salience := .supporting },
    { selector := .result, role := .conclusion }
  ]
}

run_cmd register {
  declaration := ``wrappedConditionalEquivalence
  role := .proofRule .conditionalEquivalenceUnderRestriction
  arguments := #[
    { selector := .binder `game, role := .game },
    { selector := .binder `target, role := .targetSystem },
    { selector := .result, role := .conclusion }
  ]
}

run_cmd register {
  declaration := ``pairConditionalEquivalence
  role := .proofRule .hTechnique
  arguments := #[
    { selector := .binder `left, role := .premise 0, salience := .supporting },
    { selector := .binder `right, role := .premise 1, salience := .supporting },
    { selector := .result, role := .conclusion }
  ]
}

private def testDecoderProfile : Canonical.DecoderProfile := {
  conditionalEquivalence := #[``TestCondEquiv]
  rules := #[
    {
      declaration := ``baseConditionalEquivalence
      rule := .establishConditionalEquivalence
    },
    {
      declaration := ``preserveConditionalEquivalence
      rule := .preserveConditionalEquivalence
      proofSlots := #[.conditionalEquivalence]
    },
    {
      declaration := ``wrappedConditionalEquivalence
      rule := .establishConditionalEquivalence
    }
  ]
}

private def provenance (expression : Expr) (declaration? : Option Name := none) :
    Provenance := { expression, declaration? }

private def argument (role : ArgumentRole) (source : Expr) : SemanticArgument := {
  role
  source
  provenance := provenance source
}

private def syntheticSecurityGraph : Graph :=
  let proposition := mkConst ``True
  let advantage := mkConst ``False
  let source := mkConst ``Nat
  let target := mkConst ``Int
  let restriction := mkConst ``List
  let urf := mkConst ``Bool
  let urp := mkConst ``String
  let budget := mkNatLit 8
  let bound := mkNatLit 4
  let nodes : Array Node := #[
    .proposition {
      role := .upperBound
      source := proposition
      arguments := #[argument .subject advantage, argument .bound bound]
      provenance := provenance proposition (some ``LE.le)
    },
    .quantity {
      role := .distinguishingAdvantage
      source := advantage
      arguments := #[argument .sourceSystem source, argument .targetSystem target]
      provenance := provenance advantage
    },
    .system {
      role := .transform
      source
      arguments := #[argument (.custom `transformation) restriction,
        argument .probabilityLaw urf]
      provenance := provenance source
    },
    .converter {
      role := .queryRestriction
      source := restriction
      arguments := #[argument .queryBudget budget]
      provenance := provenance restriction
    },
    .system {
      role := .uniformRandomFunction
      source := urf
      arguments := #[argument .inputSpace (mkConst ``Bool),
        argument .outputSpace (mkConst ``Bool)]
      provenance := provenance urf
    },
    .system {
      role := .transform
      source := target
      arguments := #[argument (.custom `transformation) restriction,
        argument .probabilityLaw urp]
      provenance := provenance target
    },
    .system {
      role := .uniformRandomPermutation
      source := urp
      arguments := #[argument .alphabet (mkConst ``Bool)]
      provenance := provenance urp
    }
  ]
  let edge (parent child : Nat) (role : ArgumentRole) : Edge := {
    parent := { index := parent }
    child := { index := child }
    argument := argument role nodes[child]!.provenance.expression
  }
  {
    root := { index := 0 }
    nodes
    edges := #[
      edge 0 1 .subject,
      edge 1 2 .sourceSystem,
      edge 1 5 .targetSystem,
      edge 2 3 (.custom `transformation),
      edge 2 4 .probabilityLaw,
      edge 5 3 (.custom `transformation),
      edge 5 6 .probabilityLaw
    ]
  }

private def requirePlan (environment : Environment) (name : Name) : MetaM ProofPlan := do
  let some plan <- Plan.fromDeclaration? environment name
    | throwError "missing discourse test proof plan for {name}"
  return plan

private def sentenceSignature (result : Realize.Document) : Array (MoveKind × String) :=
  result.sentences.map fun sentence => (sentence.kind, sentence.text)

private def hasEvidence (result : Discourse.Document) (reference : EvidenceRef) : Bool :=
  result.evidenceIndex.any fun item => item.reference == reference

private def supportChildren (supports : Array Discourse.Support) :
    Array Discourse.Detail :=
  supports.foldl (fun result support => result ++ support.children) #[]

run_cmd liftTermElabM do
  let environment <- getEnv
  let ceBlind <- requirePlan environment ``Tests.ProofPlan.ceThenBlind
  let discourse ← Discourse.ofGraphAndPlan syntheticSecurityGraph ceBlind
  let result ← Realize.document discourse

  let some context := discourse.security
    | throwError "typed security context was not recovered"
  unless context.sourceSystem? == some { index := 2 } &&
      context.targetSystem? == some { index := 5 } &&
      context.sourceRole? == some .sourceSystem &&
      context.targetRole? == some .targetSystem do
    throwError "source/target system roles were not retained"
  unless context.sourceDescription?.map (·.baseRole) ==
        some .uniformRandomFunction &&
      context.targetDescription?.map (·.baseRole) ==
        some .uniformRandomPermutation &&
      context.sourceDescription?.bind (·.queryRestriction?) == some { index := 3 } &&
      context.targetDescription?.bind (·.queryRestriction?) == some { index := 3 } do
    throwError "recursive system descriptions lost the URF/URP base or query restriction"
  unless context.queryBudget?.map (·.formal) == some (mkNatLit 8) &&
      context.bound?.map (·.formal) == some (mkNatLit 4) do
    throwError "query budget or security bound was not recovered"

  unless discourse.moves.map (·.kind) == #[
      .stateSecurityGoal,
      .conditionalEquivalenceReduction,
      .remainingBlindWinningObligation,
      .blindWinningEstimate,
      .combineConditionalEquivalenceBlind
    ] do
    throwError "the CE-to-blind proof did not produce its conventional discourse plan"
  unless discourse.moves[1]!.evidence == #[.proofStep 0] &&
      discourse.moves[3]!.evidence == #[.proofStep 1] &&
      discourse.moves[4]!.evidence.contains (.proofStep 0) &&
      discourse.moves[4]!.evidence.contains (.proofStep 1) do
    throwError "discourse moves lost their proof-step identifiers"
  unless hasEvidence discourse (.statementNode { index := 4 }) &&
      hasEvidence discourse (.proofStep 0) &&
      hasEvidence discourse (.proofStep 1) &&
      hasEvidence discourse (.formalFallback 0) do
    throwError "the discourse evidence index is incomplete"

  let prose := String.intercalate " " (result.sentences.map (·.text) |>.toList)
  unless prose.contains "a query-restricted uniform random function" &&
      prose.contains "a query-restricted uniform random permutation" &&
      prose.contains "under the stated query budget" &&
      prose.contains "It remains to bound this blind winning probability" &&
      prose.contains "The formal derivation is retained" do
    throwError "semantic roles or fail-closed prose fallback were not realized"
  if prose.contains "reduces the distinguishing advantage" ||
      prose.contains "Combining" || prose.contains "bad event" ||
      prose.contains "switching" || prose.contains "ceRule" then
    throwError "an unlicensed connective, inferred event, or theorem-name template escaped"

  let alphaOne <- requirePlan environment ``Tests.ProofPlan.ceAlphaOne
  let alphaTwo <- requirePlan environment ``Tests.ProofPlan.ceAlphaTwo
  let alias <- requirePlan environment ``Tests.ProofPlan.ceAlias
  let exactPlan <- requirePlan environment ``Tests.ProofPlan.ceExact
  let applyPlan <- requirePlan environment ``Tests.ProofPlan.ceApply
  let realizePlan (plan : ProofPlan) : MetaM Realize.Document := do
    let discourse ← Discourse.ofGraphAndPlan syntheticSecurityGraph plan
    Realize.document discourse
  let alphaOneResult ← realizePlan alphaOne
  let alphaTwoResult ← realizePlan alphaTwo
  let aliasResult ← realizePlan alias
  let exactResult ← realizePlan exactPlan
  let applyResult ← realizePlan applyPlan
  unless sentenceSignature alphaOneResult == sentenceSignature alphaTwoResult &&
      sentenceSignature alphaOneResult == sentenceSignature aliasResult &&
      sentenceSignature exactResult == sentenceSignature applyResult do
    throwError "alpha-renaming, registered aliases, or exact/apply changed the realized discourse"

  let hPlan <- requirePlan environment ``Tests.ProofPlan.hProof
  let hybridPlan <- requirePlan environment ``Tests.ProofPlan.hybridProof
  let gameHopPlan <- requirePlan environment ``Tests.ProofPlan.gameHopProof
  let hResult ← realizePlan hPlan
  let hybridResult ← realizePlan hybridPlan
  let gameHopResult ← realizePlan gameHopPlan
  unless hResult.sentences.map (·.kind) ==
      #[.stateSecurityGoal, .hTechnique] &&
      hResult.sentences[1]!.details.map (·.kind) == #[.counting] &&
      hResult.sentences[1]!.details[0]!.semanticDepth == 1 &&
      hybridResult.sentences.map (·.kind) ==
        #[.stateSecurityGoal, .hybrid] &&
      gameHopResult.sentences.map (·.kind) ==
        #[.stateSecurityGoal, .gameHop] do
    throwError "different cryptographic proof genres collapsed to one discourse plan"

  -- A registered macro, its registered body, and the body's proof premise are
  -- three actual disclosure levels rather than peer phrases carrying depth
  -- metadata.  The existing `hViaMacro` fixture has exactly this shape.
  let macroPlan <- requirePlan environment ``Tests.ProofPlan.hViaMacro
  let macroDiscourse ← Discourse.ofGraphAndPlan syntheticSecurityGraph macroPlan
  let some macroMove := macroDiscourse.moves.find? fun move => move.kind == .hTechnique
    | throwError "the recursive macro proof has no H-technique root move"
  let macroChildren := supportChildren macroMove.supports
  unless macroChildren.size == 1 && macroChildren[0]!.kind == .hTechnique do
    throwError "the checked macro expansion was flattened or detached from its root"
  let countingChildren := supportChildren macroChildren[0]!.supports
  unless countingChildren.size == 1 && countingChildren[0]!.kind == .counting &&
      countingChildren[0]!.supports.isEmpty do
    throwError "the nested counting premise was not retained as a grandchild"

  -- The CE wrapper and generic preservation theorem have one canonical
  -- conclusion.  Postorder normalization keeps the richer generic theorem,
  -- merges both evidence references, and leaves the base CE beneath it.
  let recursiveCePlan <- requirePlan environment ``ceRecursiveDisclosure
  let recursiveCe ← Discourse.ofGraphAndPlan syntheticSecurityGraph recursiveCePlan
    testDecoderProfile
  let some ceRoot := recursiveCe.moves.find? fun move =>
      move.kind == .conditionalEquivalenceReduction
    | throwError "the recursive CE fixture has no reduction root"
  let ceChildren := supportChildren ceRoot.supports
  unless ceChildren.size == 1 &&
      ceChildren[0]!.kind == .registeredRule .conditionalEquivalenceUnderRestriction &&
      ceChildren[0]!.derivation?.any (fun derivation =>
        derivation.rule == .preserveConditionalEquivalence) &&
      ceChildren[0]!.primaryEvidence == .proofStep 2 &&
      ceChildren[0]!.evidence.contains (.proofStep 1) &&
      ceChildren[0]!.evidence.contains (.proofStep 2) do
    throwError "the redundant CE wrapper was not replaced by its richer generic rule"
  let baseChildren := supportChildren ceChildren[0]!.supports
  unless baseChildren.size == 1 &&
      baseChildren[0]!.kind == .registeredRule .collisionConditionalEquivalence &&
      baseChildren[0]!.primaryEvidence == .proofStep 3 do
    throwError "the base collision CE was flattened or lost during wrapper normalization"

  -- Deduplication is scoped to one proof-premise branch.  The same normalized
  -- CE chain used independently by two premises must remain present twice.
  let independentPlan <- requirePlan environment ``independentEqualBranches
  let independent ← Discourse.ofGraphAndPlan syntheticSecurityGraph independentPlan
    testDecoderProfile
  let some independentRoot := independent.moves.find? fun move => move.kind == .hTechnique
    | throwError "the independent-branches fixture has no root move"
  unless independentRoot.supports.size == 2 &&
      independentRoot.supports.all (fun support =>
        support.children.size == 1 &&
          support.children[0]!.derivation?.any (fun derivation =>
            derivation.rule == .preserveConditionalEquivalence)) do
    throwError "equal claims from independent support branches were globally deduplicated"

  let ceDetailPlan <- requirePlan environment ``ceWithExpansionDetail
  let ceDetailResult ← realizePlan ceDetailPlan
  unless ceDetailResult.sentences.map (·.kind) == #[
      .stateSecurityGoal,
      .conditionalEquivalenceReduction,
      .remainingBlindWinningObligation
    ] &&
      ceDetailResult.sentences[1]!.details.map (·.kind) ==
        #[.registeredRule .conditionalEquivalenceUnderRestriction] &&
      ceDetailResult.sentences[1]!.details[0]!.semanticDepth == 1 &&
      (ceDetailResult.sentences[1]!.details[0]!.text.contains
          "checked conclusion" ||
        ceDetailResult.sentences[1]!.details[0]!.text.contains
          "formal derivation") &&
      !ceDetailResult.sentences[1]!.details[0]!.text.contains
        "query restriction preserves" &&
      !ceDetailResult.sentences[1]!.details[0]!.text.contains "therefore" &&
      ceDetailResult.toJsonString.contains "semanticDepth" do
    throwError "conditional-equivalence expansion details were dropped during realization"

  let fallbackPlan <- requirePlan environment ``Tests.ProofPlan.unclassified
  let fallbackDiscourse ← Discourse.ofGraphAndPlan syntheticSecurityGraph fallbackPlan
  let fallbackResult ← Realize.document fallbackDiscourse
  unless fallbackDiscourse.moves.map (·.kind) ==
      #[.stateSecurityGoal, .formalFallback] &&
      !fallbackDiscourse.evidenceIndex.isEmpty &&
      fallbackResult.toJsonString.contains "formal-fallback" do
    throwError "an unclassified proof region was not retained as formal fallback"

run_cmd liftTermElabM do
  let proposition := mkConst ``True
  let proof := mkConst ``True.intro
  let lower := mkNatLit 1
  let upper := mkNatLit 2
  let real : Canonical.SystemTerm := .opaque (mkNatLit 3)
  let ideal : Canonical.SystemTerm := .opaque (mkNatLit 4)
  let game : Canonical.GameTerm := .opaque (mkNatLit 5)
  let target : Canonical.SystemTerm := .opaque (mkNatLit 6)
  let ceClaim : Canonical.Claim := .conditionalEquivalence proposition game target
  let estimateClaim : Canonical.Claim := .blindWinningBound proposition game
    (.expression upper)
  let advantageClaim : Canonical.Claim := .advantageBound proposition .fullyDefined
    real ideal (.expression upper)
  let scalarClaim : Canonical.Claim := .blindWinningBound proposition game
    (.coercion upper (.expression upper))
  let constructionClaim : Canonical.Claim := .construction proposition
    (.opaque (mkNatLit 7)) (.opaque (mkNatLit 8)) (.opaque (mkNatLit 9))
    (.expression upper)
  let distanceClaim : Canonical.Claim := .distanceBound proposition real ideal
    (.expression upper)

  let obligation (slot : Canonical.ObligationSlot)
      (claim? : Option Canonical.Claim := none) : Canonical.ProofObligation := {
    slot
    proposition := claim?.map (·.source) |>.getD proposition
    evidence := proof
    claim?
    provenance := provenance proof
  }
  let derivation (rule : Canonical.DerivationRule) (claim : Canonical.Claim)
      (formula? : Option Canonical.FormulaTerm := none)
      (obligations : Array Canonical.ProofObligation := #[]) :
      Canonical.DerivationApplication := {
    rule
    conclusion := .claim claim
    formula?
    obligations
    source := proof
    provenance := provenance proof
  }
  let realizeMove (kind : MoveKind) (rootClaim? : Option Canonical.Claim)
      (application : Canonical.DerivationApplication) : MetaM String := do
    let source : Discourse.Document := {
      security := none
      rootClaim?
      planKind := .generic
      moves := #[{
        id := 0
        kind
        primaryEvidence? := none
        evidence := #[]
        derivation? := some application
      }]
      evidenceIndex := #[]
    }
    let result ← Realize.document source
    return result.sentences[0]!.text

  let constructionReady ← realizeMove (.registeredRule .distanceBound)
    (some constructionClaim) (derivation .deriveDistanceBound distanceClaim)
  let constructionMissing ← realizeMove (.registeredRule .distanceBound)
    (some advantageClaim) (derivation .deriveDistanceBound distanceClaim)
  unless !constructionReady.contains "therefore" &&
      !constructionMissing.contains "therefore" &&
      constructionReady.contains "Explicitly" do
    throwError "an unattested construction connective escaped into reader prose"

  let commonReady ← realizeMove (.registeredRule .commonDomainDataProcessing) none <|
    derivation (.custom `commonDomainDataProcessing) distanceClaim
  let commonMissing ← realizeMove (.registeredRule .commonDomainDataProcessing) none <|
    derivation (.custom `commonDomainDataProcessing) advantageClaim
  unless !commonReady.contains "applying the converter" &&
      !commonMissing.contains "applying the converter" &&
      commonReady.contains "Explicitly" do
    throwError "checked-library common-domain wording escaped without a linguistic license"

  let reductionReady ← realizeMove .conditionalEquivalenceReduction none <|
    derivation .conditionalEquivalenceToBlindWinning advantageClaim none #[
      obligation .conditionalEquivalence (some ceClaim)
    ]
  let reductionMissing ← realizeMove .conditionalEquivalenceReduction none <|
    derivation .conditionalEquivalenceToBlindWinning advantageClaim
  unless !reductionReady.contains "therefore" &&
      !reductionMissing.contains "therefore" &&
      reductionReady.contains "Explicitly" do
    throwError "an unattested promoted reduction escaped into reader prose"

  let restrictionReady ← realizeMove
    (.registeredRule .conditionalEquivalenceUnderRestriction) none <|
    derivation .preserveConditionalEquivalence ceClaim none #[
      obligation .sourceTotal,
      obligation .targetTotal,
      obligation .conditionalEquivalence (some ceClaim)
    ]
  let restrictionMissing ← realizeMove
    (.registeredRule .conditionalEquivalenceUnderRestriction) none <|
    derivation .preserveConditionalEquivalence ceClaim none #[
      obligation .sourceTotal,
      obligation .conditionalEquivalence (some ceClaim)
    ]
  unless !restrictionReady.contains "therefore" &&
      !restrictionMissing.contains "therefore" &&
      restrictionReady.contains "Explicitly" do
    throwError "an unattested restriction connective escaped into reader prose"

  let scalarFormula : Canonical.FormulaTerm :=
    .scalarMonotonicity proposition lower upper
  let scalarReady ← realizeMove (.registeredRule .scalarClosure) none <|
    derivation (.custom `scalarClosure) scalarClaim (some scalarFormula) #[
      obligation .sideCondition (some estimateClaim)
    ]
  let scalarMissingFormula ← realizeMove (.registeredRule .scalarClosure) none <|
    derivation (.custom `scalarClosure) scalarClaim none #[
      obligation .sideCondition (some estimateClaim)
    ]
  let scalarMissingEstimate ← realizeMove (.registeredRule .scalarClosure) none <|
    derivation (.custom `scalarClosure) scalarClaim (some scalarFormula)
  unless !scalarReady.contains "therefore" &&
      !scalarMissingFormula.contains "therefore" &&
      !scalarMissingEstimate.contains "therefore" &&
      scalarReady.contains "Explicitly" do
    throwError "an unattested scalar connective escaped into reader prose"

end Tests.Discourse
