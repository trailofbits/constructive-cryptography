import Informalization.Semantics.Plan

namespace Tests.ProofPlan

open Lean Meta Elab Command
open Informalization.Semantics
open Informalization.Semantics.Registry
open Informalization.Semantics.ProofEvidence
open Informalization.Semantics.Plan
open Informalization.Semantics.Canonical
open Informalization.Semantics.CanonicalProof

theorem ceRule (P : Prop) (h : P) : P := h
theorem ceAliasRule (P : Prop) (h : P) : P := h
theorem blindWinningRule (P : Prop) (h : P) : P := h
theorem hRule (P : Prop) (h : P) : P := h
theorem hybridRule (P : Prop) (h : P) : P := h
theorem gameHopRule (P : Prop) (h : P) : P := h
theorem countingRule (P : Prop) (h : P) : P := h
theorem commonDomainRule (P : Prop) (h : P) : P := h
theorem conditionalUniformRule (P : Prop) (h : P) : P := h
theorem scalarClosureRule (P : Prop) (h : P) : P := h

def thetaView (n : Nat) : Nat := n
theorem thetaRewriteRule (n : Nat) : thetaView n = n := rfl

def historyAttachment (blockForm limit system : Nat) : Nat :=
  blockForm + limit + system

theorem attachmentFormulaRule (blockForm limit system : Nat) :
    historyAttachment blockForm limit system = blockForm + limit + system := rfl

def converterAtom (n : Nat) : Nat := n
def converterSerial (outer inner : Nat) : Nat := outer + inner

theorem converterEqualityRule (outer middle inner : Nat) :
    converterSerial (converterSerial (converterAtom outer) (converterAtom middle))
        (converterAtom inner) =
      converterSerial (converterAtom outer)
        (converterSerial (converterAtom middle) (converterAtom inner)) :=
  Nat.add_assoc outer middle inner

def WrappedForall (α : Type) (P : α → Prop) : Prop := ∀ x, P x

/-- Its fully applied result unfolds to a `forall`; this still is a complete
application of the declaration telescope. -/
theorem wrappedForallRule (α : Type) (P : α → Prop)
    (h : WrappedForall α P) : WrappedForall α P := h

/-- A project-owned semantic helper whose checked body intentionally composes
two already registered rules.  Its catalog entry below exposes no premise
interface, so proof evidence treats it as a bounded semantic macro. -/
theorem hMacroRule (P : Prop) (h : P) : P := hRule P (countingRule P h)

/-- An unregistered helper with the same implementation shape.  The evidence
extractor must not unfold it merely because useful rules happen to occur in
its body. -/
theorem unregisteredHelper (P : Prop) (h : P) : P := ceRule P h

theorem cbcEndpointDirect (P : Prop) (h : P) : P :=
  commonDomainRule P (conditionalUniformRule P (scalarClosureRule P h))

theorem cbcSemanticHelper (P : Prop) (h : P) : P :=
  commonDomainRule P (conditionalUniformRule P (scalarClosureRule P h))

theorem cbcEndpointViaHelper (P : Prop) (h : P) : P :=
  cbcSemanticHelper P h

theorem cbcEndpointViaSimpa (P : Prop) (h : P) : P := by
  simpa only [] using cbcSemanticHelper P h

private def proofRuleEntry (declaration : Name) (role : ProofRuleRole) : Entry := {
  declaration
  role := .proofRule role
  arguments := #[
    { selector := .binder `P, role := .subject },
    { selector := .binder `h, role := .premise 0, salience := .supporting },
    { selector := .result, role := .conclusion }
  ]
}

run_cmd register (proofRuleEntry ``ceRule .conditionalEquivalenceToBlindWinning)
run_cmd register (proofRuleEntry ``ceAliasRule .conditionalEquivalenceToBlindWinning)
run_cmd register (proofRuleEntry ``blindWinningRule .blindWinningBound)
run_cmd register (proofRuleEntry ``hRule .hTechnique)
run_cmd register (proofRuleEntry ``hybridRule .triangleHybrid)
run_cmd register (proofRuleEntry ``gameHopRule .gamePlayingFundamentalLemma)
run_cmd register (proofRuleEntry ``countingRule .counting)
run_cmd register (proofRuleEntry ``commonDomainRule .commonDomainDataProcessing)
run_cmd register (proofRuleEntry ``conditionalUniformRule .conditionalUniformOutputs)
run_cmd register (proofRuleEntry ``scalarClosureRule .scalarClosure)
run_cmd register {
  declaration := ``thetaRewriteRule
  role := .proofRule .restrictionApplicationEquation
  arguments := #[
    { selector := .binder `n, role := .queryBudget },
    { selector := .result, role := .conclusion }
  ]
}
run_cmd register {
  declaration := ``attachmentFormulaRule
  role := .proofRule .restrictionApplicationEquation
  arguments := #[
    { selector := .binder `blockForm, role := .custom `blockForm },
    { selector := .binder `limit, role := .custom `blockLimit },
    { selector := .binder `system, role := .sourceSystem },
    { selector := .result, role := .conclusion }
  ]
}
run_cmd register {
  declaration := ``converterEqualityRule
  role := .proofRule .restrictionApplicationEquation
  arguments := #[
    { selector := .binder `outer, role := .custom `outerConverter },
    { selector := .binder `middle, role := .custom `middleConverter },
    { selector := .binder `inner, role := .custom `innerConverter },
    { selector := .result, role := .conclusion }
  ]
}
run_cmd register {
  declaration := ``wrappedForallRule
  role := .proofRule .conditionalEquivalence
  arguments := #[
    { selector := .binder `h, role := .premise 0, salience := .supporting },
    { selector := .result, role := .conclusion }
  ]
}
run_cmd register {
  declaration := ``cbcEndpointDirect
  role := .proofRule .advantageBound
  expandProof := true
  arguments := #[
    { selector := .binder `P, role := .subject },
    { selector := .binder `h, role := .premise 0, salience := .supporting },
    { selector := .result, role := .conclusion }
  ]
}
run_cmd register {
  declaration := ``cbcEndpointViaHelper
  role := .proofRule .advantageBound
  expandProof := true
  arguments := #[
    { selector := .binder `P, role := .subject },
    { selector := .binder `h, role := .premise 0, salience := .supporting },
    { selector := .result, role := .conclusion }
  ]
}
run_cmd register {
  declaration := ``cbcEndpointViaSimpa
  role := .proofRule .advantageBound
  expandProof := true
  arguments := #[
    { selector := .binder `P, role := .subject },
    { selector := .binder `h, role := .premise 0, salience := .supporting },
    { selector := .result, role := .conclusion }
  ]
}
run_cmd register {
  declaration := ``hMacroRule
  role := .proofRule .hTechnique
  arguments := #[
    { selector := .binder `P, role := .subject },
    { selector := .result, role := .conclusion }
  ]
}

theorem ceAlphaOne (P : Prop) (proofOfP : P) : P := ceRule P proofOfP
theorem ceAlphaTwo (Renamed : Prop) (witness : Renamed) : Renamed :=
  ceRule Renamed witness
theorem ceAlias (P : Prop) (h : P) : P := ceAliasRule P h

/-- An unregistered transitivity-shaped wrapper keeps the two registered
proof moves as siblings, as happens in a `calc` chain. -/
theorem proofChain (P : Prop) (_first second : P) : P := second

theorem ceThenBlind (P : Prop) (h : P) : P :=
  proofChain P (ceRule P h) (blindWinningRule P h)

theorem blindWinningProof (P : Prop) (h : P) : P := blindWinningRule P h

theorem ceBlindInline (P : Prop) (h : P) : P :=
  blindWinningRule P (ceRule P h)

theorem ceBlindThroughHave (P : Prop) (h : P) : P := by
  have localProof : P := ceRule P h
  exact blindWinningRule P localProof

theorem hViaMacro (P : Prop) (h : P) : P := hMacroRule P h
theorem cbcRootDirect (P : Prop) (h : P) : P := cbcEndpointDirect P h
theorem cbcRootViaHelper (P : Prop) (h : P) : P := cbcEndpointViaHelper P h
theorem cbcRootViaSimpa (P : Prop) (h : P) : P := cbcEndpointViaSimpa P h
theorem cbcMissingMaterialPremise (P : Prop) : P → P := cbcEndpointDirect P
theorem thetaByExact (n : Nat) : thetaView n = n := thetaRewriteRule n
theorem thetaByRw (n : Nat) : thetaView n = n := by rw [thetaRewriteRule n]
theorem thetaBySimpa (n : Nat) : thetaView n = n := by
  simpa only [] using thetaRewriteRule n
theorem thetaByCalc (n : Nat) : thetaView n = n := by
  calc
    thetaView n = n := thetaRewriteRule n
theorem attachmentByExact (blockForm limit system : Nat) :
    historyAttachment blockForm limit system = blockForm + limit + system :=
  attachmentFormulaRule blockForm limit system
theorem attachmentByRw (blockForm limit system : Nat) :
    historyAttachment blockForm limit system = blockForm + limit + system := by
  rw [attachmentFormulaRule]
theorem attachmentBySimpa (blockForm limit system : Nat) :
    historyAttachment blockForm limit system = blockForm + limit + system := by
  simpa only [] using attachmentFormulaRule blockForm limit system
theorem attachmentByCalc (blockForm limit system : Nat) :
    historyAttachment blockForm limit system = blockForm + limit + system := by
  calc
    historyAttachment blockForm limit system = blockForm + limit + system :=
      attachmentFormulaRule blockForm limit system
theorem converterEqualityByExact (outer middle inner : Nat) :
    converterSerial (converterSerial (converterAtom outer) (converterAtom middle))
        (converterAtom inner) =
      converterSerial (converterAtom outer)
        (converterSerial (converterAtom middle) (converterAtom inner)) :=
  converterEqualityRule outer middle inner
theorem converterEqualityByHave (outer middle inner : Nat) :
    converterSerial (converterSerial (converterAtom outer) (converterAtom middle))
        (converterAtom inner) =
      converterSerial (converterAtom outer)
        (converterSerial (converterAtom middle) (converterAtom inner)) := by
  have equation := converterEqualityRule outer middle inner
  exact equation
theorem converterEqualityByRw (outer middle inner : Nat) :
    converterSerial (converterSerial (converterAtom outer) (converterAtom middle))
        (converterAtom inner) =
      converterSerial (converterAtom outer)
        (converterSerial (converterAtom middle) (converterAtom inner)) := by
  rw [converterEqualityRule outer middle inner]
theorem converterEqualityBySimpa (outer middle inner : Nat) :
    converterSerial (converterSerial (converterAtom outer) (converterAtom middle))
        (converterAtom inner) =
      converterSerial (converterAtom outer)
        (converterSerial (converterAtom middle) (converterAtom inner)) := by
  simpa only [] using converterEqualityRule outer middle inner
theorem converterEqualityByCalc (outer middle inner : Nat) :
    converterSerial (converterSerial (converterAtom outer) (converterAtom middle))
        (converterAtom inner) =
      converterSerial (converterAtom outer)
        (converterSerial (converterAtom middle) (converterAtom inner)) := by
  calc
    converterSerial (converterSerial (converterAtom outer) (converterAtom middle))
        (converterAtom inner) =
        converterSerial (converterAtom outer)
          (converterSerial (converterAtom middle) (converterAtom inner)) :=
      converterEqualityRule outer middle inner
theorem converterEqualityWithExtraFact (outer middle inner : Nat) :
    converterSerial (converterSerial (converterAtom outer) (converterAtom middle))
        (converterAtom inner) =
      converterSerial (converterAtom outer)
        (converterSerial (converterAtom middle) (converterAtom inner)) := by
  have _unused : outer = outer := rfl
  exact converterEqualityRule outer middle inner
theorem ceBehindUnregisteredHelper (P : Prop) (h : P) : P :=
  unregisteredHelper P h

theorem wrappedForallProof (α : Type) (P : α → Prop)
    (h : WrappedForall α P) : WrappedForall α P :=
  wrappedForallRule α P h

theorem ceExact (P : Prop) (h : P) : P := by
  exact ceRule P h

theorem ceApply (P : Prop) (h : P) : P := by
  apply ceRule
  exact h

theorem hProof (P : Prop) (h : P) : P := hRule P (countingRule P h)
theorem hybridProof (P : Prop) (h : P) : P := hybridRule P h
theorem gameHopProof (Bad : Prop) (hBad : Bad) : Bad := gameHopRule Bad hBad
theorem ceBadName (Bad : Prop) (hBad : Bad) : Bad := ceRule Bad hBad

theorem unclassified (P : Prop) (h : P) : P := h

/-- A registered theorem constant used without its proof premise is not a
fully applied proof-rule application. -/
theorem partialRegisteredUse (P : Prop) : P → P := hRule P

private def requirePlan (environment : Environment) (name : Name) : MetaM ProofPlan := do
  let some plan ← Plan.fromDeclarationWith? environment (#[] : Catalog) name
    | throwError "missing proof plan for {name}"
  return plan

private def attachmentProfile : DecoderProfile := {
  rules := #[{
    declaration := ``attachmentFormulaRule
    rule := .custom `restrictionApplicationEquation
    operands := #[
      { selector := .binder `blockForm, slot := `blockForm },
      { selector := .binder `limit, slot := `blockLimit },
      { selector := .binder `system, slot := `system }
    ]
    formula? := some .restrictionAttachment
  }]
}

private def requireAttachmentPlan (environment : Environment) (name : Name) :
    MetaM ProofPlan := do
  let some plan ← Plan.fromDeclarationWithProfile? environment (#[] : Catalog)
      attachmentProfile name
    | throwError "missing attachment-formula proof plan for {name}"
  return plan

private def converterEqualityProfile : DecoderProfile := {
  converterAtoms := #[``converterAtom]
  converterSerialCompositions := #[``converterSerial]
  rules := #[{
    declaration := ``converterEqualityRule
    rule := .custom `restrictionApplicationEquation
    operands := #[
      { selector := .binder `outer, slot := `outerConverter },
      { selector := .binder `middle, slot := `middleConverter },
      { selector := .binder `inner, slot := `innerConverter }
    ]
    formula? := some .converterEquality
  }]
}

private def requireConverterEqualityPlan (environment : Environment) (name : Name) :
    MetaM ProofPlan := do
  let some plan ← Plan.fromDeclarationWithProfile? environment (#[] : Catalog)
      converterEqualityProfile name
    | throwError "missing converter-equality proof plan for {name}"
  return plan

private def requireSingleGenre (plan : ProofPlan) (genre : Genre) : MetaM Unit := do
  unless plan.dominantGenre? == some genre do
    throwError "expected dominant genre {repr genre}, got {repr plan.dominantGenre?}"

private partial def checkCanonicalObligations : CanonicalProof → MetaM Unit
  | .fallback node =>
      node.children.forM checkCanonicalObligations
  | .rule node => do
      for premise in node.premises do
        if let some obligation := premise.obligation? then
          let same ← withLCtx premise.proof.primaryEvidence.localContext #[] do
            isDefEq obligation.proposition premise.proof.goal.source
          unless same do
            throwError "a canonical premise goal differs from its parent obligation"
        checkCanonicalObligations premise.proof
      if let some expansion := node.macroExpansion? then
        checkCanonicalObligations expansion

private def checkCanonicalRoot (plan : ProofPlan) : MetaM Unit := do
  let payload := plan.canonicalProof.primaryEvidence
  let same ← withLCtx payload.localContext #[] do
    isDefEq plan.canonicalProof.goal.source payload.expected
  unless same do
    throwError "the canonical proof root differs from the checked theorem conclusion"
  checkCanonicalObligations plan.canonicalProof

run_cmd liftTermElabM do
  let environment ← getEnv

  let alphaOne ← requirePlan environment ``ceAlphaOne
  let alphaTwo ← requirePlan environment ``ceAlphaTwo
  let alias ← requirePlan environment ``ceAlias
  let exactPlan ← requirePlan environment ``ceExact
  let applyPlan ← requirePlan environment ``ceApply

  checkCanonicalRoot alphaOne
  checkCanonicalRoot exactPlan

  requireSingleGenre alphaOne .conditionalEquivalence
  unless alphaOne.semanticFingerprint == alphaTwo.semanticFingerprint do
    throwError "alpha-renaming changed the semantic proof-plan fingerprint"
  unless alphaOne.semanticFingerprint == alias.semanticFingerprint do
    throwError "a registered semantic alias changed the proof-plan fingerprint"
  unless exactPlan.semanticFingerprint == applyPlan.semanticFingerprint do
    throwError "exact/apply refactoring changed the semantic proof-plan fingerprint"

  let ceBlind ← requirePlan environment ``ceThenBlind
  unless ceBlind.genres ==
      #[.conditionalEquivalence, .blindWinningBound] do
    throwError "conditional equivalence and the blind-winning bound were not retained distinctly"
  unless ceBlind.kind == .conditionalEquivalenceBlind do
    throwError "the CE-to-blind chain was not recognized as a composite plan"
  if ceBlind.genres.contains .hTechnique || ceBlind.genres.contains .gameHop then
    throwError "the CE-to-blind chain was mislabeled as H-technique or game hopping"

  let blindWinning ← requirePlan environment ``blindWinningProof
  requireSingleGenre blindWinning .blindWinningBound
  unless blindWinning.kind == .blindWinningBound do
    throwError "a standalone blind-winning estimate was mislabeled as counting"

  let ceBlindInlinePlan ← requirePlan environment ``ceBlindInline
  let ceBlindHavePlan ← requirePlan environment ``ceBlindThroughHave
  unless ceBlindInlinePlan.semanticFingerprint == ceBlindHavePlan.semanticFingerprint do
    throwError "moving registered evidence into a local have changed the semantic proof plan"
  unless ceBlindHavePlan.steps.size == 2 &&
      ceBlindHavePlan.steps[0]!.genre == .blindWinningBound &&
      ceBlindHavePlan.steps[1]!.genre == .conditionalEquivalence &&
      ceBlindHavePlan.steps[1]!.semanticDepth == 1 do
    throwError "a registered helper application hidden behind a local have was not recovered"
  unless ceBlindInlinePlan.stepViews.map (·.stepId) ==
      Array.range ceBlindInlinePlan.steps.size do
    throwError "flat compatibility step IDs are not stable preorder indices"
  unless ceBlindInlinePlan.supportForest.size == 1 do
    throwError "an inline premise proof did not retain one recursive support root"
  let inlineRoot := ceBlindInlinePlan.supportForest[0]!
  unless inlineRoot.view.stepId == 0 && inlineRoot.premiseChildren.size == 1 &&
      inlineRoot.macroChildren.isEmpty do
    throwError "logical-premise and macro support edges were conflated"
  let inlineChild := inlineRoot.premiseChildren[0]!
  match inlineChild.view.origin with
  | .premise parentStepId key descriptor =>
      unless parentStepId == 0 && key.telescopePosition == descriptor.position &&
          key.proofOrdinal == 0 && descriptor.role == .premise 0 do
        throwError "recursive premise support lost its stable obligation identity"
  | _ => throwError "an inline proof dependency was not classified as a premise edge"
  unless ceBlindInlinePlan.primaryEvidence.size == ceBlindInlinePlan.steps.size &&
      ceBlindInlinePlan.allEvidence.size > ceBlindInlinePlan.primaryEvidence.size do
    throwError "the primary support view replaced rather than retained all checked evidence"

  let macroPlan ← requirePlan environment ``hViaMacro
  unless macroPlan.genres == #[.hTechnique, .counting] &&
      macroPlan.steps.size == 3 &&
      macroPlan.steps[0]!.semanticDepth == 0 &&
      macroPlan.steps[1]!.semanticDepth == 1 &&
      macroPlan.steps[2]!.semanticDepth == 2 do
    throwError "bounded semantic-macro expansion did not expose its registered child plan"
  unless macroPlan.fallbackEvidence.isEmpty do
    throwError "macro implementation evidence was not covered at its semantic boundary"
  unless macroPlan.supportForest.size == 1 do
    throwError "the semantic macro did not retain one recursive support root"
  let macroRoot := macroPlan.supportForest[0]!
  unless macroRoot.premiseChildren.isEmpty && macroRoot.macroChildren.size == 1 do
    throwError "macro implementation evidence was mislabeled as a logical premise"
  let macroChild := macroRoot.macroChildren[0]!
  match macroChild.view.origin with
  | .macroExpansion parentStepId =>
      unless parentStepId == macroRoot.view.stepId do
        throwError "macro support points to the wrong registered parent"
  | _ => throwError "semantic macro support lost its expansion edge"

  let cbcDirect ← requirePlan environment ``cbcRootDirect
  let cbcViaHelper ← requirePlan environment ``cbcRootViaHelper
  let cbcViaSimpa ← requirePlan environment ``cbcRootViaSimpa
  let semanticRoles (plan : ProofPlan) := plan.steps.map (·.application.role)
  let expectedCbcRoles := #[.advantageBound, .commonDomainDataProcessing,
    .conditionalUniformOutputs, .scalarClosure]
  unless semanticRoles cbcDirect == expectedCbcRoles &&
      semanticRoles cbcViaHelper == expectedCbcRoles &&
      semanticRoles cbcViaSimpa == expectedCbcRoles do
    throwError "helper insertion or simpa refactoring changed expanded CBC semantics"
  unless cbcDirect.kind == cbcViaHelper.kind &&
      cbcDirect.kind == cbcViaSimpa.kind &&
      !cbcDirect.hasFallback && !cbcViaHelper.hasFallback &&
      !cbcViaSimpa.hasFallback do
    throwError "refactored CBC semantic output changed genre or lost evidence coverage"

  let missingMaterial ← requirePlan environment ``cbcMissingMaterialPremise
  unless missingMaterial.steps.isEmpty && missingMaterial.hasFallback do
    throwError "an expanded CBC endpoint with a missing material premise did not fail closed"

  let thetaExact ← requirePlan environment ``thetaByExact
  let thetaRw ← requirePlan environment ``thetaByRw
  let thetaSimpa ← requirePlan environment ``thetaBySimpa
  let thetaCalc ← requirePlan environment ``thetaByCalc
  for plan in #[thetaExact, thetaRw, thetaSimpa, thetaCalc] do
    unless semanticRoles plan == #[.restrictionApplicationEquation] && !plan.hasFallback do
      throwError "rw, simpa, or calc changed the theta-preservation semantics"
  let attachmentExact ← requireAttachmentPlan environment ``attachmentByExact
  let attachmentRw ← requireAttachmentPlan environment ``attachmentByRw
  let attachmentSimpa ← requireAttachmentPlan environment ``attachmentBySimpa
  let attachmentCalc ← requireAttachmentPlan environment ``attachmentByCalc
  for plan in #[attachmentExact, attachmentRw, attachmentSimpa, attachmentCalc] do
    unless semanticRoles plan == #[ProofRuleRole.restrictionApplicationEquation] && !plan.hasFallback &&
        (plan.stepViews[0]?.bind (·.derivation?) |>.bind (·.formula?) |>.any
          (fun formula => match formula with
            | .restrictionAttachment .. => true
            | _ => false)) do
      throwError "rw, simpa, calc, or helper shape changed the attachment formula AST"
  let converterExact ← requireConverterEqualityPlan environment
    ``converterEqualityByExact
  let converterHave ← requireConverterEqualityPlan environment
    ``converterEqualityByHave
  let converterRw ← requireConverterEqualityPlan environment
    ``converterEqualityByRw
  let converterSimpa ← requireConverterEqualityPlan environment
    ``converterEqualityBySimpa
  let converterCalc ← requireConverterEqualityPlan environment
    ``converterEqualityByCalc
  let converterExtra ← requireConverterEqualityPlan environment
    ``converterEqualityWithExtraFact
  let converterVariants : Array ProofPlan := #[converterExact, converterHave,
    converterRw, converterSimpa, converterCalc, converterExtra]
  let converterFingerprint := converterVariants[0]!.presentationFingerprint
  for plan in converterVariants do
    unless plan.presentationFingerprint == converterFingerprint && !plan.hasFallback &&
        (plan.stepViews[0]?.bind (·.derivation?) |>.bind (·.formula?) |>.any
          (fun formula => match formula with
            | .converterEquality .. => true
            | _ => false)) do
      throwError "proof packaging changed the converter-equality semantic formula"
  unless macroChild.premiseChildren.size == 1 &&
      macroChild.premiseChildren[0]!.view.stepId == 2 do
    throwError "nested logical support below a macro expansion was flattened"
  let some shallowMacroPlan ← Plan.fromDeclarationWith? environment (#[] : Catalog)
      ``hViaMacro 512 0
    | throwError "missing shallow semantic-macro plan"
  unless shallowMacroPlan.steps.size == 1 do
    throwError "the semantic-macro expansion depth bound was ignored"

  let unregisteredHelperPlan ← requirePlan environment ``ceBehindUnregisteredHelper
  unless unregisteredHelperPlan.steps.isEmpty do
    throwError "an unregistered helper declaration was recursively unfolded"

  let wrappedForallPlan ← requirePlan environment ``wrappedForallProof
  unless wrappedForallPlan.steps.size == 1 &&
      wrappedForallPlan.steps[0]!.application.role == .conditionalEquivalence do
    throwError "a complete rule application was rejected after its result unfolded to a forall"

  unless alphaOne.steps.size == 1 && alphaOne.steps[0]!.premises.size == 1 do
    throwError "the registered rule or its proof-valued premise was not retained"
  unless alphaOne.steps[0]!.premises[0]!.descriptor.role == .premise 0 &&
      alphaOne.steps[0]!.premises[0]!.descriptor.salience == .supporting do
    throwError "registered premise metadata was not retained"
  match alphaOne.steps[0]!.premises[0]!.evidence with
  | .fallback payload _ =>
      unless payload.expected.isFVar do
        throwError "fallback premise does not retain its exact proposition"
  | .rule .. => throwError "an unregistered hypothesis was fabricated into a proof rule"

  let hPlan ← requirePlan environment ``hProof
  requireSingleGenre hPlan .hTechnique
  unless hPlan.genres == #[.hTechnique, .counting] do
    throwError "nested H-technique/counting genres were not kept distinct"
  unless hPlan.steps.size == 2 && hPlan.steps[0]!.semanticDepth == 0 &&
      hPlan.steps[1]!.semanticDepth == 1 do
    throwError "semantic premise nesting was not retained"

  let hybrid ← requirePlan environment ``hybridProof
  let gameHop ← requirePlan environment ``gameHopProof
  let ceBad ← requirePlan environment ``ceBadName
  requireSingleGenre hybrid .hybrid
  requireSingleGenre gameHop .gameHop
  requireSingleGenre ceBad .conditionalEquivalence
  if gameHop.semanticFingerprint == ceBad.semanticFingerprint then
    throwError "game hopping and conditional equivalence were conflated"

  let fallback ← requirePlan environment ``unclassified
  unless fallback.steps.isEmpty && fallback.hasFallback &&
      !fallback.fallbackEvidence.isEmpty do
    throwError "unclassified proof content was not retained as fallback evidence"
  unless fallback.fallbackEvidence.size == 1 do
    throwError "nested structural wrappers duplicated an irreducible fallback leaf"

  let partialPlan ← requirePlan environment ``partialRegisteredUse
  unless partialPlan.steps.isEmpty && partialPlan.hasFallback do
    throwError "a partially applied registered constant was classified as a proof rule"

end Tests.ProofPlan
