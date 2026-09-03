import Informalization.Semantics.RandomSystems
import Informalization.Semantics.Validation
import Tests.Canonical

namespace Tests.Semantics

open Lean Meta Elab Command
open Informalization.Semantics
open Informalization.Semantics.Registry
open Informalization.Semantics.Validation

def mockSystem (input output : Type) : Type := input → output

def mockWrappedSystem (input output : Type) : {carrier : Type // carrier = carrier} :=
  ⟨input → output, rfl⟩

def mockAdvantage (source target : Nat) : Nat := source + target

theorem mockEquivalenceRule {source target : Nat} (evidence : source = target) :
    source = target := evidence

run_cmd register {
  declaration := ``mockSystem
  role := .system .uniformRandomFunction
  arguments := #[
    { selector := .binder `input, role := .inputSpace },
    { selector := .binder `output, role := .outputSpace }
  ]
}

run_cmd register {
  declaration := ``mockWrappedSystem
  role := .game .enhanceWithMBO
  arguments := #[
    { selector := .binder `input, role := .inputSpace, slot? := some `input },
    { selector := .binder `output, role := .outputSpace, slot? := some `output }
  ]
}

run_cmd register {
  declaration := ``mockAdvantage
  role := .quantity .distinguishingAdvantage
  arguments := #[
    { selector := .binder `source, role := .sourceSystem },
    { selector := .binder `target, role := .targetSystem }
  ]
}

run_cmd register {
  declaration := ``mockEquivalenceRule
  role := .proofRule .exactEquivalence
  arguments := #[
    { selector := .binder `source, role := .sourceSystem, slot? := some `source },
    { selector := .binder `target, role := .targetSystem, slot? := some `target },
    { selector := .binder `evidence, role := .premise 0,
      slot? := some `equivalence },
    { selector := .result, role := .conclusion, slot? := some `result }
  ]
}

private structure Recovery where
  source : Expr
  node : Node

private def recoverMockSystem (environment : Environment) (leftName rightName : Name) :
    MetaM Recovery :=
  withLocalDeclD leftName (mkSort .zero) fun left =>
    withLocalDeclD rightName (mkSort .zero) fun right => do
      let source := mkApp2 (mkConst ``mockSystem) left right
      let some node ← recover? environment source
        | throwError "mock system was not recovered"
      return { source, node }

private def recoverProjectedMockSystem (environment : Environment)
    (leftName rightName : Name) : MetaM Recovery :=
  withLocalDeclD leftName (mkSort .zero) fun left =>
    withLocalDeclD rightName (mkSort .zero) fun right => do
      let wrapped := mkApp2 (mkConst ``mockWrappedSystem) left right
      let source ← mkAppM ``Subtype.val #[wrapped]
      let some node ← recover? environment source
        | throwError "projected mock system was not recovered"
      return { source, node }

private def recoverMockRule (environment : Environment) : MetaM Recovery :=
  withLocalDeclD `left (mkConst ``Nat) fun left =>
    withLocalDeclD `right (mkConst ``Nat) fun right => do
      let proposition ← mkAppM ``Eq #[left, right]
      withLocalDeclD `proof proposition fun proof => do
        let source ← mkAppM ``mockEquivalenceRule #[proof]
        let some node ← recover? environment source
          | throwError "mock proof rule was not recovered"
        return { source, node }

private def securityGateResults (environment : Environment) : MetaM (Bool × Bool) :=
  withLocalDeclD `realSystem (mkConst ``Nat) fun realSystem =>
    withLocalDeclD `idealSystem (mkConst ``Nat) fun idealSystem =>
      withLocalDeclD `bound (mkConst ``Nat) fun bound => do
        let advantage := mkApp2 (mkConst ``mockAdvantage) realSystem idealSystem
        let securityRoot ← mkAppM ``LE.le #[advantage, bound]
        let arithmeticRoot ← mkAppM ``LE.le #[realSystem, bound]
        return (← isSecurityStatementRoot environment securityRoot,
          ← isSecurityStatementRoot environment arithmeticRoot)

run_cmd liftTermElabM do
  let environment ← getEnv

  let some urfEntry := lookup? environment `RandomSystems.PDS.urf
    | throwError "uniform-random-function registration is absent"
  unless urfEntry.role == .system .uniformRandomFunction do
    throwError "uniform-random-function registration has the wrong typed role"
  let ambientReduction :=
    `RandomSystems.Ambient.RandomSystem.advantage_le_supWinProb_blind_of_conditionallyEquivalent
  let some ambientReductionEntry := lookup? environment ambientReduction
    | throwError "ambient conditional-equivalence reduction registration is absent"
  unless ambientReductionEntry.role ==
      .proofRule .conditionalEquivalenceToBlindWinning do
    throwError "ambient conditional-equivalence reduction has the wrong typed role"
  let some ambientReductionRule :=
      Informalization.Semantics.Canonical.RandomSystemsProfile.profile.rules.find?
        (·.declaration == ambientReduction)
    | throwError "ambient conditional-equivalence reduction canonical profile is absent"
  unless ambientReductionRule.rule == .conditionalEquivalenceToBlindWinning &&
      ambientReductionRule.proofSlots == #[.custom `gameDomain,
        .custom `targetDomain, .conditionalEquivalence, .custom `refinement] do
    throwError "ambient conditional-equivalence reduction has an unstable proof contract"
  if (lookup? environment `List).isSome then
    throwError "the generic List declaration must not be registered as a transcript"
  let duplicateSlotCatalog : Catalog := #[{
    declaration := ``mockSystem
    role := .system .uniformRandomFunction
    arguments := #[
      { selector := .binder `input, role := .inputSpace, slot? := some `carrier },
      { selector := .binder `output, role := .outputSpace, slot? := some `carrier }
    ]
  }]
  unless (validateCatalog environment duplicateSlotCatalog).contains
      (.duplicateSlot ``mockSystem `carrier) do
    throwError "catalog validation accepted duplicate semantic slots"
  let unlicensedRole : ProofRuleRole := .custom `unlicensedReaderRule
  let unlicensedRule :=
    Informalization.Semantics.LanguageDesign.proofRuleRole unlicensedRole
  let unlicensedCatalog : Catalog := #[{
    declaration := ``mockEquivalenceRule
    role := .proofRule unlicensedRole
  }]
  unless (validateCatalog environment unlicensedCatalog).contains
      (.missingSourceAttestation ``mockEquivalenceRule unlicensedRule) do
    throwError "catalog validation accepted a proof rule with no dialect source"
  if (publicLanguageLicenseFor?
      `RandomSystems.CommonDomain.ProbabilityRandomSystem.edist_apply_le
      .commonDomainDataProcessing).isSome then
    throwError "a checked-library relation was treated as a public prose license"
  unless (publicLanguageLicenseFor?
      `Applications.CBCCombinatorics.mass_cbcBad_le
      .collisionMassBound).isSome do
    throwError "an exact CBC fallback occurrence lost its application-scoped language license"
  let reductionDeclaration :=
    `RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
  unless (publicLanguageLicenseForOccurrence?
      (some `RandomSystems.Switching.urf_urp_switching)
      reductionDeclaration .conditionalEquivalenceToBlindWinning).isSome do
    throwError "the exact switching reduction occurrence lost its language license"
  if (publicLanguageLicenseForOccurrence?
      (some `Applications.CBCMAC.cbc_constructs_within)
      reductionDeclaration .conditionalEquivalenceToBlindWinning).isSome then
    throwError "a switching-only reduction license leaked into CBC"
  let ambientReductionDeclaration :=
    `RandomSystems.Ambient.RandomSystem.advantage_le_supWinProb_blind_of_conditionallyEquivalent
  unless (publicLanguageLicenseForOccurrence?
      (some `CBCMAC.cbc_randomness_expander)
      ambientReductionDeclaration .conditionalEquivalenceToBlindWinning).isSome do
    throwError "the live CBC ambient conditional-equivalence reduction lost its language license"
  if (publicLanguageLicenseForOccurrence?
      (some `Applications.CBCMAC.cbc_constructs_within)
      ambientReductionDeclaration .conditionalEquivalenceToBlindWinning).isSome then
    throwError "the CBC ambient reduction license leaked to an unrelated theorem root"

  let first ← recoverMockSystem environment `X `Y
  let renamed ← recoverMockSystem environment `RenamedInput `RenamedOutput
  unless first.node.role == .system .uniformRandomFunction &&
      renamed.node.role == .system .uniformRandomFunction do
    throwError "local-variable renaming changed semantic system classification"
  unless first.node.arguments.map (·.role) == #[.inputSpace, .outputSpace] &&
      renamed.node.arguments.map (·.role) == #[.inputSpace, .outputSpace] do
    throwError "local-variable renaming changed semantic argument roles"
  unless first.node.provenance.declaration? == some ``mockSystem &&
      first.node.provenance.expression == first.source do
    throwError "semantic recovery lost source provenance"

  let proof ← recoverMockRule environment
  match proof.node with
  | .proofApplication application =>
      unless application.role == .exactEquivalence &&
          application.provenance.expression == proof.source &&
          application.arguments.map (·.role) ==
            #[.sourceSystem, .targetSystem, .premise 0, .conclusion] do
        throwError "proof-rule IR construction failed"
  | _ => throwError "a proof-rule registration did not construct a proof application"

  let some proofEntry := lookup? environment ``mockEquivalenceRule
    | throwError "mock proof-rule schema is absent"
  unless proofEntry.hasUniqueSlots &&
      (proofEntry.bindingForSlot? `equivalence).map (·.role) == some (.premise 0) &&
      proofEntry.slotForRole? (.premise 0) == some `equivalence &&
      (proofEntry.bindingForSlot? `result).map (·.role) == some .conclusion do
    throwError "stable semantic proof-obligation slots were not preserved"
  let resolved ← resolveBindings proofEntry proof.source
  unless (resolved.find? (·.binding.slot? == some `equivalence)).map
      (·.argument.role) == some (.premise 0) do
    throwError "resolving a rule application lost its named obligation slot"

  let projected ← recoverProjectedMockSystem environment `ProjectedInput `ProjectedOutput
  unless headDeclaration? projected.source == some ``Subtype.val do
    throwError "projection fixture did not elaborate through Subtype.val"
  unless projected.node.role == .game .enhanceWithMBO &&
      projected.node.arguments.map (·.role) == #[.inputSpace, .outputSpace] &&
      projected.node.provenance.expression == projected.source do
    throwError "proof-erasing subtype projection lost its registered constructor operands"

  let randomSystemsCatalog := Informalization.Semantics.RandomSystems.catalog
  let canonicalRules := #[
    (`RandomSystems.PDG.condEquiv_filterQueries,
      #[`queryBudget, `game, `target, `sourceTotal, `targetTotal,
        `conditionalEquivalence, `result]),
    (`RandomSystems.PDG.conditional_equivalence_theorem,
      #[`game, `target, `sourceNonnegative, `targetNonnegative, `equalWeight,
        `conditionalEquivalence, `result]),
    (`RandomSystems.PDS.conditional_equivalence_theorem_adjoin,
      #[`source, `target, `condition, `sourceNonnegative, `targetNonnegative,
        `equalWeight, `conditionalEquivalence, `result]),
    (`RandomSystems.PDG.conditional_equivalence_theorem_blind,
      #[`game, `target, `sourceNonnegative, `targetNonnegative, `equalWeight,
        `targetNormalized, `sourceDomain, `targetDomain, `conditionalEquivalence,
        `result]),
    (`RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv,
      #[`game, `target, `sourceNonnegative, `targetNonnegative, `equalWeight,
        `conditionalEquivalence, `result])
  ]
  for (declaration, slots) in canonicalRules do
    let some entry := lookupCatalog? randomSystemsCatalog declaration
      | throwError "canonical Random Systems rule is absent: {declaration}"
    unless entry.hasUniqueSlots && slots.all (entry.bindingForSlot? · |>.isSome) do
      throwError "canonical Random Systems rule has missing or duplicate slots: {declaration}"

  let (securityAccepted, arithmeticAccepted) ← securityGateResults environment
  unless securityAccepted do
    throwError "a registered advantage bound failed the security-statement gate"
  if arithmeticAccepted then
    throwError "an arithmetic inequality passed the security-statement gate"
  withLocalDeclD `leftMetric (mkConst ``Nat) fun leftMetric =>
    withLocalDeclD `rightMetric (mkConst ``Nat) fun rightMetric => do
      let arbitraryDistance ← mkAppM ``EDist.edist #[leftMetric, rightMetric]
      let arbitraryBound ← mkAppM ``LE.le #[arbitraryDistance, mkNatLit 7]
      if ← isSecurityStatementRootWith environment randomSystemsCatalog
          arbitraryBound then
        throwError "an arbitrary pseudo-emetric distance passed the Random Systems security gate"

end Tests.Semantics
