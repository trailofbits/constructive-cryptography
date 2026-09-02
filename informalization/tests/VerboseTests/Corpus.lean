import Verbose
import Verbose.RandomSystems
import Verbose.RandomSystems.Relations

open Lean Elab Command
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Corpus
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.Verbose

namespace CryptoLanguage.Verbose.Tests.Corpus

private unsafe def auditCatalog : CommandElabM Unit := do
  let catalog ← registeredSentenceDescriptors
  for entry in catalog do
    unless entry.sourceAttestation.isPubliclyLicensed do
      throwError "sentence {entry.ruleId.layer}.{entry.ruleId.family}.{entry.ruleId.rule} has no valid source contract"
    if entry.sourceAttestation.source == .cr18Fallback then
      throwError "generic Verbose grammar may not be licensed by the application-only CR18 fallback corpus"
    if entry.sourceAttestation.source == .checkedLibrary then
      throwError "a checked Lean declaration cannot by itself license public English"
    if let .ok rendered := English.renderTemplate entry then
      if rendered.toLower.contains "monitor" || rendered.toLower.contains "augment" then
        throwError "sentence {entry.ruleId.layer}.{entry.ruleId.family}.{entry.ruleId.rule} uses an unlicensed monitoring/augmentation gloss: {rendered}"

  if catalog.any (·.ruleId == rsEnhanceWithMBO) then
    throwError "the unattested generic MBO-enhancement frame leaked into the public catalog"

  if catalog.any (·.ruleId == rsForgetGame) then
    throwError "the application-only ignore-MBO frame leaked into the public catalog"

  if catalog.any (·.ruleId == rsConditionalLaw) ||
      catalog.any (·.ruleId == rsConditionalBlindComparison) ||
      catalog.any (·.ruleId == rsBlindWinningBound) ||
      catalog.any (·.ruleId == rsWinningMassIdentity) ||
      catalog.any (·.ruleId == rsMassBound) then
    throwError "an application-only Random Systems proof frame leaked into the public catalog"

  if catalog.any (·.ruleId == rsDeclareRestrictedURF) then
    throwError "the rejected restricted-URF prose declaration leaked into the public catalog"

  let some systemBinder := catalog.find? (·.ruleId == rsBindSystem)
    | throwError "the typed Random Systems binder disappeared from the public catalog"
  unless systemBinder.schema.inputs ==
      CryptoLanguage.LanguageDesign.SurfaceContract.systemForm.operands &&
      systemBinder.schema.outputs ==
        CryptoLanguage.LanguageDesign.SurfaceContract.systemForm.bindings do
    throwError "the typed Random Systems binder drifted from its executable surface contract"

  if catalog.any (·.ruleId == rsRestrictedEnhancedURFGameNonnegative) then
    throwError "the rejected by-construction property sentence leaked into the public catalog"

  let some mbo := catalog.find? (·.ruleId == rsDefineCharacterizedMBO)
    | throwError "the source-licensed characterized-MBO form disappeared from the public catalog"
  unless mbo.sourceAttestation.source == .projectControlled &&
      mbo.supportingSourceAttestations.map (·.source) ==
        #[.primaryJost, .primaryLiuMau20] do
    throwError "the characterized-MBO form lost its split syntax/ontology/discourse provenance"

  unless RandomSystems.conditionalLaw.supportsNamedFact &&
      RandomSystems.filterConditionalLaw.supportsNamedFact &&
      RandomSystems.Relations.forgetGame.supportsNamedFact do
    throwError "one of the three checked `Fact`-capable Random Systems assertions lost its claim constructor"
  let closingOnlyFactCapability :=
    RandomSystems.conditionalBlindComparison.supportsNamedFact ||
      RandomSystems.blindWinningBound.supportsNamedFact ||
      RandomSystems.Relations.enhanceWithMBO.supportsNamedFact
  if closingOnlyFactCapability then
    throwError "a closing-only assertion was incorrectly advertised as `Fact`-capable"

run_cmd auditCatalog

end CryptoLanguage.Verbose.Tests.Corpus
