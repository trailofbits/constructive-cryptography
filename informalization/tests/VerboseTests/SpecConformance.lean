import Verbose
import Verbose.English.Statements
import Verbose.RandomSystems
import Verbose.RandomSystems.Relations

/-!
# Executable specification conformance

`LanguageDesign.SurfaceContract.forms` is the authority. This test consumes
that value directly: it parses every canonical witness, checks sentence-owned
forms against the persistent semantic registry, and verifies that the prose
spec contains the exact generated projection. Complete proof fixtures then
check the corresponding elaboration and lowering traces.
-/

open Lean Elab Command Parser
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.SurfaceContract
open CryptoLanguage.LanguageDesign.Contract
open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.English.Statements
open scoped CryptoVerbose

namespace CryptoLanguage.Verbose.Tests.SpecConformance

private def parserCategory : SurfaceContract.ParserContext → Name
  | .theoremGiven => `cryptoVerboseGiven
  | .tactic => `tactic

private unsafe def auditExecutableContract : CommandElabM Unit := do
  let environment ← getEnv
  let descriptors ← registeredSentenceDescriptors
  for descriptor in descriptors do
    let some contract := Contract.ruleContractFor? descriptor.ruleId
      | throwError "registered sentence {descriptor.formId.family}.{descriptor.formId.form} has no language-contract entry"
    unless contract.implementation == .implemented do
      throwError "registered sentence {descriptor.formId.family}.{descriptor.formId.form} is classified as {repr contract.implementation} by the language contract"
    if descriptor.sourceAttestation.isPubliclyLicensed then
      unless !(SurfaceContract.canonicalFormsForRule descriptor.ruleId).isEmpty do
        throwError "public sentence {descriptor.formId.family}.{descriptor.formId.form} has no canonical surface in the language contract"
      match CryptoLanguage.Verbose.English.renderTemplate descriptor with
      | .ok _ => pure ()
      | .error message =>
          throwError "public sentence {descriptor.formId.family}.{descriptor.formId.form} cannot realize its contract template: {message}"
  for form in forms do
    unless form.witnessComplete do
      throwError "surface-contract form {form.id} does not assign every typed template hole"
    match Parser.runParserCategory environment (parserCategory form.parserContext)
        form.parserWitness with
    | .error message =>
        throwError "surface-contract form {form.id} no longer parses its own witness:\n{message}\n\nwitness:\n{form.parserWitness}"
    | .ok _ => pure ()
    match form.owner with
    | .sentence ruleId =>
        let matching := descriptors.filter (fun descriptor => descriptor.ruleId == ruleId)
        unless matching.size == 1 do
          throwError "surface-contract form {form.id} requires exactly one registered descriptor for {ruleId.layer}.{ruleId.family}.{ruleId.rule}; found {matching.size}"
        let descriptor := matching[0]!
        unless descriptor.schema.inputs == form.operands &&
            descriptor.schema.outputs == form.bindings do
          throwError "surface-contract form {form.id} disagrees with the registered ontology schema"
    | .theoremBinder ruleId =>
        unless ruleId == CryptoLanguage.LanguageDesign.Rules.structuralTheorem do
          throwError "surface-contract theorem binder {form.id} is not owned by the theorem declaration rule"
    | .assertionEnvelope =>
        unless form.id == factForm.id do
          throwError "an unrecognized assertion envelope entered the surface contract"

  unless (forms.map (fun form => form.id)).toList.eraseDups.length == forms.size do
    throwError "surface-contract form identifiers must be unique"

  for contract in Contract.ruleContracts do
    if contract.publication == .published && contract.ruleId != structuralTheorem then
      unless descriptors.any (·.ruleId == contract.ruleId) do
        throwError "published authoring rule {contract.ruleId.layer}.{contract.ruleId.family}.{contract.ruleId.rule} has no registered implementation descriptor"

  let specification ← IO.FS.readFile "VERBOSE_SPEC.md"
  let beginMarker := "<!-- GENERATED_VERBOSE_SURFACE_BEGIN -->"
  let endMarker := "<!-- GENERATED_VERBOSE_SURFACE_END -->"
  unless (specification.splitOn beginMarker).length == 2 &&
      (specification.splitOn endMarker).length == 2 do
    throwError "VERBOSE_SPEC.md must contain exactly one generated surface-contract block"
  unless specification.contains documentationBlock do
    throwError "VERBOSE_SPEC.md is stale: regenerate its surface block from LanguageDesign.SurfaceContract.documentationBlock"
  let actualDigest := specificationReviewDigest specification
  unless actualDigest == reviewedSpecificationDigest do
    throwError "VERBOSE_SPEC.md changed after its last implementation review: expected digest {reviewedSpecificationDigest}, actual {actualDigest}. Review the implementation impact, then update reviewedSpecificationDigest."

run_cmd auditExecutableContract

end CryptoLanguage.Verbose.Tests.SpecConformance
