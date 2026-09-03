/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CBCMAC
import Informalization.Semantics.CBC
import Informalization.Semantics.Plan
import Informalization.Semantics.Validation

/-!
# Live CBC frontend contract

This test imports the real `cbc-mac-cc` project. It checks that the reusable
Random Systems profile understands the theorem's general mathematical shape,
that the thin CBC profile adds only CBC vocabulary, and that the checked proof
exposes the intended mathematical spine.
-/

namespace Tests.CBCFrontend

open Lean Meta Elab Command
open Informalization.Semantics
open Informalization.Semantics.Canonical
open Informalization.Semantics.Plan
open Informalization.Semantics.Registry
open Informalization.Semantics.Validation

partial def converterDeclarations : ConverterTerm → Array Name
  | .opaque _ => #[]
  | .named _ declaration _ | .restriction _ declaration _ => #[declaration]
  | .serialComposition _ outer inner =>
      converterDeclarations outer ++ converterDeclarations inner

partial def systemConverterDeclarations : SystemTerm → Array Name
  | .opaque _ | .named .. | .uniformRandomFunction .. |
      .uniformRandomPermutation .. => #[]
  | .presentationQuotient _ presentation =>
      systemConverterDeclarations presentation
  | .converterApplication _ converter underlying =>
      converterDeclarations converter ++ systemConverterDeclarations underlying
  | .transform _ _ underlying | .queryRestriction _ _ underlying =>
      systemConverterDeclarations underlying
  | .forgetGame _ _ => #[]

partial def systemDeclarations : SystemTerm → Array Name
  | .opaque _ | .uniformRandomFunction .. | .uniformRandomPermutation .. => #[]
  | .named _ declaration _ => #[declaration]
  | .presentationQuotient _ presentation => systemDeclarations presentation
  | .converterApplication _ _ underlying |
      .transform _ _ underlying | .queryRestriction _ _ underlying =>
      systemDeclarations underlying
  | .forgetGame _ _ => #[]

partial def systemHasQueryRestriction : SystemTerm → Bool
  | .queryRestriction .. => true
  | .presentationQuotient _ presentation =>
      systemHasQueryRestriction presentation
  | .converterApplication _ _ underlying | .transform _ _ underlying =>
      systemHasQueryRestriction underlying
  | _ => false

def requirePlan (environment : Environment) (declaration : Name) : MetaM ProofPlan := do
  let some plan ← Plan.fromDeclarationWithProfile? environment
      Informalization.Semantics.CBC.catalog
      Informalization.Semantics.CBC.profile declaration
    | throwError "CBC proof plan was not recovered"
  return plan

run_cmd liftTermElabM do
  let environment ← getEnv
  let visibleCatalog := Informalization.Semantics.CBC.catalog.filter fun entry =>
    (environment.find? entry.declaration).isSome
  let issues := validateCatalog environment visibleCatalog
  unless issues.isEmpty do
    throwError "CBC catalog does not match the live project: {repr issues}"

  let information ← getConstInfo ``CBCMAC.cbc_randomness_expander
  forallTelescope information.type fun _ conclusion => do
    let some genericClaim ← Canonical.decodeClaim?
        Canonical.RandomSystemsProfile.profile conclusion
      | throwError "the reusable Random Systems profile did not decode the CBC theorem"
    match genericClaim with
    | .distanceBound .. => pure ()
    | _ => throwError "the reusable profile did not classify the root distance bound"

    let some claim ← Canonical.decodeClaim?
        Informalization.Semantics.CBC.profile conclusion
      | throwError "the CBC extension did not decode the theorem"
    match claim with
    | .distanceBound _ left right upper =>
        let leftConverters := systemConverterDeclarations left
        let rightConverters := systemConverterDeclarations right
        let leftSystems := systemDeclarations left
        let rightSystems := systemDeclarations right
        for declaration in #[``CBCMAC.theta, ``CBCMAC.cbc] do
          unless leftConverters.contains declaration do
            throwError "the real CBC system lost converter {declaration}"
        unless systemHasQueryRestriction left &&
            Informalization.Semantics.CBC.profile.queryRestrictionConverters.contains
              ``RandomSystems.Ambient.DDC.queryLimit do
          throwError "the real CBC system lost its canonical query restriction"
        unless rightConverters.contains ``CBCMAC.theta do
          throwError "the ideal CBC system lost its block restriction"
        if rightConverters.contains ``CBCMAC.cbc then
          throwError "the ideal CBC system was assigned the CBC converter"
        unless leftSystems.contains ``CBCMAC.R do
          throwError "the real CBC system lost the uniform round function"
        unless rightSystems.contains ``CBCMAC.V do
          throwError "the ideal CBC system lost the VIL random function"
        match upper with
        | .quadraticCollision .. => pure ()
        | _ =>
            throwError "the standard quadratic collision bound was not decoded structurally"
    | _ => throwError "the CBC theorem was not classified as a distance bound"

  if Informalization.Semantics.RandomSystems.catalog.any fun entry =>
      entry.declaration.toString.startsWith "CBCMAC." then
    throwError "the reusable Random Systems catalog acquired application vocabulary"

  let plan ← requirePlan environment ``CBCMAC.cbc_randomness_expander
  let roles := plan.steps.map (·.application.role)
  -- The proof may inline the exact MBO-forgetting identity.  Require the
  -- paper-level conditional-equivalence route, not that optional proof-term
  -- boundary.
  for required in #[
      ProofRuleRole.collisionConditionalEquivalence,
      .conditionalEquivalenceUnderRestriction,
      .blindWinningBound,
      .commonDomainDataProcessing,
      .restrictionApplicationEquation,
      .conditionalEquivalenceToBlindWinning] do
    unless roles.contains required do
      throwError "CBC proof plan omitted semantic rule {repr required}; got {repr roles}"

end Tests.CBCFrontend
