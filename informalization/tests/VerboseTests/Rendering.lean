import Verbose
import Verbose.RandomSystems
import Verbose.RandomSystems.Relations

open Lean
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.Verbose

namespace CryptoLanguage.Verbose.Tests.Rendering

private def dummyOperand (operandRole : ArgumentRole)
    (note? : Option String := none) : ElaboratedOperand :=
  ⟨operandRole, .sort .zero, .sort (.succ .zero), note?⟩

private def compositionInvocation : RuleInvocation :=
  ⟨acCompose, #[
    dummyOperand (role `firstLeg) (some "the real-to-middle leg"),
    dummyOperand (role `secondLeg)
  ]⟩

private def compositionPlan : English.CanonicalRenderPlan :=
  ⟨#[
    ⟨role `firstLeg, "firstConstruction"⟩,
    ⟨role `secondLeg, "secondConstruction"⟩
  ]⟩

#guard English.renderCanonical compositionInvocation compositionPlan ==
  .ok "The construction follows by composing firstConstruction noted \"the real-to-middle leg\" and secondConstruction"

private def filteredInvocation : RuleInvocation :=
  ⟨acFiltered, #[
    dummyOperand (role `commutation),
    dummyOperand (role `simulatorAdmission),
    dummyOperand (role `proof)]⟩

private def filteredPlan : English.CanonicalRenderPlan := ⟨#[
  ⟨role `commutation, "commutes"⟩,
  ⟨role `simulatorAdmission, "simulatorAdmitted"⟩,
  ⟨role `proof, "equation"⟩
]⟩

#guard English.renderCanonical filteredInvocation filteredPlan ==
  .ok "The filtered construction follows from equation using commutes and simulatorAdmitted"

private def replacementInvocation : RuleInvocation :=
  ⟨acReplaceProtocol, #[dummyOperand (role `construction),
    dummyOperand (role `equation)]⟩

private def replacementPlan : English.CanonicalRenderPlan := ⟨#[
  ⟨role `construction, "construction"⟩,
  ⟨role `equation, "converterEquation"⟩
]⟩

#guard English.renderCanonical replacementInvocation replacementPlan ==
  .ok "Replacing the converter in construction using converterEquation, we obtain the required construction"

private def simulatorInvocation : RuleInvocation :=
  ⟨acSimulator, #[dummyOperand (role `simulator)]⟩

#guard English.renderCanonical simulatorInvocation
    ⟨#[⟨role `simulator, "simulator"⟩]⟩ ==
  .ok "We use simulator to prove the construction"

private def rightContextInvocation : RuleInvocation :=
  ⟨acContextRight, #[dummyOperand (role `context),
    dummyOperand (role `construction)]⟩

#guard English.renderCanonical rightContextInvocation ⟨#[
    ⟨role `context, "context"⟩,
    ⟨role `construction, "baseConstruction"⟩]⟩ ==
  .ok "With context as the right parallel context, the construction follows from baseConstruction"

/- Rendering refuses to synthesize an omitted mathematical choice from the
stored kernel expression. -/
#guard match English.renderCanonical compositionInvocation
    ⟨#[⟨role `firstLeg, "firstConstruction"⟩]⟩ with
  | .error _ => true
  | .ok _ => false

private def blindInvocation : RuleInvocation :=
  ⟨rsBlindUniversal, #[dummyOperand (role `game)]⟩

private def blindPlan : English.CanonicalRenderPlan :=
  ⟨#[
    ⟨role `game, "collisionGame"⟩,
    ⟨role `environment, "environment"⟩,
    ⟨role `nonadaptive, "nonadaptive"⟩,
    ⟨role `nonadaptive.type, "NonAdaptive environment"⟩,
    ⟨role `rounds, "rounds"⟩
  ]⟩

#guard match English.renderCanonical blindInvocation blindPlan with
  | .error message => message.contains "pending source attestation"
  | .ok _ => false

private def conditionalOccurrence : AssertionOccurrenceSummary := {
  invocation := ⟨rsConditionalLaw, #[
    dummyOperand (role `game), dummyOperand (role `system),
    dummyOperand (role `proof)]⟩
  exactConclusion := .const `True []
  destination := .localFact `conditionalLaw
  evidenceAnchor := { proofHash := 0, inferredTypeHash := 0 }
  applicationKey? := some {
    profile := "switching"
    declaration := `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching
    backendDeclaration :=
      `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw
    ruleId := rsConditionalLaw
  }
}

private def conditionalPlan : English.CanonicalRenderPlan := ⟨#[
  ⟨role `game, "restrictedGame"⟩,
  ⟨role `system, "restrictedPermutation"⟩,
  ⟨role `proof, "conditionalProof"⟩
]⟩

#guard match English.renderAssertionOccurrence conditionalOccurrence conditionalPlan with
  | .error message => message.contains "pending source attestation"
  | .ok _ => false

#guard match English.effectiveApplicationLicense?
    "switching"
    `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching
    `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw
    rsConditionalLaw with
  | some license =>
      English.renderAssertionOccurrenceWithApplicationLicense
        conditionalOccurrence conditionalPlan license ==
          .ok "Fact conditionalLaw: The game restrictedGame is conditionally equivalent to restrictedPermutation by conditionalProof"
  | none => false

/- An exact switching license cannot authorize a different occurrence, even
when that occurrence uses the same rule identifier. -/
#guard match English.effectiveApplicationLicense?
    "switching"
    `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching
    `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw
    rsConditionalLaw with
  | some license =>
      match English.renderAssertionOccurrenceWithApplicationLicense
          { conditionalOccurrence with
            applicationKey? := some {
              profile := "some-other-application"
              declaration := `Some.Other.Theorem
              backendDeclaration :=
                `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw
              ruleId := rsConditionalLaw
            } }
          conditionalPlan license with
      | .error message => message.contains "does not authorize"
      | .ok _ => false
  | none => false

#guard (CryptoLanguage.LanguageDesign.Corpus.applicationAttestationFor?
    "switching" `Some.Other.Theorem
    `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw
    rsConditionalLaw).isNone

private def mboInvocation : RuleInvocation :=
  ⟨rsDefineCharacterizedMBO, #[dummyOperand (role `assignment),
    dummyOperand (role `characterization)]⟩

private def mboPlan : English.CanonicalRenderPlan := ⟨#[
  ⟨role `condition, "collisionMBO"⟩,
  ⟨role `assignment, "collisionCondition"⟩,
  ⟨role `characterization, "collisionCharacterization"⟩]⟩

#guard English.renderCanonical mboInvocation mboPlan == .ok
  "Let collisionMBO be the MBO given by collisionCondition, which is set on a query history exactly when two distinct queries in that history receive the same answer, as shown by collisionCharacterization"

private def systemInvocation : RuleInvocation :=
  ⟨rsBindSystem, #[dummyOperand (role `value)]⟩

#guard English.renderCanonical systemInvocation ⟨#[
    ⟨role `system, "restrictedURF"⟩,
    ⟨role `value, "[q] URF(X)"⟩]⟩ ==
  .ok (SurfaceContract.systemBinder "restrictedURF" "[q] URF(X)")

#guard SurfaceContract.naturalNumberForm.abstractForm ==
  SurfaceContract.naturalNumberBinder "NAME"
#guard SurfaceContract.factForm.abstractForm ==
  SurfaceContract.namedFact "NAME" "ASSERTION by PROOF"

/- Rejected RS declaration/property rules have no canonical renderer. -/
#guard match English.renderCanonical
    ⟨rsDeclareRestrictedURF, #[dummyOperand (role `alphabet),
      dummyOperand (role `queryBudget)]⟩
    ⟨#[⟨role `system, "restrictedFunction"⟩, ⟨role `alphabet, "X"⟩,
      ⟨role `queryBudget, "q"⟩]⟩ with
  | .error _ => true
  | .ok _ => false

end CryptoLanguage.Verbose.Tests.Rendering
