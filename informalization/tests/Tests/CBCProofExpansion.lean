import CBCMAC.ConditionalEquivalence
import Informalization.Semantics.CBC
import Informalization.Semantics.Discourse
import Informalization.Semantics.Plan
import Informalization.Semantics.Realize

/-!
# CBC semantic proof expansion

This focused integration test does not import or edit the downstream CBC main
theorem. It checks the stable lower theorem that supplies the collision-free
output law. In particular, an immediately applied lambda in its elaborated
proof must not hide the registered mathematical lemma from the reader tree.
-/

namespace Tests.CBCProofExpansion

open Lean Meta Elab Command
open Informalization.Semantics
open RandomSystems
open RandomSystems.ConditionalEquivalence

universe u

noncomputable section

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

theorem collisionConditionalEquivalenceProbe [Nontrivial M]
    (blockForm : M → List X)
    (prefixFree : ∀ left right, left ≠ right →
      ¬ blockForm left <+: blockForm right)
    (condition : (X → X) → System.MC M)
    (condition_eq_cbcBad : ∀ function messages,
      (condition function).1 messages = decide
        (CBCMAC.CBCCombinatorics.cbcBad function blockForm messages)) :
    RandomSystems.PDG.ofFunction
        (RandomFunction.uniform X X).law.1
        (fun function message =>
          CBCMAC.CBCCombinatorics.cbc function (blockForm message))
        condition |≡ (RandomFunction.uniform M X : RandomSystems.PDS M X) :=
  CBCMAC.cbc_conditionallyEquivalent_urf_of_condition_eq_cbcBad
    blockForm prefixFree condition condition_eq_cbcBad

run_cmd liftTermElabM do
  let environment ← getEnv
  let some plan ← Plan.fromDeclarationWithProfile? environment
      Informalization.Semantics.CBC.catalog
      Informalization.Semantics.CBC.profile
      ``collisionConditionalEquivalenceProbe 512 1
    | throwError "could not recover the CBC conditional-equivalence proof"
  let roles := plan.steps.map fun step => step.application.role
  unless roles == #[
      .collisionConditionalEquivalence,
      .conditionalUniformOutputs
    ] do
    throwError
      "the CBC conditional-equivalence expansion lost its output-law lemma: {repr roles}"
  unless plan.steps[1]!.application.provenance.declaration? == some
      `CBCMAC.CBCCombinatorics.mass_cbc_outputs_and_not_cbcBad_on_list_eq do
    throwError "the output-law node is not backed by the checked CBC mass identity"
  unless plan.supportForest.size == 1 &&
      plan.supportForest[0]!.macroChildren.size == 1 &&
      plan.supportForest[0]!.macroChildren[0]!.view.stepId == 1 do
    throwError "the output-law lemma is not nested under the collision equivalence"

  let some detailedPlan ← Plan.fromDeclarationWithProfile? environment
      Informalization.Semantics.CBC.catalog
      Informalization.Semantics.CBC.profile
      ``collisionConditionalEquivalenceProbe 512 2
    | throwError "could not expand the checked CBC output-law proof"
  unless detailedPlan.steps.any (fun step =>
      step.application.provenance.declaration? ==
        some `CBCMAC.CBCCombinatorics.cbcLastInput_injOn &&
      step.application.role == .distinctTerminalInputs) do
    throwError "the collision-free output law lost its checked terminal-input lemma"
  let information ← getConstInfo ``collisionConditionalEquivalenceProbe
  forallTelescope information.type fun _ conclusion => do
    let some graph ← Registry.recoverGraphWith? environment
        Informalization.Semantics.CBC.catalog conclusion
      | throwError "could not recover the CBC conditional-equivalence statement"
    let discourse ← Discourse.ofGraphAndPlan graph plan
      Informalization.Semantics.CBC.profile
    let realized ← Realize.document discourse
    let some collisionEquivalence ← pure <| realized.sentences.find? fun sentence =>
        sentence.kind == .registeredRule .collisionConditionalEquivalence
      | throwError "the collision-equivalence sentence was not realized"
    let some outputLaw ← pure <| collisionEquivalence.details.find? fun detail =>
        detail.kind == .registeredRule .conditionalUniformOutputs
      | throwError "the checked output law is not expandable from the collision equivalence"
    unless outputLaw.text.contains "\\Pr_" &&
        outputLaw.text.contains "\\mathsf{Bad}_{B,L}" do
      throwError "the output-law expansion did not render its checked probability identity"

end

end Tests.CBCProofExpansion
