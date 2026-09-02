import LanguageDesign

/-!
# Executable language-contract acceptance

This target is intentionally independent of the evolving Random Systems
checkout. It makes the shared design fail closed before either frontend is
built.
-/

open CryptoLanguage.LanguageDesign

namespace CryptoLanguage.LanguageDesign.ContractTests

open Contract SurfaceContract
open Presentation

private def theoremPresentationWitness : TheoremPresentation := {
  declaration := `Example.securityTheorem
  title := "A Reader-Facing Theorem"
  introductions := #[{
    fragments := #[
      .text "Let ",
      .reference {
        target := .theoremBinder `X
        latex := "X"
        hoverLatex := "X"
        description := "The finite sample space."
      },
      .text " be the sample space."
    ]
  }]
}

#guard Contract.isValid
#guard Contract.entityFamilies.size == 14
#guard Contract.compilationRules.size == 23
#guard Contract.missingEntityConcepts.isEmpty
#guard Contract.missingRelations.isEmpty
#guard Contract.missingRules.isEmpty
#guard Contract.unknownCanonicalSurfaceRules.isEmpty
#guard Contract.publishedAuthoringRulesWithoutCanonicalSurface.isEmpty
#guard SurfaceContract.forms.all (·.witnessComplete)
#guard theoremPresentationWitness.isWellFormed
#guard theoremPresentationWitness.introductions[0]!.fragments[1]! ==
  .reference {
    target := .theoremBinder `X
    latex := "X"
    hoverLatex := "X"
    description := "The finite sample space."
  }
#guard !({ theoremPresentationWitness with title := "" }).isWellFormed
#guard !({ theoremPresentationWitness with introductions := #[] }).isWellFormed

#guard SurfaceContract.canonicalFormById? `rs.bindSystem |>.any fun form =>
  form.template.abstractForm == "Let system be the system value"

#guard SurfaceContract.canonicalFormById? `rs.defineCharacterizedMBO |>.any fun form =>
  form.template.holeIds == #[`condition, `assignment, `characterization]

#guard SurfaceContract.canonicalFormById?
    `informalization.ignoreCollisionMbo |>.any fun form =>
  form.template.instantiate #[(`game, "G"), (`system, "\nFORMULA")] ==
    "Consider the collision game G, whose MBO records a nontrivial collision among the inputs to the round function. Its underlying system is \nFORMULA."

#guard SurfaceContract.canonicalFormById?
    `informalization.conditionalEquivalenceReduction |>.any fun form =>
  form.template.holeIds == #[`conditionalEquivalence, `consequence]

#guard SurfaceContract.canonicalFormById?
    `informalization.collisionEquivalenceReduction |>.any fun form =>
  form.template.holeIds == #[`game, `consequence]

#guard SurfaceContract.canonicalFormById?
    `informalization.commonDomainBridge |>.any fun form =>
  form.template.abstractForm ==
    "The resulting comparison reduces, by common-domain data processing, to the corresponding normalized PDS advantage."

end CryptoLanguage.LanguageDesign.ContractTests
