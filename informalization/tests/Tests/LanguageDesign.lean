import Informalization.Semantics.LanguageDesign

open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open Informalization.Semantics
open CryptoLanguage.LanguageDesign.Corpus

namespace Tests.LanguageDesign

#guard Informalization.Semantics.LanguageDesign.argumentRole .game == role `game
#guard Informalization.Semantics.LanguageDesign.argumentRole (.premise 3) ==
  role (.num `premise 3)
#guard Informalization.Semantics.LanguageDesign.proofRuleRole .hTechnique ==
  rsHCoefficient
#guard Informalization.Semantics.LanguageDesign.proofRuleRole
    .conditionalEquivalenceToBlindWinning == rsConditionalBlindBound
#guard Informalization.Semantics.LanguageDesign.nodeRole
    (.proposition .conditionalEquivalence) ==
      .relation CryptoLanguage.LanguageDesign.Ontology.Relations.conditionalEquivalence

#guard attestationFor? proofCollisionConditionalEquivalence |>.any
  (fun attestation => attestation.source == .checkedLibrary &&
    !attestation.isPubliclyLicensed)

#guard attestationForDeclaration?
    `RandomSystems.Switching.urf_collision_condEquiv_urp
    proofCollisionConditionalEquivalence |>.any
      (fun attestation => attestation.source == .cr18Fallback &&
        attestation.construction == `switching.urfCollisionConditionalEquivalence)

#guard attestationForDeclaration?
    `Applications.CBCCombinatorics.not_cbcBad_implies_uniform_outputs
    proofConditionalUniformOutputs |>.any
      (fun attestation => attestation.source == .cr18Fallback &&
        attestation.construction == `cbc.uniformConsistentOutputs)

end Tests.LanguageDesign
