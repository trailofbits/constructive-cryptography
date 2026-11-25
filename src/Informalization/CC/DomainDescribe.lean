/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Core.Presentation
import Informalization.Core.Overlay
import Informalization.CC.Registry
import Commons.Definitions.Encryption
import Commons.Definitions.MAC
import Commons.Definitions.Cipher
import Commons.Definitions.Signature
import Commons.Definitions.PublicKeyEncryption
import Commons.Definitions.KEM
import Commons.Schemes.Bytes
import Probability.Distribution

/-!
# Zero-Edit Domain Descriptions (`paper_describe_for`) for Core `Commons` & `Probability` Types

Registers checked pure-data `PaperDescribeRule` entries on upstream cryptographic and probabilistic
structures without modifying upstream `Commons/` or `Probability/` files:
* `Commons.SymmetricEncryption` (`\mathcal{E}` style, `gen`/`enc`/`dec`)
* `Commons.MAC` (`\mathcal{M}` style, `gen`/`tag`/`verify`)
* `Commons.BlockCipher` (`\mathsf{E}` style, `encrypt`/`decrypt`)
* `Commons.SignatureScheme` (`\mathcal{S}` style, `gen`/`sign`/`verify`)
* `Commons.PublicKeyEncryption` (`\mathcal{E}` style, `gen`/`enc`/`dec`)
* `Commons.KEM` (`\mathcal{K}` style, `gen`/`encaps`/`decaps`)
* `Probability.Distribution.ProbDist` & `Probability.Distribution`
-/

namespace Informalization.CC.DomainDescribe

open Informalization.Core.Presentation
open Informalization.Core.Overlay

paper_describe_for Commons.SymmetricEncryption "symmetric-key encryption scheme"
  (plural := "symmetric-key encryption schemes")
  (carrier := false)
  (varStyle := .mathcal)
  (qualifier := "with key space {K}, message space {M}, and ciphertext space {C}")
  (unpack := [gen, enc, dec])

paper_describe_for Commons.MAC "message authentication code"
  (plural := "message authentication codes")
  (carrier := false)
  (varStyle := .mathcal)
  (qualifier := "with key space {K}, message space {M}, and tag space {T}")
  (unpack := [gen, tag, verify])

paper_describe_for Commons.BlockCipher "block cipher"
  (plural := "block ciphers")
  (carrier := false)
  (varStyle := .mathsf)
  (qualifier := "with key space {K} and block space {X}")
  (unpack := [encrypt, decrypt])

paper_describe_for Commons.SignatureScheme "digital signature scheme"
  (plural := "digital signature schemes")
  (carrier := false)
  (varStyle := .mathcal)
  (qualifier := "with public keys {PK}, secret keys {SK}, messages {M}, and signatures {Sig}")
  (unpack := [gen, sign, verify])

paper_describe_for Commons.PublicKeyEncryption "public-key encryption scheme"
  (plural := "public-key encryption schemes")
  (carrier := false)
  (varStyle := .mathcal)
  (qualifier := "with public keys {PK}, secret keys {SK}, messages {M}, and ciphertexts {C}")
  (unpack := [gen, enc, dec])

paper_describe_for Commons.KEM "key encapsulation mechanism"
  (plural := "key encapsulation mechanisms")
  (carrier := false)
  (varStyle := .mathcal)
  (qualifier := "with public keys {PK}, secret keys {SK}, ciphertexts {C}, and keys {K}")
  (unpack := [gen, encaps, decaps])

paper_describe_for Probability.Distribution.ProbDist "probability distribution"
  (plural := "probability distributions")
  (carrier := false)
  (qualifier := "over {0}")

paper_describe_for Probability.Distribution "sub-probability distribution"
  (plural := "sub-probability distributions")
  (carrier := false)
  (qualifier := "over {0}")

paper_describe_for Commons.Bytes "fixed-length byte string"
  (plural := "fixed-length byte strings")
  (carrier := false)
  (qualifier := "of length {0}")

paper_describe_for Commons.ByteString "bounded-length byte string"
  (plural := "bounded-length byte strings")
  (carrier := false)
  (qualifier := "of length at most {0}")

paper_describe_for SystemAlgebra.Domain "admissible-query domain"
  (plural := "admissible-query domains")
  (carrier := false)
  (qualifier := "from {0} to {1}")

paper_describe_for SystemAlgebra.RandomSystem "random system"
  (plural := "random systems")
  (carrier := false)

paper_describe_for List "finite sequence"
  (plural := "finite sequences")
  (carrier := false)
  (qualifier := "over {0}")

paper_describe_for Finset "finite set"
  (plural := "finite sets")
  (carrier := false)
  (qualifier := "of {0}")

paper_describe_for SystemAlgebra.Domain.Distinguisher "compatible distinguisher"
  (plural := "compatible distinguishers")
  (carrier := false)

paper_describe_for SystemAlgebra.Domain.DistinguisherBehavior "compatible distinguisher"
  (plural := "compatible distinguishers")
  (carrier := false)

/-!
## Opaque Proof-Boundary Guards (`C5`: MBO / PDG Internal Plumbing)

Prevents proof-graph expansion from descending into low-level RandomSystems
MBO/PDG internal coupling and unset-probability plumbing lemmas (while preserving
top-level `RuleExplainer` summaries in `CC/Families/Games.lean`).
-/

informal_opaque SystemAlgebra.RandomSystem.RepliesAtQueriedInterface.of_visible
informal_opaque SystemAlgebra.RandomSystem.mass_unsetMBOs_le_visible
informal_opaque SystemAlgebra.RandomSystem.winProbability_le_of_unsetProbability
informal_opaque SystemAlgebra.Domain.Distinguisher.winProbability_le_of_unsetProbability
informal_opaque SystemAlgebra.RandomSystem.transcriptDistance_visible_le_of_unsetProbability
informal_opaque SystemAlgebra.RandomSystem.GameEquivalent.transcriptDistance_visible_le
informal_opaque SystemAlgebra.RandomSystem.GameEquivalent.winProbability_eq
informal_opaque SystemAlgebra.PDG.visible_behavior
informal_opaque SystemAlgebra.PDG.monotoneMBO_behavior
informal_opaque SystemAlgebra.PDG.repliesAtQueriedInterface_behavior
informal_opaque SystemAlgebra.PDG.exists_transcript_withMBO
informal_opaque SystemAlgebra.PDG.unsetProbability_behavior
informal_opaque SystemAlgebra.PDG.one_sub_le_unsetProbability_behavior
informal_opaque SystemAlgebra.PDG.conditionallyEquivalent_behavior
informal_opaque SystemAlgebra.PDG.gameEquivalent_behavior_of_isCoupling
informal_opaque SystemAlgebra.Interface.win_le
informal_opaque SystemAlgebra.Interface.dist_visible_le
informal_opaque SystemAlgebra.Interface.conditionallyEquivalent_ofPDG_iff
informal_opaque SystemAlgebra.Interface.game_dist_le
informal_opaque SystemAlgebra.Interface.game_dist_ofSingleFunction_le
informal_opaque SystemAlgebra.Domain.SolverBehavior.decision_surjective
informal_opaque SystemAlgebra.Domain.SolverBehavior.decision_absorb

/-!
## Opaque Proof-Boundary Guards (RandomSystems / Revealed H-Coefficient / Probability Plumbing)

Keeps expanded proof trees mathematical by preventing descent into low-level transcript-law
normalization, mixture mass, and finite-support distribution algebra while preserving top-level
`RuleExplainer` summaries in `CC/Families/Transcript.lean`.
-/

informal_opaque SystemAlgebra.RandomSystem.ext
informal_opaque SystemAlgebra.RandomSystem.mix_mass
informal_opaque SystemAlgebra.RandomSystem.mass_nonneg
informal_opaque SystemAlgebra.RandomSystem.sLaw_isProbDist
informal_opaque SystemAlgebra.RandomSystem.sLaw_apply
informal_opaque SystemAlgebra.RandomSystem.kernelLaw_eq_jointLaw
informal_opaque SystemAlgebra.RandomSystem.revealMass_nonneg
informal_opaque SystemAlgebra.RandomSystem.revealLaw_apply
informal_opaque SystemAlgebra.RandomSystem.kernelLaw_apply
informal_opaque SystemAlgebra.RandomSystem.kernelLaw_nonNeg
informal_opaque SystemAlgebra.RandomSystem.fTransform_fst_revealLaw
informal_opaque SystemAlgebra.RandomSystem.fTransform_fst_kernelLaw
informal_opaque SystemAlgebra.RandomSystem.kernelLaw_mass_eq_expect
informal_opaque SystemAlgebra.TypedSystem.possible_domain
informal_opaque Probability.Distribution.uniform_isProbDist
informal_opaque Probability.Distribution.isProbDist_single
informal_opaque Probability.Distribution.mass_singleton
informal_opaque Probability.Distribution.expect_const
informal_opaque Probability.Distribution.uniform_apply

end Informalization.CC.DomainDescribe
