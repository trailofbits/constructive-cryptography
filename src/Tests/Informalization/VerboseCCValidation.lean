/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Verbose
import Informalization.Render.Json
import Informalization.Render.Html
import Informalization.CLI
import Examples.PRGLengthExtension
import Examples.AuthenticatedEncryption.Security
import Examples.Games
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Typed.SamplingDistance
import RandomSystems.Typed.Distinguisher

/-!
# End-to-End Validation of Paper-Grounded Verbose-CC Authoring & Trace Decompilation

Seven flagship Constructive Cryptography, Indifferentiability, Game-Playing, H-Coefficient,
and Tightness-Sandwich proofs authored with `open scoped VerboseCC`, with zero `sorry` and
only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. **PRG Length Extension** (`prgLengthExtension_verbose`): `With notation`, `Proof overview`,
   `Define hybrid ... where`, `We claim ... explaining`, `By non-expansion`, and `By hybrid chain`
   with `because "..." => ...` step notes.
2. **Authenticated Encryption Composition** (`aeadComposition_verbose` &
   `aeadHybridReduction_verbose`): `By "..." it suffices to show`, `By sequential composition`,
   `By context insensitivity on the right`, `By routine calculation`, and `We conclude`.
3. **Indifferentiability Serial Simulator Composition** (`indiffSerialComposition_verbose`):
   `We claim`, `We exhibit simulator`, `We note`, `Construct using`,
   `By composition-order invariance`.
4. **Games & Revealed Extended H-Technique** (`gameCollision_verbose` &
   `extendedHCoefficient_verbose`): `Ignoring the MBO of`, `By conditional equivalence`,
   `Let ... denote ... explaining`, and `By the extended H-technique`.
5. **Tightness Sandwich** (`bitDistinguishingTightness_verbose`): `We prove matching lower and upper bounds:`
   splitting into `lower bound` (with `We exhibit distinguisher` and `By bounding decision probabilities`)
   and `upper bound` (with `By the extended H-technique`).
-/

namespace Tests.Informalization.VerboseCCValidation

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open SystemAlgebra Probability Commons
open Informalization.Core.Presentation Informalization.Core.ContextProfile
open scoped NNReal SystemAlgebra
open scoped VerboseCC

noncomputable section

informal_symbol Commons.Evaluation.Port "\\mathsf{Port}_{\\mathrm{eval}}"
informal_symbol Commons.AE.Port "\\mathsf{Port}_{\\mathrm{AE}}"
informal_symbol Commons.AE.system.perPort "\\mathbf{E}_{\\mathsf{AE}}"
informal_symbol Commons.Encryption.system.perPort "\\mathbf{E}_{\\mathsf{enc}}"
informal_symbol Commons.AE.PTXT.perPort "\\mathsf{PTXT}"
informal_hide_args Commons.AE.PTXT.perPort 0 1
informal_symbol Commons.AE.CCA.perPort "\\mathsf{CCA}"
informal_hide_args Commons.AE.CCA.perPort 0 1
informal_symbol Commons.AE.Ideal.perPort "\\mathsf{Ideal}"
informal_hide_args Commons.AE.Ideal.perPort 0 1
informal_symbol SystemAlgebra.PDS.behavior "\\mathrm{beh}_{\\mathrm{PDS}}"
informal_symbol SystemAlgebra.PDG.behavior "\\mathrm{beh}_{\\mathrm{PDG}}"
informal_symbol SystemAlgebra.TypedSystem.ofAutomaton "\\mathrm{ofAut}_{\\mathrm{sys}}"
informal_symbol SystemAlgebra.PDG.ofAutomaton "\\mathrm{ofAut}_{\\mathrm{PDG}}"
informal_symbol ConstructiveCryptography.AdmissibleDistinguishers.admissible "\\mathrm{admissible}_{\\mathcal{D}}"
informal_symbol ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.admissible "\\mathrm{admissible}_{\\Delta}"
informal_noun SystemAlgebra.DDE "interactive environment" "interactive environments"

informal_opaque GameExamples.collision_win_le
informal_opaque GameExamples.collision_conditionallyEquivalent
informal_opaque AuthenticatedEncryption.hybrid_ideal_distance_le
informal_opaque AuthenticatedEncryption.collisionGame_conditionallyEquivalent
informal_opaque AuthenticatedEncryption.collisionGame_badProbability_le
informal_opaque AuthenticatedEncryption.collisionGame_isProbDist
informal_opaque AuthenticatedEncryption.hybrid_visible
informal_opaque AuthenticatedEncryption.hybrid_system
informal_opaque SystemAlgebra.RandomSystem.RepliesAtQueriedInterface.of_visible
informal_opaque SystemAlgebra.RandomSystem.ext
informal_opaque SystemAlgebra.RandomSystem.mix_mass
informal_opaque SystemAlgebra.RandomSystem.kernelLaw_mass_eq_expect
informal_opaque SystemAlgebra.RandomSystem.sLaw_isProbDist
informal_opaque SystemAlgebra.RandomSystem.sLaw_apply
informal_opaque Probability.Distribution.uniform_isProbDist
informal_opaque Probability.Distribution.isProbDist_single
informal_opaque Probability.Distribution.mass_singleton
informal_opaque Probability.Distribution.expect_const
informal_opaque Probability.Distribution.uniform_apply
informal_title SystemAlgebra.RandomSystem.ext "random-system extensionality"
informal_title Probability.Distribution.isProbDist_single "point-mass normalization"

/-! ## PRG Length Extension (`SchemeContext`) -/

section SchemePRGSection
paper_context SchemeContext

/-- Doubling a PRG from `S → S × S` to `S → S × S × S` via the two-call converter constructions
`𝓡₁` and `𝓡₂` incurs at most `2 * ε` distinguishing advantage against a uniform triple. -/
theorem prgLengthExtension_verbose
    {S : Type} [Fintype S] [Nonempty S]
    (G : S → S × S) {q : Commons.Evaluation.Port → ℕ} {ε : ENNReal}
    (hPRG : Δ (Examples.PRGLengthExtension.PRGReal.perPort G
      (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q))
      (Commons.MemorylessSource.perPort (S × S) 𝒰[S × S]) ≤ ε) :
    Δ (Examples.PRGLengthExtension.PRGReal.perPort (Examples.PRGLengthExtension.H G)
      (budget := q))
      (Commons.MemorylessSource.perPort (S × S × S) 𝒰[S × S × S]) ≤ 2 * ε := by
  With notation (Examples.PRGLengthExtension.PRGReal.perPort G
    (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q)) as "\\mathbf{G}_{q_1}"
    explaining "the single-call pseudorandom generator system under the first-call budget $q_1$"
  With notation (Examples.PRGLengthExtension.PRGReal.perPort G
    (budget := Examples.PRGLengthExtension.𝓡₂.insideBudget S q)) as "\\mathbf{G}_{q_2}"
    explaining "the single-call pseudorandom generator system under the second-call budget $q_2$"
  With notation (Commons.MemorylessSource.perPort (S × S) 𝒰[S × S]
    (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q)) as "\\mathbf{U}_{S^2}"
    explaining "a uniform pair source on $S \\times S$"
  With notation (Commons.MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q)) as "\\mathbf{U}_{S^3}"
    explaining "a uniform triple source on $S \\times S \\times S$"
  With notation (Examples.PRGLengthExtension.PRGReal.perPort (Examples.PRGLengthExtension.H G)
    (budget := q)) as "\\mathbf{G}^{\\mathrm{ext}}"
    explaining "the length-extended PRG system wrapping $H(s)$"
  With notation (Examples.PRGLengthExtension.𝓡₁.perPort G (budget := q)) as "\\mathcal{R}_1"
    explaining "the converter factoring out the first call to $G$"
  With notation (Examples.PRGLengthExtension.𝓡₂.perPort S (budget := q)) as "\\mathcal{R}_2"
    explaining "the converter forwarding the uniform prefix and factoring out the second call to $G$"
  Proof overview "We interpolate between ${Examples.PRGLengthExtension.PRGReal.perPort (Examples.PRGLengthExtension.H G) (budget := q)} and the ideal uniform triple ${Commons.MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q)} under query budget ${q} via two intermediate hybrids, replacing the first and second calls to ${G} in turn."
  Define hybrid M₁ := Examples.PRGLengthExtension.𝓡₁.perPort G (budget := q) •
    Commons.MemorylessSource.perPort (S × S) 𝒰[S × S]
      (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q)
    where "the first generator call is replaced by a fresh uniform pair while the second call remains pseudorandom"
  Define hybrid M₂ := Examples.PRGLengthExtension.𝓡₂.perPort S (budget := q) •
    (@id (TypedSystem (Commons.Evaluation.perPort Unit (S × S)
      (Examples.PRGLengthExtension.𝓡₂.insideBudget S q)))
      (Commons.MemorylessSource.perPort (S × S) 𝒰[S × S]
        (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q)))
    where "both generator calls are replaced by independent uniform pairs"
  We claim hFirstCall :
      Δ (Examples.PRGLengthExtension.𝓡₁.perPort G (budget := q) •
          Examples.PRGLengthExtension.PRGReal.perPort G
            (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q))
        M₁ ≤ ε
      explaining "by non-expansion under ${Examples.PRGLengthExtension.𝓡₁.perPort G (budget := q)} applied to the base PRG assumption" by
    By non-expansion
    exact hPRG
  We claim hSecondCall :
      Δ (Examples.PRGLengthExtension.𝓡₂.perPort S (budget := q) •
          Examples.PRGLengthExtension.PRGReal.perPort G
            (budget := Examples.PRGLengthExtension.𝓡₂.insideBudget S q))
        M₂ ≤ ε
      explaining "by non-expansion under ${Examples.PRGLengthExtension.𝓡₂.perPort S (budget := q)} applied to the base PRG assumption" by
    By non-expansion
    exact hPRG
  Present pseudocode "hybrid" "Length-Extension Hybrid Sequence"
    "on initial seed $s \\leftarrow \\mathcal{U}(S)$ under query budget ${q}:\n  extended generator: $(a, b) \\leftarrow G(s);\\; (c, d) \\leftarrow G(b);\\; \\mathbf{return}\\; (a, c, d)$\n  hybrid $M_1$: $(a, b) \\leftarrow \\mathcal{U}(S \\times S);\\; (c, d) \\leftarrow G(b);\\; \\mathbf{return}\\; (a, c, d)$\n  hybrid $M_2$: $a \\leftarrow \\mathcal{U}(S);\\; (c, d) \\leftarrow \\mathcal{U}(S \\times S);\\; \\mathbf{return}\\; (a, c, d)$"
  New paragraph "Two-step hybrid chain."
  rw [two_mul]
  By hybrid chain {
    cc_calc statistical
      Examples.PRGLengthExtension.PRGReal.perPort (Examples.PRGLengthExtension.H G) (budget := q)
        = Examples.PRGLengthExtension.𝓡₁.perPort G (budget := q) •
            Examples.PRGLengthExtension.PRGReal.perPort G
              (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q) :=
          because "by isolating the first PRG call via converter $\\mathcal{R}_1$" =>
            by
              By routine calculation "rewriting the length extension as a converter attachment" {
                exact Examples.PRGLengthExtension.prgReal_H_eq G q
              }
      _ ≈[ε] M₁ :=
          because "by replacing the first PRG call with $\\mathbf{U}_{S^2}$ via non-expansion" =>
            hFirstCall
      _ = Examples.PRGLengthExtension.𝓡₂.perPort S (budget := q) •
            Examples.PRGLengthExtension.PRGReal.perPort G
              (budget := Examples.PRGLengthExtension.𝓡₂.insideBudget S q) :=
          because "by regrouping the uniform prefix into the second-call converter $\\mathcal{R}_2$" =>
            Examples.PRGLengthExtension.𝓡₁_smul_prgRand G q
      _ ≈[ε] M₂ :=
          because "by replacing the second PRG call with $\\mathbf{U}_{S^2}$ via non-expansion" =>
            hSecondCall
      _ = Commons.MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q) :=
          because "by folding the two independent uniform pairs into $\\mathbf{U}_{S^3}$" =>
            Examples.PRGLengthExtension.𝓡₂_smul_prgRand q
  }

informal_title prgLengthExtension_verbose "Length Extension for Pseudorandom Generators"
informal_kind prgLengthExtension_verbose "Theorem"
informal_section prgLengthExtension_verbose
  "PRG Length Extension via Two-Call Converters"
  "We study sequential length extension of a pseudorandom generator over a finite nonempty seed space via two-call converters and non-expansion under query budget $q$."
informal_section_prelude prgLengthExtension_verbose "symbolTable" "Notation" "PRG Length Extension Symbols"
  "Parameter | Meaning\n---|---\n$S$ | Finite nonempty seed space\n$G : S \\to S \\times S$ | Base single-call pseudorandom generator\n$q$ | Per-port query budget on the outer evaluation interface\n$\\varepsilon$ | Distinguishing advantage bound for a single generator call"
informal_section_prelude_decl prgLengthExtension_verbose Examples.PRGLengthExtension.H
  "construction" "Definition" "Length-Extending Map H"
informal_section_prelude_decl prgLengthExtension_verbose Examples.PRGLengthExtension.𝓡₁.perPort
  "converterDef" "Converter" "First-Call Factoring Converter"
informal_section_prelude_decl prgLengthExtension_verbose Examples.PRGLengthExtension.𝓡₂.perPort
  "converterDef" "Converter" "Second-Call Factoring Converter"

end SchemePRGSection

/-! ## Flagship 2: Authenticated Encryption Composition (`ChannelContext`) & Reduction (`SchemeContext`) -/

section ChannelCompositionSection
paper_context ChannelContext

/-- Context-insensitive lifting of a symmetric encryption step alongside an authentication key,
composed sequentially with an authenticated-encryption converter step. -/
theorem aeadComposition_verbose
    {A B C K : Interface}
    (encConv : B ⟶ A) (macConv : C ⟶ B ⊗ K)
    (realChannel : TypedSystem A) (cpaChannel : TypedSystem B)
    (macKey : TypedSystem K) (aeIdeal : TypedSystem C)
    {ε₁ ε₂ : ENNReal}
    (hEnc : ({realChannel} : Specification (TypedSystem A)) —[encConv; ε₁]→ {cpaChannel})
    (hMac : ({cpaChannel ∥ macKey} : Specification (TypedSystem (B ⊗ K)))
      —[macConv; ε₂]→ {aeIdeal}) :
    ({realChannel ∥ macKey} : Specification (TypedSystem (A ⊗ K)))
      —[macConv ≫ (encConv ▷ K); ε₁ + ε₂]→ {aeIdeal} := by
  With role cpaChannel as "confidential channel"
  With role macKey as "authentication key"
  Proof overview "We first lift the confidentiality construction from ${realChannel} to ${cpaChannel} via ${encConv} within error ${ε₁} alongside the parallel authentication key ${macKey} using context insensitivity, then compose sequentially with the outer authentication step from ${cpaChannel ∥ macKey} to ${aeIdeal} via ${macConv}."
  By "sequential composability with the outer ${macConv} step on ${cpaChannel ∥ macKey}" it suffices to show hLifted :
      ({realChannel ∥ macKey} : Specification (TypedSystem (A ⊗ K)))
        —[encConv ▷ K; ε₁]→ {cpaChannel ∥ macKey} by
    By sequential composition of hLifted and hMac
  By context insensitivity on the right with {macKey} using hEnc

informal_title aeadComposition_verbose "Sequential Composition of Authenticated Encryption"
informal_kind aeadComposition_verbose "Theorem"
informal_section aeadComposition_verbose
  "Authenticated Encryption Composition and Concrete Reduction"
  "We formalize Banfi's constructive composition of authenticated encryption from confidentiality and plaintext integrity, first across abstract channels and then as a concrete finite-query reduction."
informal_section_prelude aeadComposition_verbose "definition" "Composition Model" "Constructive AEAD Composition"
  "In the constructive framework, authenticated encryption combines the $\\mathrm{INT}\\text{-}\\mathrm{PTXT}$ integrity filter and the $\\mathrm{IND}\\text{-}\\mathrm{CCA}$ decryption filter via hybrid reductions, relating the real AEAD system to the ideal encryption system up to a quadratic birthday collision penalty."

end ChannelCompositionSection

section SchemeAEADSection
paper_context SchemeContext

/-- Concrete authenticated encryption advantage decomposition combining the plaintext-integrity
and ciphertext-indistinguishability terms (`2 * ε_p + 2 * ε_c`) with the collision penalty. -/
theorem aeadHybridReduction_verbose
    {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : Commons.SymmetricEncryption K M C) (q : Commons.AE.Port → ℕ)
    {ε_p ε_c : ENNReal}
    (hPTXT : Δ (Commons.AE.system.perPort scheme (budget := q))
      (Commons.AE.PTXT.perPort M C (budget := q) •
        Commons.AE.system.perPort scheme (budget := q)) ≤ ε_p)
    (hCCA : Δ (Commons.AE.system.perPort scheme (budget := q))
      (Commons.AE.CCA.perPort M C (budget := q) •
        Commons.AE.system.perPort scheme (budget := q)) ≤ ε_c) :
    Δ (Commons.AE.system.perPort scheme (budget := q))
      (Commons.AE.Ideal.perPort M C (budget := q) •
        Commons.Encryption.system.perPort scheme (budget := Commons.AE.Ideal.insideBudget M C q)) ≤
      2 * ε_p + 2 * ε_c +
        (((q Commons.AE.Port.enc : ℝ≥0) ^ 2 / (Fintype.card M : ℝ≥0) : ℝ≥0) : ENNReal) := by
  With notation (Commons.AE.system.perPort scheme (budget := q)) as "\\mathcal{E}"
    explaining "the real authenticated-encryption system for $\\mathsf{scheme}$"
  With notation (Commons.AE.PTXT.perPort M C (budget := q)) as "\\mathsf{PTXT}"
    explaining "the plaintext-integrity filter converter"
  With notation (Commons.AE.CCA.perPort M C (budget := q)) as "\\mathsf{CCA}"
    explaining "the chosen-ciphertext filter converter"
  With notation (Commons.AE.PTXT.perPort M C (budget := q) •
    Commons.AE.system.perPort scheme (budget := q)) as "\\mathcal{E}_{\\mathsf{ptxt}}"
    explaining "the plaintext-filtered authenticated-encryption hybrid"
  With notation (Commons.AE.CCA.perPort M C (budget := q) •
    Commons.AE.system.perPort scheme (budget := q)) as "\\mathcal{E}_{\\mathsf{cca}}"
    explaining "the CCA-filtered authenticated-encryption hybrid"
  With notation (Commons.AE.Ideal.perPort M C (budget := q) •
    Commons.Encryption.system.perPort scheme (budget := Commons.AE.Ideal.insideBudget M C q)) as "\\mathcal{E}_{\\mathsf{ideal}}"
    explaining "the ideal authenticated-encryption system"
  Proof overview "We reduce ${Δ (Commons.AE.system.perPort scheme (budget := q)) (Commons.AE.Ideal.perPort M C (budget := q) • Commons.Encryption.system.perPort scheme (budget := Commons.AE.Ideal.insideBudget M C q))} to the four PTXT/CCA hybrid transitions via the AEAD collision-hybrid bound, then substitute ${ε_p} and ${ε_c}."
  By "the hybrid decomposition of ${scheme} together with the plaintext-collision penalty ${(q Commons.AE.Port.enc : ℝ≥0) ^ 2 / (Fintype.card M : ℝ≥0)}" it suffices to show hBase :
      Δ (Commons.AE.system.perPort scheme (budget := q))
        (Commons.AE.PTXT.perPort M C (budget := q) •
          Commons.AE.system.perPort scheme (budget := q)) +
          Δ (Commons.AE.system.perPort scheme (budget := q))
            (Commons.AE.CCA.perPort M C (budget := q) •
              Commons.AE.system.perPort scheme (budget := q)) +
        Δ (Commons.AE.system.perPort scheme (budget := q))
          (Commons.AE.PTXT.perPort M C (budget := q) •
            Commons.AE.system.perPort scheme (budget := q)) +
      Δ (Commons.AE.system.perPort scheme (budget := q))
        (Commons.AE.CCA.perPort M C (budget := q) •
          Commons.AE.system.perPort scheme (budget := q)) ≤
        2 * ε_p + 2 * ε_c by {
    By routine calculation "combining the AEAD collision-hybrid bound with the four component hops" {
      exact (AuthenticatedEncryption.real_ideal_distance_le scheme q).trans
        (add_le_add hBase le_rfl)
    }
  }
  We conclude "Summing ${ε_p} and ${ε_c} twice yields $2\\varepsilon_p + 2\\varepsilon_c$." by {
    exact (add_le_add (add_le_add (add_le_add hPTXT hCCA) hPTXT) hCCA).trans_eq <| by
      rw [two_mul ε_p, two_mul ε_c, add_assoc (ε_p + ε_c) ε_p ε_c,
        add_assoc ε_p ε_c (ε_p + ε_c), add_comm ε_c (ε_p + ε_c),
        add_assoc ε_p ε_c ε_c, ← add_assoc ε_p ε_p (ε_c + ε_c)]
  }

informal_title aeadHybridReduction_verbose "Authenticated Encryption from IND-CCA and INT-PTXT"
informal_kind aeadHybridReduction_verbose "Theorem"
informal_section_prelude aeadHybridReduction_verbose "symbolTable" "Notation" "Authenticated-Encryption Hybrid Systems"
  "Symbol | Meaning\n---|---\n$\\mathcal{E}$ | Real authenticated-encryption system $\\mathbf{E}_{\\mathsf{AE}}(\\mathrm{scheme})$ under budget $q$\n$\\mathsf{PTXT},\\; \\mathsf{CCA}$ | Plaintext-integrity and chosen-ciphertext filter converters\n$\\mathcal{E}_{\\mathsf{ptxt}} := \\mathsf{PTXT} \\cdot \\mathcal{E}$ | Plaintext-filtered authenticated-encryption hybrid\n$\\mathcal{E}_{\\mathsf{cca}} := \\mathsf{CCA} \\cdot \\mathcal{E}$ | Chosen-ciphertext-filtered authenticated-encryption hybrid\n$\\mathcal{E}_{\\mathsf{ideal}} := \\mathsf{Ideal} \\cdot \\mathbf{E}_{\\mathsf{enc}}(\\mathrm{scheme})$ | Ideal authenticated-encryption system from encryption alone\n$\\varepsilon_p,\\; \\varepsilon_c$ | Bounds on the $\\mathsf{PTXT}$ and $\\mathsf{CCA}$ distinguishing advantages"
informal_section_prelude_decl aeadHybridReduction_verbose Commons.AE.PTXT.perPort
  "converterDef" "Filter" "Plaintext-Integrity Filter Converter"
informal_section_prelude_decl aeadHybridReduction_verbose Commons.AE.CCA.perPort
  "converterDef" "Filter" "Chosen-Ciphertext Filter Converter"
informal_section_prelude_decl aeadHybridReduction_verbose Commons.AE.Ideal.perPort
  "converterDef" "Wrapper" "Ideal Authenticated-Encryption Converter"

end SchemeAEADSection

/-! ## Indifferentiability Serial Simulator Composition (`IndiffContext`) -/

section IndiffSection
paper_context IndiffContext

/-- Serial composition of an indifferentiable protocol and an ideal-world application via
exhibition of the admitted simulator and composition-order invariance. -/
theorem indiffSerialComposition_verbose
    {H H' P Q B : Interface}
    (protocol : H ⊗ P ⟶ B) (application : H' ⟶ H)
    (simulators : Set (P ⟶ Q)) (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (real : TypedSystem B) (ideal : TypedSystem (H ⊗ Q)) (target : TypedSystem (H' ⊗ Q))
    {ε δ : ENNReal}
    (indifferentiable : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ ε)
    (idealApplication : Δ ((application ▷ Q) • ideal) target ≤ δ) :
    ({real} : Specification (TypedSystem B)) —[(application ▷ P) ≫ protocol]→
      Commons.Indifferentiability.specification target simulators (ε + δ) := by
  With notation simulator as "\\sigma" explaining "the explicit indifferentiability simulator at the $P$-interface"
  With notation simulators as "\\Sigma" explaining "the class of admitted simulators"
  Proof overview "We first package ${protocol} as an indifferentiability claim via ${simulator} on the adversarial interface ${P}, turn the ${application} distance bound between ${(application ▷ Q) • ideal} and ${target} into a concrete construction step, and compose both serially."
  We claim hIndiff :
      ({real} : Specification (TypedSystem B)) —[protocol]→
        Commons.Indifferentiability.specification ideal simulators ε
      explaining "by attaching ${simulator} on the adversarial interface ${P}" by
    We exhibit simulator simulator on interface P
    · exact admitted
    · exact indifferentiable
  New paragraph "Application step and composition."
  We note hApp :
      ({ideal} : Specification (TypedSystem (H ⊗ Q))) —[application ▷ Q; δ]→ {target}
      explaining "from the assumed distance bound between ${(application ▷ Q) • ideal} and ${target} within error ${δ}" by
    Construct using idealApplication
  By composition-order invariance composing hIndiff and hApp

informal_title indiffSerialComposition_verbose "Serial Composition of Indifferentiable Constructions"
informal_kind indiffSerialComposition_verbose "Theorem"
informal_section indiffSerialComposition_verbose
  "Indifferentiability and Serial Composition"
  "Under Maurer--Renner indifferentiability, an honest application converter and a relaxed simulator specification compose sequentially by commuting the outer converter past the simulator on the adversarial interface."
informal_section_prelude indiffSerialComposition_verbose "definition" "Specification" "Indifferentiability Simulator Relaxation"
  "Given an ideal system $\\mathbf{S}$, an adversarial simulator class $\\Sigma$, and an error tolerance $\\varepsilon$, the indifferentiability specification collects all simulator images $\\Sigma \\cdot \\mathbf{S} = \\{(H \\triangleleft \\sigma) \\cdot \\mathbf{S} : \\sigma \\in \\Sigma\\}$ under statistical $\\varepsilon$-relaxation."

end IndiffSection

/-! ## Games, H-Coefficients, and Tightness Sandwich (`GameBasedContext`) -/

section GameBasedSection
paper_context GameBasedContext

/-- Any compatible solver's advantage between the AEAD collision-hybrid system and the ideal
AEAD system is bounded by the plaintext-collision game-winning bound. -/
theorem gameCollision_verbose
    {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : Commons.SymmetricEncryption K M C) (q : Commons.AE.Port → ℕ)
    {s : (TypedSystem (Commons.AE.perPort M C q) → ℝ) ×
      (TypedGame (Commons.AE.perPort M C q) → ℝ)}
    (hs : s ∈ ConstructiveCryptography.DistinctionGames.solvers (Commons.AE.perPort M C q)) :
    |s.1 (AuthenticatedEncryption.Hybrid scheme q) -
        s.1 (Commons.AE.Ideal.perPort M C • Commons.Encryption.system.perPort scheme)| ≤
      ↑(q Commons.AE.Port.enc) ^ 2 / ↑(Fintype.card M) := by
  With notation (GameExamples.collision scheme q) as "\\mathbf{G}_{\\mathrm{coll}}"
    explaining "the collision game recording whether two encryption queries repeat a plaintext"
  With notation (AuthenticatedEncryption.Hybrid scheme q) as "\\mathcal{H}"
    explaining "the AEAD collision-hybrid system"
  With notation (Commons.AE.Ideal.perPort M C (budget := q) •
    Commons.Encryption.system.perPort scheme (budget := Commons.AE.Ideal.insideBudget M C q)) as "\\mathcal{E}_{\\mathsf{ideal}}"
    explaining "the ideal AEAD system"
  Proof overview "We identify ${AuthenticatedEncryption.Hybrid scheme q} as the underlying system obtained by ignoring the MBO of ${GameExamples.collision scheme q}, reduce any solver's advantage via conditional equivalence, and apply the birthday-style query bound."
  Ignoring the MBO of (GameExamples.collision scheme q) via (GameExamples.collision_visible scheme q)
  New paragraph "Reduction via conditional equivalence."
  By "conditional equivalence between ${GameExamples.collision scheme q} and ${Commons.AE.Ideal.perPort M C (budget := q) • Commons.Encryption.system.perPort scheme (budget := Commons.AE.Ideal.insideBudget M C q)} while the MBO remains unset" it suffices to show hWin :
      s.2 (GameExamples.collision scheme q) ≤
        ↑(q Commons.AE.Port.enc) ^ 2 / ↑(Fintype.card M) by {
    have hCond :
        |s.1 (ConstructiveCryptography.DistinctionGames.visible (GameExamples.collision scheme q)) -
            s.1 (Commons.AE.Ideal.perPort M C • Commons.Encryption.system.perPort scheme)| ≤
          s.2 (GameExamples.collision scheme q) := by
      By conditional equivalence from (GameExamples.collision_conditionallyEquivalent scheme q) using hs
    exact hCond.trans hWin
  }
  We conclude "Bounding the probability of provoking a plaintext-collision MBO across ${q Commons.AE.Port.enc} encryption queries establishes the bound." by {
    exact GameExamples.collision_win_le scheme q
      (ConstructiveCryptography.DistinctionGames.solvers_winner hs)
  }

informal_title gameCollision_verbose "Game-Playing Bound for AEAD Collisions"
informal_kind gameCollision_verbose "Theorem"
informal_section gameCollision_verbose
  "Game Playing, Monotone Binary Outputs, and the H-Coefficient Technique"
  "We connect code-based game-playing bounds for monotone binary outputs (MBOs) with the revealed H-coefficient technique and establish a tight one-query distinguisher sandwich."
informal_section_prelude gameCollision_verbose "definition" "Game Model" "Monotone Binary Outputs and Conditional Equivalence"
  "A game system $G$ exposes an underlying observable system $\\mathrm{visible}(G)$ together with a monotone binary output (MBO) flag. When two systems agree conditioned on the MBO remaining unset, any solver advantage is bounded by the winning probability $\\Pr[\\mathrm{MBO}(G) = 1]$."
informal_section_prelude gameCollision_verbose "symbolTable" "Notation" "Collision-Game Systems"
  "Symbol | Meaning\n---|---\n$\\mathcal{H}$ | AEAD collision-hybrid system $\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathcal{E}$\n$\\mathbf{G}_{\\mathrm{coll}}$ | Collision game whose observable system is $\\mathcal{H}$ and whose MBO flags repeated plaintexts\n$\\mathcal{E}_{\\mathsf{ideal}}$ | Ideal AEAD system $\\mathsf{Ideal}\\,\\mathbf{E}_{\\mathsf{enc}}(\\mathrm{scheme})$\n$s = (s_1, s_2)$ | Solver pair with system distinguisher $s_1$ and game-winning functional $s_2$"

/-- Revealed Extended H-Technique with non-trivial ideal randomness and bad-transcript split,
leaving the ideal reveal law, good-transcript ratio, and bad-mass combinatorics to standard Lean. -/
theorem extendedHCoefficient_verbose (A : Interface) (S : TypedSystem A) :
    Δ S S ≤ ((1 / 2 : ℝ≥0) : ENNReal) := by
  Proof overview "We express ${S} as a trivial one-point mixture and apply the revealed Extended H-Technique, augmenting ideal transcripts with an independent coin flip whose ${Bool.true} outcome is declared bad."
  Let P denote Probability.Distribution.ProbDist.single ()
    where "the degenerate one-point prior distribution on ${Unit}"
  We note hp : S.1 = SystemAlgebra.RandomSystem.mix P (fun _ => S.1) by
    By routine calculation "verifying that the trivial one-point mixture reproduces ${S}" {
      apply SystemAlgebra.RandomSystem.ext
      intro h
      simp only [SystemAlgebra.RandomSystem.mix_mass, ne_eq, one_ne_zero, not_false_eq_true,
        Finsupp.support_single, Finsupp.single_eq_same, one_mul, Finset.sum_const,
        Finset.card_singleton, one_smul, P, Probability.Distribution.ProbDist.single]
    }
  By the extended H-technique
    mixing real (fun _ => S.1) over P using hp
    revealing (fun _ _ => false) and (fun _ => Probability.Distribution.uniform Bool)
    with bad transcripts (fun τ => τ.2 = true) bound by (1 / 2)
    with good ratio loss 0
  · exact fun _ => Probability.Distribution.uniform_isProbDist (A := Bool)
  · intro τ hg
    rcases τ with ⟨h, b⟩
    cases b with
    | false =>
        simp only [sub_zero, SystemAlgebra.RandomSystem.kernelMass,
          Probability.Distribution.uniform_apply, Fintype.card_bool, Nat.cast_ofNat, one_div,
          one_mul, SystemAlgebra.RandomSystem.revealMass, Probability.Distribution.ProbDist.single,
          ne_eq, one_ne_zero, not_false_eq_true, Finsupp.support_single, Finsupp.single_eq_same,
          ↓reduceIte, Finset.sum_const, Finset.card_singleton, one_smul, P]
        linarith [S.1.mass_nonneg h]
    | true =>
        exact (hg rfl).elim
  · intro E n _ hE
    rw [SystemAlgebra.RandomSystem.kernelLaw_mass_eq_expect]
    have hmass : (Probability.Distribution.uniform Bool).mass (fun b => b = true) = 1 / 2 := by
      rw [Probability.Distribution.mass_singleton]
      norm_num [Probability.Distribution.uniform_apply]
    simp only [hmass, Probability.Distribution.expect_const,
      (S.1.sLaw_isProbDist (hE _ S.2) n).weight_eq, mul_one, le_refl]

informal_title extendedHCoefficient_verbose "Revealed H-Coefficient Security Bound"
informal_kind extendedHCoefficient_verbose "Theorem"
informal_section_prelude_decl extendedHCoefficient_verbose SystemAlgebra.RandomSystem.HCoefficient
  "definition" "Technique" "Revealed H-Coefficient Witness"

/-! ## Tightness Sandwich (`lower_bound` + `upper_bound`) -/

/-- One-query Boolean bit interface with budget 1. -/
abbrev bitInterface : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

informal_symbol bitInterface "\\mathcal{I}_{\\mathrm{bit}}"

/-- Deterministic bit system answering every single-port query with constant bit `c`. -/
def fixedBit (c : Bool) : TypedSystem bitInterface :=
  TypedSystem.ofFunction fun _ _ => c

/-- Randomized bit system drawing `c ← 𝒰(Bool)` and behaving like `fixedBit c`. -/
def sampledBit : TypedSystem bitInterface :=
  TypedSystem.sample (Probability.Distribution.uniform Bool) fixedBit

/-- Single query `()` at port `()`. -/
def bitQuery : DDE (Σ i, bitInterface.X i) (Σ i, bitInterface.Y i) :=
  DDE.ofQueries [⟨(), ()⟩]

/-- Transcript witnessing reply `true`. -/
def trueBitTranscript : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i)) :=
  [(⟨(), ()⟩, ⟨(), true⟩)]

private lemma bitQuery_bounded : QueryBounded 1 bitQuery := by
  intro ys hd
  cases ys with
  | nil => simp
  | cons _ _ =>
      simp only [bitQuery, DDE.ofQueries, SystemAlgebra.fixedQueries, List.length_cons,
        List.getElem?_cons_succ, List.getElem?_nil] at hd
      exact absurd hd (by simp)

private lemma bitQuery_compatible : bitInterface.inputDomain.Compatible bitQuery := by
  intro _ _ h x _ _ hx
  have hh : h.length = 0 := by
    have hb := bitQuery_bounded (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)
    simp only [List.length_map] at hb
    omega
  have he : h = [] := List.length_eq_zero_iff.mp hh
  subst h
  simp only [bitInterface, Interface.queryBudget, ne_eq, Interface.inputDomain, Domain.ofInputs,
    List.append_eq_nil_iff, List.map_eq_nil_iff, List.cons_ne_self, and_false, not_false_eq_true,
    List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add,
    add_le_iff_nonpos_left, nonpos_iff_eq_zero, List.length_eq_zero_iff, true_and]

private lemma trueBitTranscript_good : Good bitQuery.1 1 trueBitTranscript := by
  constructor
  · apply (FollowsStrategy.snoc_iff (h := [])).mpr
    refine ⟨FollowsStrategy.nil, ?_⟩
    simp [bitQuery, DDE.ofQueries, SystemAlgebra.fixedQueries]
  · exact Or.inl rfl

/-- Explicit compatible one-query distinguisher checking whether the bit reply equals `true`. -/
def bitObserver : bitInterface.inputDomain.Distinguisher :=
  Distribution.ProbDist.single ⟨envProbe bitQuery (fun t => t.1.zip t.2 = trueBitTranscript),
    envProbe_isDDD bitQuery_bounded,
    Domain.envProbe_decisionCompatible bitQuery_compatible _⟩

/-- Typed behavior of `bitObserver`. -/
def bitObserverBehavior : TypedDistinguisher bitInterface := bitObserver.behavior

informal_symbol bitObserverBehavior "D"

private lemma bitObserver_fixed_prob (b : Bool) :
    bitObserverBehavior.1 (fixedBit b) = if b then 1 else 0 := by
  change bitObserver.probability (fixedBit b).1 = if b then 1 else 0
  simp only [bitObserver, Distribution.ProbDist.single, Domain.Distinguisher.probability,
    Finsupp.sum_single_index, zero_mul, one_mul]
  rw [RandomSystem.decisionProbability_envProbe bitQuery_bounded _ (fixedBit b).2]
  have zip_proj (h : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i))) :
      (h.map Prod.fst).zip (h.map Prod.snd) = h := (List.zip_of_prod rfl rfl).symm
  simp only [zip_proj]
  rw [Distribution.mass_singleton, RandomSystem.sLaw_apply, ite_eq_left trueBitTranscript_good]
  cases b <;> norm_num [fixedBit, TypedSystem.ofFunction_mass, bitInterface, trueBitTranscript]

private lemma bitObserver_false_prob :
    bitObserverBehavior.1 (fixedBit false) = 0 := by
  simpa using bitObserver_fixed_prob false

private lemma bitObserver_sampled_prob :
    bitObserverBehavior.1 sampledBit = 1 / 2 := by
  change bitObserver.probability sampledBit.1 = 1 / 2
  rw [sampledBit, TypedSystem.sample, Domain.Distinguisher.probability_mix]
  have h0 := bitObserver_fixed_prob false
  have h1 := bitObserver_fixed_prob true
  change bitObserver.probability (fixedBit false).1 = 0 at h0
  change bitObserver.probability (fixedBit true).1 = 1 at h1
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  norm_num [Distribution.uniform_apply, h0, h1]

/-- Exact tightness sandwich `Δ (fixedBit false) sampledBit = 1 / 2`: matching lower bound via an
explicit one-query distinguisher and upper bound via the Extended H-Technique. -/
theorem bitDistinguishingTightness_verbose :
    ((1 / 2 : ℝ≥0) : ENNReal) ≤ Δ (fixedBit false) sampledBit ∧
      Δ (fixedBit false) sampledBit ≤ ((1 / 2 : ℝ≥0) : ENNReal) := by
  With notation (fixedBit false) as "\\mathbf{F}_0"
    explaining "the constant-$\\mathsf{false}$ one-query bit system"
  With notation sampledBit as "\\mathbf{F}_{\\mathrm{rand}}"
    explaining "the uniformly randomized one-query bit system"
  Proof overview "We prove matching ${(1 / 2 : ℝ≥0)} lower and upper bounds on ${Δ (fixedBit false) sampledBit}: the lower bound exhibits ${bitObserverBehavior} checking for output ${Bool.true}, while the upper bound applies the Extended H-Technique."
  We prove matching lower and upper bounds :
  lower bound {
    Present pseudocode "distinguisher" "One-Query Bit Distinguisher"
      "distinguisher ${bitObserverBehavior} given oracle $\\mathbf{F}$:\n  query $b \\leftarrow \\mathbf{F}()$ on ${bitInterface}\n  return $b = \\mathsf{true}$"
    We exhibit distinguisher bitObserverBehavior
    By bounding decision probabilities of bitObserverBehavior via bitObserver_false_prob and bitObserver_sampled_prob
  }
  upper bound {
    Let P₁ denote Probability.Distribution.ProbDist.single ()
      where "the degenerate one-point distribution on ${Unit}"
    We note hMix : (fixedBit false).1 = SystemAlgebra.RandomSystem.mix P₁ (fun _ => (fixedBit false).1) by
      By routine calculation "verifying that the trivial one-point mixture reproduces ${fixedBit false}" {
        apply SystemAlgebra.RandomSystem.ext
        intro h
        simp only [SystemAlgebra.RandomSystem.mix_mass, P₁, Probability.Distribution.ProbDist.single,
          ne_eq, one_ne_zero, not_false_eq_true, Finsupp.support_single, Finsupp.single_eq_same,
          one_mul, Finset.sum_const, Finset.card_singleton, one_smul]
      }
    By the extended H-technique
      mixing real (fun _ => (fixedBit false).1) over P₁ using hMix
      revealing (fun _ _ => ()) and (fun _ => Finsupp.single () 1)
      with bad transcripts (fun τ => τ.1 = trueBitTranscript) bound by (1 / 2)
      with good ratio loss 0
    · exact fun _ => Probability.Distribution.isProbDist_single ()
    · intro τ hg
      rcases τ with ⟨h, ⟨⟩⟩
      simp only [sub_zero, one_mul, SystemAlgebra.RandomSystem.kernelMass,
        Finsupp.single_eq_same, mul_one, SystemAlgebra.RandomSystem.revealMass,
        Probability.Distribution.ProbDist.single, ne_eq, one_ne_zero, not_false_eq_true,
        Finsupp.support_single, ↓reduceIte, Finset.sum_const, Finset.card_singleton, one_smul, P₁]
      cases h with
      | nil =>
          simp [sampledBit, TypedSystem.sample_mass, fixedBit, TypedSystem.ofFunction_mass,
            bitInterface, Interface.queryBudget, Probability.Distribution.uniform_apply]
          have hc : (Probability.Distribution.uniform Bool).support.card ≤ 2 :=
            (Finset.card_le_univ _).trans_eq Fintype.card_bool
          have hcR : ((Probability.Distribution.uniform Bool).support.card : ℝ) ≤ 2 := by
            exact_mod_cast hc
          linarith
      | cons hd tl =>
          cases tl with
          | nil =>
              rcases hd with ⟨⟨i, x⟩, ⟨j, y⟩⟩
              cases i; cases x; cases j; cases y with
              | false =>
                  simp [sampledBit, TypedSystem.sample_mass, fixedBit,
                    TypedSystem.ofFunction_mass, bitInterface, Interface.queryBudget,
                    Probability.Distribution.uniform_apply]
                  norm_num
              | true =>
                  exfalso
                  exact hg rfl
          | cons hd2 tl2 =>
              have hz : ∀ c, (fixedBit c).1 (hd :: hd2 :: tl2) = 0 := fun c => by
                simp [fixedBit, TypedSystem.ofFunction_mass, bitInterface, Interface.queryBudget]
              have hs0 : sampledBit.1 (hd :: hd2 :: tl2) = 0 := by
                rw [sampledBit, TypedSystem.sample_mass]
                exact Finset.sum_eq_zero (fun c _ => by simp [hz c])
              simpa [hs0] using (hz false).ge
    · intro E n _ _
      rw [SystemAlgebra.RandomSystem.kernelLaw_mass_eq_expect]
      have hUnitMass (h : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i))) :
          Probability.Distribution.mass (Finsupp.single () (1 : ℝ))
            (fun _ => h = trueBitTranscript) =
            if h = trueBitTranscript then 1 else 0 := by
        simp [Probability.Distribution.mass, Finsupp.sum_single_index]
      simp_rw [hUnitMass]
      have hGoodMass :
          ((sampledBit.1.sLaw (↑E) n).mass (fun h => h = trueBitTranscript)) ≤ 1 / 2 := by
        rw [Probability.Distribution.mass_singleton, SystemAlgebra.RandomSystem.sLaw_apply]
        split_ifs
        · rw [sampledBit, TypedSystem.sample_mass]
          simp [fixedBit, TypedSystem.ofFunction_mass, bitInterface, Interface.queryBudget,
            trueBitTranscript, Probability.Distribution.uniform_apply]
        · norm_num
      have heq :
          (sampledBit.1.sLaw (↑E) n).expect (fun h => if h = trueBitTranscript then (1 : ℝ) else 0) =
            (sampledBit.1.sLaw (↑E) n).mass (fun h => h = trueBitTranscript) := by
        rw [Probability.Distribution.expect, Probability.Distribution.mass]
        simp only [mul_ite, mul_one, mul_zero]
        convert rfl
      linarith
  }

informal_title bitDistinguishingTightness_verbose "Tightness of One-Query Bit Distinguishing"
informal_kind bitDistinguishingTightness_verbose "Theorem"
informal_section_prelude bitDistinguishingTightness_verbose "interfaceSpec" "Bit Interface" "One-Query Boolean Bit Systems"
  "Over the single-query Boolean interface $\\mathcal{I}_{\\mathrm{bit}}$ with unit budget, we compare the constant-false system $\\mathbf{F}_0$ against the uniform-bit mixture $\\mathbf{F}_{\\mathrm{rand}}$ drawing $c \\leftarrow \\mathcal{U}(\\{\\mathsf{false}, \\mathsf{true}\\})$ before answering the single query."

end GameBasedSection

end

/-! ## Axiom Audits (Standard Axioms Only, Zero `sorry`) -/

#print axioms prgLengthExtension_verbose
#print axioms aeadComposition_verbose
#print axioms aeadHybridReduction_verbose
#print axioms indiffSerialComposition_verbose
#print axioms gameCollision_verbose
#print axioms extendedHCoefficient_verbose
#print axioms bitDistinguishingTightness_verbose

/-! ## Export Rendered JSON & HTML + Zero-Leakage Check -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let targetDecls : Array Name := #[
    `Tests.Informalization.VerboseCCValidation.prgLengthExtension_verbose,
    `Tests.Informalization.VerboseCCValidation.aeadComposition_verbose,
    `Tests.Informalization.VerboseCCValidation.aeadHybridReduction_verbose,
    `Tests.Informalization.VerboseCCValidation.indiffSerialComposition_verbose,
    `Tests.Informalization.VerboseCCValidation.gameCollision_verbose,
    `Tests.Informalization.VerboseCCValidation.extendedHCoefficient_verbose,
    `Tests.Informalization.VerboseCCValidation.bitDistinguishingTightness_verbose
  ]
  let doc ← liftTermElabM <| Informalization.Render.Json.buildDocument
    "Constructive Cryptography Proofs"
    (some "Selected theorems on pseudorandom generators, authenticated encryption, indifferentiability, games, and the H-coefficient technique")
    targetDecls
  let texts := Informalization.CLI.collectDocumentTexts doc
  let leaks := Informalization.Core.Hygiene.auditZeroLeakage texts
  unless leaks.isEmpty do
    throwError "Verbose-CC informalization leaked {leaks.size} forbidden string(s): {leaks}"
  let outDir : System.FilePath :=
    "/Users/marcilunga/.gemini/antigravity/brain/63ffab73-7f96-4075-be50-4d10a715e8ee/scratch/cc-validation"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "verbose_cc.json") (Informalization.Render.Json.renderDocumentJson doc)
  IO.FS.writeFile (outDir / "verbose_cc.html") (Informalization.Render.Html.renderDocumentHtml doc)
  IO.println s!"VerboseCCValidation: exported {doc.entries.size} entries, auditZeroLeakage = {leaks.size}"

end Tests.Informalization.VerboseCCValidation
