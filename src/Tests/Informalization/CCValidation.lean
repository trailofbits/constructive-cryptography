/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization
import Examples.AuthenticatedEncryption.Security
import Examples.PRGLengthExtension
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
import Examples.Games
import Tests.RevealedHCoefficient

/-!
# Generic CC Informalization Validation Bench (Zero Per-Theorem Hacks)

Validates all three output surfaces (Lean Infoview `#informalize_show`, standalone ETH CADMO
HTML, and canonical JSON for Verso + CI gates) across four diverse built-in Constructive
Cryptography examples with **zero per-theorem overlays or hardcoded essays**:
1. Authenticated Encryption (`AuthenticatedEncryption.ae_of_ind_cca_int_ptxt`, `real_ideal_distance_le`)
2. PRG Length Extension (`Examples.PRGLengthExtension.prg_length_extension`)
3. Indifferentiability Composition (`constructs_of_simulatorImage`, `serial_simulatorImage`, `mixed_application_of_indifferentiability`)
4. Games, MBOs & Revealed H-Coefficient (`GameExamples.win_le_of_reduction`, `GameExamples.hybrid_ideal_advantage_le`, `SystemAlgebra.Interface.distance_le_of_hCoefficient`)
-/

informal_symbol Commons.Evaluation.Port "\\mathsf{Port}_{\\mathrm{eval}}"
informal_symbol Commons.AE.Port "\\mathsf{Port}_{\\mathrm{AE}}"
informal_symbol Commons.AE.system.perPort "\\mathrm{system}_{\\mathrm{AE}}"
informal_symbol Commons.Encryption.system.perPort "\\mathrm{system}_{\\mathrm{enc}}"
informal_symbol SystemAlgebra.PDS.behavior "\\mathrm{beh}_{\\mathrm{PDS}}"
informal_symbol SystemAlgebra.PDG.behavior "\\mathrm{beh}_{\\mathrm{PDG}}"
informal_symbol SystemAlgebra.TypedSystem.ofAutomaton "\\mathrm{ofAut}_{\\mathrm{sys}}"
informal_symbol SystemAlgebra.PDG.ofAutomaton "\\mathrm{ofAut}_{\\mathrm{PDG}}"
informal_symbol ConstructiveCryptography.AdmissibleDistinguishers.admissible "\\mathrm{admissible}_{\\mathcal{D}}"
informal_symbol ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.admissible "\\mathrm{admissible}_{\\Delta}"

informal_opaque GameExamples.collision_win_le
informal_opaque GameExamples.collision_conditionallyEquivalent
informal_opaque AuthenticatedEncryption.hybrid_ideal_distance_le
informal_opaque AuthenticatedEncryption.collisionGame_conditionallyEquivalent
informal_opaque AuthenticatedEncryption.collisionGame_badProbability_le
informal_opaque AuthenticatedEncryption.collisionGame_isProbDist
informal_opaque AuthenticatedEncryption.hybrid_visible
informal_opaque AuthenticatedEncryption.hybrid_system
informal_opaque SystemAlgebra.RandomSystem.RepliesAtQueriedInterface.of_visible

informal_title AuthenticatedEncryption.ae_of_ind_cca_int_ptxt
  "Authenticated Encryption from IND-CCA and INT-PTXT"
informal_kind AuthenticatedEncryption.ae_of_ind_cca_int_ptxt "Theorem"
informal_section_prelude_decl AuthenticatedEncryption.ae_of_ind_cca_int_ptxt
  Commons.AE.PTXT.perPort "converterDef" "Filter" "Plaintext-Integrity Filter Converter"
informal_section_prelude_decl AuthenticatedEncryption.ae_of_ind_cca_int_ptxt
  Commons.AE.CCA.perPort "converterDef" "Filter" "Chosen-Ciphertext Filter Converter"
informal_section_prelude_decl AuthenticatedEncryption.ae_of_ind_cca_int_ptxt
  Commons.AE.Ideal.perPort "converterDef" "Wrapper" "Ideal Authenticated-Encryption Converter"
informal_title AuthenticatedEncryption.real_ideal_distance_le
  "Hybrid Distance Bound for Authenticated Encryption"
informal_kind AuthenticatedEncryption.real_ideal_distance_le "Lemma"
informal_title Examples.PRGLengthExtension.prg_length_extension
  "Length Extension of a Pseudorandom Generator"
informal_kind Examples.PRGLengthExtension.prg_length_extension "Theorem"
informal_section_prelude_decl Examples.PRGLengthExtension.prg_length_extension
  Examples.PRGLengthExtension.H "construction" "Definition" "Length-Extending Map H"
informal_section_prelude_decl Examples.PRGLengthExtension.prg_length_extension
  Examples.PRGLengthExtension.𝓡₁.perPort "converterDef" "Converter" "First-Call Factoring Converter"
informal_section_prelude_decl Examples.PRGLengthExtension.prg_length_extension
  Examples.PRGLengthExtension.𝓡₂.perPort "converterDef" "Converter" "Second-Call Factoring Converter"
informal_title ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage
  "Construction from an Admitted Simulator Witness"
informal_kind ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage "Lemma"
informal_section_prelude_decl ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage
  ConstructiveCryptography.CryptographicAlgebra.Specification.simulatorImage
  "definition" "Specification" "Admitted Simulator Image"
informal_section_prelude ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage
  "definition" "Relaxation" "Statistical Relaxation of a Specification"
  "For any specification $\\mathcal{S}$ and error bound $\\varepsilon \\ge 0$, the statistical relaxation $\\mathcal{S}^{\\varepsilon}$ consists of all resources $R$ within distinguishing advantage $\\Delta(R, S) \\le \\varepsilon$ of some $S \\in \\mathcal{S}$."
informal_title ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage
  "Serial Composition under Indifferentiability"
informal_kind ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage "Theorem"
informal_title ConstructiveCryptography.CryptographicAlgebra.Specification.mixed_application_of_indifferentiability
  "Mixed Honest Applications with a Common Simulator"
informal_kind ConstructiveCryptography.CryptographicAlgebra.Specification.mixed_application_of_indifferentiability "Theorem"
informal_title GameExamples.win_le_of_reduction
  "Winning Probability Bound under Game Reduction"
informal_kind GameExamples.win_le_of_reduction "Lemma"
informal_section_prelude GameExamples.win_le_of_reduction
  "definition" "Game Model" "Game Reductions and Monotone Binary Outputs"
  "Game reductions transport solver advantage bounds along interface converters, while conditional equivalence bounds any solver between a game's underlying random system and a target system by the game's winning probability."
informal_title GameExamples.hybrid_ideal_advantage_le
  "AEAD Collision-Hybrid Advantage via Conditional Equivalence"
informal_kind GameExamples.hybrid_ideal_advantage_le "Theorem"
informal_section_prelude_decl GameExamples.hybrid_ideal_advantage_le
  Commons.AE.Ideal.perPort "converterDef" "Wrapper" "Ideal Authenticated-Encryption Converter"
informal_title SystemAlgebra.Interface.distance_le_of_hCoefficient
  "Distinguishing Bound via the Revealed H-Coefficient Technique"
informal_kind SystemAlgebra.Interface.distance_le_of_hCoefficient "Theorem"
informal_section_prelude_decl SystemAlgebra.Interface.distance_le_of_hCoefficient
  SystemAlgebra.RandomSystem.HCoefficient "definition" "Technique" "Revealed H-Coefficient Witness"

#informalize_show Examples.PRGLengthExtension.prg_length_extension
#informalize_show AuthenticatedEncryption.ae_of_ind_cca_int_ptxt
#informalize_show ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage
#informalize_show GameExamples.hybrid_ideal_advantage_le

section ExportValidationBench

open Informalization.Core.Hygiene
open Informalization.Render.Json
open Informalization.Render.Html

private def exportTarget (outDir : System.FilePath) (slug title subtitle : String)
    (decls : Array Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  let (jsonStr, htmlStr, leaks) ← Lean.Elab.Command.runTermElabM fun _ => do
    let doc ← buildDocument title (some subtitle) decls
    let mut texts : Array String := #[]
    for e in doc.entries do
      for p in e.statement do
        for inl in p do
          match inl with
          | .text s | .emph s | .inlineMath s => texts := texts.push s
          | .displayMath s pt => texts := texts.push (s ++ pt)
          | .symbol _ d _ => texts := texts.push d
          | .citation l d => texts := texts.push (l ++ " " ++ d)
      for n in e.proof do
        texts := texts ++ n.collectAllText
    let leaks := auditZeroLeakage texts
    return (renderDocumentJson doc, renderDocumentHtml doc, leaks)
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / s!"{slug}.json") jsonStr
  IO.FS.writeFile (outDir / s!"{slug}.html") htmlStr
  IO.println s!"[CCValidation] exported {slug}: {htmlStr.length}B HTML, {jsonStr.length}B JSON, core leaks={leaks.size}"
  if !leaks.isEmpty then
    for l in leaks.take 10 do
      IO.println s!"  LEAK: {l}"

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let outDir : System.FilePath :=
    "/Users/marcilunga/.gemini/antigravity/brain/63ffab73-7f96-4075-be50-4d10a715e8ee/scratch/cc-validation"
  exportTarget outDir "aead"
    "Authenticated Encryption from IND-CCA and INT-PTXT"
    "Authenticated encryption via INT-PTXT, IND-CCA, and birthday collision bounds"
    #[`AuthenticatedEncryption.ae_of_ind_cca_int_ptxt,
      `AuthenticatedEncryption.real_ideal_distance_le]
  exportTarget outDir "prg"
    "PRG Length Extension"
    "Sequential length extension of a pseudorandom generator via two-call converters"
    #[`Examples.PRGLengthExtension.prg_length_extension]
  exportTarget outDir "indifferentiability"
    "Indifferentiability and Serial Simulator Composition"
    "Serial composition and mixed honest applications under indifferentiability"
    #[`ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage,
      `ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage,
      `ConstructiveCryptography.CryptographicAlgebra.Specification.mixed_application_of_indifferentiability]
  exportTarget outDir "games_hcoeff"
    "Games, Monotone Binary Outputs, and Revealed H-Coefficients"
    "Game reductions, monotone binary outputs, and the revealed H-coefficient technique"
    #[`GameExamples.win_le_of_reduction,
      `GameExamples.hybrid_ideal_advantage_le,
      `SystemAlgebra.Interface.distance_le_of_hCoefficient]

end ExportValidationBench
