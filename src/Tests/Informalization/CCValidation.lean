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
    "Generic CC informalization of Examples/AuthenticatedEncryption/Security.lean (zero per-theorem overlays)"
    #[`AuthenticatedEncryption.ae_of_ind_cca_int_ptxt,
      `AuthenticatedEncryption.real_ideal_distance_le]
  exportTarget outDir "prg"
    "PRG Length Extension"
    "Generic CC informalization of Examples/PRGLengthExtension.lean (DSL converters, memoryless sources, cc_calc)"
    #[`Examples.PRGLengthExtension.prg_length_extension]
  exportTarget outDir "indifferentiability"
    "Indifferentiability and Serial Simulator Composition"
    "Generic CC informalization of ConstructiveCryptography/CryptographicAlgebra/Indifferentiability.lean"
    #[`ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage,
      `ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage,
      `ConstructiveCryptography.CryptographicAlgebra.Specification.mixed_application_of_indifferentiability]
  exportTarget outDir "games_hcoeff"
    "Games, Monotone Binary Outputs, and Revealed H-Coefficients"
    "Generic CC informalization of Examples/Games.lean and RandomSystems/Distance/RevealedHCoefficient.lean"
    #[`GameExamples.win_le_of_reduction,
      `GameExamples.hybrid_ideal_advantage_le,
      `SystemAlgebra.Interface.distance_le_of_hCoefficient]

end ExportValidationBench
