/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.CLI
import Paper.PRGLengthExtension
import Paper.Composition
import Paper.AEAD
import Paper.Indifferentiability
import Paper.GamesHCoeff

/-!
# Benchmark Validation & Export Harness (B1–B6)

Imports all five Iteration-2 benchmark modules, audits axioms across every flagship theorem
(ensuring zero `sorry` and standard Lean axioms only), enforces `auditZeroLeakage = 0`, and
exports `prg`, `aead`, `indifferentiability`, `games_hcoeff`, and `verbose_cc` (JSON + HTML)
into `/Users/marcilunga/.gemini/antigravity/brain/63ffab73-7f96-4075-be50-4d10a715e8ee/scratch/cc-validation`.
-/

namespace Paper.ExportCC

open Lean Elab Command
open Informalization.Core.Hygiene
open Informalization.Render.Json
open Informalization.Render.Html

/-! ## Axiom Audits (Standard Lean Axioms Only, Zero `sorryAx`) -/

#print axioms Paper.PRGLengthExtension.prg_length_extension
#print axioms Paper.Composition.serial_parallel_composition
#print axioms Paper.AEAD.aead_hybrid_distance_le
#print axioms Paper.AEAD.aead_of_ind_cca_int_ptxt
#print axioms Paper.Indifferentiability.constructs_of_simulator_witness
#print axioms Paper.Indifferentiability.serial_indifferentiability_composition
#print axioms Paper.Indifferentiability.mixed_honest_application
#print axioms Paper.GamesHCoeff.mbo_reduction_bound
#print axioms Paper.GamesHCoeff.aead_collision_mbo_bound
#print axioms Paper.GamesHCoeff.h_coefficient_method
#print axioms Paper.GamesHCoeff.point_vs_uniform_tightness

private def exportAndAudit (outDir : System.FilePath) (slug title subtitle : String)
    (decls : Array Name) : CommandElabM Unit := do
  let doc ← liftTermElabM <| buildDocument title (some subtitle) decls
  let texts := Informalization.CLI.collectDocumentTexts doc
  let leaks := auditZeroLeakage texts
  unless leaks.isEmpty do
    throwError "[Paper.ExportCC] bundle `{slug}` failed auditZeroLeakage ({leaks.size} leak(s)): {leaks}"
  IO.FS.createDirAll outDir
  let jsonStr := renderDocumentJson doc
  let htmlStr := renderDocumentHtml doc
  IO.FS.writeFile (outDir / s!"{slug}.json") jsonStr
  IO.FS.writeFile (outDir / s!"{slug}.html") htmlStr
  IO.println s!"[Paper.ExportCC] exported {slug}: {doc.entries.size} entries, {htmlStr.length}B HTML, {jsonStr.length}B JSON, auditZeroLeakage = {leaks.size}"

#eval show CommandElabM Unit from do
  let outDir : System.FilePath :=
    "/Users/marcilunga/.gemini/antigravity/brain/63ffab73-7f96-4075-be50-4d10a715e8ee/scratch/cc-validation"
  exportAndAudit outDir "prg"
    "PRG Length Extension"
    "Sequential length extension of a pseudorandom generator in Constructive Cryptography"
    #[`Paper.PRGLengthExtension.prg_length_extension]
  exportAndAudit outDir "aead"
    "Authenticated Encryption from IND-CCA and INT-PTXT"
    "Authenticated encryption via INT-PTXT, IND-CCA, and Banfi's plaintext-collision birthday bound"
    #[`Paper.AEAD.aead_hybrid_distance_le,
      `Paper.AEAD.aead_of_ind_cca_int_ptxt]
  exportAndAudit outDir "indifferentiability"
    "Indifferentiability and Serial Simulator Composition"
    "Maurer–Renner simulator witnesses, P-interface serial composition, and mixed honest applications"
    #[`Paper.Indifferentiability.constructs_of_simulator_witness,
      `Paper.Indifferentiability.serial_indifferentiability_composition,
      `Paper.Indifferentiability.mixed_honest_application]
  exportAndAudit outDir "games_hcoeff"
    "Games, Monotone Binary Outputs, and the H-Coefficient Method"
    "MBO game-playing reductions, AEAD collision bounds, H-coefficient decomposition, and general-N tightness"
    #[`Paper.GamesHCoeff.mbo_reduction_bound,
      `Paper.GamesHCoeff.aead_collision_mbo_bound,
      `Paper.GamesHCoeff.h_coefficient_method,
      `Paper.GamesHCoeff.point_vs_uniform_tightness]
  exportAndAudit outDir "verbose_cc"
    "Constructive Cryptography and Random-System Proofs"
    "PRG extension, serial-parallel composition, AEAD, indifferentiability, MBO games, and H-coefficients"
    #[`Paper.PRGLengthExtension.prg_length_extension,
      `Paper.Composition.serial_parallel_composition,
      `Paper.AEAD.aead_hybrid_distance_le,
      `Paper.AEAD.aead_of_ind_cca_int_ptxt,
      `Paper.Indifferentiability.constructs_of_simulator_witness,
      `Paper.Indifferentiability.serial_indifferentiability_composition,
      `Paper.Indifferentiability.mixed_honest_application,
      `Paper.GamesHCoeff.mbo_reduction_bound,
      `Paper.GamesHCoeff.aead_collision_mbo_bound,
      `Paper.GamesHCoeff.h_coefficient_method,
      `Paper.GamesHCoeff.point_vs_uniform_tightness]

end Paper.ExportCC
