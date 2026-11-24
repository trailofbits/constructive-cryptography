/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Explanation
import Informalization.Core.ProofGraph

/-!
# Canonical JSON Export (Shared by Standalone CADMO HTML & Verso)

Serializes any checked `Explanation.Document` to stable, versioned JSON so the isolated
Verso consumer package and CI quality gates can consume the exact same proof tree without
duplicating Lean evaluation.
-/

namespace Informalization.Render.Json

open Lean Meta
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph

/-- Deduplicate symbol inspectors by stable `key`. -/
def dedupInspectors (xs : Array SymbolInspector) : Array SymbolInspector := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array SymbolInspector := #[]
  for item in xs do
    if !seen.contains item.key then
      seen := seen.insert item.key
      out := out.push item
  return out

/-- Build a canonical `Document` from an ordered list of declaration names. -/
def buildDocument (title : String) (subtitle? : Option String := none)
    (decls : Array Name) (config : Informalization.Core.ProofGraph.Config := {}) : MetaM Document := do
  let mut entries : Array Entry := #[]
  let mut inspectors : Array SymbolInspector := #[]
  for d in decls do
    let (entry, ins) ← informalizeDeclaration d config
    entries := entries.push entry
    inspectors := inspectors ++ ins
  return {
    title
    subtitle?
    defaultMode := .paper
    entries
    inspectors := dedupInspectors inspectors
  }

/-- Serialize a `Document` as pretty-printed JSON. -/
def renderDocumentJson (doc : Document) : String :=
  (toJson doc).pretty

/-- Write a checked declaration's `Document` JSON to disk. -/
elab "#informalize_json " decl:ident " to " path:str : command => do
  let jsonStr ← Elab.Command.runTermElabM fun _ => do
    let declName ← Elab.realizeGlobalConstNoOverloadWithInfo decl
    let doc ← buildDocument (humanLemmaLabel (← getEnv) declName) none #[declName]
    return renderDocumentJson doc
  IO.FS.writeFile path.getString jsonStr

end Informalization.Render.Json
