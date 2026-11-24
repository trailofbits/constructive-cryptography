/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoInformalization.Schema
import VersoInformalization.CadmoBlocks

/-!
# `verso-informalize` CLI

Lightweight isolated Lean executable that decodes any canonical `Explanation.Document` JSON
exported by `Informalization.Render.Json` and either:
* `inspect <doc.json>` — verifies schema decoding and prints entry/inspector/axiom summary;
* `render-body <doc.json> <out.html>` — renders static ETH CADMO HTML body blocks;
* `verso-stub <doc.json> <out.lean> [ModuleName]` — emits a Verso literate `.lean` chapter stub.
-/

open VersoInformalization.Schema
open VersoInformalization.CadmoBlocks

private def usage : String :=
  "Usage:\n" ++
  "  verso-informalize inspect <doc.json>\n" ++
  "  verso-informalize render-body <doc.json> <out.html> [--auditor]\n" ++
  "  verso-informalize verso-stub <doc.json> <out.lean> [ModuleName]\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["inspect", jsonPath] =>
      let doc ← loadDocumentFile jsonPath
      IO.println s!"Title: {doc.title}"
      IO.println s!"Entries: {doc.entries.size}"
      IO.println s!"Inspectors: {doc.inspectors.size}"
      for e in doc.entries do
        let status := if e.axioms.hasSorry then "SORRY" else s!"{e.axioms.axioms.size} axioms"
        IO.println s!"  - [{e.header}] {e.declaration} ({status}, {e.proof.size} top-level proof nodes)"
      return 0
  | "render-body" :: jsonPath :: outPath :: rest =>
      let mode := if rest.contains "--auditor" then ViewMode.auditor else ViewMode.paper
      let doc ← loadDocumentFile jsonPath
      let html := renderDocumentBodyHtml doc mode
      IO.FS.writeFile outPath html
      IO.println s!"Wrote CADMO HTML body to {outPath}"
      return 0
  | "verso-stub" :: jsonPath :: outPath :: rest =>
      let modName := rest.headD "Chapter"
      let doc ← loadDocumentFile jsonPath
      let stub := renderVersoChapterStub doc jsonPath modName
      IO.FS.writeFile outPath stub
      IO.println s!"Wrote Verso chapter stub to {outPath}"
      return 0
  | _ =>
      IO.eprintln usage
      return 1
