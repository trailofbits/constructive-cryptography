/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Explanation
import Informalization.Core.Hygiene
import Informalization.Core.ProofGraph
import Informalization.Render.Json
import Informalization.Render.Html
import Informalization.CC.All

/-!
# Standalone Informalization CLI Runner

Loads compiled Lean `.olean` modules via `Lean.importModules`, runs the unified Kyle Miller /
Constructive Cryptography informalization pipeline (`Informalization.Render.Json.buildDocument`),
and exports:
* standalone offline-ready ETH CADMO monograph HTML (`--html <path>`),
* canonical checked JSON IR for Verso & CI (`--json <path>`),
* optional strict hygiene & sorry-free audit (`--strict`, using `Hygiene.auditZeroLeakage`).

## Usage

```text
informalize --module <ModName> [--module <ModName> ...]
            [--title "Document Title"] [--subtitle "Subtitle"]
            [--html out.html] [--json out.json]
            [--max-depth 4] [--strict]
            <DeclName> [<DeclName> ...]
```
-/

namespace Informalization.CLI

open Lean Meta
open Informalization.Core.Explanation
open Informalization.Core.Hygiene
open Informalization.Core.ProofGraph
open Informalization.Render.Json
open Informalization.Render.Html

/-- Parsed command-line options for the informalization runner. -/
structure CliOptions where
  modules : Array Name := #[]
  decls : Array Name := #[]
  title? : Option String := none
  subtitle? : Option String := none
  htmlPath? : Option System.FilePath := none
  jsonPath? : Option System.FilePath := none
  maxLemmaDepth : Nat := 4
  strict : Bool := false
  showHelp : Bool := false
  deriving Inhabited

/-- Parse a dotted Lean name string (`Foo.Bar.baz`) into a `Lean.Name`. -/
def parseDottedName (s : String) : Name :=
  s.splitOn "." |>.foldl (init := .anonymous) fun acc part =>
    if part.isEmpty then acc else .str acc part

/-- Print CLI usage help to stderr. -/
def usageText : String :=
  String.intercalate "\n" [
    "Usage: informalize [OPTIONS] <DeclName> [<DeclName> ...]",
    "",
    "Options:",
    "  --module <ModName>     Lean module to load via importModules (repeatable)",
    "  --title <Title>        Document title (defaults to first declaration's label)",
    "  --subtitle <Subtitle>  Optional document subtitle",
    "  --html <Path>          Write standalone ETH CADMO HTML to <Path>",
    "  --json <Path>          Write canonical JSON IR to <Path>",
    "  --max-depth <Nat>      Maximum cross-lemma recursion depth (default: 4)",
    "  --strict               Fail if Hygiene.auditZeroLeakage or sorryAx audit finds issues",
    "  -h, --help             Show this help message"
  ]

/-- Clean recursive argument parser supporting flags and positional `<DeclName>` arguments. -/
def parseCliArgs (args : List String) : Except String CliOptions :=
  let rec loop (xs : List String) (opts : CliOptions) : Except String CliOptions :=
    match xs with
    | [] => .ok opts
    | "-h" :: _ | "--help" :: _ => .ok { opts with showHelp := true }
    | "--strict" :: rest => loop rest { opts with strict := true }
    | "--module" :: mod :: rest =>
        let nm := parseDottedName mod
        if nm.isAnonymous then .error s!"invalid module name: '{mod}'"
        else loop rest { opts with modules := opts.modules.push nm }
    | ["--module"] => .error "--module requires a module name"
    | "--title" :: t :: rest => loop rest { opts with title? := some t }
    | ["--title"] => .error "--title requires a string value"
    | "--subtitle" :: s :: rest => loop rest { opts with subtitle? := some s }
    | ["--subtitle"] => .error "--subtitle requires a string value"
    | "--html" :: p :: rest => loop rest { opts with htmlPath? := some ⟨p⟩ }
    | ["--html"] => .error "--html requires an output path"
    | "--json" :: p :: rest => loop rest { opts with jsonPath? := some ⟨p⟩ }
    | ["--json"] => .error "--json requires an output path"
    | "--max-depth" :: nStr :: rest =>
        match nStr.toNat? with
        | some n => loop rest { opts with maxLemmaDepth := n }
        | none => .error s!"--max-depth expects a natural number, got '{nStr}'"
    | ["--max-depth"] => .error "--max-depth requires a natural number"
    | arg :: rest =>
        if arg.startsWith "-" then
          .error s!"unknown option: '{arg}'"
        else
          let nm := parseDottedName arg
          if nm.isAnonymous then .error s!"invalid declaration name: '{arg}'"
          else loop rest { opts with decls := opts.decls.push nm }
  loop args {}

/-- Flatten all reader-facing text inside a single `SymbolInspector` for strict zero-leakage checks. -/
private def collectInspectorTexts (ins : SymbolInspector) : Array String := Id.run do
  let mut out : Array String := #[ins.display]
  if let some rb := ins.roleBadge? then out := out.push rb
  if let some ds := ins.docString? then out := out.push ds
  for c in ins.clauses do out := out.push c
  for hyp in ins.sectionAssumptions do
    out := out ++ hyp.map Inline.collectText
  match ins.kind with
  | .mathDefinition eq summary =>
      out := out.push eq
      out := out.push summary
  | .localShorthand eq desc =>
      out := out.push eq
      out := out.push desc
  | .parameter desc => out := out.push desc
  | .witnessCard title rows =>
      out := out.push title
      for (k, v) in rows do
        out := out.push k
        out := out.push v
  | .interfaceTable ports dom budget =>
      out := out.push dom
      out := out.push budget
      for r in ports do
        out := out.push r.port
        out := out.push r.queryLatex
        out := out.push r.replyLatex
  | .dslPseudocode hdr _ _ => out := out.push hdr
  | .ccDiagram _ summary => out := out.push summary
  return out

/-- Flatten all reader-facing text across an entire `Document` for strict zero-leakage auditing. -/
def collectDocumentTexts (doc : Document) : Array String := Id.run do
  let inlineTexts (xs : Array Inline) : Array String := xs.map Inline.collectText
  let mut out : Array String := #[doc.title]
  if let some sub := doc.subtitle? then
    out := out.push sub
  for entry in doc.entries do
    if let some t := entry.title? then
      out := out.push t
    if let some sc := entry.sectionContext? then
      for para in sc.paragraphs do
        out := out ++ inlineTexts para
      for ins in sc.inspectors do
        out := out ++ collectInspectorTexts ins
    if let some amb := entry.ambient? then
      out := out ++ inlineTexts amb.summary
    for para in entry.statement do
      out := out ++ inlineTexts para
    for ins in entry.localInspectors do
      out := out ++ collectInspectorTexts ins
    for node in entry.proof do
      out := out ++ node.collectAllText
  for ins in doc.inspectors do
    out := out ++ collectInspectorTexts ins
  return out

/-- Run a `MetaM` computation against a loaded `Environment`. -/
def runMetaOnEnv {α : Type} (env : Environment) (m : MetaM α) : IO α := do
  let coreCtx : Core.Context := {
    fileName := "<informalize>"
    fileMap := default
  }
  let coreState : Core.State := { env }
  let metaCtx : Meta.Context := {}
  let metaState : Meta.State := {}
  let ((res, _), _) ← (m.run metaCtx metaState).toIO coreCtx coreState
  return res

/-- Ensure parent directory of an output file exists before writing. -/
private def writeFileCreatingParents (path : System.FilePath) (content : String) : IO Unit := do
  if let some parent := path.parent then
    if !parent.toString.isEmpty then
      IO.FS.createDirAll parent
  IO.FS.writeFile path content

/-- Execute the informalization CLI with parsed options. -/
def runCli (opts : CliOptions) : IO UInt32 := do
  if opts.showHelp then
    IO.println usageText
    return 0
  if opts.modules.isEmpty then
    IO.eprintln "error: at least one --module <ModName> is required\n"
    IO.eprintln usageText
    return 1
  if opts.decls.isEmpty then
    IO.eprintln "error: at least one positional <DeclName> is required\n"
    IO.eprintln usageText
    return 1
  if opts.htmlPath?.isNone && opts.jsonPath?.isNone && !opts.strict then
    IO.eprintln "error: specify at least one of --html <path>, --json <path>, or --strict\n"
    IO.eprintln usageText
    return 1
  Lean.initSearchPath (← Lean.findSysroot)
  let imports : Array Import := opts.modules.map fun m => { module := m }
  let env ← Lean.importModules imports {} (trustLevel := 1024)
  let title := match opts.title? with
    | some t => t
    | none =>
        match opts.decls[0]? with
        | some d => humanLemmaLabel env d
        | none => "Constructive Cryptography Informalization"
  let config : Informalization.Core.ProofGraph.Config := { maxLemmaDepth := opts.maxLemmaDepth }
  let doc ← runMetaOnEnv env (buildDocument title opts.subtitle? opts.decls config)
  if let some jsonPath := opts.jsonPath? then
    writeFileCreatingParents jsonPath (renderDocumentJson doc)
    IO.println s!"Wrote JSON IR to {jsonPath}"
  if let some htmlPath := opts.htmlPath? then
    writeFileCreatingParents htmlPath (renderDocumentHtml doc)
    IO.println s!"Wrote ETH CADMO HTML to {htmlPath}"
  if opts.strict then
    let texts := collectDocumentTexts doc
    let leaks := auditZeroLeakage texts
    let mut sorryErrors : Array String := #[]
    for entry in doc.entries do
      if entry.axioms.hasSorry then
        sorryErrors := sorryErrors.push s!"Declaration '{entry.declaration}' depends on sorryAx"
    if !leaks.isEmpty || !sorryErrors.isEmpty then
      IO.eprintln "Strict informalization audit FAILED:"
      for e in sorryErrors do
        IO.eprintln s!"  [sorry] {e}"
      for v in leaks do
        IO.eprintln s!"  [leak]  {v}"
      return 2
    IO.println s!"Strict audit passed ({doc.entries.size} entries, {texts.size} text segments checked, 0 leaks, 0 sorry)."
  return 0

end Informalization.CLI

/-- Standalone executable entrypoint (`lake exe informalize` or `lean --run`). -/
def main (args : List String) : IO UInt32 := do
  match Informalization.CLI.parseCliArgs args with
  | .error msg =>
      IO.eprintln s!"error: {msg}\n"
      IO.eprintln Informalization.CLI.usageText
      return 1
  | .ok opts =>
      try
        Informalization.CLI.runCli opts
      catch e =>
        IO.eprintln s!"error: {e}"
        return 1
