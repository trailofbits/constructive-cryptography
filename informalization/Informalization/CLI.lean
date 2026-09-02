/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller.Describe
import Informalization.MassotMiller.RandomSystems
import Informalization.MassotMillerWeb
import Informalization.Semantics.CBC
import Informalization.Semantics.CanonicalRandomSystems
import Informalization.Semantics.Explanation
import Informalization.Semantics.RandomSystems
import Informalization.Semantics.Report

/-! Command-line entry point for the domain-neutral informalization backend. -/

open Lean Meta
open Informalization.MassotMiller
open Informalization.MassotMiller.InfoTree
open Informalization.MassotMiller.Describe

namespace Informalization.CLI

private inductive Profile where
  | generic
  | randomSystems
  | randomSystemsCBC
  | randomSystemsLegacy
  deriving Inhabited, BEq

private structure Cli where
  fileName : String
  declarations : Array Name := #[]
  raw : Bool := false
  tree : Bool := false
  jsonPath? : Option String := none
  semanticJsonPath? : Option String := none
  htmlPath? : Option String := none
  lakeRoot? : Option String := none
  profile : Profile := .generic
  config : Describe.Config := {}

private def usage : String :=
  "usage: informalize SOURCE.lean DECLARATION [DECLARATION ...] " ++
  "[--json=PATH] [--semantic-json=PATH] [--html=PATH] [--details=none|all|N] " ++
  "[--no-goals] [--no-tooltips] [--no-trailers] [--lake-root=PATH] " ++
  "[--profile=generic|random-systems|random-systems-cbc|random-systems-legacy] [--tree] [--raw]"

private def optionValue? (argument leading : String) : Option String :=
  (argument.dropPrefix? leading).map (·.toString)

private def parseExpansion (value : String) : Except String InitialExpansion :=
  if value == "none" || value == "collapsed" then return .collapsed
  else if value == "all" || value == "expanded" then return .expanded
  else
    match value.toNat? with
    | some depth => return .through depth
    | none => throw s!"invalid detail level: {value}"

private def parseCli : List String → Except String Cli
  | [] => throw usage
  | fileName :: rest => do
      let mut result : Cli := { fileName }
      for argument in rest do
        if argument == "--raw" then result := { result with raw := true, tree := true }
        else if argument == "--tree" then result := { result with tree := true }
        else if argument == "--no-goals" then
          result := { result with config := { result.config with goalMarkers := false } }
        else if argument == "--no-tooltips" then
          result := { result with config := { result.config with referenceTooltips := false } }
        else if argument == "--no-trailers" then
          result := { result with config := { result.config with formalTrailers := false } }
        else if let some path := optionValue? argument "--json=" then
          result := { result with jsonPath? := some path }
        else if let some path := optionValue? argument "--semantic-json=" then
          result := { result with semanticJsonPath? := some path }
        else if let some path := optionValue? argument "--html=" then
          result := { result with htmlPath? := some path }
        else if let some path := optionValue? argument "--lake-root=" then
          result := { result with lakeRoot? := some path }
        else if let some profile := optionValue? argument "--profile=" then
          if profile == "generic" then pure ()
          else if profile == "random-systems" then
            result := { result with
              profile := .randomSystems
              config := { result.config with
                language := Informalization.MassotMiller.RandomSystems.languageConfig } }
          else if profile == "random-systems-cbc" then
            result := { result with
              profile := .randomSystemsCBC
              config := { result.config with
                language := Informalization.MassotMiller.RandomSystems.languageConfig } }
          else if profile == "random-systems-legacy" then
            result := { result with
              profile := .randomSystemsLegacy
              config := { result.config with
                language := Informalization.MassotMiller.RandomSystems.languageConfig } }
          else throw s!"unknown language profile: {profile}"
        else if let some level := optionValue? argument "--details=" then
          result := { result with config :=
            { result.config with initialExpansion := ← parseExpansion level } }
        else if argument.startsWith "--" then throw s!"unknown option: {argument}"
        else result := { result with declarations := result.declarations.push argument.toName }
      if result.declarations.isEmpty then throw usage
      return result

private def moduleNameFromPath (path : System.FilePath) : Name :=
  let stem := path.fileStem.getD "Input"
  Name.mkSimple ("InformalizationInput_" ++ stem)

private def absolutePath (path : System.FilePath) : IO System.FilePath := do
  if path.isAbsolute then return path
  return (← IO.currentDir) / path

private def lakeSetupFor (path : System.FilePath) (lakeRoot? : Option String) :
    IO (Option ModuleSetup) := do
  let path ← absolutePath path
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["setup-file", path.toString]
    cwd := lakeRoot?.map System.FilePath.mk
  }
  IO.eprint output.stderr
  if output.exitCode != 0 then return none
  match Json.parse output.stdout >>= fromJson? with
  | .ok setup => return some setup
  | .error message =>
      IO.eprintln s!"could not parse Lake module setup: {message}"
      return none

private partial def treeLines (tree : TacticTree) (depth : Nat := 0) : Array String :=
  let pad := String.ofList (List.replicate (2 * depth) ' ')
  let target := tree.event.target.map goalIdString |>.getD "<none>"
  let produced := String.intercalate "," (tree.event.produced.toList.map goalIdString)
  let proof := if tree.event.proofTerm?.isSome then " term=yes" else " term=no"
  let current := s!"{pad}{syntaxString tree.event.source} [{target} -> {produced}]{proof}"
  tree.children.foldl (fun out child => out ++ treeLines child (depth + 1)) #[current]

private def goalQueue (goals : List MVarId) : String :=
  "[" ++ String.intercalate "," (goals.map goalIdString) ++ "]"

private def rawTacticLine (index : Nat) (tactic : CapturedTactic) : String :=
  let info := tactic.info
  s!"#{index} elaborator={info.elaborator} kind={info.stx.getKind} " ++
    s!"before={goalQueue info.goalsBefore} after={goalQueue info.goalsAfter} " ++
    s!"syntax={repr (syntaxString tactic)}"

private def printDebug (cli : Cli) (module : ElaboratedModule) : IO Unit := do
  for name in cli.declarations do
    IO.println s!"{name}:"
    if cli.raw then
      for index in Array.range (module.forDeclaration name).size do
        if let some tactic := (module.forDeclaration name)[index]? then
          IO.println (rawTacticLine index tactic)
    let forest := module.tacticForestFor name
    if forest.isEmpty then IO.println "  <no tactic tree>"
    else for tacticTree in forest do
      for line in treeLines tacticTree do IO.println line

private def ensureParent (path : System.FilePath) : IO Unit :=
  IO.FS.createDirAll (path.parent.getD ".")

private def writeOutputs (cli : Cli) (document : Document) : IO Unit := do
  let page : WebPage := {
    title := String.intercalate ", " (cli.declarations.toList.map (·.toString))
    declarations := document
  }
  if let some path := cli.jsonPath? then
    if path == "-" then IO.println (documentToJson document).pretty
    else
      let path := System.FilePath.mk path
      ensureParent path
      IO.FS.writeFile path ((documentToJson document).pretty ++ "\n")
  if let some path := cli.htmlPath? then
    page.writeHtmlBundle (System.FilePath.mk path)
  if cli.jsonPath?.isNone && cli.semanticJsonPath?.isNone && cli.htmlPath?.isNone && !cli.tree then
    IO.println (documentToJson document).pretty

private def semanticCatalog (profile : Profile) :
    Informalization.Semantics.Registry.Catalog :=
  match profile with
  | .generic => #[]
  | .randomSystems =>
      Informalization.Semantics.RandomSystems.catalog
  | .randomSystemsCBC =>
      Informalization.Semantics.CBC.catalog
  | .randomSystemsLegacy =>
      Informalization.Semantics.RandomSystems.catalog

private def semanticReports (module : ElaboratedModule) (names : Array Name)
    (catalog : Informalization.Semantics.Registry.Catalog)
    (canonicalProfile : Informalization.Semantics.Canonical.DecoderProfile := {}) :
    IO (Array Informalization.Semantics.Report.DeclarationReport) := do
  names.mapM fun name => do
    let some context := module.contextFor name
      | throw (IO.userError s!"missing elaboration context for semantic report: {name}")
    context.runMetaM {} do
      let information ← getConstInfo name
      forallTelescope information.type fun _ conclusion =>
        Informalization.Semantics.Report.ofConclusion module.environment catalog name conclusion
          canonicalProfile

private def canonicalDecoderProfile (profile : Profile) :
    Informalization.Semantics.Canonical.DecoderProfile :=
  match profile with
  | .generic => {}
  | .randomSystems =>
      Informalization.Semantics.Canonical.RandomSystemsProfile.profile
  | .randomSystemsCBC =>
      Informalization.Semantics.CBC.profile
  | .randomSystemsLegacy =>
      Informalization.Semantics.Canonical.RandomSystemsProfile.profile

private def validateSemanticCatalog (module : ElaboratedModule)
    (catalog : Informalization.Semantics.Registry.Catalog) : IO Unit := do
  let visibleCatalog := catalog.filter fun entry =>
    (module.environment.find? entry.declaration).isSome
  let validationIssues :=
    Informalization.Semantics.Registry.validateCatalog module.environment visibleCatalog
  unless validationIssues.isEmpty do
    throw (IO.userError s!"semantic catalog does not match the target environment: \
      {repr validationIssues}")

private def writeSemanticOutput (cli : Cli)
    (reports : Array Informalization.Semantics.Report.DeclarationReport) : IO Unit := do
  let some outputPath := cli.semanticJsonPath? | return ()
  let output := (Informalization.Semantics.Report.documentToJson reports).pretty ++ "\n"
  if outputPath == "-" then IO.print output
  else
    let path := System.FilePath.mk outputPath
    ensureParent path
    IO.FS.writeFile path output

private def semanticInitialExpansion : Describe.InitialExpansion →
    Informalization.Semantics.Explanation.InitialExpansion
  | .collapsed => .collapsed
  | .expanded => .expanded
  | .through depth => .through depth

private def semanticPresentationConfig (config : Describe.Config) :
    Informalization.Semantics.Explanation.Config := {
  initialExpansion := semanticInitialExpansion config.initialExpansion
  -- Provenance remains in the semantic report.  The paper surface contains
  -- mathematical expansions, not implementation-facing proof-step labels.
  evidenceTooltips := false
  checkedSourceCue := false
  formalTrailers := false
}

/-- Replace only those legacy proof bodies for which the checked semantic
pipeline produced a complete discourse document.  The theorem statement stays
on the existing LeanTeX/English path; unsupported declarations remain visible
through the ordinary Massot--Miller fallback. -/
private def semanticDocument (module : ElaboratedModule) (legacy : Document)
    (reports : Array Informalization.Semantics.Report.DeclarationReport)
    (canonicalProfile : Informalization.Semantics.Canonical.DecoderProfile)
    (config : Describe.Config) : IO Document :=
  legacy.mapM fun declaration =>
    match reports.find? fun report => report.declaration.toString == declaration.name with
    | some report => match report.discourse? with
        | some discourse => do
            let some context := module.contextFor report.declaration
              | throw (IO.userError s!"missing elaboration context for semantic goals: \
                  {report.declaration}")
            context.runMetaM {} do
              let information ← getConstInfo report.declaration
              let goalLanguage := {
                Informalization.MassotMiller.RandomSystems.goalLanguageConfig with
                checkedPropositionRenderer? := some
                  (Informalization.Semantics.Realize.checkedPropositionLatex?
                    canonicalProfile)
              }
              let goals ← Informalization.Semantics.GoalState.build
                information.type discourse goalLanguage
              let semanticStatement := discourse.sentences.find? (fun sentence =>
                sentence.kind == .stateSecurityGoal) |>.map (·.text)
                |>.getD declaration.statement.trimAscii.toString
              return Informalization.Semantics.Explanation.replaceProof
                { declaration with statement := semanticStatement }
                discourse
                (semanticPresentationConfig config)
                goals
        | none => pure declaration
    | none => pure declaration

unsafe def run (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let cli ← match parseCli args with
    | .ok value => pure value
    | .error message => IO.eprintln message; return 2
  let path : System.FilePath := cli.fileName
  let some setup ← lakeSetupFor path cli.lakeRoot? | return 1
  let instrumentationImports := match cli.profile with
  | .generic => #[`Informalization]
  -- The semantic profiles carry their registries in the generator process;
  -- injecting those modules into the source environment can change simp and
  -- elaboration behavior.  Re-elaborate these inputs under their own imports.
  | .randomSystems | .randomSystemsCBC => #[]
  | .randomSystemsLegacy =>
        #[`Informalization, `LeanTeX.RandomSystemsSyntax]
  let some module ← elaborateFile (← absolutePath path) (moduleNameFromPath path)
      (some setup) instrumentationImports
    | return 1
  if cli.tree then printDebug cli module
  -- Semantic pages retain this document as their complete concrete proof
  -- tree.  Keep the tree and its goal states, but omit implementation-branded
  -- tactic trailers from the reader-facing refinement.
  let canonicalProfile := canonicalDecoderProfile cli.profile
  let concreteConfig := match cli.profile with
    | .randomSystems | .randomSystemsCBC =>
        { cli.config with
          formalTrailers := false
          language := {
            cli.config.language with
            checkedPropositionRenderer? := some
              (Informalization.Semantics.Realize.checkedPropositionLatex?
                canonicalProfile)
          }
        }
    | .generic | .randomSystemsLegacy => cli.config
  let legacyOutput ← Describe.document module cli.declarations concreteConfig
  let found := legacyOutput.map (·.name)
  let missing := cli.declarations.filter fun name => !found.contains name.toString
  unless missing.isEmpty do
    IO.eprintln ("declarations not found in elaborated source: " ++
      String.intercalate ", " (missing.toList.map (·.toString)))
    return 1
  let catalog := semanticCatalog cli.profile
  validateSemanticCatalog module catalog
  let reports ← if cli.profile == .generic && cli.semanticJsonPath?.isNone then
      pure #[]
    else
      semanticReports module cli.declarations catalog canonicalProfile
  let output ← match cli.profile with
  | .randomSystems | .randomSystemsCBC =>
        semanticDocument module legacyOutput reports canonicalProfile cli.config
    | .generic | .randomSystemsLegacy => pure legacyOutput
  writeSemanticOutput cli reports
  writeOutputs cli output
  return 0

end Informalization.CLI

unsafe def main (args : List String) : IO UInt32 :=
  Informalization.CLI.run args
