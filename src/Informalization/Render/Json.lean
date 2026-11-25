/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Explanation
import Informalization.Core.Ontology
import Informalization.Core.Overlay
import Informalization.Core.ProofGraph

/-!
# Canonical JSON Export (Shared by Standalone CADMO HTML & Verso)

Serializes any checked `Explanation.Document` to stable, versioned JSON so the isolated
Verso consumer package and CI quality gates can consume the exact same proof tree without
duplicating Lean evaluation.

Also performs **Section-Fixed Context hoisting**: when a numbered paper section (`§N`)
contains two or more theorems sharing parameters and assumptions (such as `p : SpongeParameters`,
`limits : Limits`, `hp : supportedSponge p`, `hl : admittedLimits limits`), those shared
declarations and standing assumptions are hoisted once into a `SectionContext` under the
numbered section header and omitted from individual theorem statements inside that section.
-/

namespace Informalization.Render.Json

open Lean Meta
open Informalization.Core.Explanation
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Overlay
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

/-- Segment `decls` into `(sectionNumber?, groupDecls)` preserving declaration order.
Entries before the first `informal_section` stay unsectioned (`none`). -/
private def groupDeclsBySection (env : Environment) (decls : Array Name) :
    Array (Option Nat × Array Name) := Id.run do
  let mut groups : Array (Option Nat × Array Name) := #[]
  let mut curSec? : Option Nat := none
  let mut curDecls : Array Name := #[]
  let mut secCounter : Nat := 0
  for d in decls do
    let ov := getOverlay env d
    if ov.sectionTitle?.isSome then
      if !curDecls.isEmpty then
        groups := groups.push (curSec?, curDecls)
      secCounter := secCounter + 1
      curSec? := some secCounter
      curDecls := #[d]
    else
      curDecls := curDecls.push d
  if !curDecls.isEmpty then
    groups := groups.push (curSec?, curDecls)
  return groups

/-- Analyze a multi-entry numbered section and compute any section-fixed parameters and
standing assumptions that can be soundly hoisted into a `SectionContext`. -/
private def analyzeSectionHoisting (secNum : Nat) (grpDecls : Array Name) :
    MetaM (Option (SectionContext × HoistedContext)) := do
  if grpDecls.size < 2 then return none
  let env ← getEnv
  let mut summaries : Array SignatureSummary := #[]
  for d in grpDecls do
    let some info := env.find? d | return none
    let tbl := buildSymbolTable env d
    summaries := summaries.push (← extractSignatureSummary tbl info.type)
  let total := summaries.size
  -- 1. Aggregate parameters across entries (detecting any symbol/type inconsistencies)
  let mut orderedSyms : Array String := #[]
  let mut symCount : Std.HashMap String Nat := {}
  let mut symTypes : Std.HashMap String (Std.HashSet String) := {}
  let mut firstParam : Std.HashMap String SigParam := {}
  let mut entryParamSets : Array (Std.HashSet String) := #[]
  for sum in summaries do
    let mut seenInEntry : Std.HashSet String := {}
    for p in sum.params do
      if !seenInEntry.contains p.sym then
        seenInEntry := seenInEntry.insert p.sym
        if !firstParam.contains p.sym then
          orderedSyms := orderedSyms.push p.sym
          firstParam := firstParam.insert p.sym p
        symCount := symCount.insert p.sym ((symCount.getD p.sym 0) + 1)
        let ts := (symTypes.getD p.sym {}).insert p.typeKey
        symTypes := symTypes.insert p.sym ts
    entryParamSets := entryParamSets.push seenInEntry
  -- 2. Select consistent, shared parameters (must appear in every entry of the section)
  let mut candidateSyms : Array String := #[]
  for sym in orderedSyms do
    let consistent := (symTypes.getD sym {}).size == 1
    let cnt := symCount.getD sym 0
    if consistent then
      if cnt == total then
        candidateSyms := candidateSyms.push sym
  -- 3. Topological dependency closure: only keep parameters whose dependencies are also hoisted
  let mut hoistedSet : Std.HashSet String := {}
  for s in candidateSyms do
    hoistedSet := hoistedSet.insert s
  for _ in [:candidateSyms.size] do
    let mut changed := false
    let mut nextSet : Std.HashSet String := {}
    for s in candidateSyms do
      if hoistedSet.contains s then
        let p := firstParam.get! s
        if p.depSyms.all hoistedSet.contains then
          nextSet := nextSet.insert s
        else
          changed := true
    hoistedSet := nextSet
    if !changed then break
  let hoistedParams : Array SigParam :=
    candidateSyms.filterMap fun s =>
      if hoistedSet.contains s then some (firstParam.get! s) else none
  if hoistedParams.isEmpty then
    return none
  -- 4. Select section-fixed assumptions (Soundness guard: EVERY entry in the section that
  --    introduces all free variables of the assumption MUST assume it!)
  let mut orderedHypKeys : Array String := #[]
  let mut hypCount : Std.HashMap String Nat := {}
  let mut firstHyp : Std.HashMap String SigHyp := {}
  for sum in summaries do
    let mut seenHyp : Std.HashSet String := {}
    for h in sum.hyps do
      if !seenHyp.contains h.key then
        seenHyp := seenHyp.insert h.key
        if h.depSyms.all hoistedSet.contains then
          if !firstHyp.contains h.key then
            orderedHypKeys := orderedHypKeys.push h.key
            firstHyp := firstHyp.insert h.key h
          hypCount := hypCount.insert h.key ((hypCount.getD h.key 0) + 1)
  let mut hoistedHyps : Array SigHyp := #[]
  let mut hoistedHypSet : Std.HashSet String := {}
  for hk in orderedHypKeys do
    let h := firstHyp.get! hk
    let cnt := hypCount.getD hk 0
    if cnt ≥ 2 && cnt == total then
      let entriesWithDeps := entryParamSets.foldl (init := 0) fun acc pset =>
        if h.depSyms.all pset.contains then acc + 1 else acc
      if entriesWithDeps == cnt then
        hoistedHyps := hoistedHyps.push h
        hoistedHypSet := hoistedHypSet.insert hk
  -- 5. Build SectionContext and enriched section-fixed SymbolInspectors
  let secId := s!"sec-{secNum}"
  let paragraphs := formatSectionContextParagraphs
    (hoistedParams.map (·.intro)).toList (hoistedHyps.map (·.inlines))
  let sectionInspectors : Array SymbolInspector :=
    hoistedParams.map fun p =>
      let assumptions := hoistedHyps.filterMap fun h =>
        if h.depSyms.contains p.sym then some h.inlines else none
      {
        key := s!"sec:{secNum}:{p.cleanName}"
        display := p.sym
        kind := .parameter p.roleDescription
        leanName? := none
        leanType := p.leanType
        roleBadge? := some s!"fixed in §{secNum}"
        sectionId? := some secId
        sectionAssumptions := assumptions
      }
  let secCtx : SectionContext := {
    sectionId := secId
    sectionNumber := secNum
    paragraphs
    inspectors := sectionInspectors
  }
  let hoistedCtx : HoistedContext := {
    paramSyms := hoistedSet
    hypKeys := hoistedHypSet
    sectionId? := some secId
    sectionNumber? := some secNum
  }
  return some (secCtx, hoistedCtx)

/-- Split multi-paragraph prelude body prose into parsed `Array Inline` paragraphs. -/
private def parsePreludeParagraphs (txt : String) : Array (Array Inline) := Id.run do
  let norm := (txt.replace "\r\n" "\n").replace "\r" "\n"
  let mut out : Array (Array Inline) := #[]
  for para in norm.splitOn "\n\n" do
    let collapsed := (para.replace "\n" " ").trimAscii.toString
    if !collapsed.isEmpty then
      out := out.push (parseProseWithMath collapsed)
  return out

/-- Split DSL pseudocode source text into indented `PseudocodeLine`s. -/
private def splitDslPreludeLines (src : String) : Array PseudocodeLine := Id.run do
  let rawLines := ((src.replace "\r\n" "\n").replace "\r" "\n").splitOn "\n"
  let mut out : Array PseudocodeLine := #[]
  for rawLine in rawLines do
    let leadWs := rawLine.toList.takeWhile fun c => c == ' ' || c == '\t'
    let sp := leadWs.foldl (init := 0) fun acc c => acc + (if c == '\t' then 2 else 1)
    let trimmed := rawLine.trimAscii.toString
    if !trimmed.isEmpty then
      let collapsed := String.intercalate " " (trimmed.splitOn " " |>.filter (!·.isEmpty))
      out := out.push { indent := sp / 2, inlines := parseProseWithMath collapsed }
  return out

/-- Materialize `DeclOverlay.sectionPreludes` into checked `PreludeBlock`s, inspecting any
declaration-backed `declName?` targets and ensuring their inspectors are present in `doc.inspectors`. -/
private def materializeSectionPreludes (tbl : SymbolTable) (declName : Name)
    (specs : Array PreludeSpec) (existingIns : Array SymbolInspector) :
    MetaM (Array PreludeBlock × Array SymbolInspector × Array String) := do
  let env ← getEnv
  let mut blocks : Array PreludeBlock := #[]
  let mut extraIns : Array SymbolInspector := #[]
  let mut extraRefKeys : Array String := #[]
  for idx in [:specs.size] do
    let spec := specs[idx]!
    let blockId := s!"prelude-{declName.toString}-{idx}"
    let mut body := parsePreludeParagraphs spec.bodyText
    let mut lines : Array PseudocodeLine := spec.lines.map fun (ind, ln) =>
      { indent := ind, inlines := parseProseWithMath ln }
    let mut rows : Array PreludeRow := spec.rows.map fun (l, r) =>
      { left := parseProseWithMath l, right := parseProseWithMath r }
    let mut declKey? : Option String := none
    let mut diagramHtml? : Option String := none
    if let some targetDecl := spec.declName? then
      let existing? := (existingIns ++ extraIns).find? (·.key == targetDecl.toString)
      let ins? ← match existing? with
        | some ins => pure (some ins)
        | none =>
            let (_, typeIns, proofIns) ←
              (← scopedInspectorCollectorRef.get) tbl targetDecl (mkConst ``True) none {} #[targetDecl]
            let found? := (typeIns ++ proofIns).find? (·.key == targetDecl.toString)
            if let some ins := found? then
              extraIns := extraIns.push ins
            pure found?
      if let some ins := ins? then
        declKey? := some ins.key
        if !extraRefKeys.contains ins.key then
          extraRefKeys := extraRefKeys.push ins.key
        match ins.kind with
        | .dslPseudocode _ dslBody fullSource =>
            if lines.isEmpty && body.isEmpty then
              let src := if dslBody.trimAscii.isEmpty then fullSource else dslBody
              lines := splitDslPreludeLines src
            if let some info := env.find? targetDecl then
              let diagExpr := match info with
                | .defnInfo dinfo => if !info.type.isForall then dinfo.value else info.type
                | _ => info.type
              diagramHtml? ← try (← diagramHookRef.get) tbl diagExpr catch _ => pure none
        | .interfaceTable ports domainLatex budgetNote =>
            if rows.isEmpty then
              rows := ports.map fun p =>
                { left := #[.text p.port], right := #[.inlineMath s!"{p.queryLatex} \\to {p.replyLatex}"] }
            if body.isEmpty then
              if !domainLatex.isEmpty then
                body := body.push #[.text "Domain: ", .inlineMath domainLatex, .text "."]
              if !budgetNote.trimAscii.isEmpty then
                let bn := budgetNote.trimAscii.toString
                body := body.push (parseProseWithMath (if bn.endsWith "." then bn else bn ++ "."))
        | .ccDiagram svgOrHtml summaryLatex =>
            diagramHtml? := some svgOrHtml
            if body.isEmpty && !summaryLatex.trimAscii.isEmpty then
              body := #[#[.displayMath summaryLatex "."]]
        | .mathDefinition eqLatex proseSummary =>
            if body.isEmpty then
              if !proseSummary.trimAscii.isEmpty then
                body := body.push (parseProseWithMath proseSummary)
              if !eqLatex.trimAscii.isEmpty then
                body := body.push #[.displayMath eqLatex "."]
              for cl in ins.clauses do
                if !cl.trimAscii.isEmpty then
                  lines := lines.push { indent := 0, inlines := #[.inlineMath cl] }
            if let some info := env.find? targetDecl then
              diagramHtml? ← try (← diagramHookRef.get) tbl info.type catch _ => pure none
        | .witnessCard cardTitle wRows =>
            if body.isEmpty && !cardTitle.trimAscii.isEmpty then
              body := #[#[.text (if cardTitle.endsWith "." then cardTitle else cardTitle ++ ".")]]
            if rows.isEmpty then
              rows := wRows.map fun (k, v) =>
                { left := #[.text k], right := parseProseWithMath v }
        | .parameter roleDesc =>
            if body.isEmpty && !roleDesc.trimAscii.isEmpty then
              body := #[parseProseWithMath roleDesc]
        | .localShorthand eqLatex roleDesc =>
            if body.isEmpty then
              if !roleDesc.trimAscii.isEmpty then
                body := body.push (parseProseWithMath roleDesc)
              if !eqLatex.trimAscii.isEmpty then
                body := body.push #[.displayMath eqLatex "."]
      else
        if let some info := env.find? targetDecl then
          diagramHtml? ← try (← diagramHookRef.get) tbl info.type catch _ => pure none
          if body.isEmpty then
            let tyTex ← try exprToLatex info.type tbl catch _ => pure ""
            if !tyTex.isEmpty then
              body := #[#[.displayMath tyTex "."]]
    blocks := blocks.push {
      id := blockId
      kind := spec.kind
      label := spec.label
      title := spec.title
      body
      lines
      rows
      declKey?
      diagramHtml?
    }
  return (blocks, extraIns, extraRefKeys)

/-- Build a canonical `Document` from an ordered list of declaration names, automatically
hoisting section-fixed parameters & standing assumptions inside numbered sections. -/
def buildDocument (title : String) (subtitle? : Option String := none)
    (decls : Array Name) (config : Informalization.Core.ProofGraph.Config := {})
    (extraDocDecls : Array Name := #[]) : MetaM Document := do
  let env ← getEnv
  let groups := groupDeclsBySection env decls
  let docDecls : NameSet :=
    (decls ++ extraDocDecls).foldl (init := {}) fun s d => s.insert d
  let mut entries : Array Entry := #[]
  let mut inspectors : Array SymbolInspector := #[]
  for (secNum?, grpDecls) in groups do
    let hoistedResult? ← match secNum? with
      | some secNum => analyzeSectionHoisting secNum grpDecls
      | none => pure none
    let secId? := secNum?.map fun secNum => s!"sec-{secNum}"
    let secCtx? := hoistedResult?.map (·.1)
    let hoistedCtx? := hoistedResult?.map (·.2)
    for idx in [:grpDecls.size] do
      let d := grpDecls[idx]!
      let (entry, ins) ← informalizeDeclarationWithContext d config hoistedCtx? docDecls
      let ov := getOverlay env d
      let (sectionPreludes, preludeIns, preludeRefKeys) ←
        if ov.sectionPreludes.isEmpty then pure (#[], #[], #[])
        else materializeSectionPreludes (buildSymbolTable env d) d ov.sectionPreludes (inspectors ++ ins)
      let mut refKeys := entry.referencedKeys
      for rk in preludeRefKeys do
        if !refKeys.contains rk then
          refKeys := refKeys.push rk
      let entry := {
        entry with
        sectionId? := entry.sectionId? <|> secId?
        sectionContext? := if idx == 0 then secCtx? else entry.sectionContext?
        sectionPreludes := entry.sectionPreludes ++ sectionPreludes
        referencedKeys := refKeys
      }
      entries := entries.push entry
      inspectors := inspectors ++ ins ++ preludeIns
  return {
    title
    subtitle?
    defaultMode := .paper
    entries
    inspectors := dedupInspectors inspectors
  }

/-- Serialize a `Document` as compact JSON. -/
def renderDocumentJson (doc : Document) : String :=
  (toJson doc).compress

/-- Write a checked declaration's `Document` JSON to disk. -/
elab "#informalize_json " decl:ident " to " path:str : command => do
  let jsonStr ← Elab.Command.runTermElabM fun _ => do
    let declName ← Elab.realizeGlobalConstNoOverloadWithInfo decl
    let doc ← buildDocument (humanDeclarationTitle (← getEnv) declName) none #[declName]
    return renderDocumentJson doc
  IO.FS.writeFile path.getString jsonStr

end Informalization.Render.Json
