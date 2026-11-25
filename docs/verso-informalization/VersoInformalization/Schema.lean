/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# Canonical `Explanation.Document` JSON Schema Loader

Standalone decoder for the canonical JSON IR emitted by `Informalization.Render.Json`
(`Informalization.Core.Explanation.Document`).

Because this module depends only on Lean's built-in `Lean.Data.Json`, it compiles cleanly
under any Lean 4 toolchain required by Verso without importing `ConstructiveCryptography`
or `Informalization`.
-/

namespace VersoInformalization.Schema

open Lean

/-- Reader disclosure preset matching `Explanation.ViewMode`. -/
inductive ViewMode
  | paper
  | auditor
  deriving DecidableEq, Repr, BEq, Inhabited

instance : ToJson ViewMode where
  toJson
    | .paper => Json.str "paper"
    | .auditor => Json.str "auditor"

instance : FromJson ViewMode where
  fromJson?
    | Json.str "paper" => .ok .paper
    | Json.str "auditor" => .ok .auditor
    | other => .error s!"Expected ViewMode ('paper' | 'auditor'), got: {other.compress}"

/-- Inline content inside a mathematical sentence. -/
inductive Inline
  | text (value : String)
  | emph (value : String)
  | inlineMath (latex : String)
  | displayMath (latex : String) (punct : String := ".")
  | symbol (key : String) (display : String) (isMath : Bool := true)
  | citation (label : String) (detail : String := "")
  deriving Repr, BEq, Inhabited

instance : ToJson Inline where
  toJson
    | .text value => Json.mkObj [("text", Json.mkObj [("value", toJson value)])]
    | .emph value => Json.mkObj [("emph", Json.mkObj [("value", toJson value)])]
    | .inlineMath latex => Json.mkObj [("inlineMath", Json.mkObj [("latex", toJson latex)])]
    | .displayMath latex punct =>
        Json.mkObj [("displayMath", Json.mkObj [("latex", toJson latex), ("punct", toJson punct)])]
    | .symbol key display isMath =>
        Json.mkObj [("symbol", Json.mkObj [
          ("key", toJson key), ("display", toJson display), ("isMath", toJson isMath)])]
    | .citation label detail =>
        Json.mkObj [("citation", Json.mkObj [("label", toJson label), ("detail", toJson detail)])]

private def getOptField? [FromJson α] (j : Json) (key : String) : Except String (Option α) :=
  match j.getObjVal? key with
  | .error _ => .ok none
  | .ok Json.null => .ok none
  | .ok v => some <$> fromJson? v

private def getFieldD [FromJson α] (j : Json) (key : String) (default : α) : Except String α := do
  match ← getOptField? j key with
  | some v => return v
  | none => return default

instance : FromJson Inline where
  fromJson? j := do
    if let .ok v := j.getObjVal? "text" then
      match v with
      | Json.str s => return .text s
      | _ => return .text (← v.getObjValAs? String "value")
    else if let .ok v := j.getObjVal? "emph" then
      match v with
      | Json.str s => return .emph s
      | _ => return .emph (← v.getObjValAs? String "value")
    else if let .ok v := j.getObjVal? "inlineMath" then
      match v with
      | Json.str s => return .inlineMath s
      | _ => return .inlineMath (← v.getObjValAs? String "latex")
    else if let .ok v := j.getObjVal? "displayMath" then
      match v with
      | Json.str s => return .displayMath s "."
      | _ =>
          let latex ← v.getObjValAs? String "latex"
          let punct ← getFieldD v "punct" "."
          return .displayMath latex punct
    else if let .ok v := j.getObjVal? "symbol" then
      let key ← v.getObjValAs? String "key"
      let display ← v.getObjValAs? String "display"
      let isMath ← getFieldD v "isMath" true
      return .symbol key display isMath
    else if let .ok v := j.getObjVal? "citation" then
      let label ← v.getObjValAs? String "label"
      let detail ← getFieldD v "detail" ""
      return .citation label detail
    else
      .error s!"Unrecognized Inline JSON: {j.compress}"

/-- One row in a `Rendering`-style interface port table (`Port / Query / Reply`). -/
structure PortRow where
  port : String
  queryLatex : String
  replyLatex : String
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Type-aware inspector payload opened when a reader clicks a named symbol. -/
inductive InspectorKind
  | interfaceTable (ports : Array PortRow) (domainLatex : String) (budgetNote : String := "")
  | dslPseudocode (header : String) (body : String) (fullSource : String)
  | ccDiagram (svgOrHtml : String) (summaryLatex : String)
  | mathDefinition (equationLatex : String) (proseSummary : String := "")
  | witnessCard (title : String) (rows : Array (String × String))
  | parameter (roleDescription : String)
  | localShorthand (equationLatex : String) (roleDescription : String := "")
  deriving Repr, BEq, Inhabited

instance : ToJson InspectorKind where
  toJson
    | .interfaceTable ports domainLatex budgetNote =>
        Json.mkObj [("interfaceTable", Json.mkObj [
          ("ports", toJson ports),
          ("domainLatex", toJson domainLatex),
          ("budgetNote", toJson budgetNote)
        ])]
    | .dslPseudocode header body fullSource =>
        Json.mkObj [("dslPseudocode", Json.mkObj [
          ("header", toJson header),
          ("body", toJson body),
          ("fullSource", toJson fullSource)
        ])]
    | .ccDiagram svgOrHtml summaryLatex =>
        Json.mkObj [("ccDiagram", Json.mkObj [
          ("svgOrHtml", toJson svgOrHtml),
          ("summaryLatex", toJson summaryLatex)
        ])]
    | .mathDefinition equationLatex proseSummary =>
        Json.mkObj [("mathDefinition", Json.mkObj [
          ("equationLatex", toJson equationLatex),
          ("proseSummary", toJson proseSummary)
        ])]
    | .witnessCard title rows =>
        Json.mkObj [("witnessCard", Json.mkObj [
          ("title", toJson title),
          ("rows", toJson rows)
        ])]
    | .parameter roleDescription =>
        Json.mkObj [("parameter", Json.mkObj [
          ("roleDescription", toJson roleDescription)
        ])]
    | .localShorthand equationLatex roleDescription =>
        Json.mkObj [("localShorthand", Json.mkObj [
          ("equationLatex", toJson equationLatex),
          ("roleDescription", toJson roleDescription)
        ])]

instance : FromJson InspectorKind where
  fromJson? j := do
    if let .ok v := j.getObjVal? "interfaceTable" then
      let ports ← getFieldD v "ports" (#[] : Array PortRow)
      let domainLatex ← getFieldD v "domainLatex" ""
      let budgetNote ← getFieldD v "budgetNote" ""
      return .interfaceTable ports domainLatex budgetNote
    else if let .ok v := j.getObjVal? "dslPseudocode" then
      let header ← getFieldD v "header" ""
      let body ← getFieldD v "body" ""
      let fullSource ← getFieldD v "fullSource" ""
      return .dslPseudocode header body fullSource
    else if let .ok v := j.getObjVal? "ccDiagram" then
      let svgOrHtml ← getFieldD v "svgOrHtml" ""
      let summaryLatex ← getFieldD v "summaryLatex" ""
      return .ccDiagram svgOrHtml summaryLatex
    else if let .ok v := j.getObjVal? "mathDefinition" then
      let equationLatex ← getFieldD v "equationLatex" ""
      let proseSummary ← getFieldD v "proseSummary" ""
      return .mathDefinition equationLatex proseSummary
    else if let .ok v := j.getObjVal? "witnessCard" then
      let title ← getFieldD v "title" ""
      let rows ← getFieldD v "rows" (#[] : Array (String × String))
      return .witnessCard title rows
    else if let .ok v := j.getObjVal? "parameter" then
      match v with
      | Json.str s => return .parameter s
      | _ =>
          let roleDescription ← getFieldD v "roleDescription" ""
          return .parameter roleDescription
    else if let .ok v := j.getObjVal? "localShorthand" then
      let equationLatex ← getFieldD v "equationLatex" ""
      let roleDescription ← getFieldD v "roleDescription" ""
      return .localShorthand equationLatex roleDescription
    else
      .error s!"Unrecognized InspectorKind JSON: {j.compress}"

/-- Complete checked inspector record for one symbol, shorthand, section parameter, or declaration. -/
structure SymbolInspector where
  key : String
  display : String
  kind : InspectorKind
  leanName? : Option String := none
  leanType : String
  sourceFile? : Option String := none
  sourceLine? : Option Nat := none
  roleBadge? : Option String := none
  sectionId? : Option String := none
  sectionAssumptions : Array (Array Inline) := #[]
  clauses : Array String := #[]
  docString? : Option String := none
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson SymbolInspector where
  fromJson? j := do
    let key ← j.getObjValAs? String "key"
    let display ← j.getObjValAs? String "display"
    let kind ← j.getObjValAs? InspectorKind "kind"
    let leanName? ← getOptField? j "leanName"
    let leanType ← getFieldD j "leanType" ""
    let sourceFile? ← getOptField? j "sourceFile"
    let sourceLine? ← getOptField? j "sourceLine"
    let roleBadge? ← getOptField? j "roleBadge"
    let sectionId? ← getOptField? j "sectionId"
    let sectionAssumptions ← getFieldD j "sectionAssumptions" (#[] : Array (Array Inline))
    let clauses ← getFieldD j "clauses" (#[] : Array String)
    let docString? ← getOptField? j "docString"
    return {
      key, display, kind, leanName?, leanType, sourceFile?, sourceLine?,
      roleBadge?, sectionId?, sectionAssumptions, clauses, docString?
    }

/-- One hygienized local context entry inside a Kyle Miller goal-state inspector. -/
structure ContextEntry where
  name? : Option String := none
  description : String
  isHypothesis : Bool := false
  usedInGoal : Bool := true
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson ContextEntry where
  fromJson? j := do
    let name? ← getOptField? j "name"
    let description ← j.getObjValAs? String "description"
    let isHypothesis ← getFieldD j "isHypothesis" false
    let usedInGoal ← getFieldD j "usedInGoal" true
    return { name?, description, isHypothesis, usedInGoal }

/-- Checked proof-state checkpoint (context + target). -/
structure GoalState where
  context : Array ContextEntry
  targetLatex : String
  targetProse? : Option String := none
  rawLeanGoal? : Option String := none
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson GoalState where
  fromJson? j := do
    let context ← getFieldD j "context" (#[] : Array ContextEntry)
    let targetLatex ← j.getObjValAs? String "targetLatex"
    let targetProse? ← getOptField? j "targetProse"
    let rawLeanGoal? ← getOptField? j "rawLeanGoal"
    return { context, targetLatex, targetProse?, rawLeanGoal? }

/-- One line of a structured `cc_calc` / `calc` chain. -/
structure CalcStep where
  lhsLatex : String
  relationLatex : String
  rhsLatex : String
  reason : Array Inline
  diagramHtml? : Option String := none
  justification : Array (String × String) := #[]
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson CalcStep where
  fromJson? j := do
    let lhsLatex ← getFieldD j "lhsLatex" ""
    let relationLatex ← getFieldD j "relationLatex" "="
    let rhsLatex ← getFieldD j "rhsLatex" ""
    let reason ← getFieldD j "reason" (#[] : Array Inline)
    let diagramHtml? ← getOptField? j "diagramHtml"
    let justification ← getFieldD j "justification" (#[] : Array (String × String))
    return { lhsLatex, relationLatex, rhsLatex, reason, diagramHtml?, justification }

/-- A node in the single unified recursive proof tree. -/
inductive ProofNode
  | step
      (id : String)
      (content : Array Inline)
      (children : Array ProofNode)
      (goal? : Option GoalState := none)
      (diagramHtml? : Option String := none)
      (originDecl? : Option String := none)
      (isWrapper : Bool := false)
      (defaultExpanded : Bool := false)
  | calcChain
      (id : String)
      (intro : Array Inline)
      (steps : Array (CalcStep × Array ProofNode))
      (goal? : Option GoalState := none)
      (originDecl? : Option String := none)
  | routineReceipt
      (id : String)
      (summary : String)
      (stepCount : Nat)
      (details : Array ProofNode)
      (goal? : Option GoalState := none)
  | flowNote
      (id : String)
      (text : String)
      (placement : String := "margin")
  | figure
      (id : String)
      (caption : Array Inline)
      (html : String)
  deriving Repr, BEq, Inhabited

mutual
  partial def proofNodeToJson : ProofNode → Json
    | .step id content children goal? diagramHtml? originDecl? isWrapper defaultExpanded =>
        Json.mkObj [
          ("kind", "step"),
          ("id", toJson id),
          ("content", toJson content),
          ("children", Json.arr (children.map proofNodeToJson)),
          ("goal", toJson goal?),
          ("diagramHtml", toJson diagramHtml?),
          ("originDecl", toJson originDecl?),
          ("isWrapper", toJson isWrapper),
          ("defaultExpanded", toJson defaultExpanded)
        ]
    | .calcChain id intro steps goal? originDecl? =>
        let stepsJson := steps.map fun (s, sub) =>
          Json.mkObj [
            ("step", toJson s),
            ("children", Json.arr (sub.map proofNodeToJson))
          ]
        Json.mkObj [
          ("kind", "calcChain"),
          ("id", toJson id),
          ("intro", toJson intro),
          ("steps", Json.arr stepsJson),
          ("goal", toJson goal?),
          ("originDecl", toJson originDecl?)
        ]
    | .routineReceipt id summary stepCount details goal? =>
        Json.mkObj [
          ("kind", "routineReceipt"),
          ("id", toJson id),
          ("summary", toJson summary),
          ("stepCount", toJson stepCount),
          ("details", Json.arr (details.map proofNodeToJson)),
          ("goal", toJson goal?)
        ]
    | .flowNote id text placement =>
        Json.mkObj [
          ("kind", "flowNote"),
          ("id", toJson id),
          ("text", toJson text),
          ("placement", toJson placement)
        ]
    | .figure id caption html =>
        Json.mkObj [
          ("kind", "figure"),
          ("id", toJson id),
          ("caption", toJson caption),
          ("html", toJson html)
        ]

  partial def proofNodeFromJson? (j : Json) : Except String ProofNode := do
    let kind ← j.getObjValAs? String "kind"
    let id ← j.getObjValAs? String "id"
    match kind with
    | "step" =>
        let content ← getFieldD j "content" (#[] : Array Inline)
        let childrenJson ← getFieldD j "children" (#[] : Array Json)
        let children ← childrenJson.mapM proofNodeFromJson?
        let goal? ← getOptField? j "goal"
        let diagramHtml? ← getOptField? j "diagramHtml"
        let originDecl? ← getOptField? j "originDecl"
        let isWrapper ← getFieldD j "isWrapper" false
        let defaultExpanded ← getFieldD j "defaultExpanded" false
        return .step id content children goal? diagramHtml? originDecl? isWrapper defaultExpanded
    | "calcChain" =>
        let intro ← getFieldD j "intro" (#[] : Array Inline)
        let rawSteps ← getFieldD j "steps" (#[] : Array Json)
        let steps ← rawSteps.mapM fun item => do
          let step ← item.getObjValAs? CalcStep "step"
          let subJson ← getFieldD item "children" (#[] : Array Json)
          let sub ← subJson.mapM proofNodeFromJson?
          return (step, sub)
        let goal? ← getOptField? j "goal"
        let originDecl? ← getOptField? j "originDecl"
        return .calcChain id intro steps goal? originDecl?
    | "routineReceipt" =>
        let summary ← getFieldD j "summary" ""
        let stepCount ← getFieldD j "stepCount" 1
        let detailsJson ← getFieldD j "details" (#[] : Array Json)
        let details ← detailsJson.mapM proofNodeFromJson?
        let goal? ← getOptField? j "goal"
        return .routineReceipt id summary stepCount details goal?
    | "flowNote" =>
        let text ← getFieldD j "text" ""
        let placement ← getFieldD j "placement" "margin"
        return .flowNote id text placement
    | "figure" =>
        let caption ← getFieldD j "caption" (#[] : Array Inline)
        let html ← getFieldD j "html" ""
        return .figure id caption html
    | other =>
        .error s!"Unknown ProofNode kind '{other}' on node '{id}'"
end

instance : ToJson ProofNode := ⟨proofNodeToJson⟩
instance : FromJson ProofNode := ⟨proofNodeFromJson?⟩

/-- Axiom-audit record attached to a checked declaration. -/
structure AxiomAudit where
  axioms : Array String
  hasSorry : Bool := false
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson AxiomAudit where
  fromJson? j := do
    let axioms ← getFieldD j "axioms" (#[] : Array String)
    let hasSorry ← getFieldD j "hasSorry" false
    return { axioms, hasSorry }

/-- Ambient context factored out once per theorem/section. -/
structure AmbientSetting where
  summary : Array Inline
  suppressedTypeclasses : Array String := #[]
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson AmbientSetting where
  fromJson? j := do
    let summary ← getFieldD j "summary" (#[] : Array Inline)
    let suppressedTypeclasses ← getFieldD j "suppressedTypeclasses" (#[] : Array String)
    return { summary, suppressedTypeclasses }

/-- Section-fixed parameters and standing assumptions hoisted once per numbered paper section. -/
structure SectionContext where
  sectionId : String
  sectionNumber : Nat
  paragraphs : Array (Array Inline)
  inspectors : Array SymbolInspector := #[]
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson SectionContext where
  fromJson? j := do
    let sectionId ← j.getObjValAs? String "sectionId"
    let sectionNumber ← j.getObjValAs? Nat "sectionNumber"
    let paragraphs ← getFieldD j "paragraphs" (#[] : Array (Array Inline))
    let inspectors ← getFieldD j "inspectors" (#[] : Array SymbolInspector)
    return { sectionId, sectionNumber, paragraphs, inspectors }

/-- One informalized declaration (Theorem, Lemma, Proposition, Definition, or Example). -/
structure Entry where
  header : String := "Theorem"
  title? : Option String := none
  declaration : String
  sectionTitle? : Option String := none
  sectionIntro? : Option String := none
  sectionContext? : Option SectionContext := none
  sectionId? : Option String := none
  ambient? : Option AmbientSetting := none
  statement : Array (Array Inline)
  localInspectors : Array SymbolInspector := #[]
  referencedKeys : Array String := #[]
  diagramHtml? : Option String := none
  proof : Array ProofNode := #[]
  axioms : AxiomAudit := ⟨#[], false⟩
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson Entry where
  fromJson? j := do
    let header ← getFieldD j "header" "Theorem"
    let title? ← getOptField? j "title"
    let declaration ← j.getObjValAs? String "declaration"
    let sectionTitle? ← getOptField? j "sectionTitle"
    let sectionIntro? ← getOptField? j "sectionIntro"
    let sectionContext? ← getOptField? j "sectionContext"
    let sectionId? ← getOptField? j "sectionId"
    let ambient? ← getOptField? j "ambient"
    let statement ← getFieldD j "statement" (#[] : Array (Array Inline))
    let localInspectors ← getFieldD j "localInspectors" (#[] : Array SymbolInspector)
    let referencedKeys ← getFieldD j "referencedKeys" (#[] : Array String)
    let diagramHtml? ← getOptField? j "diagramHtml"
    let proof ← getFieldD j "proof" (#[] : Array ProofNode)
    let axioms ← getFieldD j "axioms" ({ axioms := #[], hasSorry := false } : AxiomAudit)
    return {
      header, title?, declaration, sectionTitle?, sectionIntro?, sectionContext?,
      sectionId?, ambient?, statement, localInspectors, referencedKeys, diagramHtml?, proof, axioms
    }

/-- Complete canonical informalization document consumed by Infoview, HTML, and Verso. -/
structure Document where
  title : String
  subtitle? : Option String := none
  defaultMode : ViewMode := .paper
  entries : Array Entry
  inspectors : Array SymbolInspector := #[]
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson Document where
  fromJson? j := do
    let title ← j.getObjValAs? String "title"
    let subtitle? ← getOptField? j "subtitle"
    let defaultMode ← getFieldD j "defaultMode" ViewMode.paper
    let entries ← getFieldD j "entries" (#[] : Array Entry)
    let inspectors ← getFieldD j "inspectors" (#[] : Array SymbolInspector)
    return { title, subtitle?, defaultMode, entries, inspectors }

/-- Parse a canonical `Document` from raw JSON text. -/
def parseDocumentJson (content : String) : Except String Document := do
  let json ← Json.parse content
  fromJson? json

/-- Load and decode a canonical `Document` JSON file from disk. -/
def loadDocumentFile (path : System.FilePath) : IO Document := do
  let content ← IO.FS.readFile path
  match parseDocumentJson content with
  | .ok doc => return doc
  | .error err => throw <| IO.userError s!"Failed to decode Document JSON '{path}': {err}"

/-- Look up a `SymbolInspector` in a `Document` by stable `key`. -/
def Document.findInspector? (doc : Document) (key : String) : Option SymbolInspector :=
  doc.inspectors.find? (·.key == key)

/-- Find an `Entry` in a `Document` by Lean declaration name. -/
def Document.findEntry? (doc : Document) (decl : String) : Option Entry :=
  doc.entries.find? (·.declaration == decl)

end VersoInformalization.Schema
