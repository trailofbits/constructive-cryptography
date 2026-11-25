/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# Canonical Unified Explanation IR

One checked intermediate representation shared by all three output surfaces:
1. **Lean 4 Infoview** (`ProofWidgets` interactive component),
2. **Standalone ETH CADMO HTML** (Palatino `memoir` monograph + embedded `Rendering` diagrams),
3. **Verso Consumer Package** (papers, theses, and slides reading the exported JSON).

Crucially, there is **only one recursive proof tree** (`ProofNode`) — no separate
"semantic view vs. 700 KB concrete tactic dump" split. Clicking `⊕` descends recursively along
checked mathematical justifications, across module boundaries, while routine algebra/casts
collapse into auditable `routineReceipt` nodes and trivial Lean wrappers carry `isWrapper := true`
so **Paper mode** steps through them cleanly while **Auditor mode** can expose every boundary.
-/

namespace Informalization.Core.Explanation

open Lean

/-- Reader disclosure preset. Both modes project the exact same checked proof tree. -/
inductive ViewMode
  | paper    -- auto-inline trivial wrappers; routine receipts compact; quiet flow marginalia
  | auditor  -- expose every lemma boundary, routine receipt, and exact Lean goal state
  deriving DecidableEq, Repr, BEq, Inhabited, ToJson

/-- Provenance / trust tier attached to every emitted prose fragment and inline token. -/
inductive ProseTrust
  | kernelFormula
  | kernelProvedClaim
  | typedRef
  | intuitionGloss
  deriving DecidableEq, Repr, BEq, Inhabited

instance : ToJson ProseTrust where
  toJson
    | .kernelFormula     => Json.str "kernelFormula"
    | .kernelProvedClaim => Json.str "kernelProvedClaim"
    | .typedRef          => Json.str "typedRef"
    | .intuitionGloss    => Json.str "intuitionGloss"

/-- Inline content inside a mathematical sentence. Every underlined `symbol` points to a
type-aware `SymbolInspector` entry by stable key. -/
inductive Inline
  | text (value : String)
  | emph (value : String)
  | inlineMath (latex : String)
  | displayMath (latex : String) (punct : String := ".")
  | symbol (key : String) (display : String) (isMath : Bool := true)
  | citation (label : String) (detail : String := "")
  deriving Repr, BEq, Inhabited, ToJson

/-- Extract plain readable text/LaTeX from one `Inline` node. -/
def Inline.collectText : Inline → String
  | .text s => s
  | .emph s => s
  | .inlineMath s => s
  | .displayMath s p => s ++ p
  | .symbol _ d _ => d
  | .citation l d => if d.isEmpty then l else l ++ " " ++ d

/-- Split author prose containing `$...$`, `\(...\)`, `$$...$$`, or `\[...\]` math delimiters
(respecting `\$` escapes) into structured `Array Inline` nodes so KaTeX, offline 2D math, Verso,
Infoview, and hover-reference annotation all process embedded math identically. -/
partial def parseProseWithMath (s : String) : Array Inline := Id.run do
  let chars := s.toList
  let n := chars.length
  let arr := chars.toArray
  let mut out : Array Inline := #[]
  let mut textBuf : List Char := []
  let mut i : Nat := 0

  let flushText (buf : List Char) (acc : Array Inline) : Array Inline :=
    if buf.isEmpty then acc
    else acc.push (.text (String.ofList buf.reverse))

  let findClosing (startIdx : Nat) (close1 : Char) (close2? : Option Char := none) : Option (String × Nat) := Id.run do
    let mut j := startIdx
    let mut inner : List Char := []
    while j < n do
      let c := arr[j]!
      if c == '\\' && j + 1 < n && arr[j + 1]! == '$' && close1 == '$' && close2?.isNone then
        inner := '$' :: '\\' :: inner
        j := j + 2
      else if close2?.isSome && c == close1 && j + 1 < n && arr[j + 1]! == close2?.get! then
        return some ((String.ofList inner.reverse).trimAscii.toString, j + 2)
      else if close2?.isNone && c == close1 then
        return some ((String.ofList inner.reverse).trimAscii.toString, j + 1)
      else
        inner := c :: inner
        j := j + 1
    return none

  while i < n do
    let c := arr[i]!
    if c == '\\' && i + 1 < n then
      let nxt := arr[i + 1]!
      if nxt == '$' then
        textBuf := '$' :: textBuf
        i := i + 2
        continue
      else if nxt == '(' then
        if let some (math, nextI) := findClosing (i + 2) '\\' (some ')') then
          out := flushText textBuf out
          textBuf := []
          out := out.push (.inlineMath math)
          i := nextI
          continue
      else if nxt == '[' then
        if let some (math, nextI) := findClosing (i + 2) '\\' (some ']') then
          out := flushText textBuf out
          textBuf := []
          let mut punct := "."
          let mut k := nextI
          if k < n && (arr[k]! == '.' || arr[k]! == ',') then
            punct := arr[k]!.toString
            k := k + 1
          out := out.push (.displayMath math punct)
          i := k
          continue
    else if c == '$' then
      if i + 1 < n && arr[i + 1]! == '$' then
        if let some (math, nextI) := findClosing (i + 2) '$' (some '$') then
          out := flushText textBuf out
          textBuf := []
          let mut punct := "."
          let mut k := nextI
          if k < n && (arr[k]! == '.' || arr[k]! == ',') then
            punct := arr[k]!.toString
            k := k + 1
          out := out.push (.displayMath math punct)
          i := k
          continue
      else
        if let some (math, nextI) := findClosing (i + 1) '$' none then
          out := flushText textBuf out
          textBuf := []
          out := out.push (.inlineMath math)
          i := nextI
          continue
    textBuf := c :: textBuf
    i := i + 1

  out := flushText textBuf out
  return out

/-- One row in a `Rendering`-style interface port table (`Port / Query / Reply`). -/
structure PortRow where
  port : String
  queryLatex : String
  replyLatex : String
  deriving Repr, BEq, Inhabited, ToJson

/-- Type-aware inspector payload opened when a reader hovers or clicks any named symbol in prose. -/
inductive InspectorKind
  | interfaceTable (ports : Array PortRow) (domainLatex : String) (budgetNote : String := "")
  | dslPseudocode (header : String) (body : String) (fullSource : String)
  | ccDiagram (svgOrHtml : String) (summaryLatex : String)
  | mathDefinition (equationLatex : String) (proseSummary : String := "")
  | witnessCard (title : String) (rows : Array (String × String))
  | parameter (roleDescription : String)
  | localShorthand (equationLatex : String) (roleDescription : String := "")
  deriving Repr, BEq, Inhabited, ToJson

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

/-- One hygienized local context entry inside a Kyle Miller goal-state inspector.
Anonymous hypotheses never render as `None`: `name?` is omitted cleanly. -/
structure ContextEntry where
  name? : Option String := none
  description : String
  isHypothesis : Bool := false
  usedInGoal : Bool := true
  deriving Repr, BEq, Inhabited, ToJson

/-- A checked proof-state checkpoint (Kyle Miller's context + target view). -/
structure GoalState where
  context : Array ContextEntry
  targetLatex : String
  targetProse? : Option String := none
  rawLeanGoal? : Option String := none
  deriving Repr, BEq, Inhabited, ToJson

/-- One line of a structured `cc_calc` / `calc` chain. -/
structure CalcStep where
  lhsLatex : String
  relationLatex : String
  rhsLatex : String
  reason : Array Inline
  diagramHtml? : Option String := none
  justification : Array (String × String) := #[]  -- lightweight metadata
  deriving Repr, BEq, Inhabited, ToJson

/-- Serialize an `Inline` to JSON with optional `"trust"` and `"dataKey"` metadata while preserving
all existing 6 constructor schemas identically. -/
def inlineToJsonWithMeta (inl : Inline) (trust? : Option ProseTrust := none)
    (dataKey? : Option String := none) : Json :=
  let base := toJson inl
  match base with
  | .obj kvs =>
      let kvs := match trust? with
        | some t => kvs.insert "trust" (toJson t)
        | none => kvs
      let kvs := match dataKey?, inl with
        | some dk, .symbol _ _ _
        | some dk, .inlineMath _
        | some dk, .displayMath _ _ => kvs.insert "dataKey" (Json.str dk)
        | _, _ => kvs
      .obj kvs
  | other => other

/-- A node in the single unified recursive proof tree. -/
inductive ProofNode
  /-- A checked mathematical claim/step; clicking `⊕` expands `children`. -/
  | step
      (id : String)
      (content : Array Inline)
      (children : Array ProofNode)
      (goal? : Option GoalState := none)
      (diagramHtml? : Option String := none)
      (originDecl? : Option String := none)
      (isWrapper : Bool := false)
      (defaultExpanded : Bool := false)
      (startsParagraph : Bool := false)
      (leadHeading? : Option String := none)
      (trust? : Option ProseTrust := none)
      (inlineMeta : Array (Option ProseTrust × Option String) := #[])
  /-- A paper-style `calc` / `cc_calc` chain (alternating `=`, `≃[ε]`, `≈[ε]`, `≤`). -/
  | calcChain
      (id : String)
      (intro : Array Inline)
      (steps : Array (CalcStep × Array ProofNode))
      (goal? : Option GoalState := none)
      (originDecl? : Option String := none)
  /-- A compact, auditable receipt absorbing routine algebra/casts/indexing mechanics. -/
  | routineReceipt
      (id : String)
      (summary : String)
      (stepCount : Nat)
      (details : Array ProofNode)
      (goal? : Option GoalState := none)
  /-- Optional ~10% inconsequential flow/motivation note (visually distinct; never a claim). -/
  | flowNote
      (id : String)
      (text : String)
      (placement : String := "margin")  -- "margin" | "inline"
  /-- An inline visual figure (CC box-and-wire diagram, DSL pseudocode card, or sketch). -/
  | figure
      (id : String)
      (caption : Array Inline)
      (html : String)
  deriving Repr, BEq, Inhabited

mutual
  partial def proofNodeToJson : ProofNode → Json
    | .step id content children goal? diagramHtml? originDecl? isWrapper defaultExpanded
            startsParagraph leadHeading? trust? inlineMeta =>
        let contentJson := Json.arr <| content.mapIdx fun i inl =>
          match inlineMeta[i]? with
          | some (t?, dk?) => inlineToJsonWithMeta inl t? dk?
          | none => toJson inl
        let baseFields : List (String × Json) := [
          ("kind", "step"),
          ("id", toJson id),
          ("content", contentJson),
          ("children", Json.arr (children.map proofNodeToJson)),
          ("goal", toJson goal?),
          ("diagramHtml", toJson diagramHtml?),
          ("originDecl", toJson originDecl?),
          ("isWrapper", toJson isWrapper),
          ("defaultExpanded", toJson defaultExpanded)
        ]
        let extraPara : List (String × Json) :=
          if startsParagraph then [("startsParagraph", toJson true)] else []
        let extraHead : List (String × Json) := match leadHeading? with
          | some h => [("leadHeading", toJson h)]
          | none => []
        let extraTrust : List (String × Json) := match trust? with
          | some t => [("trust", toJson t)]
          | none => []
        Json.mkObj (baseFields ++ extraPara ++ extraHead ++ extraTrust)
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
end

instance : ToJson ProofNode := ⟨proofNodeToJson⟩

/-- Axiom-audit record attached to a checked declaration. -/
structure AxiomAudit where
  axioms : Array String
  hasSorry : Bool := false
  deriving Repr, BEq, Inhabited, ToJson

/-- Section-fixed parameters and standing assumptions hoisted once per numbered paper section. -/
structure SectionContext where
  sectionId : String
  sectionNumber : Nat
  paragraphs : Array (Array Inline)
  inspectors : Array SymbolInspector := #[]
  deriving Repr, BEq, Inhabited, ToJson

/-- Ambient context block factored out once per theorem/section (kills telescope repetition). -/
structure AmbientSetting where
  summary : Array Inline
  suppressedTypeclasses : Array String := #[]
  deriving Repr, BEq, Inhabited, ToJson

/-- One informalized declaration (Theorem, Lemma, Proposition, Corollary, Definition). -/
structure Entry where
  header : String := "Theorem"     -- "Theorem" | "Lemma" | "Proposition" | "Corollary" | "Definition"
  title? : Option String := none
  declaration : String
  sectionTitle? : Option String := none
  sectionIntro? : Option String := none
  sectionContext? : Option SectionContext := none
  sectionId? : Option String := none
  ambient? : Option AmbientSetting := none
  statement : Array (Array Inline) -- paragraphs of the formal statement
  localInspectors : Array SymbolInspector := #[]
  referencedKeys : Array String := #[]
  diagramHtml? : Option String := none
  proof : Array ProofNode := #[]
  axioms : AxiomAudit := ⟨#[], false⟩
  deriving Repr, BEq, Inhabited, ToJson

/-- A complete informalization document (one theorem or a multi-theorem monograph chapter),
consumed identically by the Lean Infoview, standalone CADMO HTML, and Verso. -/
structure Document where
  title : String
  subtitle? : Option String := none
  defaultMode : ViewMode := .paper
  entries : Array Entry
  inspectors : Array SymbolInspector := #[]
  deriving Repr, BEq, Inhabited, ToJson

/-- Helper to flatten all visible prose/LaTeX strings inside a `ProofNode` for automated
zero-leakage & typography quality gates. -/
partial def ProofNode.collectAllText (n : ProofNode) : Array String :=
  let inlineText (xs : Array Inline) : Array String := xs.map Inline.collectText
  match n with
  | .step _ content children goal? _ _ _ _ _ _ _ _ =>
      let g := match goal? with
        | some gs => #[gs.targetLatex] ++ gs.context.map (·.description)
        | none => #[]
      inlineText content ++ g ++ children.flatMap ProofNode.collectAllText
  | .calcChain _ intro steps goal? _ =>
      let s := steps.flatMap fun (cs, ch) =>
        #[cs.lhsLatex, cs.relationLatex, cs.rhsLatex] ++ inlineText cs.reason ++
          ch.flatMap ProofNode.collectAllText
      let g := match goal? with
        | some gs => #[gs.targetLatex] ++ gs.context.map (·.description)
        | none => #[]
      inlineText intro ++ s ++ g
  | .routineReceipt _ summary _ details _ =>
      #[summary] ++ details.flatMap ProofNode.collectAllText
  | .flowNote _ text _ => #[text]
  | .figure _ caption _ => inlineText caption

end Informalization.Core.Explanation
