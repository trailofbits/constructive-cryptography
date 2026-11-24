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

/-- One row in a `Rendering`-style interface port table (`Port / Query / Reply`). -/
structure PortRow where
  port : String
  queryLatex : String
  replyLatex : String
  deriving Repr, BEq, Inhabited, ToJson

/-- Type-aware inspector payload opened when a reader clicks any named symbol in prose. -/
inductive InspectorKind
  | interfaceTable (ports : Array PortRow) (domainLatex : String) (budgetNote : String := "")
  | dslPseudocode (header : String) (body : String) (fullSource : String)
  | ccDiagram (svgOrHtml : String) (summaryLatex : String)
  | mathDefinition (equationLatex : String) (proseSummary : String := "")
  | witnessCard (title : String) (rows : Array (String × String))
  | parameter (roleDescription : String)
  deriving Repr, BEq, Inhabited, ToJson

/-- Complete checked inspector record for one symbol/declaration. -/
structure SymbolInspector where
  key : String
  display : String
  kind : InspectorKind
  leanName? : Option String := none
  leanType : String
  sourceFile? : Option String := none
  sourceLine? : Option Nat := none
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
end

instance : ToJson ProofNode := ⟨proofNodeToJson⟩

/-- Axiom-audit record attached to a checked declaration. -/
structure AxiomAudit where
  axioms : Array String
  hasSorry : Bool := false
  deriving Repr, BEq, Inhabited, ToJson

/-- Ambient context block factored out once per theorem/section (kills telescope repetition). -/
structure AmbientSetting where
  summary : Array Inline
  suppressedTypeclasses : Array String := #[]
  deriving Repr, BEq, Inhabited, ToJson

/-- One informalized declaration (Theorem, Lemma, Proposition, Definition, or Example). -/
structure Entry where
  header : String := "Theorem"     -- "Theorem" | "Lemma" | "Proposition" | "Definition"
  title? : Option String := none
  declaration : String
  ambient? : Option AmbientSetting := none
  statement : Array (Array Inline) -- paragraphs of the formal statement
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
  let inlineText (xs : Array Inline) : Array String :=
    xs.map fun
      | .text s => s
      | .emph s => s
      | .inlineMath s => s
      | .displayMath s p => s ++ p
      | .symbol _ d _ => d
      | .citation l d => l ++ " " ++ d
  match n with
  | .step _ content children goal? _ _ _ _ =>
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
