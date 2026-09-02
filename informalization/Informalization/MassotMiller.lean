/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# The public Massot–Miller InformalLean document model

The constructor and JSON names in this module are pinned to the two public
InformalLean examples linked from Kyle Miller's project page.  In particular,
`withReplacement` is the six-position replacement combinator used by the real
renderer; it is not a generic disclosure panel.
-/

namespace Informalization.MassotMiller

/-- One English-rendered item in a Lean local context. -/
structure ContextItem where
  name : Option String := none
  value : Option String := none
  singularType : String := ""
  pluralType : Option String := none
  provides : Array String := #[]
  used : Bool := true
  implDetail : Bool := false
  auxDecl : Bool := false
  deriving Repr, BEq, Inhabited

/-- The proof-state record displayed by the public InformalLean goal inspector. -/
structure GoalInfo where
  targetPrefix : String := "Goal:"
  target : String
  paragraphForm : String := ""
  items : Array ContextItem := #[]
  caseName : Option String := none
  deriving Repr, BEq, Inhabited

/-- Static counterpart of the information Lean's editor hover associates with
a checked term.  `latex` identifies the paper notation to annotate; the other
fields are extracted from the elaborated environment and local context. -/
structure LeanHoverInfo where
  latex : String := ""
  name : String
  type : String
  explicit? : Option String := none
  documentation? : Option String := none
  /-- Optional reader explanation supplied by the presentation profile.  It
  augments rather than replaces the Lean-derived fields above. -/
  description? : Option String := none
  deriving Repr, BEq, Inhabited

/-- Stable source coordinates for a declaration referenced by checked
evidence.  A module name is always meaningful in a standalone reader; file
resolution remains the responsibility of an editor integration. -/
structure LeanSourceLocation where
  moduleName : String
  line : Nat
  column : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr, BEq, Inhabited

/-- Developer-facing rendering of one exact item from the checked evidence
index.  Unlike semantic prose, this record deliberately preserves Lean names
and terms. -/
structure LeanEvidenceInfo where
  label : String
  declaration? : Option String := none
  type : String
  expected? : Option String := none
  term : String
  source? : Option LeanSourceLocation := none
  deriving Repr, BEq, Inhabited

/-- A row in an aligned calculation.  The explanation justifies the relation. -/
structure ComputationStep (Explanation : Type) where
  rel : String
  rhs : String
  expl : Explanation
  deriving Repr, BEq, Inhabited

/--
The complete structured-document language exercised by the public Rudin and
Bourbaki pages and handled by their renderer.
-/
inductive Explanation where
  | empty
  | paragraphBreak
  | str (value : String)
  | human (value : String)
  | join (value : Array Explanation)
  | goalState (goalState : GoalInfo)
  | withReplacement
      (value : Explanation)
      (replace : Explanation)
      (preValue : Explanation)
      (preReplace : Explanation)
      (postValue : Explanation)
      (postReplace : Explanation)
      (expanded : Bool)
  | withTrailer (value trailer : Explanation) (expanded : Bool)
  | withToolTip (value : Explanation) (tooltip : String)
  /-- Annotate every matching mathematical atom below `value` with checked
  Lean hover data.  The wrapper changes interaction only, never visible text. -/
  | withLeanHovers (value : Explanation) (hovers : Array LeanHoverInfo)
  /-- Attach an independent, developer-facing disclosure of exact checked
  Lean evidence. Semantic expand/collapse operations do not open this panel. -/
  | withLeanEvidence (value : Explanation) (evidence : Array LeanEvidenceInfo)
      (goal? : Option GoalInfo := none) (expanded : Bool := false)
  /-- Preserve the complete concrete proof explanation behind a single
  unobtrusive theorem-level disclosure.  Unlike the flat evidence inspector,
  the proof is itself an `Explanation`, so its full recursive replacement tree
  remains available to the ordinary expand/collapse operation. -/
  | withConcreteProof (value proof : Explanation) (expanded : Bool := false)
  | indent (value : Explanation)
  | list (value : Array Explanation)
  | enumList (value : Array Explanation)
  | computation (start : String) (steps : Array (ComputationStep Explanation))
  deriving Repr, BEq, Inhabited

/-- The declaration wrapper emitted by InformalLean's `print_proof` frontend. -/
structure LemmaInfo where
  statement : String
  name : String
  header : String := "Theorem"
  /-- Optional reader-facing title, independent of the Lean declaration name. -/
  title : Option String := none
  /-- Optional structured statement.  When present it is the authoritative
  reader surface and may contain mathematical tooltips. `statement` remains a
  plain-text compatibility fallback. -/
  statementExplanation? : Option Explanation := none
  /-- Lean-derived hover for the declaration named in the theorem heading. -/
  declarationHover? : Option LeanHoverInfo := none
  explanations : Array Explanation := #[]
  deriving Repr, BEq, Inhabited

/-- A module informalization is an ordered array of declaration records. -/
abbrev Document := Array LemmaInfo

namespace Explanation

/-- Join documents without inserting text or layout of our own. -/
def concat (xs : Array Explanation) : Explanation := .join xs

/-- A collapsed replacement with the four surrounding positions empty. -/
def replacement (value replace : Explanation) : Explanation :=
  .withReplacement value replace .empty .empty .empty .empty false

/-- A collapsed trailer. -/
def trailer (value extra : Explanation) : Explanation :=
  .withTrailer value extra false

/-- Set every replacement/trailer in the currently displayed explanation tier
to the requested state.  Exact Lean evidence and the complete concrete proof
tree are independent inspection tiers, so this operation never opens or closes
them. -/
partial def setAllExpanded (state : Bool) : Explanation → Explanation
  | .empty => .empty
  | .paragraphBreak => .paragraphBreak
  | .str s => .str s
  | .human s => .human s
  | .join xs => .join (xs.map (setAllExpanded state))
  | .goalState g => .goalState g
  | .withReplacement value replace preValue preReplace postValue postReplace _ =>
      .withReplacement
        (setAllExpanded state value)
        (setAllExpanded state replace)
        (setAllExpanded state preValue)
        (setAllExpanded state preReplace)
        (setAllExpanded state postValue)
        (setAllExpanded state postReplace)
        state
  | .withTrailer value trailer _ =>
      .withTrailer (setAllExpanded state value) (setAllExpanded state trailer) state
  | .withToolTip value tooltip => .withToolTip (setAllExpanded state value) tooltip
  | .withLeanHovers value hovers => .withLeanHovers (setAllExpanded state value) hovers
  | .withLeanEvidence value evidence goal? expanded =>
      .withLeanEvidence (setAllExpanded state value) evidence goal? expanded
  | .withConcreteProof value proof expanded =>
      if expanded then
        .withConcreteProof value (setAllExpanded state proof) true
      else
        .withConcreteProof (setAllExpanded state value) proof false
  | .indent value => .indent (setAllExpanded state value)
  | .list xs => .list (xs.map (setAllExpanded state))
  | .enumList xs => .enumList (xs.map (setAllExpanded state))
  | .computation start steps =>
      .computation start (steps.map fun step =>
        { step with expl := setAllExpanded state step.expl })

/-- State transition for the reader's global expansion controls.  Expanding
selects the complete concrete proof and recursively opens every supplied
replacement and trailer.  Collapsing closes both trees and returns to the
semantic paper view.  Exact Lean-evidence panels remain independent. -/
partial def setGlobalExpansion (state : Bool) : Explanation → Explanation
  | .empty => .empty
  | .paragraphBreak => .paragraphBreak
  | .str s => .str s
  | .human s => .human s
  | .join xs => .join (xs.map (setGlobalExpansion state))
  | .goalState g => .goalState g
  | .withReplacement value replace preValue preReplace postValue postReplace _ =>
      .withReplacement
        (setGlobalExpansion state value)
        (setGlobalExpansion state replace)
        (setGlobalExpansion state preValue)
        (setGlobalExpansion state preReplace)
        (setGlobalExpansion state postValue)
        (setGlobalExpansion state postReplace)
        state
  | .withTrailer value trailer _ =>
      .withTrailer
        (setGlobalExpansion state value)
        (setGlobalExpansion state trailer)
        state
  | .withToolTip value tooltip =>
      .withToolTip (setGlobalExpansion state value) tooltip
  | .withLeanHovers value hovers =>
      .withLeanHovers (setGlobalExpansion state value) hovers
  | .withLeanEvidence value evidence goal? expanded =>
      .withLeanEvidence (setGlobalExpansion state value) evidence goal? expanded
  | .withConcreteProof value proof _ =>
      if state then
        .withConcreteProof value (setGlobalExpansion true proof) true
      else
        .withConcreteProof
          (setGlobalExpansion false value)
          (setGlobalExpansion false proof)
          false
  | .indent value => .indent (setGlobalExpansion state value)
  | .list xs => .list (xs.map (setGlobalExpansion state))
  | .enumList xs => .enumList (xs.map (setGlobalExpansion state))
  | .computation start steps =>
      .computation start (steps.map fun step =>
        { step with expl := setGlobalExpansion state step.expl })

/--
Visible authored content for the node's current expansion state.  UI glyphs and
the separate goal inspector are intentionally absent.  This function is the
acceptance oracle for verbatim-source examples.
-/
partial def visibleText : Explanation → String
  | .empty => ""
  | .paragraphBreak => "\n\n"
  | .str s => s
  | .human s => s
  | .join xs => xs.foldl (fun out x => out ++ visibleText x) ""
  | .goalState _ => ""
  | .withReplacement value replace preValue preReplace postValue postReplace expanded =>
      if expanded then
        visibleText preReplace ++ visibleText replace ++ visibleText postReplace
      else
        visibleText preValue ++ visibleText value ++ visibleText postValue
  | .withTrailer value trailer expanded =>
      visibleText value ++ if expanded then visibleText trailer else ""
  | .withToolTip value _ => visibleText value
  | .withLeanHovers value _ => visibleText value
  | .withLeanEvidence value _ _ _ => visibleText value
  | .withConcreteProof value _ _ => visibleText value
  | .indent value => visibleText value
  | .list xs | .enumList xs =>
      String.intercalate "\n" (xs.toList.map visibleText)
  | .computation start steps =>
      steps.foldl (fun out step =>
        out ++ "\n" ++ step.rel ++ " " ++ step.rhs ++ " " ++ visibleText step.expl) start

/-- Number of interactive replacement/trailer nodes. -/
partial def interactiveCount : Explanation → Nat
  | .empty | .paragraphBreak | .str _ | .human _ | .goalState _ => 0
  | .join xs | .list xs | .enumList xs =>
      xs.foldl (fun n x => n + interactiveCount x) 0
  | .withReplacement value replace preValue preReplace postValue postReplace _ =>
      1 + interactiveCount value + interactiveCount replace + interactiveCount preValue +
        interactiveCount preReplace + interactiveCount postValue + interactiveCount postReplace
  | .withTrailer value trailer _ => 1 + interactiveCount value + interactiveCount trailer
  | .withToolTip value _ | .withLeanHovers value _ | .indent value =>
      interactiveCount value
  | .withLeanEvidence value _ _ _ => 1 + interactiveCount value
  | .withConcreteProof value proof _ =>
      1 + interactiveCount value + interactiveCount proof
  | .computation _ steps =>
      steps.foldl (fun n step => n + interactiveCount step.expl) 0

end Explanation

/-- The reader-visible theorem statement, using the structured surface when
one is available. -/
def LemmaInfo.visibleStatement (decl : LemmaInfo) : String :=
  decl.statementExplanation?.map Explanation.visibleText |>.getD decl.statement

/-! ## JSON schema -/

private def optStringJson : Option String → Lean.Json
  | none => .null
  | some s => .str s

def ContextItem.toJson (item : ContextItem) : Lean.Json :=
  Lean.Json.mkObj
    [ ("value", optStringJson item.value)
    , ("used", .bool item.used)
    , ("type", .str "ContextItem")
    , ("singularType", .str item.singularType)
    , ("provides", .arr (item.provides.map .str))
    , ("pluralType", optStringJson item.pluralType)
    , ("name", optStringJson item.name)
    , ("implDetail", .bool item.implDetail)
    , ("auxDecl", .bool item.auxDecl) ]

def GoalInfo.toJson (goal : GoalInfo) : Lean.Json :=
  Lean.Json.mkObj
    [ ("type", .str "GoalInfo")
    , ("targetPrefix", .str goal.targetPrefix)
    , ("target", .str goal.target)
    , ("paragraphForm", .str goal.paragraphForm)
    , ("items", .arr (goal.items.map ContextItem.toJson))
    , ("case", optStringJson goal.caseName) ]

def LeanHoverInfo.toJson (hover : LeanHoverInfo) : Lean.Json :=
  Lean.Json.mkObj
    [ ("latex", .str hover.latex)
    , ("name", .str hover.name)
    , ("type", .str hover.type)
    , ("explicit", optStringJson hover.explicit?)
    , ("documentation", optStringJson hover.documentation?)
    , ("description", optStringJson hover.description?) ]

def LeanSourceLocation.toJson (source : LeanSourceLocation) : Lean.Json :=
  Lean.Json.mkObj
    [ ("module", .str source.moduleName)
    , ("line", .num source.line)
    , ("column", .num source.column)
    , ("endLine", .num source.endLine)
    , ("endColumn", .num source.endColumn) ]

def LeanEvidenceInfo.toJson (evidence : LeanEvidenceInfo) : Lean.Json :=
  Lean.Json.mkObj
    [ ("label", .str evidence.label)
    , ("declaration", optStringJson evidence.declaration?)
    , ("type", .str evidence.type)
    , ("expected", optStringJson evidence.expected?)
    , ("term", .str evidence.term)
    , ("source", match evidence.source? with
        | some source => source.toJson
        | none => .null) ]

partial def Explanation.toJson : Explanation → Lean.Json
  | .empty => Lean.Json.mkObj [("type", .str "Explanation.empty")]
  | .paragraphBreak => Lean.Json.mkObj [("type", .str "Explanation.paragraphBreak")]
  | .str value =>
      Lean.Json.mkObj [("value", .str value), ("type", .str "Explanation.str")]
  | .human value =>
      Lean.Json.mkObj [("value", .str value), ("type", .str "Explanation.human")]
  | .join value =>
      Lean.Json.mkObj
        [("value", .arr (value.map Explanation.toJson)), ("type", .str "Explanation.join")]
  | .goalState goal =>
      Lean.Json.mkObj
        [("type", .str "Explanation.goalState"), ("goalState", goal.toJson)]
  | .withReplacement value replace preValue preReplace postValue postReplace expanded =>
      Lean.Json.mkObj
        [ ("value", value.toJson)
        , ("type", .str "Explanation.withReplacement")
        , ("replace", replace.toJson)
        , ("preValue", preValue.toJson)
        , ("preReplace", preReplace.toJson)
        , ("postValue", postValue.toJson)
        , ("postReplace", postReplace.toJson)
        , ("expanded", .bool expanded) ]
  | .withTrailer value trailer expanded =>
      Lean.Json.mkObj
        [ ("value", value.toJson)
        , ("type", .str "Explanation.withTrailer")
        , ("trailer", trailer.toJson)
        , ("expanded", .bool expanded) ]
  | .withToolTip value tooltip =>
      Lean.Json.mkObj
        [ ("value", value.toJson)
        , ("type", .str "Explanation.withToolTip")
        , ("tooltip", .str tooltip) ]
  | .withLeanHovers value hovers =>
      Lean.Json.mkObj
        [ ("value", value.toJson)
        , ("type", .str "Explanation.withLeanHovers")
        , ("hovers", .arr (hovers.map LeanHoverInfo.toJson)) ]
  | .withLeanEvidence value evidence goal? expanded =>
      Lean.Json.mkObj
        [ ("value", value.toJson)
        , ("type", .str "Explanation.withLeanEvidence")
        , ("evidence", .arr (evidence.map LeanEvidenceInfo.toJson))
        , ("goalState", match goal? with
            | some goal => goal.toJson
            | none => .null)
        , ("expanded", .bool expanded) ]
  | .withConcreteProof value proof expanded =>
      Lean.Json.mkObj
        [ ("value", value.toJson)
        , ("type", .str "Explanation.withConcreteProof")
        , ("proof", proof.toJson)
        , ("expanded", .bool expanded) ]
  | .indent value =>
      Lean.Json.mkObj [("value", value.toJson), ("type", .str "Explanation.indent")]
  | .list value =>
      Lean.Json.mkObj
        [("value", .arr (value.map Explanation.toJson)), ("type", .str "Explanation.list")]
  | .enumList value =>
      Lean.Json.mkObj
        [("value", .arr (value.map Explanation.toJson)), ("type", .str "Explanation.enumList")]
  | .computation start steps =>
      let stepJson := steps.map fun step =>
        Lean.Json.mkObj
          [("rhs", .str step.rhs), ("rel", .str step.rel), ("expl", step.expl.toJson)]
      Lean.Json.mkObj
        [ ("type", .str "Explanation.computation")
        , ("steps", .arr stepJson)
        , ("start", .str start) ]

def LemmaInfo.toJson (decl : LemmaInfo) : Lean.Json :=
  Lean.Json.mkObj
    [ ("type", .str "LemmaInfo")
    , ("statement", .str decl.statement)
    , ("name", .str decl.name)
    , ("header", .str decl.header)
    , ("title", optStringJson decl.title)
    , ("statementExplanation", match decl.statementExplanation? with
        | some explanation => explanation.toJson
        | none => .null)
    , ("declarationHover", match decl.declarationHover? with
        | some hover => hover.toJson
        | none => .null)
    , ("explanations", .arr (decl.explanations.map Explanation.toJson)) ]

def documentToJson (doc : Document) : Lean.Json :=
  .arr (doc.map LemmaInfo.toJson)

def documentToJsonString (doc : Document) : String :=
  documentToJson doc |>.compress

/-! ## Schema and state tests -/

#guard Explanation.empty.toJson.compress == "{\"type\":\"Explanation.empty\"}"
#guard (Explanation.str "hello").toJson ==
  Lean.Json.mkObj [("value", .str "hello"), ("type", .str "Explanation.str")]

private def replacementTest : Explanation :=
  .replacement (.str "short") (.str "long")

#guard replacementTest.visibleText == "short"
#guard (replacementTest.setAllExpanded true).visibleText == "long"
#guard replacementTest.interactiveCount == 1

end Informalization.MassotMiller
