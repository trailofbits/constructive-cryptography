/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller
import Informalization.Semantics.GoalState
import Informalization.Semantics.Realize

/-!
# Semantic documents as Massot--Miller explanations

This module is the presentation bridge between the role-driven semantic
realizer and the public `MassotMiller.Explanation` document language.  It does
not choose cryptographic prose: every human-facing sentence has already been
selected by `Semantics.Realize`.

The collapsed document contains only that prose, and expanding a proof move
reveals its semantic supporting details.  When a source-level proof explanation
is available, the bridge preserves that complete recursive tree behind one
theorem-level disclosure instead of replacing or depth-limiting it.
-/

namespace Informalization.Semantics.Explanation

open Lean
open Informalization.Semantics.Canonical
open Informalization.Semantics.Discourse
open Informalization.Semantics.GoalState
open Informalization.Semantics.Realize

private abbrev PublicExplanation :=
  Informalization.MassotMiller.Explanation

/-- Initial disclosure depth for the interactive explanation tree. -/
inductive InitialExpansion where
  | collapsed
  | expanded
  | through (depth : Nat)
  deriving Inhabited, BEq, Repr

/-- Presentation-only controls.  They cannot change the prose or the evidence
selected by the semantic backend. -/
structure Config where
  header : String := "Theorem"
  initialExpansion : InitialExpansion := .collapsed
  /-- Emit Miller-style proof-state checkpoints when a separately humanized
  goal index is supplied. -/
  goalMarkers : Bool := true
  /-- Developer inspection mode.  Reader-facing documents leave this off: an
  evidence identifier is provenance, not part of the mathematical proof. -/
  evidenceTooltips : Bool := false
  /-- Show a small check mark beside sentences backed by formal evidence.
  The cue's tooltip contains stable evidence identifiers, never expressions. -/
  checkedSourceCue : Bool := false
  /-- Legacy developer inspection mode for flat exact-term panels.  Normal
  reader pages use the complete concrete proof tree instead. -/
  leanEvidencePanels : Bool := false
  /-- Deprecated compatibility field for callers using the old presentation
  configuration. -/
  formalTrailers : Bool := false
  deriving Inhabited, BEq, Repr

private def expandedAt (config : Config) (depth : Nat) : Bool :=
  match config.initialExpansion with
  | .collapsed => false
  | .expanded => true
  | .through limit => depth < limit

/-- A stable, human-readable name for a semantic evidence reference. -/
def evidenceLabel : EvidenceRef -> String
  | .statementNode node => s!"statement node {node.index}"
  | .statementArgument node position =>
      s!"statement argument {node.index}.{position}"
  | .proofStep step => s!"proof step {step}"
  | .proofPremise step premise => s!"proof premise {step}.{premise}"
  | .formalFallback fallback => s!"formal fallback {fallback}"

private def evidenceTooltip (references : Array EvidenceRef) : String :=
  "Checked against: " ++ String.intercalate ", "
    (references.toList.map evidenceLabel)

private def withLeanEvidence (config : Config) (goals : GoalState.Index)
    (primary? : Option EvidenceRef) (references : Array EvidenceRef)
    (evidence : Array Informalization.MassotMiller.LeanEvidenceInfo)
    (value : PublicExplanation) : PublicExplanation :=
  if !config.leanEvidencePanels || evidence.isEmpty then value
  else
    let goal? := primary?.bind goals.forReference? |>.orElse fun _ =>
      goals.forReferences? references
    .withLeanEvidence value evidence goal? false

private def annotatedHuman (config : Config) (text : String)
    (references : Array EvidenceRef) : PublicExplanation :=
  let visible : PublicExplanation := .str text
  if references.isEmpty then visible
  else
    let tooltip := evidenceTooltip references
    let sentence :=
      if config.evidenceTooltips then .withToolTip visible tooltip else visible
    if config.checkedSourceCue then
      .join #[sentence, .withToolTip (.str " ✓") tooltip]
    else
      sentence

private def goalMarker (config : Config) (goals : GoalState.Index)
    (reference? : Option EvidenceRef) : PublicExplanation :=
  if !config.goalMarkers then .empty
  else
    match reference?.bind goals.forReference? with
    | some goal => .goalState goal
    | none => .empty

private def intersperseParagraphs
    (items : Array PublicExplanation) : Array PublicExplanation := Id.run do
  let mut result := #[]
  for index in [0:items.size] do
    if index > 0 then result := result.push .paragraphBreak
    result := result.push items[index]!
  return result

private def presentationFragment (source : Realize.Document) :
    PresentationFragment → PublicExplanation
  | .text value => .str value
  | .reference reference =>
      let visible := .str ("\\(" ++ reference.latex ++ "\\)")
      let hoverLatex := if reference.hoverLatex.trimAscii.isEmpty then
          reference.latex
        else
          reference.hoverLatex
      match source.theoremReferenceHovers.find? (·.latex == hoverLatex) with
      | some hover => .withLeanHovers visible #[hover]
      | none => .withToolTip visible reference.description

private def presentationParagraph
    (source : Realize.Document) (paragraph : PresentationParagraph) :
    PublicExplanation :=
  .join (paragraph.fragments.map (presentationFragment source))

/-- Build the theorem opening from checked profile metadata and the separately
realized conclusion.  Every interactive symbol is tied to a theorem binder or
declaration before this layer is reached. -/
private def presentedStatement? (source : Realize.Document) :
    Option PublicExplanation := do
  let conclusion ← source.sentences.find? fun sentence =>
    sentence.kind == .stateSecurityGoal
  let conclusion := if conclusion.referenceHovers.isEmpty then
      (.str conclusion.text : PublicExplanation)
    else
      .withLeanHovers (.str conclusion.text) conclusion.referenceHovers
  match source.theoremPresentation? with
  | some presentation =>
      let paragraphs := presentation.introductions.map (presentationParagraph source)
      return .join (intersperseParagraphs (paragraphs.push conclusion))
  | none => return conclusion

/-- Render a semantic detail as a recursively refinable proof node.  The goal
marker denotes this node's explicit primary checked step; merged provenance on
the node cannot silently select a different checkpoint. -/
private partial def detailExplanation (config : Config) (goals : GoalState.Index)
    (depth : Nat) (detail : Realize.Detail) : PublicExplanation :=
  let visible : PublicExplanation := .join #[
    goalMarker config goals (some detail.primaryEvidence),
    if detail.referenceHovers.isEmpty then
      annotatedHuman config detail.text detail.evidence
    else
      .withLeanHovers
        (annotatedHuman config detail.text detail.evidence)
        detail.referenceHovers
  ]
  let semantic := if detail.children.isEmpty then visible
  else
    let children := detail.children.map
      (detailExplanation config goals (depth + 1))
    let detailed : PublicExplanation := .join #[
      visible,
      .paragraphBreak,
      .indent (.join (intersperseParagraphs children))
    ]
    .withReplacement visible detailed
      .empty .empty .empty .empty (expandedAt config depth)
  withLeanEvidence config goals (some detail.primaryEvidence)
    detail.evidence detail.leanEvidence semantic

private def detailedMove (config : Config) (goals : GoalState.Index)
    (depth : Nat) (sentence : Sentence) : PublicExplanation :=
  let visible : PublicExplanation := if sentence.referenceHovers.isEmpty then
      annotatedHuman config sentence.text sentence.evidence
    else
      .withLeanHovers
        (annotatedHuman config sentence.text sentence.evidence)
        sentence.referenceHovers
  let details := sentence.details.map
    (detailExplanation config goals (depth + 1))
  let detailBlock : PublicExplanation :=
    if details.isEmpty then .empty
    else
      .join #[
        .paragraphBreak,
        .indent (.join (intersperseParagraphs details))
      ]
  -- As in Miller's document, expanding a terse claim reveals checkpoints for
  -- its internal proof steps.  It does not add a second checkpoint to the
  -- repeated claim headline itself; the theorem-root checkpoint remains the
  -- sole marker in the collapsed proof.
  .join #[visible, detailBlock]

/-- Convert one realized top-level proof move into an interactive explanation.

The short branch is exactly the realized human sentence.  Its replacement
branch adds only registered semantic supporting moves. -/
def sentenceExplanation (_source : Realize.Document) (config : Config)
    (goals : GoalState.Index)
    (depth : Nat) (sentence : Sentence) : PublicExplanation :=
  let short : PublicExplanation := if sentence.referenceHovers.isEmpty then
      annotatedHuman config sentence.text sentence.evidence
    else
      .withLeanHovers
        (annotatedHuman config sentence.text sentence.evidence)
        sentence.referenceHovers
  let semantic := if sentence.details.isEmpty then short
  else .withReplacement short (detailedMove config goals depth sentence)
      .empty .empty .empty .empty (expandedAt config depth)
  withLeanEvidence config goals sentence.primaryEvidence?
    sentence.evidence sentence.leanEvidence semantic

private def securitySentence? (source : Realize.Document) : Option Sentence :=
  source.sentences.find? fun sentence => sentence.kind == .stateSecurityGoal

private def proofSentences (source : Realize.Document) : Array Sentence :=
  source.sentences.filter fun sentence => sentence.kind != .stateSecurityGoal

private def proofExplanations (source : Realize.Document)
    (config : Config) (goals : GoalState.Index) : Array PublicExplanation :=
  let moves := proofSentences source |>.map
    (sentenceExplanation source config goals 0)
  if moves.isEmpty then #[]
  else
    let root := if config.goalMarkers then
        goals.root?.map Informalization.MassotMiller.Explanation.goalState |>.getD .empty
      else .empty
    #[.join #[root, .join (intersperseParagraphs moves)]]

/-- Build the public theorem record with a statement supplied by the caller.
This is the integration seam for callers which already have a separately
rendered theorem statement but want the proof body to come exclusively from
the semantic discourse pipeline. -/
def toLemmaInfoWithStatement (declaration : Name) (statement : String)
    (source : Realize.Document) (config : Config := {})
    (goals : GoalState.Index := {}) :
    Informalization.MassotMiller.LemmaInfo :=
  let richStatement? := presentedStatement? source
  {
    name := declaration.toString
    statement := richStatement?.map (·.visibleText) |>.getD statement
    header := config.header
    title := source.theoremPresentation?.map (·.title)
    statementExplanation? := richStatement?
    declarationHover? := source.declarationHover?
    explanations := proofExplanations source config goals
  }

/-- Preserve caller metadata while replacing the proof body.  A checked
theorem presentation supplies a title and structured opening; an explicit
caller title takes precedence. -/
def replaceProof (metadata : Informalization.MassotMiller.LemmaInfo)
    (source : Realize.Document) (config : Config := {})
    (goals : GoalState.Index := {}) :
    Informalization.MassotMiller.LemmaInfo :=
  let richStatement? := presentedStatement? source
  let title := if metadata.title.isSome then metadata.title
    else source.theoremPresentation?.map (·.title)
  let declarationHover? := metadata.declarationHover?.orElse fun _ =>
    source.declarationHover?
  let semanticProof := proofExplanations source config goals
  let explanations :=
    if metadata.explanations.isEmpty then semanticProof
    else #[.withConcreteProof (.join semanticProof) (.join metadata.explanations) false]
  {
    metadata with
    title
    statement := richStatement?.map (·.visibleText) |>.getD metadata.statement
    statementExplanation? := richStatement?.orElse fun _ => metadata.statementExplanation?
    declarationHover?
    explanations
  }

/-- Convert a realized semantic document into the public interactive theorem
record.  The semantic security-goal sentence becomes the theorem statement;
all remaining top-level sentences form the proof in their planned order. -/
def toLemmaInfo (declaration : Name) (source : Realize.Document)
    (config : Config := {}) (goals : GoalState.Index := {}) :
    Informalization.MassotMiller.LemmaInfo :=
  let statement :=
    (securitySentence? source).map (·.text) |>.getD
      "The stated conclusion holds."
  toLemmaInfoWithStatement declaration statement source config goals

/-- Convert several named semantic documents to a public Massot--Miller
document without changing their order. -/
def toDocument (sources : Array (Name × Realize.Document))
    (config : Config := {}) (goals : GoalState.Index := {}) :
    Informalization.MassotMiller.Document :=
  sources.map fun source => toLemmaInfo source.1 source.2 config goals

end Informalization.Semantics.Explanation
