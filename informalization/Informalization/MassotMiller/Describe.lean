/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller.Decompiler
import Informalization.MassotMiller.English
import Informalization.MassotMiller.Hover

/-!
# Priority-ordered tactic describers

This module is the center of the Massot–Miller pipeline.  Describers consume
nodes of the true tactic tree, may decline without consuming a node, and emit
the published hierarchical `Explanation` language.  The proof-term decompiler
is the deterministic fallback for term-bearing and macro/automation tactics.
-/

namespace Informalization.MassotMiller.Describe

open Lean Meta
open Informalization.MassotMiller
open Informalization.MassotMiller.InfoTree
open Informalization.MassotMiller.Decompiler
open Informalization.MassotMiller.English
open Informalization.MassotMiller.Ontology

/-- Initial disclosure state.  `through n` expands exactly the first `n`
hierarchical layers; every individual node remains independently toggleable in
the web application. -/
inductive InitialExpansion where
  | collapsed
  | expanded
  | through (depth : Nat)
  deriving Repr, BEq, Inhabited

/-- Presentation controls that do not change mathematical content. -/
structure Config where
  initialExpansion : InitialExpansion := .collapsed
  goalMarkers : Bool := true
  referenceTooltips : Bool := true
  formalTrailers : Bool := true
  language : English.Config := {}

private def expandedAt (config : Config) (depth : Nat) : Bool :=
  match config.initialExpansion with
  | .collapsed => false
  | .expanded => true
  | .through limit => depth < limit

private def replacementAt (config : Config) (depth : Nat)
    (short detailed : Explanation) : Explanation :=
  .withReplacement short detailed .empty .empty .empty .empty (expandedAt config depth)

private def trailerAt (config : Config) (depth : Nat)
    (value trailer : Explanation) : Explanation :=
  .withTrailer value trailer (expandedAt config depth)

private def normalizedClause (text : String) : String :=
  let text := text.trimAscii.toString
  if text.endsWith "." then (text.dropEnd 1).toString else text

private def sentence (text : String) : String := normalizedClause text ++ "."

private def tacticSpelling (tree : TacticTree) : String := syntaxString tree.event.source

private def startsWithToken (tree : TacticTree) (token : String) : Bool :=
  let spelling := tacticSpelling tree
  spelling == token || spelling.startsWith (token ++ " ") ||
    spelling.startsWith (token ++ "\n")

private def eventGoalMarker (config : Config) (event : TacticEvent) : IO Explanation := do
  if !config.goalMarkers then return .empty
  match ← English.goalInfo event config.language with
  | some goal => return .goalState goal
  | none => return .empty

private def targetText (config : Config) (event : TacticEvent) : IO String := do
  let some goal := event.target | return "the current goal"
  let context := { event.source.context with mctx := event.source.info.mctxBefore }
  context.runMetaM {} do
    goal.withContext do
      return ← English.proposition (← goal.getType) config.language

private def goalTextAfter (config : Config) (event : TacticEvent) (goal : MVarId) : IO String := do
  let context := { event.source.context with mctx := event.source.info.mctxAfter }
  context.runMetaM {} do
    goal.withContext do
      return ← English.proposition (← goal.getType) config.language

private def firstProducedText? (config : Config) (event : TacticEvent) : IO (Option String) := do
  let some goal := event.produced[0]? | return none
  return some (← goalTextAfter config event goal)

/-- Proposition-valued local declarations introduced by a tactic.

For a source `have h : P := ...`, the goal before and after the tactic is
usually still the theorem's final goal; what changed is the local context.
Reading the produced goal itself therefore repeats the final conclusion.  The
Massot--Miller narration instead needs the context delta, namely `P`. -/
private def introducedFacts (config : Config) (event : TacticEvent) : IO (Array String) := do
  let some target := event.target | return #[]
  let beforeContext := { event.source.context with mctx := event.source.info.mctxBefore }
  let beforeIds ← beforeContext.runMetaM {} do
    target.withContext do
      let declaration ← target.getDecl
      return declaration.lctx.decls.toArray.filterMap id |>.map (·.fvarId)
  let afterContext := { event.source.context with mctx := event.source.info.mctxAfter }
  afterContext.runMetaM {} do
    let mut facts : Array String := #[]
    for goal in event.produced do
      let goalFacts ← goal.withContext do
        let declaration ← goal.getDecl
        let mut result : Array String := #[]
        for localDecl in declaration.lctx.decls.toArray.filterMap id do
          if beforeIds.contains localDecl.fvarId then continue
          if localDecl.isAuxDecl || localDecl.isImplementationDetail ||
              localDecl.binderInfo == .instImplicit then
            continue
          if ← isProp localDecl.type then
            result := result.push (← English.proposition localDecl.type config.language)
        return result
      facts := facts ++ goalFacts
    return facts.toList.eraseDups.toArray

private def localDecls (context : LocalContext) : List LocalDecl :=
  context.decls.toArray.filterMap id |>.toList

private def withSyntheticContext {α : Type} (goal : SyntheticGoal) (action : MetaM α) : MetaM α :=
  withLCtx goal.localContext #[] do
    withLocalInstances (localDecls goal.localContext) action

private def syntheticGoalMarker (config : Config) (goal : SyntheticGoal) : MetaM Explanation := do
  if !config.goalMarkers then return .empty
  return .goalState (← withSyntheticContext goal <|
    English.goalInfoFrom goal.localContext goal.target none config.language)

private def referenceName (reference : Expr) : MetaM String := do
  match reference.consumeMData with
  | .fvar id => return (← id.getDecl).userName.toString
  | .const name _ => return name.toString
  | other => return ← Ontology.exprLatex other

private def humanizeReferenceName (name : String) : String :=
  let short := (name.splitOn ".").getLast?.getD name
  short.replace "_" " "

private def referenceLabel (reference : Expr) : MetaM String := do
  match reference.consumeMData with
  | .const name _ => return humanizeReferenceName name.toString
  | _ => referenceName reference

private def referenceTooltip? (config : Config) (reference : Expr) : MetaM (Option String) := do
  try
    match reference.consumeMData with
    | .fvar id =>
        let declaration ← id.getDecl
        -- Local proof names are source identifiers, not mathematical LaTeX.
        -- Keep the exact name searchable in the hover without asking KaTeX to
        -- interpret underscores and generated identifier punctuation.
        return some s!"{declaration.userName} : {← English.proposition declaration.type config.language}"
    | .const name _ =>
        let information ← getConstInfo name
        return some (← withLCtx {} #[] <| English.statement information.type config.language)
    | _ => return none
  catch _ => return none

private def referenceDocument (config : Config) (depth : Nat)
    (reference : Expr) : MetaM Explanation := do
  let name ← referenceName reference
  -- Elaborator-generated declarations are proof plumbing, not names a reader
  -- can use.  Retain the proof subtree but give the reference a discourse
  -- role instead of leaking an unstable `_uniq`/`_hyg` identifier.
  if name.contains "_uniq" || name.contains "_hyg" then
    return .str "the preceding result"
  let visible : Explanation := .str (← referenceLabel reference)
  let visible :=
    if config.formalTrailers then
      trailerAt config depth visible (.str s!" (formal name: \\({name}\\))")
    else visible
  if !config.referenceTooltips then return visible
  match ← referenceTooltip? config reference with
  | some tooltip => return .withToolTip visible tooltip
  | none => return visible

private def childBlock (children : Array Explanation) : Explanation :=
  match children.size with
  | 0 => .empty
  | 1 => .indent children[0]!
  | _ => .enumList children

private def claim (config : Config) (depth : Nat) (target : String)
    (details : Explanation) : Explanation :=
  let target := normalizedClause target
  replacementAt config depth
    (.str s!"One can see that {target}.")
    (.join #[
      .paragraphBreak,
      .str s!"Claim: {target}. ",
      .indent details
    ])

private partial def renderSyntheticCore (config : Config) (depth : Nat)
    (tree : SyntheticTactic) (rootChildren? : Option (Array Explanation) := none) :
    MetaM Explanation := do
  let .node kind goal proofTerm children := tree
  let marker ← syntheticGoalMarker config goal
  let childDocuments ← match rootChildren? with
    | some value => pure value
    | none => children.mapM (renderSyntheticCore config (depth + 1) ·)
  let childrenBlock := childBlock childDocuments
  let body ← withSyntheticContext goal do
    match kind with
    | .intro name domain =>
        let introduction ←
          if ← isProp domain then
            pure s!"Suppose {sentence (← English.proposition domain config.language)} "
          else
            pure s!"Let \\({name}\\) be an element of {← Ontology.inlineMath domain}. "
        return .join #[.str introduction, childrenBlock]
    | .letBinding name type value =>
        if ← isProp type then
          return .join #[
            .str s!"Fact {name}: {sentence (← English.proposition type config.language)} ",
            childrenBlock]
        else
          return .join #[
            .str s!"Let \\({name} = {← Ontology.exprLatex value}\\). ",
            childrenBlock]
    | .constructor _ =>
        return .join #[
          .str "It suffices to prove each of the following claims.",
          childrenBlock]
    | .existsWitness witness =>
        return .join #[
          .str s!"Take {← Ontology.inlineMath witness} as a witness. ",
          childrenBlock]
    | .chooseLeft =>
        return .join #[.str "It suffices to prove the left alternative. ", childrenBlock]
    | .chooseRight =>
        return .join #[.str "It suffices to prove the right alternative. ", childrenBlock]
    | .assumption name =>
        let reference := mkFVar <|
          (goal.localContext.decls.toArray.filterMap id).find? (·.userName == name)
            |>.map (·.fvarId) |>.getD { name }
        return .join #[
          .str "This is exactly our hypothesis ",
          ← referenceDocument config depth reference,
          .str "."]
    | .projection index =>
        return .join #[
          .str s!"Taking component {index + 1} of the preceding fact gives the result. ",
          childrenBlock]
    | .apply reference =>
        return .join #[
          .str "Using ", ← referenceDocument config depth reference,
          .str ", it suffices to prove the following.", childrenBlock]
    | .exact reference =>
        return .join #[
          .str "The result follows from ", ← referenceDocument config depth reference,
          .str "."]
    | .reflexivity => return .str "The two sides are equal by reflexivity."
    | .contradiction =>
        return .join #[.str "A contradiction proves the goal. ", childrenBlock]
    | .cases recursor =>
        return .join #[
          .str s!"Consider the cases supplied by {recursor}. ", childrenBlock]
    | .rewrite principle =>
        return .join #[
          .str s!"Rewriting by {principle} reduces the goal to the following. ",
          childrenBlock]
    | .whnf _before _after =>
        let short : Explanation := .str "By definition this is the same goal."
        let detailed : Explanation := .join #[
          .str "Unfolding reducible notation puts the proposition in the form required by the next step. ",
          childrenBlock]
        return replacementAt config depth short detailed
    | .opaque =>
        return replacementAt config depth
          (.str "The checked term proves the goal.")
          (.str s!"The kernel-checked proof term is {← Ontology.inlineMath proofTerm}.")
  return .join #[marker, body]

/-- Render a proof-term-derived tree in the environment retained by the
frontend.  Exposing this operation keeps term-only declarations on the same
explanation path as tactic fallbacks. -/
def renderSynthetic (context : Elab.ContextInfo) (config : Config)
    (tree : SyntheticTactic) : IO Explanation :=
  context.runMetaM {} <| renderSyntheticCore config 0 tree

private def renderDecompiled (config : Config) (depth : Nat) (tree : TacticTree)
    (sourceChildren : Array Explanation) : IO (Option Explanation) := do
  let some synthetic ← Decompiler.fromEvent tree.event | return none
  let some target := tree.event.target | return none
  let context := { tree.event.source.context with mctx := tree.event.source.info.mctxAfter }
  context.runMetaM {} do
    target.withContext do
      return some (← renderSyntheticCore config depth synthetic
        (if sourceChildren.isEmpty then none else some sourceChildren))

/-- Continuation passed to a registry entry. -/
abbrev Recurse := Nat → TacticTree → IO Explanation

/-- A describer either emits a document or declines without consuming the node. -/
abbrev Describer := Config → Recurse → Nat → TacticTree → IO (Option Explanation)

private def describeChildren (recurse : Recurse) (depth : Nat) (tree : TacticTree) :
    IO (Array Explanation) := tree.children.mapM (recurse (depth + 1) ·)

private def introDescriber : Describer := fun config recurse depth tree => do
  unless startsWithToken tree "intro" || startsWithToken tree "rintro" do return none
  let marker ← eventGoalMarker config tree.event
  let nextTarget ← firstProducedText? config tree.event
  let target ← targetText config tree.event
  let wording :=
    if normalizedClause target |>.startsWith "if " then
      "Assume the hypothesis. "
    else
      "Introduce the arbitrary objects and hypotheses. "
  let children ← describeChildren recurse depth tree
  let continuation := if children.isEmpty then .empty else childBlock children
  let transition := nextTarget.map (fun value =>
    .str s!"It remains to prove {sentence value} ") |>.getD .empty
  return some (.join #[marker, .str wording, transition, continuation])

private def constructorDescriber : Describer := fun config recurse depth tree => do
  unless startsWithToken tree "constructor" || startsWithToken tree "refine ⟨" do return none
  let marker ← eventGoalMarker config tree.event
  let children ← describeChildren recurse depth tree
  let mut claims := #[]
  for index in Array.range tree.children.size do
    if let some child := tree.children[index]? then
      let target ← targetText config child.event
      let details := children[index]?.getD .empty
      claims := claims.push (claim config (depth + 1) target details)
  let summary := if claims.size == 2 then
      "By definition it suffices to prove the two claims below."
    else "By definition it suffices to prove each claim below."
  return some (.join #[marker, .str summary, .enumList claims])

private def intermediateDescriber : Describer := fun config recurse depth tree => do
  unless startsWithToken tree "have" || startsWithToken tree "suffices" ||
      startsWithToken tree "show" do return none
  let marker ← eventGoalMarker config tree.event
  let children ← describeChildren recurse depth tree
  if startsWithToken tree "have" then
    let facts ← introducedFacts config tree.event
    unless facts.isEmpty do
      let text := if facts.size == 1 then
          s!"We have {sentence facts[0]!} "
        else
          "We have the following facts: " ++
            String.intercalate " " (facts.toList.map sentence) ++ " "
      -- A sequence of `have` statements is a discourse sequence, not a tower
      -- of nested copies of the unchanged final goal.
      return some (.join #[marker, .str text, .join children])
  let mut claims := #[]
  for index in Array.range tree.children.size do
    if let some child := tree.children[index]? then
      claims := claims.push <| claim config (depth + 1) (← targetText config child.event)
        (children[index]?.getD .empty)
  let leadText := if startsWithToken tree "suffices" || startsWithToken tree "show" then
      "It suffices to establish the following."
    else "We first establish the following intermediate claim."
  return some (.join #[marker, .str leadText, childBlock claims])

private def rewriteDescriber : Describer := fun config recurse depth tree => do
  unless startsWithToken tree "rw" || startsWithToken tree "simp" ||
      startsWithToken tree "simpa" || startsWithToken tree "dsimp" ||
      startsWithToken tree "change" || startsWithToken tree "unfold" do return none
  let marker ← eventGoalMarker config tree.event
  let children ← describeChildren recurse depth tree
  let operation :=
    if startsWithToken tree "rw" then "Rewriting"
    else "Simplification"
  let next ← firstProducedText? config tree.event
  let wording := match next with
    | some target =>
        s!"{operation} reduces the goal to {sentence target} "
    | none => s!"{operation} proves the goal."
  let spelling := tacticSpelling tree
  let hidden := trailerAt config depth .empty (.str s!" Lean: {spelling}")
  return some (.join #[marker, .str wording, hidden, childBlock children])

private def casesDescriber : Describer := fun config recurse depth tree => do
  unless startsWithToken tree "cases" || startsWithToken tree "rcases" ||
      startsWithToken tree "obtain" || startsWithToken tree "induction" do return none
  let marker ← eventGoalMarker config tree.event
  let children ← describeChildren recurse depth tree
  let wording := if startsWithToken tree "induction" then
      "Proceed by induction through the following cases."
    else "Unpack the hypothesis and consider the resulting cases."
  return some (.join #[marker, .str wording, childBlock children])

private def calculationDescriber : Describer := fun config _recurse depth tree => do
  unless startsWithToken tree "calc" do return none
  let some calculation ← Decompiler.calculationFromEvent tree.event | return none
  let marker ← eventGoalMarker config tree.event
  let context := { tree.event.source.context with mctx := tree.event.source.info.mctxAfter }
  let (start, steps) ← context.runMetaM {} do
    withSyntheticContext calculation.goal do
      let start ← Ontology.inlineMath calculation.start
      let mut steps : Array (ComputationStep Explanation) := #[]
      for step in calculation.steps do
        let relation ← match Ontology.headConstant? step.relation with
          | some ``Eq => pure "="
          | some name =>
              let text := name.toString
              if text.endsWith ".le" then pure "≤"
              else if text.endsWith ".lt" then pure "<"
              else Ontology.exprLatex step.relation
          | none => Ontology.exprLatex step.relation
        steps := steps.push {
          rel := relation
          rhs := ← Ontology.inlineMath step.rhs
          expl := ← renderSyntheticCore config (depth + 1) step.proof
        }
      pure (start, steps)
  return some (.join #[marker, .computation start steps])

private def directDescriber : Describer := fun config recurse depth tree => do
  unless startsWithToken tree "exact" || startsWithToken tree "apply" ||
      startsWithToken tree "refine" || startsWithToken tree "assumption" ||
      startsWithToken tree "rfl" || startsWithToken tree "contradiction" ||
      startsWithToken tree "exact?" do return none
  let children ← describeChildren recurse depth tree
  -- Preserve the theorem explicitly cited by `exact`.  Decompiling the
  -- expected proposition first can otherwise expose reducible coercions and
  -- misdescribe this source step as a definitional equality.
  if startsWithToken tree "exact" then
    if let some term := tree.event.proofTerm? then
      let reference := term.getAppFn.consumeMData
      if reference.isConst || reference.isFVar then
        let some target := tree.event.target | return none
        let marker ← eventGoalMarker config tree.event
        let context := { tree.event.source.context with mctx := tree.event.source.info.mctxAfter }
        return some (← context.runMetaM {} do
          target.withContext do
            return .join #[marker, .str "The result follows from ",
              ← referenceDocument config depth reference, .str ".", .join children])
  if startsWithToken tree "apply" || startsWithToken tree "refine" then
    if let some term := tree.event.proofTerm? then
      let reference := term.getAppFn.consumeMData
      if reference.isConst || reference.isFVar then
        let some target := tree.event.target | return none
        let marker ← eventGoalMarker config tree.event
        let context := { tree.event.source.context with mctx := tree.event.source.info.mctxAfter }
        return some (← context.runMetaM {} do
          target.withContext do
            return .join #[marker, .str "By ",
              ← referenceDocument config depth reference,
              .str ", it suffices to verify the following. ", childBlock children])
  renderDecompiled config depth tree children

private def automationDescriber : Describer := fun config recurse depth tree => do
  unless startsWithToken tree "aesop" || startsWithToken tree "omega" ||
      startsWithToken tree "linarith" || startsWithToken tree "nlinarith" ||
      startsWithToken tree "ring" || startsWithToken tree "norm_num" ||
      startsWithToken tree "tauto" || startsWithToken tree "decide" do return none
  let children ← describeChildren recurse depth tree
  match ← renderDecompiled config depth tree children with
  | some detailed =>
      let marker ← eventGoalMarker config tree.event
      return some (.join #[marker,
        replacementAt config depth
          (.str "The goal follows by a checked calculation.") detailed])
  | none => return none

private def fallbackDescriber : Describer := fun config recurse depth tree => do
  let children ← describeChildren recurse depth tree
  match ← renderDecompiled config depth tree children with
  | some explanation => return some explanation
  | none =>
      let marker ← eventGoalMarker config tree.event
      let formal := trailerAt config depth .empty (.str s!" Lean: {tacticSpelling tree}")
      return some (.join #[marker, .str "The checked step proves the current goal.",
        formal, childBlock children])

/-- Priority order is part of the behavior: specific source-semantic handlers
run before the proof-term and inert fallbacks. -/
def defaultRegistry : Array Describer := #[
  introDescriber,
  constructorDescriber,
  intermediateDescriber,
  rewriteDescriber,
  casesDescriber,
  calculationDescriber,
  directDescriber,
  automationDescriber,
  fallbackDescriber
]

partial def describeNodeWith (registry : Array Describer) (config : Config)
    (depth : Nat) (tree : TacticTree) : IO Explanation := do
  let recurse : Recurse := describeNodeWith registry config
  for describer in registry do
    if let some result ← describer config recurse depth tree then return result
  return .empty

def describeNode (config : Config := {}) (tree : TacticTree) : IO Explanation :=
  describeNodeWith defaultRegistry config 0 tree

def describeForestWith (registry : Array Describer) (config : Config := {})
    (forest : Array TacticTree) : IO (Array Explanation) :=
  forest.mapM (describeNodeWith registry config 0)

def describeForest (config : Config := {}) (forest : Array TacticTree) :
    IO (Array Explanation) := describeForestWith defaultRegistry config forest

/-- Build one public theorem record from a fully elaborated source module. -/
def lemmaInfoWith (registry : Array Describer) (module : ElaboratedModule) (name : Name)
    (config : Config := {}) :
    IO (Option LemmaInfo) := do
  let some context := module.contextFor name | return none
  let (statement, declarationHover) ← context.runMetaM {} do
    let information ← getConstInfo name
    let statement ← withLCtx {} #[] <| English.statement information.type config.language
    let hover ← withLCtx {} #[] <|
      LeanHoverInfo.ofDeclaration "" name
    return (statement, hover)
  let forest := module.tacticForestFor name
  let explanations : Array Explanation ← if forest.isEmpty then do
      match ← Decompiler.fromDeclaration context name with
      | some synthetic => pure #[← renderSynthetic context config synthetic]
      | none => pure #[]
    else
      describeForestWith registry config forest
  return some {
    name := name.toString
    statement
    declarationHover? := some declarationHover
    explanations := #[.join explanations]
  }

def lemmaInfo (module : ElaboratedModule) (name : Name) (config : Config := {}) :
    IO (Option LemmaInfo) := lemmaInfoWith defaultRegistry module name config

/-- Generate a document with an application-supplied tactic registry.  Domain
describers can be prepended to `defaultRegistry`; the final fallback should be
retained so every checked proof remains renderable. -/
def documentWith (registry : Array Describer) (module : ElaboratedModule)
    (names : Array Name) (config : Config := {}) : IO Document :=
  names.filterMapM (lemmaInfoWith registry module · config)

def document (module : ElaboratedModule) (names : Array Name) (config : Config := {}) :
    IO Document := documentWith defaultRegistry module names config

end Informalization.MassotMiller.Describe
