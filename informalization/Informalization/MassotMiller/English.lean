/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller
import Informalization.MassotMiller.InfoTree
import Informalization.MassotMiller.Ontology

/-!
# Entity, proposition, statement, and proof-state explainers

This is the natural-language half of the Massot–Miller theorem explainer.  It
maps elaborated Lean expressions and local contexts through the English
ontology, retaining exact goal states from `TacticInfo.mctxBefore`.
-/

namespace Informalization.MassotMiller.English

open Lean Meta
open Informalization.MassotMiller
open Informalization.MassotMiller.InfoTree
open Informalization.MassotMiller.Ontology

/-- Recursive proposition renderer supplied to an application handler. -/
abbrev PropositionRecurse := Expr → MetaM String

/-- A domain extension for rendering propositions headed by `kind`.

Returning `none` leaves the proposition to the backend's generic renderer.
The recursive renderer lets an extension preserve the standard treatment of
sub-propositions without copying the backend. -/
structure PropositionHandler where
  kind : Name
  run : PropositionRecurse → Expr → Array Expr → MetaM (Option String)

/-- Language configuration for one informalization run. -/
structure Config where
  ontologyRegistry : Ontology.Registry := Ontology.defaultRegistry
  propositionHandlers : Array PropositionHandler := #[]
  /-- Optional checked semantic renderer.  It is supplied out-of-band by a
  theory profile, so extracting a source module never has to import renderer
  attributes or change proof elaboration. -/
  checkedPropositionRenderer? : Option (Expr → MetaM (Option String)) := none

def expressionLatex (expression : Expr) (_config : Config := {}) : MetaM String :=
  Ontology.exprLatex expression

def inlineMath (expression : Expr) (config : Config := {}) : MetaM String := do
  return "\\(" ++ (← expressionLatex expression config) ++ "\\)"

private def lastArgument? (arguments : Array Expr) (offset : Nat := 0) : Option Expr :=
  if offset < arguments.size then arguments[arguments.size - 1 - offset]? else none

private def binaryArguments? (expression : Expr) : Option (Expr × Expr) := do
  let arguments := expression.getAppArgs
  let right ← lastArgument? arguments
  let left ← lastArgument? arguments 1
  return (left, right)

private def parenthesize (value : String) : String := "(" ++ value ++ ")"

/-- Symbolic proposition-to-English mapper.  Unknown predicates retain their
exact elaborated expression through the LaTeX fallback. -/
partial def proposition (expression : Expr) (config : Config := {}) : MetaM String := do
  let expression ← instantiateMVars expression
  if let some renderer := config.checkedPropositionRenderer? then
    if let some rendered ← renderer expression then
      return "\\(" ++ rendered ++ "\\)"
  match expression with
  | .forallE name domain body binderInfo =>
      if body.hasLooseBVar 0 then
        withLocalDecl name binderInfo domain fun fvar => do
          let declaration ← fvar.fvarId!.getDecl
          let entity ←
            match (← Ontology.build (← getLCtx) config.ontologyRegistry).find?
                (·.id == fvar.fvarId!) with
            | some entity => pure entity
            | none =>
                pure {
                  id := fvar.fvarId!
                  name := declaration.userName
                  noun := none
                }
          let domainPhrase :=
            let nounText := entity.noun.map (·.inlineText) |>.getD "objects"
            let adjectives := String.intercalate " " (entity.adjectives.toList.map (·.text))
            let adjectivePrefix := if adjectives.isEmpty then "" else adjectives ++ " "
            adjectivePrefix ++ nounText
          let instantiatedBody := body.instantiate1 fvar
          if let .forallE _ premise consequence _ := instantiatedBody then
            if !consequence.hasLooseBVar 0 && (← isProp premise) then
              let premiseText ← proposition premise config
              let subject := domainPhrase ++ s!" \\({declaration.userName}\\)"
              if premiseText == subject ++ " is good" then
                return s!"for every good {domainPhrase} \\({declaration.userName}\\), " ++
                  (← proposition consequence config)
          let bodyText ← proposition instantiatedBody config
          return s!"for every {domainPhrase} \\({declaration.userName}\\), {bodyText}"
      else if ← isProp domain then
        return s!"if {← proposition domain config} then {← proposition body config}"
      else
        return "for every " ++ (← inlineMath domain config) ++ ", " ++
          (← proposition body config)
  | _ =>
      let head := Ontology.headConstant? expression
      let arguments := expression.getAppArgs
      if let some kind := head then
        if let some handler := config.propositionHandlers.find? (·.kind == kind) then
          let recurse : PropositionRecurse := fun value => proposition value config
          if let some rendered ← handler.run recurse expression arguments then return rendered
      match head with
      | some ``Iff =>
          let some (left, right) := binaryArguments? expression
            | return ← inlineMath expression config
          return s!"{← proposition left config} if and only if {← proposition right config}"
      | some ``And =>
          let some (left, right) := binaryArguments? expression
            | return ← inlineMath expression config
          return s!"{← proposition left config} and {← proposition right config}"
      | some ``Or =>
          let some (left, right) := binaryArguments? expression
            | return ← inlineMath expression config
          return s!"{← proposition left config} or {← proposition right config}"
      | some ``Not =>
          let some value := lastArgument? arguments | return ← inlineMath expression config
          return "it is not the case that " ++ parenthesize (← proposition value config)
      | some ``Eq => return ← inlineMath expression config
      | some ``Function.Injective =>
          let some function := lastArgument? arguments | return ← inlineMath expression config
          return (← inlineMath function config) ++ " is injective"
      | some ``Function.Surjective =>
          let some function := lastArgument? arguments | return ← inlineMath expression config
          return (← inlineMath function config) ++ " is surjective"
      | some kind =>
          let kindString := kind.toString
          if kindString.endsWith ".le" then
            return ← inlineMath expression config
          else if kindString.endsWith ".lt" then
            return ← inlineMath expression config
          else if kindString == "Membership.mem" || kindString.endsWith ".Mem" then
            let some (element, set) := binaryArguments? expression
              | return ← inlineMath expression config
            return (← inlineMath element config) ++ " is an element of " ++
              (← inlineMath set config)
          else if kindString == "Set.Subset" || kindString.endsWith ".Subset" then
            let some (left, right) := binaryArguments? expression
              | return ← inlineMath expression config
            return (← inlineMath left config) ++ " is a subset of " ++
              (← inlineMath right config)
          else return ← inlineMath expression config
      | none => return ← inlineMath expression config

private def entityName (entity : Entity) : MetaM String := do
  match entity.noun with
  | some noun => match noun.typePayload with
      | some payload =>
          if noun.kind == `Element then return entity.name.toString
          return entity.name.toString ++ " : " ++ (← Ontology.exprLatex payload.type)
      | none => return entity.name.toString
  | none => return entity.name.toString

private def entityShape (entity : Entity) : String :=
  entity.singularDescription ++ "\u0000" ++ entity.pluralDescription

private def crossReferences (left right : Entity) : Bool :=
  left.dependencies.contains right.id || right.dependencies.contains left.id

private def mayMerge (entity : Entity) (group : Array Entity) : Bool :=
  match group[0]? with
  | none => false
  | some first => entityShape entity == entityShape first &&
      group.all (fun other => !crossReferences entity other)

private def entityGroups (entities : Array Entity) : Array (Array Entity) := Id.run do
  let mut groups : Array (Array Entity) := #[]
  for entity in entities do
    match groups.back? with
    | some group =>
        if mayMerge entity group then
          groups := groups.pop.push (group.push entity)
        else
          groups := groups.push #[entity]
    | none => groups := #[#[entity]]
  return groups

private def definingGroup (group : Array Entity) : MetaM String := do
  let some first := group[0]? | return ""
  let names ← group.toList.mapM entityName
  if let some noun := first.noun then
    if noun.kind == `Element then
      if let some payload := noun.typePayload then
        let renderedType ← expressionLatex payload.type
        return "\\(" ++ String.intercalate ", " names ++
          " \\in " ++ renderedType ++ "\\)"
  if group.size == 1 then
    let description := first.singularDescription
    let predicate := match description.dropPrefix? "is " with
      | some value => value.toString
      | none => description
    return "\\(" ++ names.headD "" ++ "\\) be " ++ predicate
  else
    let description := first.pluralDescription
    let predicate := match description.dropPrefix? "are " with
      | some value => value.toString
      | none => description
    let names := names.map (fun name => "\\(" ++ name ++ "\\)")
    return Informalization.Grammar.joinAnd names ++ " be " ++ predicate

private def joinClauses : List String → String
  | [] => ""
  | [value] => value
  | [left, right] => left ++ ", and " ++ right
  | value :: rest => value ++ "; " ++ joinClauses rest

private def splitQuantifiedClause? (value : String) : Option (String × String) :=
  if !value.startsWith "for every" then none
  else match value.splitOn ", " with
    | leading :: bodyParts =>
        if bodyParts.isEmpty then none
        else some (leading, String.intercalate ", " bodyParts)
    | [] => none

private def mergeQuantifiedClauses (values : Array String) : Array String := Id.run do
  let mut groups : Array (String × Array String) := #[]
  for value in values do
    match splitQuantifiedClause? value with
    | none => groups := groups.push ("", #[value])
    | some (leading, body) =>
        match groups.findIdx? (fun group => group.1 == leading) with
        | some index =>
            if let some group := groups[index]? then
              groups := groups.setIfInBounds index (leading, group.2.push body)
        | none => groups := groups.push (leading, #[body])
  return groups.map fun (leading, bodies) =>
    if leading.isEmpty then bodies[0]?.getD ""
    else leading ++ ", " ++ Informalization.Grammar.joinAnd bodies.toList

def definingParagraph (entities : Array Entity) : MetaM String := do
  let clauses ← (entityGroups entities).toList.mapM definingGroup
  if clauses.isEmpty then return ""
  return "Let " ++ joinClauses clauses ++ "."

private def isProvided (entities : Array Entity) (name : Name) : Bool :=
  entities.any (·.provides.contains name)

private def expressionUses (expression : Expr) (id : FVarId) : Bool :=
  (Lean.collectFVars {} expression).fvarIds.contains id

/-- Render a complete local context to the public `ContextItem` schema. -/
def contextItems (localContext : LocalContext) (target : Expr) (config : Config := {}) :
    MetaM (Array ContextItem) := do
  let entities ← Ontology.build localContext config.ontologyRegistry
  let mut items : Array ContextItem := #[]
  for entity in entities do
    let declaration ← entity.id.getDecl
    let valueExpr? := match declaration with
      | .ldecl (value := value) .. => some value
      | _ => none
    let value? ← valueExpr?.mapM (expressionLatex · config)
    items := items.push {
      name := some (← entityName entity)
      value := value?
      singularType := entity.singularDescription
      pluralType := some entity.pluralDescription
      provides := entity.provides.map (·.toString)
      used := expressionUses target entity.id
    }
  for declaration in localContext.decls do
    let some declaration := declaration | continue
    if declaration.isAuxDecl then continue
    if entities.any (·.id == declaration.fvarId) || isProvided entities declaration.userName then
      continue
    if declaration.binderInfo == .instImplicit then continue
    if ← isProp declaration.type then
      items := items.push {
        singularType := ← proposition declaration.type config
        provides := #[declaration.userName.toString]
        used := true
        implDetail := declaration.isImplementationDetail
        auxDecl := declaration.isAuxDecl
      }
    else
      let valueExpr? := match declaration with
        | .ldecl (value := value) .. => some value
        | _ => none
      let value? ← valueExpr?.mapM (expressionLatex · config)
      items := items.push {
        name := some declaration.userName.toString
        value := value?
        singularType := "is an element of " ++ (← inlineMath declaration.type config)
        pluralType := some ("are elements of " ++ (← inlineMath declaration.type config))
        used := expressionUses target declaration.fvarId
        implDetail := declaration.isImplementationDetail
        auxDecl := declaration.isAuxDecl
      }
  return items

/-- A public proof-state record from an exact local context and target. -/
def goalInfoFrom (localContext : LocalContext) (target : Expr)
    (caseName : Option String := none) (config : Config := {}) : MetaM GoalInfo := do
  let localInstances ← getLocalInstances
  withLCtx localContext localInstances do
    let targetText ← proposition target config
    return {
      target := targetText
      paragraphForm := targetText
      items := ← contextItems localContext target config
      caseName
    }

/-- Exact pre-tactic goal state from a live `TacticInfo`. -/
def goalInfo (event : TacticEvent) (config : Config := {}) : IO (Option GoalInfo) := do
  let some goal := event.target | return none
  let context := { event.source.context with mctx := event.source.info.mctxBefore }
  context.runMetaM {} do
    goal.withContext do
      let declaration ← goal.getDecl
      return some (← goalInfoFrom declaration.lctx declaration.type
        (event.source.info.goalsBefore.head?.bind fun _ =>
          let name := declaration.userName
          if name.isAnonymous || name.toString.startsWith "_" then none else some name.toString)
        config)

/-- Natural theorem statement from its elaborated type. -/
def statement (type : Expr) (config : Config := {}) : MetaM String := do
  forallTelescope type fun _ conclusion => do
    let localContext ← getLCtx
    let entities ← Ontology.build localContext config.ontologyRegistry
    let introduction ← definingParagraph entities
    let mut assumptions : Array String := #[]
    for declaration in localContext.decls do
      let some declaration := declaration | continue
      if entities.any (·.id == declaration.fvarId) ||
          isProvided entities declaration.userName || declaration.binderInfo == .instImplicit then
        continue
      if ← isProp declaration.type then
        assumptions := assumptions.push (← proposition declaration.type config)
    let ordinary := assumptions.filter (fun value => !value.startsWith "for every")
    let quantified := mergeQuantifiedClauses <|
      assumptions.filter (fun value => value.startsWith "for every")
    let assumeOrdinary := if ordinary.isEmpty then "" else
      " Assume " ++ Informalization.Grammar.joinAnd ordinary.toList ++ "."
    let assumeQuantified := if quantified.isEmpty then "" else
      " Assume also that " ++ joinClauses quantified.toList ++ "."
    let suppose := assumeOrdinary ++ assumeQuantified
    let result ← proposition conclusion config
    if introduction.isEmpty && suppose.isEmpty then return result ++ "."
    return introduction ++ suppose ++ " Then " ++ result ++ "."

end Informalization.MassotMiller.English
