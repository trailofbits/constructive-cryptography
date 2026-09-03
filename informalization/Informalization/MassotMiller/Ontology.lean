/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import LeanTeX.MathlibSyntax
import Informalization.ExprLatex
import Informalization.Grammar

/-!
# Massot–Miller's English ontology

These records follow the ontology displayed in the talks.  In particular,
`Adjective.expr` and `Accessory.expr` retain the actual elaborated `Lean.Expr`;
they are not string stand-ins.
-/

namespace Informalization.MassotMiller.Ontology

open Lean Meta
open Informalization.Grammar

structure NounTypePayload where
  type : Expr
  text : String
  pluralText : String

structure Noun where
  kind : Name
  article : Article
  text : String
  pluralText : String
  inlineText : String
  inlinePluralText : String
  typePayload : Option NounTypePayload := none

structure Adjective where
  kind : Name
  expr : Expr
  article : Article
  text : String

structure Accessory where
  kind : Name
  expr : Expr
  text : String

structure Entity where
  id : FVarId
  name : Name
  noun : Option Noun := none
  provides : Array Name := #[]
  adjectives : Array Adjective := #[]
  accessories : Array Accessory := #[]
  dependencies : Array FVarId := #[]

abbrev Context := Array Entity

/-- Miller's actual LeanTeX registry is the expression fallback used by the
Massot–Miller path.  It reads local free-variable names from the live context.
MathJax-only `\texttip` output is disabled because the standalone reader uses
KaTeX and provides its own HTML interactions. -/
def exprLatex (expr : Expr) : MetaM String := do
  let expression ← instantiateMVars expr
  let rendered ← LeanTeX.run_latexPP expression {
    displayStyle := false
    mathjaxTooltips := false
  }
  if rendered.contains "\\informalizationRaw{" then
    Informalization.exprToLatexMeta expression
  else
    return rendered

def inlineMath (expr : Expr) : MetaM String := do
  return "\\(" ++ (← exprLatex expr) ++ "\\)"

private def noun (kind : Name) (text plural : String) : Noun :=
  { kind
    article := (seedArticle text).1
    text
    pluralText := plural
    inlineText := text
    inlinePluralText := plural }

private def elementNoun (type : Expr) : MetaM Noun := do
  let rendered ← inlineMath type
  return {
    noun `Element ("element of " ++ rendered) ("elements of " ++ rendered) with
    typePayload := some { type, text := rendered, pluralText := rendered }
  }

inductive Edit where
  | noun (value : Noun)
  | adjective (kind : Name) (text : String) (evidence : Expr)
  | accessory (kind : Name) (text : String) (evidence : Expr)

/-- A hand-crafted `@[english_param const.X]`-style handler. -/
structure Handler where
  kind : Name
  run : Expr → Array Expr → Option (Expr × Edit)

/-- A noun assigned from the head constructor of a value's type.  This is the
type-level counterpart of Miller's `english_param` vocabulary: applications
can say that a value of `PDS X Y` is a probabilistic system without changing
the generic renderer. -/
structure TypeHandler where
  kind : Name
  text : String
  pluralText : String

structure Registry where
  propositionHandlers : Array Handler := #[]
  typeHandlers : Array TypeHandler := #[]

private def argumentFromEnd? (arguments : Array Expr) (offset : Nat := 0) : Option Expr :=
  if offset < arguments.size then arguments[arguments.size - 1 - offset]? else none

def subjectAdjective (kind : Name) (surface : String) : Handler :=
  { kind
    run := fun proposition arguments => do
      let subject ← argumentFromEnd? arguments
      return (subject, .adjective kind surface proposition) }

def subjectNoun (kind : Name) (surface plural : String) : Handler :=
  { kind
    run := fun _ arguments => do
      let subject ← argumentFromEnd? arguments
      return (subject, .noun (noun kind surface plural)) }

/-- The domain-neutral ontology vocabulary shipped with the backend.

Applications can extend this registry with their own nouns and adjectives;
unknown concepts remain available through the exact LeanTeX fallback. -/
def defaultRegistry : Registry := {
  propositionHandlers := #[
    subjectAdjective ``Function.Injective "injective",
    subjectAdjective ``Function.Surjective "surjective",
    subjectAdjective ``Nonempty "nonempty",
    subjectAdjective "Fintype".toName "finite",
    subjectNoun "AddCommGroup".toName "additive commutative group" "additive commutative groups",
    subjectNoun "AddGroup".toName "additive group" "additive groups",
    subjectNoun "Group".toName "group" "groups"
  ]
}

def headConstant? (expr : Expr) : Option Name :=
  match expr.getAppFn.consumeMData with
  | .const name _ => some name
  | _ => none

private def dependenciesOf (expr : Expr) : Array FVarId :=
  (Lean.collectFVars {} expr).fvarIds

private def nondependentFunctionNoun (type domain body : Expr) (registry : Registry) :
    MetaM Noun := do
  if body == .sort .zero then
    if let some kind := headConstant? domain then
      if let some handler := registry.typeHandlers.find? (·.kind == kind) then
        return noun `Predicate (handler.text ++ " event") (handler.text ++ " events")
  let payload : NounTypePayload :=
    { type, text := ← inlineMath domain, pluralText := ← inlineMath domain }
  return { noun `Function "function" "functions" with typePayload := some payload }

private def entityForFVar (id : FVarId) (registry : Registry) : MetaM Entity := do
  let declaration ← id.getDecl
  let type := declaration.type
  let valueNoun ←
    if type == .sort .zero then
      pure (noun `Proposition "proposition" "propositions")
    else if type.isSort then
      pure (noun `Sort "type" "types")
    else if let some kind := headConstant? type then
      match registry.typeHandlers.find? (·.kind == kind) with
      | some handler => pure (noun handler.kind handler.text handler.pluralText)
      | none =>
        match type with
        | .forallE _ domain body _ =>
            if !body.hasLooseBVar 0 then
              nondependentFunctionNoun type domain body registry
            else
              elementNoun type
        | _ =>
            elementNoun type
    else
      match type with
      | .forallE _ domain body _ =>
          if !body.hasLooseBVar 0 then
            nondependentFunctionNoun type domain body registry
          else
          elementNoun type
      | _ =>
          elementNoun type
  return {
    id
    name := declaration.userName
    noun := some valueNoun
    dependencies := dependenciesOf type
  }

private def findById (context : Context) (id : FVarId) : Option Nat :=
  context.findIdx? (·.id == id)

private def applyEdit (entity : Entity) (edit : Edit) (provider? : Option Name) : Entity :=
  let entity := match edit with
    | .noun value => { entity with noun := some value }
    | .adjective kind text evidence =>
        let value : Adjective :=
          { kind, expr := evidence, article := (seedArticle text).1, text }
        { entity with adjectives := entity.adjectives.push value }
    | .accessory kind text evidence =>
        { entity with accessories := entity.accessories.push { kind, expr := evidence, text } }
  match provider? with
  | some provider => { entity with provides := entity.provides.push provider }
  | none => entity

/-- Construct entities in two passes: first create the named mathematical
objects, then let head-constant handlers attach nouns, adjectives, accessories,
and the hypotheses that provide them. -/
def build (localContext : LocalContext) (registry : Registry := defaultRegistry) :
    MetaM Context := do
  let declarations := localContext.decls.toArray.filterMap id
  let mut context : Context := #[]
  for declaration in declarations do
    let isProposition ← isProp declaration.type
    if !isProposition && declaration.binderInfo != .instImplicit then
      context := context.push (← entityForFVar declaration.fvarId registry)
  for declaration in declarations do
    let type := declaration.type
    let some kind := headConstant? type | continue
    let some handler := registry.propositionHandlers.find? (·.kind == kind) | continue
    let some (subject, edit) := handler.run type type.getAppArgs | continue
    let .fvar subjectId := subject.consumeMData | continue
    let some index := findById context subjectId | continue
    let provider? ← if ← isProp type then pure (some declaration.userName) else pure none
    if let some entity := context[index]? then
      context := context.setIfInBounds index (applyEdit entity edit provider?)
  return context

def Entity.article : Entity → Article
  | { adjectives, noun := some noun, .. } =>
      let head := adjectives[0]?.map (·.text) |>.getD noun.text
      (seedArticle head).1
  | _ => .a

def Entity.singularDescription (entity : Entity) : String :=
  let adjectives := String.intercalate " " (entity.adjectives.toList.map (·.text))
  let adjectivePrefix := if adjectives.isEmpty then "" else adjectives ++ " "
  let nounText := entity.noun.map (·.text) |>.getD "object"
  let accessories := entity.accessories.toList.map (·.text)
  let accessoryText := if accessories.isEmpty then "" else
    " with " ++ Informalization.Grammar.joinAnd accessories
  s!"is {entity.article} {adjectivePrefix}{nounText}{accessoryText}"

def Entity.pluralDescription (entity : Entity) : String :=
  let adjectives := String.intercalate " " (entity.adjectives.toList.map (·.text))
  let adjectivePrefix := if adjectives.isEmpty then "" else adjectives ++ " "
  let nounText := entity.noun.map (·.pluralText) |>.getD "objects"
  let accessories := entity.accessories.toList.map (·.text)
  let accessoryText := if accessories.isEmpty then "" else
    " with " ++ Informalization.Grammar.joinAnd accessories
  s!"are {adjectivePrefix}{nounText}{accessoryText}"

end Informalization.MassotMiller.Ontology
