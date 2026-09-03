/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller.English
import LeanTeX.RandomSystemsSyntax

/-!
# Random Systems language adapter

Optional vocabulary for declarations elaborated in an `abstract-crypto`
environment.  The generic backend remains independent of Random Systems: this
module recognizes elaborated constants by name and is selected explicitly by
the CLI profile.
-/

namespace Informalization.MassotMiller.RandomSystems

open Lean Meta
open Informalization.MassotMiller
open Informalization.MassotMiller.Ontology

private partial def explicitArgumentsAux (type : Expr) (arguments : Array Expr)
    (index : Nat) (result : Array Expr) : MetaM (Array Expr) := do
  if index == arguments.size then return result
  let type ← whnf type
  match type with
  | .forallE _ _ body binderInfo =>
      let argument := arguments[index]!
      let result := if binderInfo.isExplicit then result.push argument else result
      explicitArgumentsAux (body.instantiate1 argument) arguments (index + 1) result
  | _ => return result

/-- Explicit source arguments of an elaborated application, omitting inferred
types and typeclass dictionaries. -/
private def explicitArguments (expression : Expr) : MetaM (Array Expr) := do
  let function := expression.getAppFn.consumeMData
  explicitArgumentsAux (← inferType function) expression.getAppArgs 0 #[]

private def headName? (expression : Expr) : Option Name :=
  Ontology.headConstant? expression

private partial def systemPhrase (expression : Expr) : MetaM String := do
  let expression ← instantiateMVars expression
  let arguments ← explicitArguments expression
  match headName? expression with
  | some name =>
      if name == `RandomSystems.PDS.urf then
        let some input := arguments[0]? | return ← Ontology.inlineMath expression
        let some output := arguments[1]? | return ← Ontology.inlineMath expression
        return "the uniform random function from " ++
          (← Ontology.inlineMath input) ++ " to " ++
          (← Ontology.inlineMath output)
      else if name == `RandomSystems.PDS.urp then
        let some alphabet := arguments[0]? | return ← Ontology.inlineMath expression
        return "the uniform random permutation on " ++
          (← Ontology.inlineMath alphabet)
      else if name == `Probability.Distribution.fTransform then
        let some transform := arguments[0]? | return ← Ontology.inlineMath expression
        let some system := arguments[1]? | return ← Ontology.inlineMath expression
        if headName? transform == some `RandomSystems.System.filterQueries then
          let transformArguments ← explicitArguments transform
          let some budget := transformArguments[0]? | return ← Ontology.inlineMath expression
          return "the " ++ (← Ontology.inlineMath budget) ++
            "-query restriction of " ++ (← systemPhrase system)
        return ← Ontology.inlineMath expression
      else
        return ← Ontology.inlineMath expression
  | _ => return ← Ontology.inlineMath expression

private def advantageBoundHandler : English.PropositionHandler := {
  kind := ``LE.le
  run := fun _ expression _ => do
    let arguments ← explicitArguments expression
    let some left := arguments[0]? | return none
    let some bound := arguments[1]? | return none
    unless headName? left == some `RandomSystems.PDS.advFullyDefined do return none
    let systems ← explicitArguments left
    let some real := systems[0]? | return none
    let some ideal := systems[1]? | return none
    return some <| "the fully-defined distinguishing advantage between " ++
      (← systemPhrase real) ++ " and " ++ (← systemPhrase ideal) ++
      " is at most " ++ (← Ontology.inlineMath bound)
}

private def randomSystemsOntology : Ontology.Registry := {
  propositionHandlers := #[
    Ontology.subjectAdjective `Probability.Distribution.NonNeg "nonnegative",
    -- In the Random Systems vocabulary a finite carrier used by the systems
    -- is an alphabet, not implementation-level `Type` plumbing.
    Ontology.subjectNoun `Fintype "finite alphabet" "finite alphabets"
  ] ++ Ontology.defaultRegistry.propositionHandlers
  typeHandlers := #[
    { kind := `RandomSystems.PDS
      text := "probabilistic discrete system"
      pluralText := "probabilistic discrete systems" },
    { kind := `RandomSystems.System.DDE.Total
      text := "deterministic environment"
      pluralText := "deterministic environments" },
    { kind := `Nat
      text := "natural number"
      pluralText := "natural numbers" },
    { kind := `NNReal
      text := "nonnegative real number"
      pluralText := "nonnegative real numbers" }
  ] ++ Ontology.defaultRegistry.typeHandlers
}

/-- Random Systems prose layered on the domain-neutral English renderer. -/
def languageConfig : English.Config := {
  ontologyRegistry := randomSystemsOntology
  propositionHandlers := #[advantageBoundHandler]
}

/-- Random Systems vocabulary for a proof-state inspector.  The inspector
keeps propositions symbolic through LeanTeX, while still aggregating domain
entities and typeclass facts into mathematical nouns and adjectives. -/
def goalLanguageConfig : English.Config := {
  ontologyRegistry := randomSystemsOntology
  propositionHandlers := #[]
}

end Informalization.MassotMiller.RandomSystems
