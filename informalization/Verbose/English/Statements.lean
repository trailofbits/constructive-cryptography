import Verbose.Core
import Mathlib.Data.Fintype.Defs

/-!
# Controlled theorem declarations

This project-controlled command is informed by Massot's theorem/exercise
layout: a reader-facing title, an explicit telescope, a conclusion, and a proof
block. It lowers to one ordinary Lean theorem and retains the full declaration
contract in persistent semantic metadata.
-/

open Lean Elab Command Parser
open Lean.Parser.Term (bracketedBinder)
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules

namespace CryptoLanguage.Verbose.English.Statements

declare_syntax_cat cryptoVerboseGiven
declare_syntax_cat cryptoVerboseGivenTail
syntax bracketedBinder : cryptoVerboseGiven
syntax "∈" "ℕ" : cryptoVerboseGivenTail
syntax ident ident ident : cryptoVerboseGivenTail
syntax (name := cryptoVerboseSpokenGiven)
  ident ident cryptoVerboseGivenTail : cryptoVerboseGiven

inductive GivenPresentation
  | exactLeanBinder
  | finiteNonemptyAlphabet (name : Name)
  | naturalNumber (name : Name) (surfaceForm : Name)
deriving Repr, BEq, Inhabited

structure BinderPresentation where
  name : Name
  binderInfo : BinderInfo
  type : Expr
deriving Repr, Inhabited

structure TheoremPresentation where
  declaration : Name
  title : String
  exactType : Expr
  binders : Array BinderPresentation
  conclusion : Expr
  givens : Array GivenPresentation
  assumptionCount : Nat
  sentenceTrace : Array SentenceTraceEntry := #[]
  sentenceRules : Array RuleId := #[]
  assertionDestinations : Array AssertionDestination := #[]
  routineProducers : Array Name := #[]
  ruleId : RuleId := structuralTheorem
deriving Repr, Inhabited

initialize theoremPresentationRegistry :
    SimplePersistentEnvExtension TheoremPresentation
      (Array TheoremPresentation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun entries entry =>
      (entries.filter (·.declaration != entry.declaration)).push entry
    addImportedFn := fun imported =>
      imported.flatten.foldl (init := #[]) fun entries entry =>
        (entries.filter (·.declaration != entry.declaration)).push entry
  }

def theoremPresentation? (environment : Environment)
    (declaration : Name) : Option TheoremPresentation :=
  (theoremPresentationRegistry.getState environment).find?
    (·.declaration == declaration)

private structure ExpandedGiven where
  binders : TSyntaxArray ``bracketedBinder
  presentation : GivenPresentation

private partial def identifiersIn (stx : Syntax) : Array Syntax :=
  if stx.isIdent then #[stx]
  else stx.getArgs.flatMap identifiersIn

private def expandGiven (given : TSyntax `cryptoVerboseGiven) :
    CommandElabM ExpandedGiven :=
  match given with
  | `(cryptoVerboseGiven| $binder:bracketedBinder) =>
      return ⟨#[binder], .exactLeanBinder⟩
  | given => do
    if given.raw.isOfKind ``cryptoVerboseSpokenGiven then
      let identifiers := identifiersIn given.raw
      if identifiers.size == 5 &&
          identifiers[0]!.getId.toString == "a" &&
          identifiers[1]!.getId.toString == "finite" &&
          identifiers[2]!.getId.toString == "nonempty" &&
          identifiers[3]!.getId.toString == "alphabet" then
        let name : Ident := ⟨identifiers[4]!⟩
        let fintype := mkIdent ``Fintype
        let decidableEq := mkIdent ``DecidableEq
        let nonemptyType := mkIdent ``Nonempty
        return ⟨#[
          ← `(bracketedBinder| ($name : Type _)),
          ← `(bracketedBinder| [$fintype $name]),
          ← `(bracketedBinder| [$decidableEq $name]),
          ← `(bracketedBinder| [$nonemptyType $name])],
          .finiteNonemptyAlphabet name.getId⟩
      else if identifiers.size == 2 &&
          identifiers[0]!.getId.toString == "Let" then
        let name : Ident := ⟨identifiers[1]!⟩
        return ⟨#[← `(bracketedBinder| ($name : ℕ))],
          .naturalNumber name.getId SurfaceContract.naturalNumberForm.id⟩
      else
        throwErrorAt given
          "expected `a finite nonempty alphabet NAME` or `Let NAME ∈ ℕ`"
    else
      throwErrorAt given "unsupported controlled theorem binder"

private partial def telescopePresentation (type : Expr) :
    Array BinderPresentation × Expr :=
  match type with
  | .forallE name domain body binderInfo =>
      let (tail, conclusion) := telescopePresentation body
      (#[⟨name, binderInfo, domain⟩] ++ tail, conclusion)
  | conclusion => (#[], conclusion)

private def elaborateTheorem (name : Ident) (title : TSyntax `str)
    (given : Array (TSyntax `cryptoVerboseGiven))
    (assumed : TSyntaxArray ``bracketedBinder) (conclusion : Term)
    (proof : TSyntax ``Lean.Parser.Tactic.tacticSeq) : CommandElabM Unit := do
  let expanded ← given.mapM expandGiven
  let binders := (expanded.flatMap fun item => item.binders) ++ assumed
  let command ←
    `(command| set_option Elab.async false in
        theorem $name $binders:bracketedBinder* : $conclusion := by $proof)
  elabCommand command
  let declaration := (← getCurrNamespace) ++ name.getId
  let titleText := title.getString
  Lean.addDocStringCore declaration titleText
  let some declarationInfo := (← getEnv).find? declaration
    | throwError "the controlled theorem declaration was not added to the environment"
  let (binderPresentations, exactConclusion) :=
    telescopePresentation declarationInfo.type
  let trace := sentenceTraceFor (← getEnv) declaration
  modifyEnv fun environment => theoremPresentationRegistry.addEntry environment {
    declaration
    title := titleText
    exactType := declarationInfo.type
    binders := binderPresentations
    conclusion := exactConclusion
    givens := expanded.map fun item => item.presentation
    assumptionCount := assumed.size
    sentenceTrace := trace
    sentenceRules := trace.map (·.ruleId)
    assertionDestinations := trace.filterMap (·.assertionDestination?)
    routineProducers := trace.flatMap (·.routineProducers)
  }

syntax (name := cryptoVerboseTheorem)
  "Theorem" ident str
  "Given:" cryptoVerboseGiven*
  "Conclusion:" term
  "Proof:" tacticSeq "QED" : command

syntax (name := cryptoVerboseTheoremWithAssumptions)
  "Theorem" ident str
  "Given:" cryptoVerboseGiven*
  "Assume:" bracketedBinder*
  "Conclusion:" term
  "Proof:" tacticSeq "QED" : command

@[command_elab cryptoVerboseTheorem]
def elabCryptoVerboseTheorem : CommandElab
  | `(command| Theorem $name $title
      Given: $given:cryptoVerboseGiven*
      Conclusion: $conclusion
      Proof: $proof QED) =>
      elaborateTheorem name title given #[] conclusion proof
  | _ => throwUnsupportedSyntax

@[command_elab cryptoVerboseTheoremWithAssumptions]
def elabCryptoVerboseTheoremWithAssumptions : CommandElab
  | `(command| Theorem $name $title
      Given: $given:cryptoVerboseGiven*
      Assume: $assumed:bracketedBinder*
      Conclusion: $conclusion
      Proof: $proof QED) =>
      elaborateTheorem name title given assumed conclusion proof
  | _ => throwUnsupportedSyntax

end CryptoLanguage.Verbose.English.Statements
