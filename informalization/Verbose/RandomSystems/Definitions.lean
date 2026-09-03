import Verbose.Core
import RandomSystems.Technique.Switching

/-!
# Characterized Random Systems definitions

This module implements typed system binding and the accepted
definition-plus-characterization form for MBOs. The parser does not recognize
a particular system, condition, or theorem name. It validates the exact
carrier of a system binder and checks the supplied MBO characterization before
introducing the corresponding local definition.
-/

open Lean Elab Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.RandomSystems.Definitions

@[crypto_verbose_sentence] def systemBinder :=
  descriptor `rs.declaration `systemBinder rsBindSystem
    .introduction
    (.introduce SurfaceContract.systemForm.bindings)
    Relations.definition SurfaceContract.systemForm.operands
    "introduce an exact PDS system through the Random Systems binder"
    `CryptoLanguage.Verbose.RandomSystems.Definitions.Backend.systemBinder

@[crypto_verbose_sentence] def characterizedMBO :=
  descriptor `rs.declaration `characterizedMBO rsDefineCharacterizedMBO
    .introduction
    (.introduce SurfaceContract.mboForm.bindings)
    Relations.definition SurfaceContract.mboForm.operands
    "introduce an exact MBO together with its checked collision characterization"
    `CryptoLanguage.Verbose.RandomSystems.Definitions.Backend.characterizedMBO

namespace Backend

def systemBinder (name : Ident) (value : Term) : TacticM Unit := do
  evalTactic (← `(tactic| let $name := $value))

private def validateCharacterization (assignment characterization : Term) :
    TacticM Unit := withMainContext do
  let proof ← instantiateMVars (← elabTerm characterization none)
  let proofType ← instantiateMVars (← inferType proof)
  forallTelescope proofType fun arguments conclusion => do
    unless arguments.size == 2 do
      throwError "the MBO characterization must quantify over one function and one query history"
    let functionDecl ← arguments[0]!.fvarId!.getDecl
    let historyDecl ← arguments[1]!.fvarId!.getDecl
    let functionName := mkIdent functionDecl.userName
    let historyName := mkIdent historyDecl.userName
    let expectedSyntax ← `(term|
      $historyName ∈
          ($assignment (RandomSystems.System.functionEvaluator $functionName)).1 ↔
        ¬ Set.InjOn $functionName (fun x => x ∈ ($historyName).toFinset))
    let expected ← instantiateMVars
      (← elabTerm expectedSyntax (some (mkSort .zero)))
    unless conclusion == expected || (← isDefEqGuarded conclusion expected) do
      throwError "the supplied theorem does not characterize this MBO assignment on function evaluators"
  if proof.hasMVar || proofType.hasMVar then
    throwError "the MBO characterization contains unresolved metavariables"

def characterizedMBO (name : Ident) (assignment characterization : Term) :
    TacticM Unit := do
  evalTactic (← `(tactic| let $name := $assignment))
  validateCharacterization assignment characterization
  withMainContext do
    let declaration ← getLocalDeclFromUserName name.getId
    let declarationType ← instantiateMVars declaration.type
    let declarationValue? ← declaration.value?.mapM instantiateMVars
    if declarationType.hasMVar || declarationValue?.any Expr.hasMVar then
      throwError m!"the MBO assignment contains unresolved metavariables: {declarationType}"

end Backend
end CryptoLanguage.Verbose.RandomSystems.Definitions

open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.RandomSystems.Definitions

elab "crypto_verbose_rs_system_binder " name:ident ", " value:verboseReference :
    tactic => do
  let valueRef ← decodeReference value
  runSentenceWithBindings (← getRef) systemBinder (.addLocals #[name.getId])
      #[⟨role `value, valueRef⟩]
      #[⟨role `system, name.getId, none⟩] #[] <|
    backendAction Backend.systemBinder (name, valueRef.term)

elab "crypto_verbose_rs_characterized_mbo " name:ident ", "
    assignment:verboseReference ", " characterization:verboseReference : tactic => do
  let assignmentRef ← decodeReference assignment
  let characterizationRef ← decodeReference characterization
  runSentenceWithBindings (← getRef) characterizedMBO (.addLocals #[name.getId]) #[
      ⟨role `assignment, assignmentRef⟩,
      ⟨role `characterization, characterizationRef⟩] #[
      ⟨role `condition, name.getId, none⟩] #[] <|
    backendAction Backend.characterizedMBO
      (name, assignmentRef.term, characterizationRef.term)

namespace CryptoVerbose

scoped macro &"Let" name:ident &"be" &"the" &"system"
    value:term : tactic => do
  let valueRef ← `(verboseReference| $value:term)
  `(tactic| crypto_verbose_rs_system_binder $name, $valueRef)

scoped macro &"Let" name:ident &"be" &"the" &"MBO" &"given" &"by"
    assignment:verboseReference "," &"which" &"is" &"set" &"on" &"a"
    &"query" &"history" &"exactly" &"when" &"two" &"distinct" &"queries"
    &"in" &"that" &"history" &"receive" &"the" &"same" &"answer" ","
    &"as" &"shown" &"by" characterization:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_characterized_mbo $name, $assignment,
    $characterization)

end CryptoVerbose
