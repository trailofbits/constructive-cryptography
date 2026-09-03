import Verbose.Core
import Mathlib.Tactic

/-! Small typed proof operations used by the language-specific elaborators. -/

namespace CryptoLanguage.Verbose.Backend

open Lean Elab Tactic Meta Parser
open Lean.Parser.Tactic

def closeFrom (proof : Term) : TacticM Unit := do
  evalTactic (← `(tactic| exact $proof))

def guardGoal (statement : Term) : TacticM Unit := do
  withMainContext do
    withoutModifyingState do
      let announced ← elabTerm statement none
      let goalType ← getMainTarget
      unless announced == goalType || (← isDefEq announced goalType) do
        throwError m!"the announced proposition does not match the current goal\nannounced: {announced}\ncurrent goal: {goalType}"

def replaceInClaim (old new equation result : Term) : TacticM Unit := do
  withMainContext do
    let oldExpression ← elabTerm old none
    let oldType ← inferType oldExpression
    let newExpression ← elabTerm new (some oldType)
    let equationExpression ← elabTerm equation none
    let expectedEquation ← mkEq oldExpression newExpression
    let equationType ← instantiateMVars (← inferType equationExpression)
    unless equationType == expectedEquation do
      throwError "the supplied equality does not identify the displayed replacement"
    let resultExpression ← elabTerm result none
    if resultExpression.hasMVar then
      throwError "the displayed result contains unresolved metavariables"
    let target ← instantiateMVars (← getMainTarget)
    let some _ := target.eq?
      | throwError "equality-guided replacement requires an equality goal"
    let rewritten ← withoutModifyingState do
      (getMainGoal >>= fun goal => goal.rewrite target equationExpression)
    unless rewritten.mvarIds.isEmpty do
      throwError "the displayed replacement introduces unresolved side conditions"
    let expectedResult ← mkEq resultExpression resultExpression
    unless rewritten.eNew == expectedResult ||
        (← isDefEqGuarded rewritten.eNew expectedResult) do
      throwError "rewriting the current equality by the supplied equation does not yield the displayed result on both sides"
  let rewriteRule ← `(rwRule| $equation:term)
  evalTactic (← `(tactic| rw [$rewriteRule:rwRule]))

def introOne (name : Ident) : TacticM Unit := do
  withMainContext do
    let (_, next) ← (← getMainGoal).intro name.getId
    replaceMainGoal [next]

def introTwo (first second : Ident) : TacticM Unit := do
  introOne first
  introOne second

def introTwoWithType (first second : Ident) (property : Term) : TacticM Unit := do
  introTwo first second
  withMainContext do
    let expected ← elabTerm property none
    let declaration ← getLocalDeclFromUserName second.getId
    unless ← isDefEq declaration.type expected do
      throwError "the introduced condition does not have the stated proposition"

def introOneWithType (name : Ident) (proposition : Term) : TacticM Unit := do
  introOne name
  withMainContext do
    let expected ← elabTerm proposition none
    let declaration ← getLocalDeclFromUserName name.getId
    unless ← isDefEq declaration.type expected do
      throwError "the introduced assumption does not have the stated proposition"

def chooseFrom (existence : Term) (witness factName : Ident)
    (property : Term) : TacticM Unit := do
  withMainContext do
    let source ← elabTerm existence none
    let sourceType ← whnf (← instantiateMVars (← inferType source))
    unless sourceType.getAppFn.constName? == some ``Exists do
      throwError "the supplied evidence is not an existential proposition"
  let sourceName ← withMainContext <| mkFreshUserName `__verbose_source
  let source := mkIdent sourceName
  evalTactic (← `(tactic| have $source := $existence))
  evalTactic (← `(tactic| rcases ($source) with ⟨$witness, $factName⟩))
  withMainContext do
    let expected ← elabTerm property none
    let decl ← getLocalDeclFromUserName factName.getId
    unless ← isDefEq decl.type expected do
      throwError "the chosen witness does not have the stated property"

def obtainConjunction (conjunction : Term)
    (leftName : Ident) (left : Term) (rightName : Ident) (right : Term) :
    TacticM Unit := do
  withMainContext do
    let source ← elabTerm conjunction none
    let sourceType ← whnf (← instantiateMVars (← inferType source))
    let expectedLeft ← elabTerm left (some (mkSort .zero))
    let expectedRight ← elabTerm right (some (mkSort .zero))
    let expected := mkApp2 (mkConst ``And) expectedLeft expectedRight
    unless ← isDefEqGuarded sourceType expected do
      throwError "the supplied evidence is not the stated conjunction"
  let sourceName ← withMainContext <| mkFreshUserName `__verbose_source
  let source := mkIdent sourceName
  evalTactic (← `(tactic| have $source := $conjunction))
  evalTactic (← `(tactic| rcases ($source) with ⟨$leftName, $rightName⟩))
  withMainContext do
    let expectedLeft ← elabTerm left none
    let expectedRight ← elabTerm right none
    let localLeft ← getLocalDeclFromUserName leftName.getId
    let localRight ← getLocalDeclFromUserName rightName.getId
    unless ← isDefEq localLeft.type expectedLeft do
      throwError "the left conjunct does not have the stated proposition"
    unless ← isDefEq localRight.type expectedRight do
      throwError "the right conjunct does not have the stated proposition"

end CryptoLanguage.Verbose.Backend
