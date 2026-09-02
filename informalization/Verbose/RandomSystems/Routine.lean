import Verbose.Core
import RandomSystems.Technique.Switching

/-!
# Bounded Random Systems routine proofs

This module closes only constructor bookkeeping that is uniquely determined by
the current goal.  It does not choose a game, event, ideal system, proof route,
or bound.  Each successful closure records the exact proposition, checked
proof, and fixed list of declarations used by its registered producer.
-/

open Lean Elab Tactic Meta
open Probability RandomSystems

namespace CryptoLanguage.Verbose.RandomSystems.Routine

initialize registerTraceClass `CryptoLanguage.Verbose.routine

/-- Query restriction and MBO enhancement preserve the unit weight of URF,
so the resulting game has the same weight as restricted URP.  Keeping this as
one named theorem prevents the routine closer from repeatedly normalizing the
complete finite uniform distributions. -/
theorem restrictedEnhancedURF_weight_eq_restrictedURP
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : Nat)
    (condition : System.DDS X X → System.MonotoneCondition X) :
    (Switching.limitGame q (PDS.adjoin (PDS.urf X X) condition).1).weight =
      (Switching.limit q (PDS.urp X)).weight := by
  simp only [Switching.limitGame, Switching.limit, PDS.coe_adjoin,
    Distribution.weight_fTransform]
  rw [PDS.isProbDist_urf X X |>.weight_eq,
    PDS.isProbDist_urp X |>.weight_eq]

inductive GoalClass
  | canonicalNonnegativity
  | canonicalWeight
deriving Repr, BEq, Inhabited

inductive CloserId
  | restrictedEnhancedURFNonnegative
  | restrictedURPNonnegative
  | restrictedURFURPWeight
deriving Repr, BEq, Inhabited

def CloserId.label : CloserId → String
  | .restrictedEnhancedURFNonnegative =>
      "nonnegativity of a restricted game obtained by adjoining an MBO to URF"
  | .restrictedURPNonnegative => "nonnegativity of a restricted URP"
  | .restrictedURFURPWeight =>
      "equal weight of the restricted enhanced URF game and restricted URP"

def CloserId.goalClass : CloserId → GoalClass
  | .restrictedEnhancedURFNonnegative | .restrictedURPNonnegative =>
      .canonicalNonnegativity
  | .restrictedURFURPWeight => .canonicalWeight

def CloserId.semanticName : CloserId → Name
  | .restrictedEnhancedURFNonnegative =>
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedEnhancedURFNonnegative
  | .restrictedURPNonnegative =>
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative
  | .restrictedURFURPWeight =>
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURFURPWeight

def GoalClass.semanticName : GoalClass → Name
  | .canonicalNonnegativity =>
      `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalNonnegativity
  | .canonicalWeight =>
      `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalWeight

def CloserId.requiredDeclarations : CloserId → Array Name
  | .restrictedEnhancedURFNonnegative => #[
      ``RandomSystems.PDS.nonNeg_adjoin,
      ``RandomSystems.PDS.isProbDist_urf,
      ``Probability.Distribution.NonNeg.fTransform]
  | .restrictedURPNonnegative => #[
      ``RandomSystems.PDS.isProbDist_urp,
      ``Probability.Distribution.NonNeg.fTransform]
  | .restrictedURFURPWeight => #[
      ``restrictedEnhancedURF_weight_eq_restrictedURP]

structure Step where
  closer : CloserId
  goalClass : GoalClass
  /-- Complete union of the producer's fixed operational dependencies and the
  constants occurring in the emitted kernel proof. -/
  declarations : Array Name
  /-- Constants occurring in the exact checked proof term. -/
  proofDeclarations : Array Name := #[]
  cost : Nat := 1
deriving Repr, BEq, Inhabited

structure Receipt where
  schemaVersion : Nat := 2
  proposition : Expr
  proof : Expr
  inferredType : Expr
  step : Step
deriving Inhabited, TypeName

private def candidates : Array CloserId := #[
  .restrictedEnhancedURFNonnegative,
  .restrictedURPNonnegative,
  .restrictedURFURPWeight]

private partial def proofDeclarations (expression : Expr)
    (result : Array Name := #[]) : Array Name :=
  match expression with
  | .const declaration _ =>
      if result.contains declaration then result else result.push declaration
  | .app function argument =>
      proofDeclarations argument (proofDeclarations function result)
  | .lam _ domain body _ | .forallE _ domain body _ =>
      proofDeclarations body (proofDeclarations domain result)
  | .letE _ type value body _ =>
      proofDeclarations body
        (proofDeclarations value (proofDeclarations type result))
  | .mdata _ body | .proj _ _ body => proofDeclarations body result
  | _ => result

private def requireDeterminedGoal (source : Syntax) : TacticM Expr := do
  let goal ← getMainGoal
  let proposition ← goal.withContext <| instantiateMVars (← goal.getType)
  if proposition.hasMVar then
    throwErrorAt source
      "Random Systems routine synthesis requires a fully determined proposition"
  return proposition

private def applyCloser : CloserId → TacticM Unit
  | .restrictedEnhancedURFNonnegative => do
      evalTactic (← `(tactic|
        exact (RandomSystems.PDS.nonNeg_adjoin
          (RandomSystems.PDS.isProbDist_urf _ _).nonNeg _).fTransform _))
  | .restrictedURPNonnegative => do
      evalTactic (← `(tactic|
        exact (RandomSystems.PDS.isProbDist_urp _).nonNeg.fTransform _))
  | .restrictedURFURPWeight => do
      evalTactic (← `(tactic|
        exact restrictedEnhancedURF_weight_eq_restrictedURP _ _ _))

private def closesCurrentGoal (closer : CloserId) : TacticM Bool := do
  let saved ← saveState
  let goalsBefore ← getGoals
  try
    applyCloser closer
    let result := (← getGoals) == goalsBefore.tail
    saved.restore (restoreInfo := true)
    return result
  catch _ =>
    saved.restore (restoreInfo := true)
    return false

private def currentGoalClass? : TacticM (Option GoalClass) := do
  let proposition ← requireDeterminedGoal (← getRef)
  if proposition.getAppFn.constName? ==
      some ``Probability.Distribution.NonNeg then
    return some .canonicalNonnegativity
  if proposition.eq?.isSome then
    return some .canonicalWeight
  return none

def matchingClosers : TacticM (Array CloserId) := do
  let _ ← requireDeterminedGoal (← getRef)
  let some goalClass ← currentGoalClass? | return #[]
  let mut applicable := #[]
  for closer in candidates do
    unless closer.goalClass == goalClass do continue
    if ← closesCurrentGoal closer then
      applicable := applicable.push closer
  return applicable

private def emitReceipt (source : Syntax) (proofGoal : MVarId)
    (receipt : Receipt) : TacticM Unit := do
  pushInfoLeaf <| Info.ofCustomInfo {
    stx := source
    value := Dynamic.mk receipt
  }
  pushInfoLeaf <| Info.ofCustomInfo {
    stx := source
    value := Dynamic.mk ({
      producer := receipt.step.closer.semanticName
      goalClass := receipt.step.goalClass.semanticName
      proofGoal
      proposition := receipt.proposition
      proof := receipt.proof
      inferredType := receipt.inferredType
      declarations := receipt.step.declarations
      proofDeclarations := receipt.step.proofDeclarations
      cost := receipt.step.cost
    } : RoutineEvidenceAnchor)
  }
  trace[CryptoLanguage.Verbose.routine]
    "{receipt.step.closer.label}"

private def applyAndRecord (source : Syntax) (closer : CloserId)
    (proposition : Expr) : TacticM Unit := do
  let goalsBefore ← getGoals
  let some goal := goalsBefore.head?
    | throwErrorAt source "routine synthesis requires an active goal"
  applyCloser closer
  unless (← getGoals) == goalsBefore.tail do
    throwErrorAt source "the selected routine producer did not close exactly the current goal"
  let proof ← goal.withContext <| instantiateMVars (mkMVar goal)
  let inferredType ← goal.withContext <| instantiateMVars (← inferType proof)
  if proof.hasMVar || inferredType.hasMVar then
    throwErrorAt source "the routine producer left unresolved metavariables"
  /- `applyCloser` closed this exact metavariable through Lean's tactic
  elaborator, which already checks the assignment against `proposition`.
  Re-running unrestricted definitional equality here would expand complete
  uniform distributions hidden below local RS abbreviations. -/
  let checkedDeclarations ←
    CryptoLanguage.Verbose.normalizedEvidenceDeclarations proof
  let declarations := checkedDeclarations.foldl (init := closer.requiredDeclarations)
    fun result declaration =>
      if result.contains declaration then result else result.push declaration
  emitReceipt source goal {
    proposition
    proof
    inferredType
    step := ⟨closer, closer.goalClass, declarations, checkedDeclarations, 1⟩
  }

/-- Apply one caller-selected producer.  This is used only where a registered
semantic theorem fixes the exact routine-premise sequence; it performs no
search and still emits the same checked receipt as `rs_routine`. -/
def closeExpected (source : Syntax) (closer : CloserId) : TacticM Unit := do
  let proposition ← requireDeterminedGoal source
  let some goalClass ← currentGoalClass?
    | throwErrorAt source "the expected routine producer does not match this goal class"
  unless closer.goalClass == goalClass do
    throwErrorAt source "the expected routine producer has the wrong goal class"
  applyAndRecord source closer proposition

/-- Close the current goal using exactly one matching registered producer.
The three-candidate registry and unit costs form the initial fixed budget. -/
def close (source : Syntax) : TacticM Unit := do
  let proposition ← requireDeterminedGoal source
  let applicable ← matchingClosers
  unless applicable.size == 1 do
    if applicable.isEmpty then
      throwErrorAt source "no registered Random Systems routine closer matches this goal"
    else
      throwErrorAt source "more than one registered Random Systems routine closer matches this goal"
  let closer := applicable[0]!
  applyAndRecord source closer proposition

/-- Report the unique registered producer without changing the proof state. -/
def suggest (source : Syntax) : TacticM Unit := do
  let applicable ← matchingClosers
  match applicable.toList with
  | [closer] => logInfoAt source m!"rs_routine: {closer.label}"
  | [] => throwErrorAt source "no registered Random Systems routine closer matches this goal"
  | _ => throwErrorAt source
      "more than one registered Random Systems routine closer matches this goal"

end CryptoLanguage.Verbose.RandomSystems.Routine

elab "rs_routine" : tactic => do
  CryptoLanguage.Verbose.RandomSystems.Routine.close (← getRef)

elab "rs?" : tactic => do
  CryptoLanguage.Verbose.RandomSystems.Routine.suggest (← getRef)
