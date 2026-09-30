import ConstructiveCryptography.DSL.Programs
import Lean

/-!
# Obligation tactics

Tactics that discharge the generated obligations from the displayed statements of a body:
`program_bound` for a bound on its inside queries, `program_bounded` for a uniform bound of a
program, `program_cost` for an exact number of inside queries, `program_preserving` for port
preservation.
-/

namespace SystemAlgebra.DSL
open Lean Elab Tactic Meta

elab "component_continuation" : tactic => withMainContext do
  let goal ← getMainGoal
  for declaration in (← getLCtx) do
    if declaration.userName.eraseMacroScopes == `continuation_law then
      let saved ← saveState
      try
        let remaining ← goal.apply declaration.toExpr
        if remaining.isEmpty then
          replaceMainGoal []
          return
      catch _ => pure ()
      saved.restore
  throwError "No matching loop continuation."

/-- Bound the inside queries of a body by its displayed calls. -/
syntax "program_bound" : tactic

elab_rules : tactic
  | `(tactic| program_bound) => do
    let saved ← saveState
    try
      Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| first
      | apply callBound_return
      | component_continuation
      | (apply callBound_call; intro; program_bound)
      | (split <;> program_bound)
      | (apply callBound_ite <;> program_bound)
      | (apply callBound_foldr
         · intro c; program_bound
         · intro x n k continuation_law c; program_bound)
      | (apply Program.CallBound.mono
         · apply callBound_foldr
           · intro c; program_bound
           · intro x n k continuation_law c; program_bound
         · simp only [List.length_ofFn, Nat.zero_add, Nat.mul_one]; omega)))
    catch _ =>
      saved.restore
      throwError "Could not bound the inside queries of this procedure from its displayed \
        operations."

/-- Set every bound that no call constrains to zero. -/
def defaultBounds (goal : MVarId) : TacticM Unit := do
  for m in (← getMVarsNoDelayed (← instantiateMVars (mkMVar goal))) do
    if !(← m.isAssigned) && (← isDefEq (← m.getType) (mkConst ``Nat)) then
      m.assign (mkNatLit 0)
  let open_ ← (← getGoals).filterM fun g => return !(← g.isAssigned)
  unless open_.isEmpty do throwError "Unsolved bound obligations."
  setGoals []

/-- Infer a uniform bound of a program directly, or combine per-invocation bounds when the
inputs and private bindings range over finite types. A bound no call constrains is zero. -/
syntax "program_bounded " term : tactic

elab_rules : tactic
  | `(tactic| program_bounded $signature:term) => do
    let saved ← saveState
    let goal ← getMainGoal
    try
      Term.withoutErrToSorry <| withoutRecover do
        evalTactic (← `(tactic| first
          | (apply Exists.intro
             intro s i x
             cases i <;> dsimp <;> program_bound)
          | (let : ∀ i : ($signature).I, _root_.Finite (($signature).X i) := by
               intro i; cases i <;> dsimp <;> infer_instance
             apply callBound_uniform
             intro s i x; cases i <;> dsimp
             all_goals repeat' split
             all_goals (apply Exists.intro; program_bound))))
        defaultBounds goal
        Term.synthesizeSyntheticMVarsNoPostponing
    catch _ =>
      saved.restore
      throwError "Could not infer a uniform internal-query bound: each invocation must make a \
        number of inside calls bounded independently of the private state."

/-- Prove that each invocation makes exactly its inferred number of inside queries, from the
displayed calls. -/
syntax "program_cost" : tactic

elab_rules : tactic
  | `(tactic| program_cost) => do
    let saved ← saveState
    let goal ← getMainGoal
    try
      Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| first
      | exact callCost_return _
      | component_continuation
      | (apply callCost_call; intro; program_cost)
      | (split <;> program_cost)
      | (refine Program.CallCost.of_eq ?cost (callCost_foldr _ _ _ ?a 1 (fun c => ?finish)
            (fun x n k continuation_law c => ?step) _)
         case finish => program_cost
         case step => program_cost
         case cost => simp)
      | (refine Program.CallCost.of_eq ?cost (callCost_foldr _ _ _ ?a 0 (fun c => ?finish)
            (fun x n k continuation_law c => ?step) _)
         case finish => program_cost
         case step => program_cost
         case cost => simp)
      | (refine Program.CallCost.of_eq ?cost (callCost_foldr _ _ _ ?a 2 (fun c => ?finish)
            (fun x n k continuation_law c => ?step) _)
         case finish => program_cost
         case step => program_cost
         case cost => simp)))
    catch _ =>
      saved.restore
      throwError m!"Could not prove the inferred query cost from the procedure's inside \
        calls:{indentExpr (← goal.getType)}"

/-- Show that a body makes no query at the preserved labels, from its displayed calls. -/
syntax "program_avoids" : tactic

elab_rules : tactic
  | `(tactic| program_avoids) => do
    Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| first
      | apply avoids_return
      | (apply avoids_call <;>
          (first | (intro; program_avoids) | (intro o; cases o <;> (simp; done))))
      | (split <;> program_avoids)))

/-- Show that an invocation at `o` makes at most one query at the preserved labels, at `ι o`,
from its displayed calls. -/
syntax "program_preserves" : tactic

elab_rules : tactic
  | `(tactic| program_preserves) => do
    Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| first
      | apply preservesAt_return
      | (apply preservesAt_call_self <;> first
          | (intro; program_avoids)
          | (intro o' h; cases o' <;> (first | rfl | (simp at h; done))))
      | (apply preservesAt_call_other <;>
          (first | (intro; program_preserves) | (intro o; cases o <;> (simp; done))))
      | (split <;> program_preserves)))

/-- Prove that a program is port preserving along `ι`, procedure by procedure. -/
syntax "program_preserving" : tactic

elab_rules : tactic
  | `(tactic| program_preserving) => do
    let saved ← saveState
    try
      Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic|
        (intro s i x; cases i <;> dsimp <;> program_preserves)))
    catch _ =>
      saved.restore
      throwError "Could not show from the displayed calls that each procedure calls at most its \
        own inside port, at most once."

end SystemAlgebra.DSL
