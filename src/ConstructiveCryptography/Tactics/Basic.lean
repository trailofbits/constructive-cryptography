import ConstructiveCryptography.Tactics.ProofAutomationAttributes

/-! # Shared deterministic CC proof commands

Tracing, bounded rule checking and curated normalization are independent of
the resource interpretation. Semantic command rules live with their presentation.
-/

open Lean.Parser.Tactic

/-- Opt-in trace class for the exact public theorem selected by a CC
construction assembler. -/
initialize Lean.registerTraceClass `ConstructiveCryptography.ProofAutomation.rule

/-- Elaborate the supplied proof against the target before reporting the
selected theorem. -/
syntax (name := ccExactRule)
  "cc_exact_rule " str " => " term : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cc_exact_rule $label:str => $proof) =>
      closeMainGoalUsing `cc_exact_rule fun target _ => do
        let value ← elabTermEnsuringType proof target
        trace[ConstructiveCryptography.ProofAutomation.rule] "{label.getString}"
        pure value

/-- Normalize selected CC expressions using only the curated
registry. -/
syntax (name := ccNormalize) "cc_normalize" (location)? : tactic

macro_rules
  | `(tactic| cc_normalize $[at $location]?) =>
      `(tactic| simp -failIfUnchanged only [cc_normalization] $[at $location]?)

/-- Trace every rewrite used by `cc_normalize`. -/
syntax (name := ccNormalizeTrace) "cc_normalize?" (location)? : tactic

macro_rules
  | `(tactic| cc_normalize? $[at $location]?) =>
      `(tactic|
        set_option trace.Meta.Tactic.simp.rewrite true in
          cc_normalize $[at $location]?)

/-- Close a bookkeeping goal using only assumptions, reflexivity, or the two
curated registries. A registered side-condition fact may infer implicit data;
its application must close the goal without creating further obligations. -/
syntax (name := ccRoutine) "cc_routine" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cc_routine) => withMainContext do
      let initial ← saveState
      try
        withoutRecover <| Term.withoutErrToSorry <|
          evalTactic (← `(tactic|
            solve
              | assumption
              | rfl
              | exact $(mkIdent `le_rfl)
              | exact $(mkIdent `zero_le) _))
        return
      catch _ => restoreState initial
      -- Direct matching can determine data such as the common domain before
      -- simplification. Only explicitly registered facts are considered.
      let some extension ← getSimpExtension? `cc_side_condition
        | throwError "missing cc_side_condition registry"
      let rules := (← extension.getTheorems).lemmaNames.toList.filterMap fun
        | .decl name _ _ => some name
        | _ => none
      for rule in rules.mergeSort Name.quickLt do
        let saved ← saveState
        try
          withoutRecover <| Term.withoutErrToSorry <|
            evalTactic (← `(tactic| solve | apply $(mkIdent rule)))
          return
        catch _ => restoreState saved
      try
        withoutRecover <| Term.withoutErrToSorry <|
          evalTactic (← `(tactic| solve | simp_all only [cc_normalization, cc_side_condition]))
      catch _ =>
        restoreState initial
        throwError "cc_routine could not close the goal with assumptions or the curated CC registries"

open Lean Elab Tactic in
/-- Check one bounded candidate while restoring the complete tactic state. -/
def ccRuleAppliesWithoutChangingGoal
    (candidate : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic candidate
    restoreState saved
    pure true
  catch _ =>
    restoreState saved
    pure false
