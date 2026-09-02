import Verbose
import RandomSystems.Technique.Switching

open Lean Elab Tactic Meta
open Probability RandomSystems
open CryptoLanguage.Verbose.RandomSystems.Routine

namespace CryptoLanguage.Verbose.Tests.Routine

private partial def routineReceipts : InfoTree → Array Receipt
  | .hole _ => #[]
  | .context _ child => routineReceipts child
  | .node information children =>
      let here := match information with
        | .ofCustomInfo custom =>
            match custom.value.get? Receipt with
            | some receipt => #[receipt]
            | none => #[]
        | _ => #[]
      children.toArray.foldl
        (fun result child => result ++ routineReceipts child) here

private def pendingRoutineReceipts : TacticM (Array Receipt) := do
  return (← getInfoState).trees.toArray.foldl
    (fun result tree => result ++ routineReceipts tree) #[]

elab "checked_rs_routine" : tactic => do
  let countBefore := (← pendingRoutineReceipts).size
  CryptoLanguage.Verbose.RandomSystems.Routine.close (← getRef)
  let receipts := ← pendingRoutineReceipts
  unless receipts.size == countBefore + 1 do
    throwError "`rs_routine` did not emit exactly one typed receipt"
  let some receipt := receipts.back?
    | throwError "`rs_routine` emitted no typed receipt"
  unless receipt.step.cost == 1 && !receipt.step.declarations.isEmpty do
    throwError "the routine receipt lost its fixed cost or declaration support"
  if receipt.proposition.hasMVar || receipt.proof.hasMVar ||
      receipt.inferredType.hasMVar then
    throwError "the routine receipt contains unresolved metavariables"

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) : True := by
  classical
  let game : PDG X X :=
    Switching.limitGame q
      (PDS.adjoin (PDS.urf X X) Switching.collisionCondition).1
  let ideal : PDS X X := Switching.limit q (PDS.urp X)
  have gameNonnegative : game.NonNeg := by
    checked_rs_routine
  have idealNonnegative : ideal.NonNeg := by
    checked_rs_routine
  have equalWeight : game.weight = ideal.weight := by
    checked_rs_routine
  trivial

/- The registry is deliberately unable to synthesize substantive mathematics
or arbitrary propositions. -/
example {X Y : Type*} (game : PDG X Y) (system : PDS X Y)
    (conditionalLaw : PDG.CondEquiv game system) :
    PDG.CondEquiv game system := by
  fail_if_success rs_routine
  exact conditionalLaw

example (collisionMass bound : ℝ) (proof : collisionMass ≤ bound) :
    collisionMass ≤ bound := by
  fail_if_success rs_routine
  exact proof

example (P : Prop) (proof : P) : P := by
  fail_if_success rs_routine
  exact proof

end CryptoLanguage.Verbose.Tests.Routine
