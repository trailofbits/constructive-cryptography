/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Spine
import ConstructiveCryptography.Tactics.Basic
import ConstructiveCryptography.Tactics.Categorical
import ConstructiveCryptography.Tactics.Substitution
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
import Commons.Definitions.Indifferentiability
import ConstructiveCryptography.Instances.Algebra
import ConstructiveCryptography.Instances.Game
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Game.MBO
import RandomSystems.Game.UntilBad

/-!
# Typechecked Prose Interpolation (`${expr}` / `$[prop]`) & Bounded Closer (`P0.4`)

Provides compile-time verified interpolation directly inside Verbose-CC / Spine prose literals:
* `${term}` parses and elaborates in the live tactic `LocalContext`, rejecting `sorry` and
  unresolved metavariables, and embeds a kernel-transparent `spineExpr term` subterm.
* `$[prop]` parses and elaborates `prop : Prop`, proves it under a strict 20,000-heartbeat
  cap using `solve |`-guarded closers (`assumption`, `rfl`, `positivity`, `gcongr`, `linarith`,
  `norm_num`, `ENNReal`/`ℝ≥0` monotone bounds — NO `simp_all`), and embeds `spineProp proof`.
-/

namespace Informalization.Verbose.ProseInterp

open Lean Meta Elab Term Tactic
open Informalization.Core.Spine

/-- Run `act` under a strict `maxUserHB` heartbeat budget (default `20,000` user heartbeats =
`20_000_000` VM heartbeats) with `Lean.Core.withCurrHeartbeats` and catch runtime timeouts
loudly with an actionable error message. -/
def withBoundedHeartbeatsTactic {α : Type} (tag : String) (act : TacticM α)
    (maxUserHB : Nat := 20000) : TacticM α :=
  Lean.Core.withCurrHeartbeats <|
    withTheReader Core.Context (fun c =>
      let limit := maxUserHB * 1000
      { c with maxHeartbeats := if c.maxHeartbeats == 0 then limit else min c.maxHeartbeats limit }) do
      controlAt CoreM fun runInBase =>
        Lean.Core.tryCatchRuntimeEx (runInBase act) fun ex =>
          runInBase do
            if ex.isMaxHeartbeat then
              throwError "{tag}: automated closer exceeded {maxUserHB}-heartbeat budget; supply an explicit proof term or `by ...` block."
            else
              throw ex

/-- Run a single tactic syntax on `g`, preserving remaining subgoals cleanly. -/
def runTacticOnGoalBounded (g : MVarId) (tac : TSyntax `tactic) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [g]
  try
    evalTactic tac
    let rem ← getGoals
    setGoals saved
    return rem
  catch e =>
    setGoals saved
    throw e

/-- Strict, `solve |`-guarded bounded closer for `Since ... we get ...` and `$[prop]`
interpolation (20k heartbeat cap, explicit `ENNReal`/`ℝ≥0` monotone branch, ZERO `simp_all`). -/
def runBoundedAutoCloser (g : MVarId) (firstPremise? : Option (TSyntax `term) := none)
    (tag : String := "Bounded closer") : TacticM (List MVarId) :=
  withBoundedHeartbeatsTactic tag do
    match firstPremise? with
    | some firstP =>
        runTacticOnGoalBounded g (← `(tactic|
          (try cc_normalize
           first
             | (solve | exact $firstP)
             | (solve | assumption)
             | (solve | rfl)
             | (solve | exact le_rfl)
             | (solve | positivity)
             | (solve | cc_nonexpand)
             | (solve | (rw [ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff]; first | assumption | exact $firstP | cc_nonexpand))
             | (solve | (first
                 | refine add_le_add ?_ ?_
                 | refine ENNReal.add_le_add ?_ ?_
                 | refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                 | refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                 | refine le_add_of_nonneg_left (by positivity)
                 | refine le_add_of_nonneg_right (by positivity)
                 | exact le_self_add
                 | gcongr) <;> first | assumption | positivity | exact le_rfl | exact $firstP)
             | (solve | gcongr)
             | (solve | linarith)
             | (solve | norm_num)
             | (solve | (simp only [ConstructiveCryptography.cc_normalization]; first | assumption | rfl | exact le_rfl | exact $firstP)))))
    | none =>
        runTacticOnGoalBounded g (← `(tactic|
          (try cc_normalize
           first
             | (solve | assumption)
             | (solve | rfl)
             | (solve | exact le_rfl)
             | (solve | positivity)
             | (solve | cc_nonexpand)
             | (solve | (first
                 | refine add_le_add ?_ ?_
                 | refine ENNReal.add_le_add ?_ ?_
                 | refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                 | refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                 | refine le_add_of_nonneg_left (by positivity)
                 | refine le_add_of_nonneg_right (by positivity)
                 | exact le_self_add
                 | gcongr) <;> first | assumption | positivity | exact le_rfl)
             | (solve | gcongr)
             | (solve | linarith)
             | (solve | norm_num)
             | (solve | (simp only [ConstructiveCryptography.cc_normalization]; first | assumption | rfl | exact le_rfl)))))

/-- Pack `(isPropAnchor, expr)` entries into a monomorphic `Unit` `spineCons`/`spineNil` tree.
For `isPropAnchor = false`, wraps `spineExpr e`; for `isPropAnchor = true`, wraps `spineProp h`.
Safely instantiates mvars and skips un-grounded metavariable anchors so polymorphic `Since`
premises never trigger `mkAppM` metavariable errors. -/
def packSpineAnchors (anchors : Array (Bool × Expr)) : MetaM Expr := do
  let mut acc : Expr := mkConst ``spineNil
  for (isPropAnchor, rawE) in anchors.reverse do
    let e ← instantiateMVars rawE
    let ty ← instantiateMVars (← inferType e)
    if e.hasExprMVar || e.hasLevelMVar || ty.hasExprMVar || ty.hasLevelMVar then
      continue
    let hd ←
      if isPropAnchor then mkAppM ``spineProp #[e]
      else mkAppM ``spineExpr #[e]
    acc := mkApp2 (mkConst ``spineCons) hd acc
  return acc

/-- Pack an array of arbitrary typed `Expr`s as `spineExpr` anchors (`Unit`). -/
def packSpineExprs (exprs : Array Expr) : MetaM Expr :=
  packSpineAnchors (exprs.map fun e => (false, e))

private partial def scanDelimited (arr : Array Char) (startIdx : Nat)
    (openCh closeCh : Char) : Option (String × Nat) := Id.run do
  let mut depth : Nat := 1
  let mut i := startIdx
  let mut buf : List Char := []
  while i < arr.size do
    let c := arr[i]!
    if c == openCh then
      depth := depth + 1
      buf := c :: buf
    else if c == closeCh then
      depth := depth - 1
      if depth == 0 then
        return some (String.ofList buf.reverse, i + 1)
      else
        buf := c :: buf
    else
      buf := c :: buf
    i := i + 1
  return none

/-- Parse and typecheck a prose string literal containing `${expr}` and/or `$[prop]`
interpolation blocks in the live goal's `LocalContext`. Returns `(templateWithSentinels, witnessPUnit)`.
Fast path when no `$` occurs: returns `(raw, spineNil)`. -/
def parseAndElabProseInterp (raw : String) : TacticM (String × Expr) := withMainContext do
  if (raw.splitOn "${").length ≤ 1 && (raw.splitOn "$[").length ≤ 1 then
    return (raw, mkConst ``spineNil)
  let arr := raw.toList.toArray
  let env ← getEnv
  let mut out := ""
  let mut anchors : Array (Bool × Expr) := #[]
  let mut i := 0
  while i < arr.size do
    let c := arr[i]!
    if c == '\\' && i + 1 < arr.size && arr[i + 1]! == '$' then
      out := out.push '\\'
      out := out.push '$'
      i := i + 2
      continue
    if c == '$' && i + 1 < arr.size && arr[i + 1]! == '{' then
      let some (termSrc, nextI) := scanDelimited arr (i + 2) '{' '}'
        | throwError (toMessageData ("unclosed `${...}` interpolation in prose string: " ++ raw))
      let trimmed := termSrc.trimAscii.toString
      if trimmed.isEmpty then
        throwError (toMessageData ("empty `${}` interpolation in prose string: " ++ raw))
      let termStx ← match Lean.Parser.runParserCategory env `term trimmed "<prose>" with
        | .ok stx => pure stx
        | .error errMsg => throwError (toMessageData ("failed to parse `${" ++ trimmed ++ "}`: " ++ errMsg))
      let val ← Tactic.elabTerm termStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let val ← instantiateMVars val
      let valTy ← instantiateMVars (← inferType val)
      if val.hasSorry then
        throwError (toMessageData ("interpolation `${" ++ trimmed ++ "}` contains `sorry`"))
      if val.hasExprMVar || val.hasLevelMVar || valTy.hasExprMVar || valTy.hasLevelMVar then
        throwError (toMessageData ("interpolation `${" ++ trimmed ++ "}` has unresolved metavariables or universe levels"))
      let idx := anchors.size
      anchors := anchors.push (false, val)
      out := out ++ s!"@@EXPR:{idx}@@"
      i := nextI
      continue
    if c == '$' && i + 1 < arr.size && arr[i + 1]! == '[' then
      let some (propSrc, nextI) := scanDelimited arr (i + 2) '[' ']'
        | throwError "unclosed `$[...]` claim interpolation in prose string: `{raw}`"
      let trimmed := propSrc.trimAscii.toString
      if trimmed.isEmpty then
        throwError "empty `$[]` claim interpolation in prose string: `{raw}`"
      let propStx ← match Lean.Parser.runParserCategory env `term trimmed "<prose>" with
        | .ok stx => pure stx
        | .error errMsg => throwError "failed to parse `$[{trimmed}]`: {errMsg}"
      let prop ← Term.elabType propStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let prop ← instantiateMVars prop
      let pmVar ← mkFreshExprSyntheticOpaqueMVar prop `proseProp
      let rem ← try
        runBoundedAutoCloser pmVar.mvarId! none s!"Prose claim `$[{trimmed}]`"
      catch _ =>
        pure [pmVar.mvarId!]
      unless rem.isEmpty do
        throwError "interpolated claim `$[{trimmed}]` could not be proved in the current context"
      let h ← instantiateMVars pmVar
      let hTy ← instantiateMVars (← inferType h)
      if h.hasSorry then
        throwError "interpolated claim `$[{trimmed}]` uses `sorry`"
      if h.hasExprMVar || h.hasLevelMVar || hTy.hasExprMVar || hTy.hasLevelMVar then
        throwError "interpolated claim `$[{trimmed}]` has unresolved metavariables or universe levels"
      let idx := anchors.size
      anchors := anchors.push (true, h)
      out := out ++ s!"@@PROP:{idx}@@"
      i := nextI
      continue
    out := out.push c
    i := i + 1
  let witness ← packSpineAnchors anchors
  return (out, witness)

/-- Check if a raw `With notation` LaTeX target contains formula-forgery operators/quantifiers. -/
def isFormulaForgeryLatex (s : String) : Bool :=
  Informalization.Core.Presentation.isFormulaForgeryString s

end Informalization.Verbose.ProseInterp
