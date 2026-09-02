/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTeX.MathlibSyntax

/-!
# Random Systems notation

LeanTeX notation owned by the Random Systems domain adapter.  The generic
Mathlib syntax module deliberately contains no Random Systems declaration
names.
-/

namespace LeanTeX.RandomSystemsSyntax

open Lean Meta
open LeanTeX

private def regularExplicitArguments (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : Array Expr := Id.run do
  if arguments.size != parameterKinds.size then return arguments
  let mut result := #[]
  for index in Array.range arguments.size do
    if parameterKinds[index]!.isRegularExplicit then
      result := result.push arguments[index]!
  return result

private def visibleArguments (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM (Array Expr) := do
  let parameterKinds ← if parameterKinds.isEmpty then
      getParamKinds (mkAppN function arguments)
    else pure parameterKinds
  let explicit := regularExplicitArguments arguments parameterKinds
  return if explicit.isEmpty then arguments else explicit

private def argumentFromEnd (arguments : Array Expr) (offset : Nat) : LatexPrinterM Expr :=
  if _h : offset < arguments.size then
    pure arguments[arguments.size - 1 - offset]!
  else failure

private def printPDS (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let input ← latexPP (← argumentFromEnd arguments 1)
  let output ← latexPP (← argumentFromEnd arguments 0)
  let (input, bi) := input.latex
  let (output, bo) := output.latex
  return LatexData.Atom ("\\mathsf{PDS}(" ++ input ++ "," ++ output ++ ")")
    (max bi bo) none none

private def printPDG (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let input ← latexPP (← argumentFromEnd arguments 1)
  let output ← latexPP (← argumentFromEnd arguments 0)
  let (input, bi) := input.latex
  let (output, bo) := output.latex
  return LatexData.Atom ("\\mathsf{PDG}(" ++ input ++ "," ++ output ++ ")")
    (max bi bo) none none

private def printWeight (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let system ← latexPP (← argumentFromEnd
    (← visibleArguments function arguments parameterKinds) 0)
  let (latex, bigness) := system.latex
  return LatexData.Atom s!"\\lVert {latex} \\rVert" bigness none none

private def printSystemFactor (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let system ← latexPP (← argumentFromEnd arguments 1)
  let transcript ← latexPP (← argumentFromEnd arguments 0)
  let (system, bs) := system.latex
  let (transcript, bt) := transcript.latex
  return LatexData.Atom ("\\sigma_{" ++ system ++ "}(" ++ transcript ++ ")")
    (max bs bt) none none

private def printTranscriptLaw (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let hasTranscript := arguments.size >= 4
  let shift := if hasTranscript then 1 else 0
  let environment ← latexPP (← argumentFromEnd arguments (2 + shift))
  let horizon ← latexPP (← argumentFromEnd arguments (1 + shift))
  let system ← latexPP (← argumentFromEnd arguments shift)
  let (environment, be) := environment.latex
  let (horizon, bn) := horizon.latex
  let (system, bs) := system.latex
  if hasTranscript then
    let transcript ← latexPP (← argumentFromEnd arguments 0)
    let (transcript, bt) := transcript.latex
    return LatexData.Atom ("\\operatorname{tr}_{" ++ environment ++ "," ++ horizon ++
        "}(" ++ system ++ ")(" ++ transcript ++ ")")
      (max (max be bn) (max bs bt)) none none
  else
    return LatexData.Atom ("\\operatorname{tr}_{" ++ environment ++ "," ++ horizon ++
        "}(" ++ system ++ ")") (max (max be bn) bs) none none

private def printProbabilityOfBad (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let distribution ← latexPP (← argumentFromEnd arguments 1)
  let bad ← latexPP (← argumentFromEnd arguments 0)
  let (distribution, bd) := distribution.latex
  let (bad, bb) := bad.latex
  return LatexData.Atom ("\\Pr_{" ++ distribution ++ "}[" ++ bad ++ "]")
    (max bd bb) none none

private def printURF (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let input ← latexPP (← argumentFromEnd arguments 1)
  let output ← latexPP (← argumentFromEnd arguments 0)
  let (input, bi) := input.latex
  let (output, bo) := output.latex
  return LatexData.Atom ("\\mathsf{URF}_{" ++ input ++ "," ++ output ++ "}")
    (max bi bo) none none

private def printURP (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let alphabet ← latexPP (← argumentFromEnd arguments 0)
  let (alphabet, bigness) := alphabet.latex
  return LatexData.Atom ("\\mathsf{URP}_{" ++ alphabet ++ "}") bigness none none

private def printConditionalEquivalence (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let game ← latexPP (← argumentFromEnd arguments 1)
  let target ← latexPP (← argumentFromEnd arguments 0)
  let (game, bg) := game.latex
  let (target, bt) := target.latex
  return LatexData.Atom (game ++ " \\mathrel{\\mid\\!\\equiv} " ++ target)
    (max bg bt) none none

private def printForget (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let game ← latexPP (← argumentFromEnd
    (← visibleArguments function arguments parameterKinds) 0)
  let (game, bigness) := game.latex
  return LatexData.Atom ("(" ++ game ++ ")^{-}") bigness none none

private def printBlindWinning (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let game ← latexPP (← argumentFromEnd
    (← visibleArguments function arguments parameterKinds) 0)
  let (game, bigness) := game.latex
  return LatexData.Atom ("\\Gamma(b" ++ game ++ ")") bigness none none

private def printQueryRestriction (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let budget ← latexPP (← argumentFromEnd arguments 1)
  let system ← latexPP (← argumentFromEnd arguments 0)
  let (budget, bq) := budget.latex
  let (system, bs) := system.latex
  return LatexData.Atom ("[" ++ budget ++ "]" ++ system) (max bq bs) none none

private def printAdjoin (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let system ← latexPP (← argumentFromEnd arguments 1)
  let condition ← latexPP (← argumentFromEnd arguments 0)
  let (system, bs) := system.latex
  let (condition, bc) := condition.latex
  return LatexData.Atom ("\\operatorname{adjoin}(" ++ system ++ "," ++ condition ++ ")")
    (max bs bc) none none

/-- The value of `PDS.adjoin S A` is the game obtained by enhancing `S` with
the MBO defined by `A`, not a subtype projection. -/
private def printAdjoinedGame (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let value ← argumentFromEnd (← visibleArguments function arguments parameterKinds) 0
  unless value.getAppFn.consumeMData.constName? == some `RandomSystems.PDS.adjoin do
    failure
  let adjoinArguments ← visibleArguments value.getAppFn value.getAppArgs #[]
  let system ← latexPP (← argumentFromEnd adjoinArguments 1)
  let condition ← latexPP (← argumentFromEnd adjoinArguments 0)
  let (system, bs) := system.latex
  let (condition, bc) := condition.latex
  return LatexData.Atom ("\\widehat{" ++ system ++ "}^{" ++ condition ++ "}")
    (max bs bc) none none

private def printUniform (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let carrier ← latexPP (← argumentFromEnd
    (← visibleArguments function arguments parameterKinds) 0)
  let (carrier, bigness) := carrier.latex
  return LatexData.Atom ("\\operatorname{Unif}(" ++ carrier ++ ")") bigness none none

private def printMass (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let distribution ← latexPP (← argumentFromEnd arguments 1)
  let event ← latexPP (← argumentFromEnd arguments 0)
  let (distribution, bd) := distribution.latex
  let (event, be) := event.latex
  return LatexData.Atom ("\\Pr_{" ++ distribution ++ "}[" ++ event ++ "]")
    (max bd be) none none

private def printInjOn (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let map ← latexPP (← argumentFromEnd arguments 1)
  let set ← latexPP (← argumentFromEnd arguments 0)
  let (map, bm) := map.latex
  let (set, bs) := set.latex
  return LatexData.Atom ("\\operatorname{InjOn}(" ++ map ++ "," ++ set ++ ")")
    (max bm bs) none none

private def printFinsetCard (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let value ← latexPP (← argumentFromEnd
    (← visibleArguments function arguments parameterKinds) 0)
  let (value, bigness) := value.latex
  return LatexData.Atom ("\\lvert " ++ value ++ " \\rvert") bigness none none

/-- Fully-defined distinguishing advantage retains its observer-class index.
The class-distance symbol `\Delta` is reserved for `PDS.classDistance`. -/
private def printAdvantage (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let source ← latexPP (← argumentFromEnd arguments 1)
  let target ← latexPP (← argumentFromEnd arguments 0)
  let (source, bs) := source.latex
  let (target, bt) := target.latex
  return LatexData.Atom ("\\operatorname{Adv}_{\\bot}(" ++ source ++ "," ++ target ++ ")")
    (max bs bt) none none

/-- Render query filtering compositionally as CR18 Definition 3.10's `[q]S`.
This is notation for the typed `fTransform (filterQueries q) S` shape, not a
theorem-specific rewrite.  In particular, it must not be rendered as
`\theta_q`: `\theta_r` is the distinct CBC message/block-budget restriction. -/
private def printTransform (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let arguments ← visibleArguments function arguments parameterKinds
  let transform ← argumentFromEnd arguments 1
  let system ← argumentFromEnd arguments 0
  unless transform.getAppFn.consumeMData.constName? ==
      some `RandomSystems.System.filterQueries do
    failure
  let transformArguments ← visibleArguments transform.getAppFn transform.getAppArgs #[]
  let budget ← latexPP (← argumentFromEnd transformArguments 0)
  let system ← latexPP system
  let (budget, bq) := budget.latex
  let (system, bs) := system.latex
  return LatexData.Atom ("[" ++ budget ++ "]" ++ system)
    (max bq bs) none none

/-- Coercing a real-valued paper bound into `ENNReal` is an implementation
detail of the formal statement. -/
private def printOfReal (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let value ← latexPP (← argumentFromEnd
    (← visibleArguments function arguments parameterKinds) 0)
  return value

/-- Cardinalities of finite alphabets use the conventional paper notation. -/
private def printCard (function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let alphabet ← latexPP (← argumentFromEnd
    (← visibleArguments function arguments parameterKinds) 0)
  let (alphabet, bigness) := alphabet.latex
  return LatexData.Atom ("\\lvert " ++ alphabet ++ " \\rvert") bigness none none

private def dispatch (function : Expr) (arguments : Array Expr)
    (kinds : Array ParamKind) : LatexPrinterM LatexData := do
  let some name := function.getAppFn.constName? | failure
  match name.toString with
  | "RandomSystems.PDS" => printPDS function arguments kinds
  | "RandomSystems.PDG" => printPDG function arguments kinds
  | "Probability.Distribution.weight" => printWeight function arguments kinds
  | "RandomSystems.PDS.transcriptSystemFactor" => printSystemFactor function arguments kinds
  | "RandomSystems.PDS.trLawFullyDefined" => printTranscriptLaw function arguments kinds
  | "Probability.probBad" => printProbabilityOfBad function arguments kinds
  | "RandomSystems.PDS.urf" => printURF function arguments kinds
  | "RandomSystems.PDS.urp" => printURP function arguments kinds
  | "RandomSystems.PDG.CondEquiv" => printConditionalEquivalence function arguments kinds
  | "RandomSystems.PDG.forget" => printForget function arguments kinds
  | "RandomSystems.PDG.blindSupWinProb" => printBlindWinning function arguments kinds
  | "RandomSystems.Switching.limit" => printQueryRestriction function arguments kinds
  | "RandomSystems.Switching.limitGame" => printQueryRestriction function arguments kinds
  | "RandomSystems.PDS.adjoin" => printAdjoin function arguments kinds
  | "Subtype.val" => printAdjoinedGame function arguments kinds
  | "Probability.Distribution.uniform" => printUniform function arguments kinds
  | "Probability.Distribution.mass" => printMass function arguments kinds
  | "Set.InjOn" => printInjOn function arguments kinds
  | "Finset.card" => printFinsetCard function arguments kinds
  | "RandomSystems.Switching.collisionCondition" =>
      pure (LatexData.Atom "\\mathsf{Coll}" 0 none none)
  | "RandomSystems.PDS.advFullyDefined" => printAdvantage function arguments kinds
  | "Probability.Distribution.fTransform" => printTransform function arguments kinds
  | "ENNReal.ofReal" => printOfReal function arguments kinds
  | "Fintype.card" => printCard function arguments kinds
  | _ => failure

@[latex_pp_app app]
private meta def printRandomSystemsApp : LatexAppPrinter := dispatch

@[latex_pp app]
private meta def printRandomSystemsExpression : LatexPrinter := fun expression =>
  dispatch expression.getAppFn expression.getAppArgs #[]

end LeanTeX.RandomSystemsSyntax
