/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTeX.Builtins

/-!
# Name-based printers for common mathematical syntax

These rules intentionally mention only expression-kind names.  The
informalization package therefore remains independent of Mathlib, while a
source workspace that contains `Finset` and the standard coercion classes gets
ordinary mathematical notation instead of the inert exact-source fallback.
-/

namespace LeanTeX

open Lean Meta

private def lastArgument (arguments : Array Expr) : LatexPrinterM Expr :=
  match arguments.back? with
  | some argument => pure argument
  | none => failure

private def printLastArgument (_function : Expr) (arguments : Array Expr)
    (_parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  latexPP (← lastArgument arguments)

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

private def printTransparent (_function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  latexPP (← argumentFromEnd (← visibleArguments _function arguments parameterKinds) 0)

private def printLength (_function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let value ← latexPP (← argumentFromEnd
    (← visibleArguments _function arguments parameterKinds) 0)
  let (latex, bigness) := value.latex
  return LatexData.Atom s!"\\lvert {latex} \\rvert" bigness none none

private def printFactorial (_function : Expr) (arguments : Array Expr)
    (parameterKinds : Array ParamKind) : LatexPrinterM LatexData := do
  let value ← latexPP (← argumentFromEnd
    (← visibleArguments _function arguments parameterKinds) 0)
  return value.toAtom ++ "!"

@[latex_pp_app app.NatCast.natCast]
private meta def printNatCast : LatexAppPrinter := printLastArgument

@[latex_pp_app app.Nat.cast]
private meta def printNatCastLegacy : LatexAppPrinter := printLastArgument

@[latex_pp_app app.IntCast.intCast]
private meta def printIntCast : LatexAppPrinter := printLastArgument

@[latex_pp_app app.Finset.range]
private meta def printFinsetRange : LatexAppPrinter := fun _ arguments _ => do
  let bound ← latexPP (← lastArgument arguments)
  return "\\operatorname{range}\\left(" ++ bound ++ "\\right)"

@[latex_pp_app app.Finset.prod]
private meta def printFinsetProduct : LatexAppPrinter := fun _ arguments _ => do
  if arguments.size < 2 then failure
  let collectionExpr := arguments[arguments.size - 2]!
  let function := arguments[arguments.size - 1]!
  let collection ← latexPP collectionExpr
  let localContext ← getLCtx
  let collectionNames := (Lean.collectFVars {} collectionExpr).fvarIds.toList.filterMap fun id =>
    (localContext.find? id).map (fun declaration => declaration.userName)
  -- The bound name must also avoid variables occurring in the index set.  In
  -- particular, render `∏_{j ∈ range(k)} (N-j)`, never the misleading
  -- `∏_{k ∈ range(k)} (N-k)`.
  withAvoidNames collectionNames <| do
    let function ← ensureLam function `j
    let name ← getUnusedName `j function.bindingBody!
    Meta.withLocalDecl name function.binderInfo function.bindingDomain! fun boundVar => do
      let body := function.bindingBody!.instantiate1 boundVar
      let body ← latexPP body
      let binder := LatexData.atomString name.toLatex
      return ("\\prod_{" ++ binder ++ " \\in " ++ collection ++ "} " ++ body.toAtom)
        |>.resetBP .Infinity .Infinity

/-- A root dispatcher makes these printers robust when an external environment
normalizes a constant to a declaration name different from the key recorded by
the standalone package. -/
@[latex_pp_app app]
private meta def printCommonMathSyntax : LatexAppPrinter := fun function arguments kinds => do
  let some name := function.getAppFn.constName? | failure
  match name.toString with
  | "Nat.cast" | "NatCast.natCast" | "IntCast.intCast" =>
      printLastArgument function arguments kinds
  | "NNReal.toReal" | "ENNReal.ofNNReal" => printTransparent function arguments kinds
  | "List.length" => printLength function arguments kinds
  | "Nat.factorial" => printFactorial function arguments kinds
  | "Finset.range" => printFinsetRange function arguments kinds
  | "Finset.prod" => printFinsetProduct function arguments kinds
  | _ => failure

/-- External workspaces may already provide a successful application handler
for these constants.  Registering the same dispatch at the expression layer
ensures the mathematical notation takes priority over generic `f(a)` output. -/
@[latex_pp app]
private meta def printCommonMathExpression : LatexPrinter := fun expression => do
  let function := expression.getAppFn
  let arguments := expression.getAppArgs
  let some name := function.constName? | failure
  match name.toString with
  | "Nat.cast" | "NatCast.natCast" | "IntCast.intCast" =>
      printLastArgument function arguments #[]
  | "NNReal.toReal" | "ENNReal.ofNNReal" => printTransparent function arguments #[]
  | "List.length" => printLength function arguments #[]
  | "Nat.factorial" => printFactorial function arguments #[]
  | "Finset.range" => printFinsetRange function arguments #[]
  | "Finset.prod" => printFinsetProduct function arguments #[]
  | _ => failure

end LeanTeX
