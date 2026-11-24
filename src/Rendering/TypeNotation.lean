import Lean

/-!
# Familiar notation for query and reply types

Only exact core type constructors receive symbols. Each leaf and operator retains its original
expression, so the infoview can link every symbol to Lean. Named aliases remain named, and
dependent functions retain Lean syntax. No alphabet, algebraic structure or coercion is inferred.
-/

namespace CCWidget
open Lean Meta

/-- A presentation tree with original expressions at the hoverable leaves and operators. -/
inductive TypeNotation where
  | atom (source : Expr) (text : String) (precedence : Nat := 0)
  | binary (source : Expr) (symbol : String) (precedence : Nat)
      (left right : TypeNotation)
  deriving Inhabited

def TypeNotation.precedence : TypeNotation → Nat
  | .atom _ _ p | .binary _ _ p _ _ => p

/-- Equal-precedence children keep parentheses: this does not flatten products or function types. -/
def TypeNotation.text (t : TypeNotation) (context : Nat := 0) : String :=
  let body := match t with
    | .atom _ text _ => text
    | .binary _ op p l r => l.text (p + 1) ++ " " ++ op ++ " " ++ r.text (p + 1)
  if t.precedence < context then "(" ++ body ++ ")" else body

/-- A numeral is recognized only when its actual value agrees with the canonical natural.
In particular an alternative `OfNat` instance cannot turn its printed index into a bound. -/
def finiteTypeLiteral? (bound : Expr) : MetaM (Option Nat) := do
  if bound.hasExprMVar then return none
  let some n ← getNatValue? bound | return none
  if ← withoutModifyingState <| withTransparency .reducible <| isDefEq bound (mkNatLit n) then
    return some n
  return none

/-- Symbols abbreviate the actual core types. Unknown or symbolic applications remain exact Lean.
`Fin n` is presented by its natural-number values, with the empty and singleton cases explicit. -/
def typeNotation (e : Expr) (depth : Nat := 32) : MetaM TypeNotation := do
  let source := e
  let e := e.consumeMData
  let fallback : MetaM TypeNotation := do
    return .atom source ((← ppExpr source).pretty (width := 100))
      (if e.isFVar || e.isConst then 100 else 0)
  match depth with
  | 0 => fallback
  | depth + 1 =>
    for (name, symbol) in #[(``Nat, "ℕ"), (``Int, "ℤ"), (``Bool, "𝔹"),
        (``Unit, "{⋆}"), (``PUnit, "{⋆}"), (``Empty, "∅"), (``PEmpty, "∅")] do
      if e.isConstOf name then return .atom source symbol 100
    if e.isAppOfArity ``Fin 1 then
      if let some n ← finiteTypeLiteral? e.getAppArgs[0]! then
        let text := match n with
          | 0 => "∅"
          | 1 => "{0}"
          | 2 => "{0,1}"
          | 3 => "{0,1,2}"
          | n => "{0,…," ++ toString (n - 1) ++ "}"
        return .atom source text 100
    for (name, symbol, strength) in #[(``Prod, "×", 60), (``Sum, "⊕", 50)] do
      if e.isAppOfArity name 2 then
        let args := e.getAppArgs
        return .binary source symbol strength
          (← typeNotation args[0]! depth) (← typeNotation args[1]! depth)
    if let .forallE _ input output bi := e then
      if bi.isExplicit && !output.hasLooseBVars && !(← isProp e) then
        return .binary source "→" 20
          (← typeNotation input depth) (← typeNotation output depth)
    fallback

end CCWidget
