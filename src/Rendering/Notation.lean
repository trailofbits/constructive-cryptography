import Lean

/-!
# Compact notation for interface predicates

This is a syntax-directed printer, not a simplifier. It recognizes exact core declarations,
keeps connective scope, and beta-reduces literal function applications. Unsupported expressions
retain Lean's printer. The caller keeps the original expression for hover and source inspection.
-/

namespace CCWidget
open Lean Meta

/-- Text and binding strength; unknown Lean syntax is parenthesized inside known operators. -/
structure PredicateNotation where
  text : String
  precedence : Nat := 0
  deriving Inhabited

def PredicateNotation.at (p : PredicateNotation) (precedence : Nat) : String :=
  if p.precedence < precedence then "(" ++ p.text ++ ")" else p.text

/-- Only core syntax receives paper notation. Names resembling these operators are irrelevant.
The depth bound is a display limit; the complete remaining expression is always printed. -/
def predicateNotation (e : Expr) (depth : Nat := 32) : MetaM PredicateNotation := do
  let e := e.consumeMData.headBeta.consumeMData
  let fallback : MetaM PredicateNotation := do
    return ⟨(← ppExpr e).pretty (width := 100),
      if e.isFVar || e.isConst || e.isLit || e.isAppOfArity ``OfNat.ofNat 3 then 100 else 0⟩
  match depth with
  | 0 => fallback
  | depth + 1 =>
    if e.isHeadBetaTarget then return ← predicateNotation e depth
    if e.isAppOfArity ``List.nil 1 then return ⟨"ε", 100⟩
    if e.isAppOfArity ``List.length 2 then
      return ⟨"|" ++ (← predicateNotation e.getAppArgs[1]! depth).text ++ "|", 100⟩
    let binary := #[(``And, 2, "∧", 30), (``Or, 2, "∨", 20), (``Iff, 2, "↔", 10),
      (``Eq, 3, "=", 50), (``Ne, 3, "≠", 50), (``LE.le, 4, "≤", 50),
      (``LT.lt, 4, "<", 50), (``HAdd.hAdd, 6, "+", 60), (``HMul.hMul, 6, "·", 70)]
    for (name, arity, symbol, strength) in binary do
      if e.isAppOfArity name arity then
        let args := e.getAppArgs
        let l ← predicateNotation args[arity - 2]! depth
        let r ← predicateNotation args[arity - 1]! depth
        -- Parenthesize equal-precedence children: no associativity law is assumed.
        return ⟨l.at (strength + 1) ++ " " ++ symbol ++ " " ++ r.at (strength + 1), strength⟩
    if e.isAppOfArity ``Not 1 then
      return ⟨"¬" ++ (← predicateNotation e.getAppArgs[0]! depth).at 80, 80⟩
    if let .forallE name ty body bi := e then
      unless ← isProp e do return ← fallback
      if !body.hasLooseBVars && (← isProp ty) then
        let l ← predicateNotation ty depth
        let r ← predicateNotation body depth
        return ⟨l.at 11 ++ " ⇒ " ++ r.at 11, 10⟩
      return ← withLocalDecl ((← getLCtx).getUnusedName name) bi ty fun x => do
        let binder := (← ppExpr x).pretty
        let type := (← ppExpr ty).pretty (width := 100)
        let type := if ty.isFVar || ty.isConst then type else "(" ++ type ++ ")"
        let p ← predicateNotation (body.instantiate1 x) depth
        return ⟨"∀ " ++ binder ++ " : " ++ type ++ ", " ++ p.text, 5⟩
    fallback

/-- A predicate on input histories is shown as a set, retaining its actual binder type in
the source expression. No nonemptiness, budget, or other condition is inferred or omitted. -/
def domainNotation (predicate : Expr) : MetaM String := do
  let .forallE _ ty _ _ ← whnf (← inferType predicate)
    | return (← ppExpr predicate).pretty (width := 100)
  withLocalDeclD ((← getLCtx).getUnusedName `h) ty fun h => do
    let binder := (← ppExpr h).pretty
    let p ← predicateNotation (mkApp predicate h)
    return "{ " ++ binder ++ " | " ++ p.text ++ " }"

end CCWidget
