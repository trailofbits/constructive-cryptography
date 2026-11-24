/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Hygiene

/-!
# Extensible 2D `Expr → LaTeX` Pretty-Printer (`LeanTeX`)

Inspired by Kyle Miller's `LeanTeX`, upgraded with:
* automatic preprocessing through `Hygiene.normalizeForPresentation`;
* a persistent, compile-time-validated registry of 2D LaTeX application handlers
  (so CC operators `Δ`, `∥`, `—[π; ε]→`, `≃[ε]`, `≈[ε]`, `|≡`, juxtaposition `αR`,
  right-interface attachment `Sσ`, and domain symbols like `Π±` render in authentic
  paper typography without hardcoding domain logic into the core printer);
* scoped symbol overrides (resolving notation clashes like `r` for rate vs. `P` for
  public queries);
* precedence-aware minimal parenthesization and total TeX-safe fallback escaping.
-/

namespace Informalization.Core.LeanTeX

open Lean Meta Informalization.Core.Hygiene

/-- Scoped symbol overrides threaded through one informalization pass (e.g., mapping
a constant name, local binder name, or repeated subexpression to a preferred LaTeX symbol,
and suppressing ambient leading explicit arguments on verbose Lean definitions). -/
structure SymbolTable where
  constAliases : NameMap String := {}
  binderAliases : Std.HashMap String String := {}
  hiddenArgs : NameMap (List Nat) := {}
  zeroArgConsts : NameSet := {}
  exprAliases : Array (Expr × String) := #[]
  deriving Inhabited

def SymbolTable.withConst (t : SymbolTable) (n : Name) (latex : String) : SymbolTable :=
  { t with constAliases := t.constAliases.insert n latex }

def SymbolTable.withBinder (t : SymbolTable) (binder : String) (latex : String) : SymbolTable :=
  { t with binderAliases := t.binderAliases.insert binder latex }

def SymbolTable.withHiddenArgs (t : SymbolTable) (n : Name) (idxs : List Nat) : SymbolTable :=
  { t with hiddenArgs := t.hiddenArgs.insert n idxs }

def SymbolTable.withZeroArgConst (t : SymbolTable) (n : Name) : SymbolTable :=
  { t with zeroArgConsts := t.zeroArgConsts.insert n }

def SymbolTable.withExprAlias (t : SymbolTable) (e : Expr) (latex : String) : SymbolTable :=
  { t with exprAliases := t.exprAliases.push (e, latex) }

/-- Callback for recursive child printing with precedence `ctxPrec`. -/
abbrev Recurse := Nat → Expr → MetaM String

/-- A registered 2D LaTeX handler for applications headed by `head`.
Returns `some (renderedLatex, ownPrecedence)` if handled, or `none` to fall back. -/
structure AppHandler where
  head : Name
  priority : Nat := 100
  run : SymbolTable → Recurse → Expr → Array Expr → MetaM (Option (String × Nat))

/-- Global registry of domain-extensible 2D LaTeX handlers (CC, Probability, SequenceHash, …). -/
initialize latexAppHandlers :
    IO.Ref (NameMap (Array AppHandler)) ← IO.mkRef {}

/-- Register a 2D LaTeX handler at runtime/init time. -/
def registerAppHandler (h : AppHandler) : IO Unit :=
  latexAppHandlers.modify fun m =>
    let arr : Array AppHandler := (m.getD h.head #[]).push h
    -- Higher priority runs first
    let sorted := arr.qsort fun a b => a.priority > b.priority
    m.insert h.head sorted

/-- Safe TeX escaping for fallback identifiers and literals. -/
def escapeLatex (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '\\' => "\\textbackslash{}"
      | '{'  => "\\{"
      | '}'  => "\\}"
      | '_'  => "\\_"
      | '^'  => "\\^{}"
      | '#'  => "\\#"
      | '%'  => "\\%"
      | '&'  => "\\&"
      | '$'  => "\\$"
      | '~'  => "\\textasciitilde{}"
      | _    => c.toString

/-- Format a short mathematical identifier cleanly: single Latin/Greek letters stay bare
italic (`x`, `q`, `ε`), multi-letter names use `\mathrm` or `\mathsf` cleanly, and
trailing numeric subscripts render as `x_1`, `q_e`. -/
partial def formatMathIdent (s : String) : String :=
  let s := s.trimAscii.toString
  if s.isEmpty then "x"
  else if s.startsWith "\\" then s -- already LaTeX (from alias)
  else
    -- Common Greek Unicode -> LaTeX commands
    match s with
    | "α" => "\\alpha" | "β" => "\\beta" | "γ" => "\\gamma" | "δ" => "\\delta"
    | "ε" => "\\varepsilon" | "ζ" => "\\zeta" | "η" => "\\eta" | "θ" => "\\theta" | "ι" => "\\iota"
    | "κ" => "\\kappa" | "λ" => "\\lambda" | "μ" => "\\mu" | "ν" => "\\nu"
    | "π" => "\\pi" | "ρ" => "\\rho" | "σ" => "\\sigma" | "τ" => "\\tau"
    | "φ" => "\\varphi" | "χ" => "\\chi" | "ψ" => "\\psi" | "ω" => "\\omega"
    | "Γ" => "\\Gamma" | "Δ" => "\\Delta" | "Θ" => "\\Theta" | "Λ" => "\\Lambda"
    | "Π" => "\\Pi" | "Σ" => "\\Sigma" | "Φ" => "\\Phi" | "Ψ" => "\\Psi" | "Ω" => "\\Omega"
    | "ℓ" => "\\ell"
    | "ℝ" => "\\mathbb{R}" | "ℕ" => "\\mathbb{N}" | "ℤ" => "\\mathbb{Z}"
    | "𝓡" => "\\mathcal{R}" | "𝓢" => "\\mathcal{S}" | "𝓣" => "\\mathcal{T}"
    | "𝓟" => "\\mathcal{P}" | "𝒟" => "\\mathcal{D}" | "𝒰" => "\\mathcal{U}"
    | _ =>
      if s.length == 1 then escapeLatex s
      else
        -- Handle trailing prime (e.g. `H'` -> `H'`, `R'` -> `R'`)
        if s.endsWith "'" && s.length == 2 then
          let base := (s.dropEnd 1).toString
          formatMathIdent base ++ "'"
        else
        -- Convert Unicode subscript digits `₀..₉` to ASCII digits for subscript splitting
        let subDigit : Char → Option Char
          | '₀' => some '0' | '₁' => some '1' | '₂' => some '2' | '₃' => some '3'
          | '₄' => some '4' | '₅' => some '5' | '₆' => some '6' | '₇' => some '7'
          | '₈' => some '8' | '₉' => some '9' | c => if c.isDigit then some c else none
        let chars := s.toList
        let revDigits := chars.reverse.takeWhile fun c => (subDigit c).isSome
        let baseLen := chars.length - revDigits.length
        if !revDigits.isEmpty && baseLen > 0 && baseLen ≤ 2 then
          let base := String.ofList (chars.take baseLen)
          let digits := String.ofList (revDigits.reverse.filterMap subDigit)
          formatMathIdent base ++ "_{" ++ digits ++ "}"
        else
          "\\mathrm{" ++ escapeLatex s ++ "}"

/-- Wrap `s` in `\left(…\right)` iff `childPrec < ctxPrec`. -/
def parenIf (ctxPrec childPrec : Nat) (s : String) : String :=
  if childPrec < ctxPrec then s!"\\left({s}\\right)" else s

private def argFromEnd? (args : Array Expr) (offset : Nat) : Option Expr :=
  if offset < args.size then args[args.size - 1 - offset]? else none

private def lastTwo? (args : Array Expr) : Option (Expr × Expr) := do
  let r ← argFromEnd? args 0
  let l ← argFromEnd? args 1
  return (l, r)

/-- Render a natural-number literal (handling Lean's `OfNat.ofNat` encoding). -/
private def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | _ =>
      if e.isAppOf ``OfNat.ofNat then
        match e.getAppArgs[1]? with
        | some (Expr.lit (.natVal n)) => some n
        | _ => none
      else none

/-- Core recursive `Expr → LaTeX` printer (runs inside `MetaM` so free variables resolve
to their clean local-context names and `Fintype.card` / `Nat.choose` render idiomatically). -/
partial def renderAux (tbl : SymbolTable) (ctxPrec : Nat) (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  if let some (_, alias) := tbl.exprAliases.find? (fun (pat, _) => pat == e) then
    return alias
  if let some n := natLit? e then
    return toString n
  match e with
  | .mdata _ inner => renderAux tbl ctxPrec inner
  | .lit (.natVal n) => return toString n
  | .lit (.strVal s) => return "\\texttt{\"" ++ escapeLatex s ++ "\"}"
  | .sort lvl =>
      return if lvl.isZero then "\\mathrm{Prop}" else "\\mathrm{Type}"
  | .fvar id =>
      let decl ← id.getDecl
      let clean := cleanBinderName decl.userName "x"
      match tbl.binderAliases.get? clean with
      | some alias => return alias
      | none => return formatMathIdent clean
  | .bvar i => return "x_{" ++ toString i ++ "}"
  | .mvar _ => return "\\text{?}"
  | .const name _ =>
      if let some alias := tbl.constAliases.get? name then
        return alias
      match name with
      | ``Nat => return "\\mathbb{N}"
      | ``Int => return "\\mathbb{Z}"
      | ``Bool => return "\\{0,1\\}"
      | ``Unit | ``PUnit => return "\\{\\star\\}"
      | ``Empty | ``PEmpty => return "\\emptyset"
      | ``True => return "\\top"
      | ``False => return "\\bot"
      | _ =>
          if name == `Real then return "\\mathbb{R}"
          if name == `NNReal then return "\\mathbb{R}_{\\ge 0}"
          if name == `ENNReal then return "\\mathbb{R}_{\\ge 0}^{\\infty}"
          return formatMathIdent (shortConstName name)
  | .forallE nm dom body bi =>
      if body.hasLooseBVar 0 then
        withLocalDecl nm bi dom fun fv => do
          let varStr ← renderAux tbl 100 fv
          let bodyStr ← renderAux tbl 10 (body.instantiate1 fv)
          if ← isAmbientTypeclass dom then
            return bodyStr
          return parenIf ctxPrec 10 s!"\\forall {varStr},\\; {bodyStr}"
      else
        if ← isProp dom then
          let a ← renderAux tbl 26 dom
          let b ← renderAux tbl 25 body
          return parenIf ctxPrec 25 s!"{a} \\implies {b}"
        else
          let a ← renderAux tbl 31 dom
          let b ← renderAux tbl 30 body
          return parenIf ctxPrec 30 s!"{a} \\to {b}"
  | .lam nm dom body bi =>
      withLocalDecl nm bi dom fun fv => do
        let varStr ← renderAux tbl 100 fv
        let bodyStr ← renderAux tbl 10 (body.instantiate1 fv)
        return parenIf ctxPrec 10 s!"{varStr} \\mapsto {bodyStr}"
  | .letE nm ty val body _ =>
      let valStr ← renderAux tbl 0 val
      withLetDecl nm ty val fun fv => do
        let varStr ← renderAux tbl 100 fv
        let bodyStr ← renderAux tbl ctxPrec (body.instantiate1 fv)
        return "\\text{let } " ++ varStr ++ " = " ++ valStr ++ " \\text{ in } " ++ bodyStr
  | .proj _ idx s =>
      let base ← renderAux tbl 90 s
      let field := if idx == 0 then "1" else if idx == 1 then "2" else toString (idx + 1)
      return parenIf ctxPrec 90 (base ++ "_{" ++ field ++ "}")
  | .app .. =>
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs
      if let .const head _ := fn then
        -- 1. Check domain-registered 2D handlers first (CC, Probability, SequenceHash, …)
        let handlers ← latexAppHandlers.get
        if let some hs := handlers.get? head then
          for h in hs do
            if let some (out, prec) ← h.run tbl (renderAux tbl) e args then
              return parenIf ctxPrec prec out
        -- 2. Built-in core math 2D layout rules
        if let some (out, prec) ← renderCoreApp tbl head args then
          return parenIf ctxPrec prec out
        -- 3. Zero-argument short notation (e.g. `blockBytes (hash p)` -> `r`)
        if tbl.zeroArgConsts.contains head then
          return ← renderAux tbl 95 fn
        -- 4. Generic constant application (omit implicit, typeclass, and hidden ambient args!)
        let info ← getConstInfo head
        let explicitArgs ← collectExplicitArgs info.type args
        let hidden := tbl.hiddenArgs.getD head []
        let visibleArgs : Array Expr :=
          (explicitArgs.foldl (init := (0, #[])) fun (i, acc) a =>
            (i + 1, if hidden.contains i then acc else acc.push a)).2
        let headStr ← renderAux tbl 95 fn
        if visibleArgs.isEmpty then
          return headStr
        let renderedArgs ← visibleArgs.mapM (renderAux tbl 0)
        let argList := String.intercalate ", " renderedArgs.toList
        return parenIf ctxPrec 85 s!"{headStr}\\!\\left({argList}\\right)"
      else
        let fnStr ← renderAux tbl 85 fn
        let renderedArgs ← args.mapM (renderAux tbl 0)
        let argList := String.intercalate ", " renderedArgs.toList
        return parenIf ctxPrec 85 s!"{fnStr}\\!\\left({argList}\\right)"
where
  collectExplicitArgs (ty : Expr) (args : Array Expr) : MetaM (Array Expr) := do
    let mut curTy := ty
    let mut out : Array Expr := #[]
    for arg in args do
      curTy ← whnfD curTy
      match curTy with
      | .forallE _ _ body bi =>
          if bi.isExplicit then
            out := out.push arg
          curTy := body.instantiate1 arg
      | _ =>
          out := out.push arg
    return out

  renderCoreApp (tbl : SymbolTable) (head : Name) (args : Array Expr) :
      MetaM (Option (String × Nat)) := do
    match head with
    | ``Eq =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 50 l} = {← renderAux tbl 50 r}", 50)
    | ``Ne =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 50 l} \\ne {← renderAux tbl 50 r}", 50)
    | ``LE.le =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 50 l} \\le {← renderAux tbl 50 r}", 50)
    | ``LT.lt =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 50 l} < {← renderAux tbl 50 r}", 50)
    | ``GE.ge =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 50 l} \\ge {← renderAux tbl 50 r}", 50)
    | ``GT.gt =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 50 l} > {← renderAux tbl 50 r}", 50)
    | ``Iff =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 20 l} \\iff {← renderAux tbl 20 r}", 20)
    | ``And =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 40 l} \\wedge {← renderAux tbl 40 r}", 40)
    | ``Or =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 35 l} \\vee {← renderAux tbl 35 r}", 35)
    | ``Not =>
        let some a := argFromEnd? args 0 | return none
        return some (s!"\\neg {← renderAux tbl 75 a}", 75)
    | ``HAdd.hAdd | ``Add.add =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 65 l} + {← renderAux tbl 65 r}", 65)
    | ``HSub.hSub | ``Sub.sub =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 65 l} - {← renderAux tbl 66 r}", 65)
    | ``HMul.hMul | ``Mul.mul =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 70 l} \\cdot {← renderAux tbl 70 r}", 70)
    | ``HDiv.hDiv | ``Div.div =>
        let some (l, r) := lastTwo? args | return none
        return some ("\\frac{" ++ (← renderAux tbl 0 l) ++ "}{" ++ (← renderAux tbl 0 r) ++ "}", 72)
    | ``HPow.hPow | ``Pow.pow =>
        let some (l, r) := lastTwo? args | return none
        return some ("{" ++ (← renderAux tbl 80 l) ++ "}^{" ++ (← renderAux tbl 0 r) ++ "}", 78)
    | ``Neg.neg =>
        let some a := argFromEnd? args 0 | return none
        return some (s!"-{← renderAux tbl 75 a}", 75)
    | ``Min.min =>
        let some (l, r) := lastTwo? args | return none
        return some ("\\min\\!\\left\\{" ++ (← renderAux tbl 0 l) ++ ",\\, " ++ (← renderAux tbl 0 r) ++ "\\right\\}", 85)
    | ``Max.max =>
        let some (l, r) := lastTwo? args | return none
        return some ("\\max\\!\\left\\{" ++ (← renderAux tbl 0 l) ++ ",\\, " ++ (← renderAux tbl 0 r) ++ "\\right\\}", 85)
    | ``Membership.mem =>
        -- In Lean/Mathlib `Membership.mem s x` means `x ∈ s`
        let some (set, elem) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 50 elem} \\in {← renderAux tbl 50 set}", 50)
    | ``HasSubset.Subset =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 50 l} \\subseteq {← renderAux tbl 50 r}", 50)
    | ``Singleton.singleton =>
        let some a := argFromEnd? args 0 | return none
        return some ("\\{" ++ (← renderAux tbl 0 a) ++ "\\}", 90)
    | ``Prod =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 60 l} \\times {← renderAux tbl 60 r}", 60)
    | ``Sum =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"{← renderAux tbl 60 l} \\oplus {← renderAux tbl 60 r}", 60)
    | ``Prod.mk =>
        let some (l, r) := lastTwo? args | return none
        return some (s!"({← renderAux tbl 0 l}, {← renderAux tbl 0 r})", 90)
    | _ =>
        if head == `Dvd.dvd then
          let some (a, b) := lastTwo? args | return none
          return some (s!"{← renderAux tbl 50 a} \\mid {← renderAux tbl 50 b}", 50)
        if head == `abs then
          let some a := argFromEnd? args 0 | return none
          return some (s!"\\left|{← renderAux tbl 0 a}\\right|", 90)
        if head == `Nat.choose then
          let some (n, k) := lastTwo? args | return none
          return some ("\\binom{" ++ (← renderAux tbl 0 n) ++ "}{" ++ (← renderAux tbl 0 k) ++ "}", 85)
        if head == `Fintype.card || head == `Finset.card then
          let some a := argFromEnd? args 0 | return none
          return some (s!"\\left|{← renderAux tbl 0 a}\\right|", 90)
        if head == `List.length then
          let some a := argFromEnd? args 0 | return none
          return some (s!"\\left|{← renderAux tbl 0 a}\\right|", 90)
        if head == `Fin then
          let some n := argFromEnd? args 0 | return none
          return some (s!"[\\,{← renderAux tbl 0 n}\\,]", 90)
        return none

/-- Public entry point: run the hygiene/normalization firewall, then print 2D LaTeX. -/
def exprToLatex (e : Expr) (tbl : SymbolTable := {}) (ctxPrec : Nat := 0) : MetaM String := do
  let clean ← normalizeForPresentation e
  renderAux tbl ctxPrec clean

end Informalization.Core.LeanTeX
