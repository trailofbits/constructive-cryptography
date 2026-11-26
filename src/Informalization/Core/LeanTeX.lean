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

/-- Font style applied to rendered local variables of an annotated type (`varStyle?`). -/
inductive MathFontStyle
  | italic
  | mathcal
  | mathbf
  | mathbb
  | mathsf
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Scoped symbol overrides threaded through one informalization pass (e.g., mapping
a constant name, local binder name, or repeated subexpression to a preferred LaTeX symbol,
and suppressing ambient leading explicit arguments on verbose Lean definitions). -/
structure SymbolTable where
  constAliases : NameMap String := {}
  binderAliases : Std.HashMap String String := {}
  hiddenArgs : NameMap (List Nat) := {}
  zeroArgConsts : NameSet := {}
  exprAliases : Array (Expr × String) := #[]
  fvarStyles : Std.HashMap FVarId MathFontStyle := {}
  shortAliases : NameMap String := {}
  constTemplates : NameMap String := {}
  usedNames : Std.HashSet String := {}
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

def SymbolTable.withFVarStyle (t : SymbolTable) (id : FVarId) (st : MathFontStyle) : SymbolTable :=
  { t with fvarStyles := t.fvarStyles.insert id st }

def SymbolTable.withShortAlias (t : SymbolTable) (n : Name) (latex : String) : SymbolTable :=
  { t with shortAliases := t.shortAliases.insert n latex }

def SymbolTable.withConstTemplate (t : SymbolTable) (n : Name) (tmpl : String) : SymbolTable :=
  { t with constTemplates := t.constTemplates.insert n tmpl }

def SymbolTable.withUsedName (t : SymbolTable) (s : String) : SymbolTable :=
  if s.isEmpty then t else { t with usedNames := t.usedNames.insert s }

def SymbolTable.withUsedNames (t : SymbolTable) (ss : Array String) : SymbolTable :=
  ss.foldl SymbolTable.withUsedName t

def SymbolTable.withNormalizedExprAlias (t : SymbolTable) (e : Expr) (latex : String) :
    MetaM SymbolTable := do
  let clean ← normalizeForPresentation e
  return t.withExprAlias clean latex

/-- Callback for recursive child printing with precedence `ctxPrec`. -/
abbrev Recurse := Nat → Expr → MetaM String

/-- Extensible hook for resolving `varStyle?` on local variables (`FVarId` + type `Expr`).
Registered by `Core/Presentation.lean` using `paperDescribeExt` and typeclass context. -/
initialize fvarStyleHookRef : IO.Ref (FVarId → Expr → MetaM (Option MathFontStyle)) ←
  IO.mkRef (fun _ _ => pure none)

def registerFVarStyleHook (f : FVarId → Expr → MetaM (Option MathFontStyle)) : IO Unit :=
  fvarStyleHookRef.set f

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

/-- Whether a rendered LaTeX fragment contains a multi-letter styled command macro
such as `\mathsf{...}`, `\mathbf{...}`, `\mathrm{...}`, `\mathcal{...}`, or `\mathbb{...}`. -/
def hasStyledLatexMacro (s : String) : Bool :=
  ["\\mathsf{", "\\mathbf{", "\\mathrm{", "\\mathcal{", "\\mathbb{",
   "\\text{", "\\operatorname{", "\\boldsymbol{"].any fun m => (s.splitOn m).length > 1

/-- Join two juxtaposed CC/mathematical tokens, always separating adjacent multi-letter styled
tokens (`\mathsf{...}`, `\mathbf{...}`, `\mathrm{...}`, `\mathcal{...}`) with `\,` so tokens
never glue together (e.g. `\mathsf{PTXT}\,\mathsf{CCA}\,\mathbf{E}_{\mathsf{AE}}`). -/
def juxtaposeMath (left right : String) : String :=
  let l := left.trimAscii.toString
  let r := right.trimAscii.toString
  if l.isEmpty then r
  else if r.isEmpty then l
  else if hasStyledLatexMacro l || hasStyledLatexMacro r then
    s!"{l}\\,{r}"
  else if l.endsWith "}" || l.endsWith ")" then
    s!"{l}\\,{r}"
  else if l.startsWith "\\" then
    s!"{l} {r}"
  else if l.length == 1 && r.startsWith "\\" then
    s!"{l}{r}"
  else
    s!"{l}\\,{r}"

/-- Format a short mathematical identifier cleanly: single Latin/Greek letters stay bare
italic (`x`, `q`, `ε`), multi-letter names use `\mathrm` cleanly, Unicode subscripts (`εₚ`,
`x₁`) and ASCII short subscripts (`ε_c`, `x_0`, `q_e`, `ε_p`) render as `base_{sub}`, and
trailing primes (`w'`, `w''`) are preserved. -/
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
      else if s.endsWith "'" && s.length > 1 then
        let base := (s.dropEnd 1).toString
        formatMathIdent base ++ "'"
      else
        -- Handle ASCII subscript `<ident>_<sub1..3>` (e.g. `ε_c`, `x_0`, `q_e`, `ε_p`)
        let underParts := s.splitOn "_"
        if underParts.length == 2 then
          let base := underParts[0]!
          let sub := underParts[1]!
          if !base.isEmpty && !sub.isEmpty && sub.length ≤ 3 && sub.all Char.isAlphanum &&
             (base.length ≤ 2 || (base.length ≤ 3 && sub.all Char.isDigit)) then
            formatMathIdent base ++ "_{" ++ sub ++ "}"
          else
            "\\mathrm{" ++ escapeLatex s ++ "}"
        else
          -- Convert Unicode subscript digits `₀..₉` and subscript letters `ₚ, ₑ, ...`
          let subChar : Char → Option Char
            | '₀' => some '0' | '₁' => some '1' | '₂' => some '2' | '₃' => some '3'
            | '₄' => some '4' | '₅' => some '5' | '₆' => some '6' | '₇' => some '7'
            | '₈' => some '8' | '₉' => some '9'
            | 'ₐ' => some 'a' | 'ₑ' => some 'e' | 'ₕ' => some 'h' | 'ᵢ' => some 'i'
            | 'ⱼ' => some 'j' | 'ₖ' => some 'k' | 'ₗ' => some 'l' | 'ₘ' => some 'm'
            | 'ₙ' => some 'n' | 'ₒ' => some 'o' | 'ₚ' => some 'p' | 'ᵣ' => some 'r'
            | 'ₛ' => some 's' | 'ₜ' => some 't' | 'ᵤ' => some 'u' | 'ᵥ' => some 'v'
            | 'ₓ' => some 'x'
            | c => if c.isDigit then some c else none
          let chars := s.toList
          let revSubs := chars.reverse.takeWhile fun c => (subChar c).isSome
          let baseLen := chars.length - revSubs.length
          if !revSubs.isEmpty && baseLen > 0 && baseLen ≤ 2 then
            let base := String.ofList (chars.take baseLen)
            let subStr := String.ofList (revSubs.reverse.filterMap subChar)
            formatMathIdent base ++ "_{" ++ subStr ++ "}"
          else
            "\\mathrm{" ++ escapeLatex s ++ "}"

/-- Wrap the base stem of a math identifier in `MathFontStyle` while preserving trailing primes
and subscripts cleanly (e.g., `G₀` + `.mathbf` → `\mathbf{G}_{0}`, `E'` + `.mathcal` → `\mathcal{E}'`). -/
partial def applyMathFontStyle (style : MathFontStyle) (raw : String) : String :=
  if style == .italic then
    formatMathIdent raw
  else
    let s := raw.trimAscii.toString
    if s.isEmpty then formatMathIdent raw
    else if s.startsWith "\\mathcal" || s.startsWith "\\mathbf" ||
            s.startsWith "\\mathbb" || s.startsWith "\\mathsf" then
      s
    else
      let rec peelPrimes (str : String) (primes : String) : String × String :=
        if str.endsWith "'" && str.length > 1 then
          peelPrimes (str.dropEnd 1).toString (primes ++ "'")
        else (str, primes)
      let (noPrimes, primes) := peelPrimes s ""
      let styleStem (stem : String) : String :=
        let inner := formatMathIdent stem
        if inner.startsWith "\\mathcal" || inner.startsWith "\\mathbf" ||
           inner.startsWith "\\mathbb" || inner.startsWith "\\mathsf" then inner
        else if inner.startsWith "\\mathrm{" && inner.endsWith "}" then
          let body := ((inner.drop 8).dropEnd 1).toString
          let upperShort := !body.isEmpty && body.length ≤ 2 && body.all (fun c => 'A' ≤ c && c ≤ 'Z')
          match style with
          | .italic => inner
          | .mathcal => if upperShort then "\\mathcal{" ++ body ++ "}" else inner
          | .mathbf  => "\\mathbf{" ++ body ++ "}"
          | .mathbb  => if upperShort then "\\mathbb{" ++ body ++ "}" else inner
          | .mathsf  => "\\mathsf{" ++ body ++ "}"
        else
          let upperShort := !stem.isEmpty && stem.length ≤ 2 && stem.all (fun c => 'A' ≤ c && c ≤ 'Z')
          match style with
          | .italic => inner
          | .mathcal => if upperShort then "\\mathcal{" ++ inner ++ "}" else inner
          | .mathbf  => "\\mathbf{" ++ inner ++ "}"
          | .mathbb  => if upperShort then "\\mathbb{" ++ inner ++ "}" else inner
          | .mathsf  => "\\mathsf{" ++ inner ++ "}"
      let underParts := noPrimes.splitOn "_"
      if underParts.length == 2 then
        let base := underParts[0]!
        let sub := underParts[1]!
        if !base.isEmpty && !sub.isEmpty && sub.length ≤ 3 && sub.all Char.isAlphanum &&
           (base.length ≤ 2 || (base.length ≤ 3 && sub.all Char.isDigit)) then
          styleStem base ++ "_{" ++ sub ++ "}" ++ primes
        else
          styleStem noPrimes ++ primes
      else
        let subChar : Char → Option Char
          | '₀' => some '0' | '₁' => some '1' | '₂' => some '2' | '₃' => some '3'
          | '₄' => some '4' | '₅' => some '5' | '₆' => some '6' | '₇' => some '7'
          | '₈' => some '8' | '₉' => some '9'
          | 'ₐ' => some 'a' | 'ₑ' => some 'e' | 'ₕ' => some 'h' | 'ᵢ' => some 'i'
          | 'ⱼ' => some 'j' | 'ₖ' => some 'k' | 'ₗ' => some 'l' | 'ₘ' => some 'm'
          | 'ₙ' => some 'n' | 'ₒ' => some 'o' | 'ₚ' => some 'p' | 'ᵣ' => some 'r'
          | 'ₛ' => some 's' | 'ₜ' => some 't' | 'ᵤ' => some 'u' | 'ᵥ' => some 'v'
          | 'ₓ' => some 'x'
          | c => if c.isDigit then some c else none
        let chars := noPrimes.toList
        let revSubs := chars.reverse.takeWhile fun c => (subChar c).isSome
        let baseLen := chars.length - revSubs.length
        if !revSubs.isEmpty && baseLen > 0 && baseLen ≤ 2 then
          let base := String.ofList (chars.take baseLen)
          let subStr := String.ofList (revSubs.reverse.filterMap subChar)
          styleStem base ++ "_{" ++ subStr ++ "}" ++ primes
        else
          styleStem noPrimes ++ primes

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

private def isZeroLit (e : Expr) : Bool :=
  match natLit? e with
  | some 0 => true
  | _ =>
      let c := e.consumeMData
      c.isAppOf ``Zero.zero || c.isConstOf ``Nat.zero

private def isOneLit (e : Expr) : Bool :=
  match natLit? e with
  | some 1 => true
  | _ => e.consumeMData.isAppOf ``One.one

/-- Sound display-only algebraic simplification (`x + 0 → x`, `0 + x → x`, `x - 0 → x`,
`1 * x → x`, `x * 1 → x`), recursively handling nested identities such as `(1 - 0) · μ → μ`. -/
private partial def simplifyDisplayArith (tbl : SymbolTable) (e : Expr) : Expr :=
  let c := e.consumeMData
  if tbl.exprAliases.any (fun (pat, _) => pat.consumeMData == c) then c
  else
    let fn := c.getAppFn.consumeMData
    let args := c.getAppArgs
    let exactBin? (arity : Nat) : Option (Expr × Expr) :=
      if args.size == arity then some (args[arity - 2]!, args[arity - 1]!) else none
    if fn.isConstOf ``HAdd.hAdd then
      if let some (l, r) := exactBin? 6 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isZeroLit r' then l' else if isZeroLit l' then r' else c
      else c
    else if fn.isConstOf ``Add.add then
      if let some (l, r) := exactBin? 4 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isZeroLit r' then l' else if isZeroLit l' then r' else c
      else c
    else if fn.isConstOf ``Nat.add then
      if let some (l, r) := exactBin? 2 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isZeroLit r' then l' else if isZeroLit l' then r' else c
      else c
    else if fn.isConstOf ``HSub.hSub then
      if let some (l, r) := exactBin? 6 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isZeroLit r' then l' else c
      else c
    else if fn.isConstOf ``Sub.sub then
      if let some (l, r) := exactBin? 4 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isZeroLit r' then l' else c
      else c
    else if fn.isConstOf ``Nat.sub then
      if let some (l, r) := exactBin? 2 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isZeroLit r' then l' else c
      else c
    else if fn.isConstOf ``HMul.hMul then
      if let some (l, r) := exactBin? 6 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isOneLit l' then r' else if isOneLit r' then l' else c
      else c
    else if fn.isConstOf ``Mul.mul then
      if let some (l, r) := exactBin? 4 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isOneLit l' then r' else if isOneLit r' then l' else c
      else c
    else if fn.isConstOf ``Nat.mul then
      if let some (l, r) := exactBin? 2 then
        let l' := simplifyDisplayArith tbl l
        let r' := simplifyDisplayArith tbl r
        if isOneLit l' then r' else if isOneLit r' then l' else c
      else c
    else c

/-- Merge a subscript `field` onto `base`, avoiding invalid KaTeX double subscripts such as
`z_{1}_{2}` by merging trailing `_{...}` into `z_{1,2}`. -/
private def appendSubscript (base field : String) : String := Id.run do
  if base.endsWith "}" then
    let arr := base.toList.toArray
    let mut depth : Int := 0
    let mut matchIdx? : Option Nat := none
    let mut i := arr.size
    while i > 0 do
      i := i - 1
      let c := arr[i]!
      let escaped := i > 0 && arr[i - 1]! == '\\'
      if !escaped then
        if c == '}' then depth := depth + 1
        else if c == '{' then
          depth := depth - 1
          if depth == 0 then
            matchIdx? := some i
            break
    match matchIdx? with
    | some idx =>
        if idx > 0 && arr[idx - 1]! == '_' && !(idx > 1 && arr[idx - 2]! == '\\') then
          return (base.dropEnd 1).toString ++ "," ++ field ++ "}"
        else
          return base ++ "_{" ++ field ++ "}"
    | none => return base ++ "_{" ++ field ++ "}"
  else
    let arr := base.toList.toArray
    if arr.size ≥ 2 && arr[arr.size - 2]! == '_' &&
       !(arr.size ≥ 3 && arr[arr.size - 3]! == '\\') && arr[arr.size - 1]!.isAlphanum then
      return (base.dropEnd 1).toString ++ "{" ++ arr[arr.size - 1]!.toString ++ "," ++ field ++ "}"
    else
      return base ++ "_{" ++ field ++ "}"

/-- If `e` is a finite `List.cons` chain ending in `List.nil`, return its element `Expr`s. -/
private partial def collectListElems? (e : Expr) : Option (List Expr) :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf ``List.nil && args.size ≤ 1 then
    some []
  else if fn.isConstOf ``List.cons && args.size == 3 then
    (collectListElems? args[2]!).map (args[1]! :: ·)
  else
    none

/-- Choose a bound variable name for `Finset.sum` / `Finset.prod` / `Finset.filter` / `List.sum`
that never collides with free variables or rendered symbols in the domain/set expression
(preventing bound-variable shadowing such as `∑_{x ∈ x}`). -/
private def chooseUnshadowedSumBinder (tbl : SymbolTable) (nm : Name) (dom : Expr)
    (avoidStrings : Array String) (avoidExprs : Array Expr) (fallback : String := "i") :
    MetaM Name := do
  let lctx ← getLCtx
  let mut taken : Std.HashSet String := {}
  for d in lctx do
    if !d.isAuxDecl && !d.isImplementationDetail && d.binderInfo != .instImplicit then
      if let some s := cleanBinderName? d.userName then
        taken := taken.insert s
  for ex in avoidExprs do
    for fvid in (Lean.collectFVars {} ex).fvarIds do
      if let some d := lctx.find? fvid then
        taken := taken.insert (cleanBinderName d.userName "x")
  let base := cleanBinderName nm fallback
  let isFreeOfShadow (cand : String) : MetaM Bool := do
    if taken.contains cand then return false
    let candTex ←
      match tbl.binderAliases.get? cand with
      | some al => pure al
      | none =>
          withLocalDecl (Name.mkSimple cand) .default dom fun fv => do
            match (← (← fvarStyleHookRef.get) fv.fvarId! dom) with
            | some st => pure (applyMathFontStyle st cand)
            | none => pure (formatMathIdent cand)
    if avoidStrings.any (fun s => s == candTex || mathDispAppearsIn #[s] candTex) then
      return false
    if cand != candTex && avoidStrings.any (fun s => s == cand || mathDispAppearsIn #[s] cand) then
      return false
    return true
  if ← isFreeOfShadow base then
    return Name.mkSimple base
  for cand in ["y", "t", "e", "j", "k", "u", "v"] do
    if ← isFreeOfShadow cand then
      return Name.mkSimple cand
  let mut p := base ++ "'"
  for _ in [:6] do
    if ← isFreeOfShadow p then
      return Name.mkSimple p
    p := p ++ "'"
  freshShadowFreeName nm fallback

/-- Pick a fresh local LaTeX display name that avoids `usedNames` while preserving distinct
non-colliding names. -/
def pickFreshLocalSymbol (used : Std.HashSet String) (preferred : String) : String :=
  if !used.contains preferred then preferred
  else
    let primed := #[preferred ++ "'", preferred ++ "''"]
    match primed.find? (!used.contains ·) with
    | some p => p
    | none =>
        let pool := #["w", "z", "u", "v", "t", "y", "a", "b"].flatMap fun pfx =>
          #[1, 2, 3, 4, 5, 6].map fun i => s!"{pfx}_\{{i}}"
        (pool.find? (!used.contains ·)).getD (preferred ++ "_{1}")

/-- Recognize membership expressions `x ∈ S` (`Membership.mem`, `Set.Mem`, `Set.mem`, `List.Mem`),
returning `(elem, set)`. -/
def matchMembershipExpr? (e : Expr) : Option (Expr × Expr) :=
  let c := e.consumeMData
  let fn := c.getAppFn.consumeMData
  let args := c.getAppArgs
  if fn.isConstOf ``Membership.mem && args.size == 5 then
    some (args[4]!, args[3]!)
  else if fn.isConstOf `Set.Mem && args.size == 3 then
    some (args[2]!, args[1]!)
  else if fn.isConstOf `Set.mem && args.size == 3 then
    some (args[1]!, args[2]!)
  else if fn.isConstOf ``List.Mem && args.size == 3 then
    some (args[1]!, args[2]!)
  else
    none

/-- Recognize negated membership `¬ (x ∈ S)` or `(x ∈ S) → False`, returning `(elem, set)`. -/
def matchNotMembershipExpr? (e : Expr) : Option (Expr × Expr) :=
  let c := e.consumeMData
  if c.isAppOf ``Not && c.getAppArgs.size == 1 then
    matchMembershipExpr? c.getAppArgs[0]!
  else match c with
    | .forallE _ dom body _ =>
        if !body.hasLooseBVar 0 && body.consumeMData.isConstOf ``False then
          matchMembershipExpr? dom
        else none
    | _ => none

/-- Core recursive `Expr → LaTeX` printer with per-call $O(\text{DAG})$ memoization on closed
subterms (runs inside `MetaM` so free variables resolve cleanly). -/
private partial def renderAuxMemo (memo : IO.Ref (Std.HashMap (Expr × Nat) String))
    (tbl : SymbolTable) (ctxPrec : Nat) (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  let cacheKey? := if !e.hasLooseBVars && !e.hasExprMVar then some (e, ctxPrec) else none
  if let some k := cacheKey? then
    if let some hit := (← memo.get).get? k then
      return hit
  let out ← renderUncached e
  if let some k := cacheKey? then
    memo.modify (·.insert k out)
  return out
where
  recGo (prec : Nat) (x : Expr) : MetaM String :=
    renderAuxMemo memo tbl prec x
  renderUncached (e : Expr) : MetaM String := do
    if let some (_, alias) := tbl.exprAliases.reverse.find? (fun (pat, _) => pat.consumeMData == e.consumeMData) then
      return alias
    if let some n := natLit? e then
      return toString n
    match e with
    | .mdata _ inner => recGo ctxPrec inner
    | .lit (.natVal n) => return toString n
    | .lit (.strVal s) => return "\\texttt{\"" ++ escapeLatex s ++ "\"}"
    | .sort lvl =>
        return if lvl.isZero then "\\mathrm{Prop}" else "\\mathrm{Type}"
    | .fvar id =>
        let decl ← id.getDecl
        let clean := cleanBinderName decl.userName "x"
        match tbl.binderAliases.get? clean with
        | some alias => return alias
        | none =>
            match tbl.fvarStyles.get? id with
            | some st => return applyMathFontStyle st clean
            | none =>
                match (← (← fvarStyleHookRef.get) id decl.type) with
                | some st => return applyMathFontStyle st clean
                | none => return formatMathIdent clean
    | .bvar i => return "x_{" ++ toString i ++ "}"
    | .mvar _ => return "\\text{?}"
    | .const name _ =>
        if let some alias := tbl.shortAliases.get? name then
          return alias
        if let some alias := tbl.constAliases.get? name then
          if (alias.splitOn "#1").length > 1 then
            let mut cleanAlias := alias
            for k in [1:10] do
              cleanAlias := cleanAlias.replace s!"#{k}" "\\cdot"
            return cleanAlias
          return alias
        match name with
        | ``Nat => return "\\mathbb{N}"
        | ``Int => return "\\mathbb{Z}"
        | ``Bool => return "\\{0,1\\}"
        | ``Unit | ``PUnit => return "\\{\\star\\}"
        | ``Empty | ``PEmpty => return "\\emptyset"
        | ``True => return "\\top"
        | ``False => return "\\mathsf{False}"
        | _ =>
            if name == `Real then return "\\mathbb{R}"
            if name == `NNReal then return "\\mathbb{R}_{\\ge 0}"
            if name == `ENNReal then return "\\mathbb{R}_{\\ge 0}^{\\infty}"
            if name == ``Prod.fst || name == ``PProd.fst || name == ``Sigma.fst then return "\\pi_{1}"
            if name == ``Prod.snd || name == ``PProd.snd || name == ``Sigma.snd then return "\\pi_{2}"
            return formatMathIdent (shortConstName name)
    | .forallE nm dom body bi =>
        let isUnitDom := dom.consumeMData == mkConst ``Unit || dom.consumeMData == mkConst ``PUnit
        if isUnitDom && !body.hasLooseBVar 0 then
          recGo ctxPrec body
        else if ← isAmbientTypeclass dom then
          withLocalDecl nm bi dom fun fv => recGo ctxPrec (body.instantiate1 fv)
        else if ← isProp dom then
          if !body.hasLooseBVar 0 && body.consumeMData.isConstOf ``False then
            let domNorm ← normalizeForPresentation dom
            if let some (elem, set) := matchMembershipExpr? domNorm then
              return parenIf ctxPrec 50 s!"{← recGo 50 elem} \\notin {← recGo 50 set}"
          let a ← recGo 26 dom
          let b ←
            if body.hasLooseBVar 0 then
              withLocalDecl nm bi dom fun fv => recGo 25 (body.instantiate1 fv)
            else recGo 25 body
          return parenIf ctxPrec 25 s!"{a} \\implies {b}"
        else if body.hasLooseBVar 0 then
          let freshNm ← freshShadowFreeName nm "x"
          withLocalDecl freshNm bi dom fun fv => do
            let varStr ← recGo 100 fv
            let bodyStr ← recGo 10 (body.instantiate1 fv)
            return parenIf ctxPrec 10 s!"\\forall {varStr},\\; {bodyStr}"
        else
          let a ← recGo 31 dom
          let b ← recGo 30 body
          return parenIf ctxPrec 30 s!"{a} \\to {b}"
    | .lam nm dom body bi =>
        -- Drop vacuous unused `Unit`/`PUnit` lambdas (e.g., unkeyed `fun (_ : Unit) => H`)
        let isUnitDom := dom.consumeMData == mkConst ``Unit || dom.consumeMData == mkConst ``PUnit
        if isUnitDom && !body.hasLooseBVar 0 then
          recGo ctxPrec body
        else
          -- Avoid shadowed `x ↦ x ↦ ...` when binders collide with visible context
          let chosenNm ←
            if (cleanBinderName? nm).isSome then
              freshShadowFreeName nm "x"
            else
              let lctx ← getLCtx
              let existing := lctx.foldl (init := ([] : List String)) fun acc d =>
                match cleanBinderName? d.userName with
                | some s => s :: acc
                | none => acc
              let pool := ["x", "y", "z", "u", "v", "w"]
              match pool.find? (fun p => !existing.contains p) with
              | some fresh => pure (Name.mkSimple fresh)
              | none => freshShadowFreeName nm "x"
          withLocalDecl chosenNm bi dom fun fv => do
            let varStr ← recGo 100 fv
            let bodyStr ← recGo 10 (body.instantiate1 fv)
            return parenIf ctxPrec 10 s!"{varStr} \\mapsto {bodyStr}"
    | .letE nm ty val body _ =>
        if nm == `this || nm.eraseMacroScopes == `this || nm.hasMacroScopes || (cleanBinderName? nm).isNone then
          let red ← normalizeForPresentation (body.instantiate1 val)
          recGo ctxPrec red
        else
          let valStr ← recGo 0 val
          withLetDecl nm ty val fun fv => do
            let varStr ← recGo 100 fv
            let bodyStr ← recGo ctxPrec (body.instantiate1 fv)
            return "\\text{let } " ++ varStr ++ " = " ++ valStr ++ " \\text{ in } " ++ bodyStr
    | .proj structName idx s =>
        if (structName == ``Fin || structName == ``Subtype) && idx == 0 then
          return ← recGo ctxPrec s
        let base ← recGo 90 s
        if structName == ``Prod || structName == ``PProd || structName == ``Sigma then
          let field := if idx == 0 then "1" else if idx == 1 then "2" else toString (idx + 1)
          return parenIf ctxPrec 90 (appendSubscript base field)
        let env ← getEnv
        match getStructureInfo? env structName with
        | some info =>
            if h : idx < info.fieldNames.size then
              let fname := info.fieldNames[idx]
              if (structName == ``Fin || structName == ``Subtype) && fname == `val then
                return ← recGo ctxPrec s
              return parenIf ctxPrec 90 (base ++ ".\\mathrm{" ++ escapeLatex fname.toString ++ "}")
            else
              return parenIf ctxPrec 90 (appendSubscript base (toString (idx + 1)))
        | none =>
            return parenIf ctxPrec 90 (appendSubscript base (toString (idx + 1)))
    | .app .. =>
        let fn := e.getAppFn.consumeMData
        let args := e.getAppArgs
        if let .const head _ := fn then
          -- 1. Check domain-registered 2D handlers first (CC, Probability, SequenceHash, …)
          let handlers ← latexAppHandlers.get
          if let some hs := handlers.get? head then
            for h in hs do
              if let some (out, prec) ← h.run tbl recGo e args then
                return parenIf ctxPrec prec out
          -- 1b. Sound display-only algebraic identities (`x + 0`, `x - 0`, `1 * x`, `(1 - 0) * μ`)
          let simp := simplifyDisplayArith tbl e
          if simp != e.consumeMData then
            return ← recGo ctxPrec simp
          -- 2. Built-in core math 2D layout rules
          if let some (out, prec) ← renderCoreApp tbl head args then
            return parenIf ctxPrec prec out
          -- 2b. Template notation (`#1`, `#2`, ...) from `@[math_notation]`
          if let some tmpl := tbl.constTemplates.get? head then
            let info ← getConstInfo head
            let explicitArgs ← collectExplicitArgs info.type args
            let hidden := tbl.hiddenArgs.getD head []
            let visibleArgs : Array Expr :=
              (explicitArgs.foldl (init := (0, #[])) fun (i, acc) a =>
                (i + 1, if hidden.contains i then acc else acc.push a)).2
            if tmpl.trimAscii.toString == "#1 \\oplus #2" && visibleArgs.size == 2 then
              let lStr ← recGo 65 visibleArgs[0]!
              let rStr ← recGo 66 visibleArgs[1]!
              return parenIf ctxPrec 65 (lStr ++ " \\oplus " ++ rStr)
            let renderedArgs ← visibleArgs.mapM (recGo 0)
            let mut out := tmpl
            for idx in [:renderedArgs.size] do
              out := out.replace s!"#{idx + 1}" renderedArgs[idx]!
            for k in [renderedArgs.size + 1 : 10] do
              out := out.replace s!"#{k}" "\\cdot"
            return parenIf ctxPrec 85 out
          -- 3. Zero-argument short notation (e.g. `blockBytes (hash p)` -> `r`)
          if tbl.zeroArgConsts.contains head then
            return ← recGo 95 fn
          -- 3b. Structure projection function lookup via `Lean.getStructureInfo?`
          let env ← getEnv
          if !tbl.constAliases.contains head && !tbl.shortAliases.contains head then
            if let some projInfo := env.getProjectionFnInfo? head then
              if let some (.ctorInfo cinfo) := env.find? projInfo.ctorName then
                let structName := cinfo.induct
                if (structName == ``Fin || structName == ``Subtype) &&
                   projInfo.i == 0 && args.size == projInfo.numParams + 1 then
                  return ← recGo ctxPrec args[projInfo.numParams]!
                if !Lean.isClass env structName &&
                   structName != ``Prod && structName != ``PProd &&
                   structName != ``Sigma && structName != ``Subtype &&
                   structName != ``Fin &&
                   args.size > projInfo.numParams then
                  if let some sinfo := getStructureInfo? env structName then
                    if h : projInfo.i < sinfo.fieldNames.size then
                      let structStr ← recGo 90 args[projInfo.numParams]!
                      let fname := sinfo.fieldNames[projInfo.i]
                      let base := structStr ++ ".\\mathrm{" ++ escapeLatex fname.toString ++ "}"
                      if args.size == projInfo.numParams + 1 then
                        return parenIf ctxPrec 90 base
                      else
                        let info ← getConstInfo head
                        let hidden := tbl.hiddenArgs.getD head []
                        let visibleTrailing ← collectVisibleTrailingArgs info.type args (projInfo.numParams + 1) hidden
                        if visibleTrailing.isEmpty then
                          return parenIf ctxPrec 90 base
                        let renderedArgs ← visibleTrailing.mapM (recGo 0)
                        let argList := String.intercalate ", " renderedArgs.toList
                        return parenIf ctxPrec 85 s!"{base}\\!\\left({argList}\\right)"
          -- 4. Generic constant application (omit implicit, typeclass, and hidden ambient args!)
          let info ← getConstInfo head
          let explicitArgs ← collectExplicitArgs info.type args
          let hidden := tbl.hiddenArgs.getD head []
          let visibleArgs : Array Expr :=
            (explicitArgs.foldl (init := (0, #[])) fun (i, acc) a =>
              (i + 1, if hidden.contains i then acc else acc.push a)).2
          let headStr ← recGo 95 fn
          if visibleArgs.isEmpty then
            return headStr
          let renderedArgs ← visibleArgs.mapM (recGo 0)
          let argList := String.intercalate ", " renderedArgs.toList
          return parenIf ctxPrec 85 s!"{headStr}\\!\\left({argList}\\right)"
        else
          let fnStr ← recGo 85 fn
          let renderedArgs ← args.mapM (recGo 0)
          let argList := String.intercalate ", " renderedArgs.toList
          return parenIf ctxPrec 85 s!"{fnStr}\\!\\left({argList}\\right)"
  collectVisibleTrailingArgs (ty : Expr) (args : Array Expr) (startIdx : Nat)
      (hidden : List Nat) : MetaM (Array Expr) := do
    let mut curTy := ty
    let mut out : Array Expr := #[]
    let mut expIdx : Nat := 0
    for idx in [:args.size] do
      let arg := args[idx]!
      let f ← match curTy.consumeMData with
        | x@(.forallE ..) => pure x
        | other => withTransparency .reducible (whnf other)
      match f.consumeMData with
      | .forallE _ dom body bi =>
          if bi.isExplicit then
            let skipProof ←
              if !dom.hasLooseBVars then
                (try isProp dom catch _ => pure false)
              else pure false
            if !skipProof then
              if idx ≥ startIdx && !hidden.contains expIdx then
                out := out.push arg
              expIdx := expIdx + 1
          curTy := body.instantiate1 arg
      | _ =>
          if idx ≥ startIdx then
            out := out.push arg
    return out
  collectExplicitArgs (ty : Expr) (args : Array Expr) : MetaM (Array Expr) := do
    let mut curTy := ty
    let mut out : Array Expr := #[]
    for arg in args do
      let f ← match curTy.consumeMData with
        | x@(.forallE ..) => pure x
        | other => withTransparency .reducible (whnf other)
      match f.consumeMData with
      | .forallE _ dom body bi =>
          if bi.isExplicit then
            let skipProof ←
              if !dom.hasLooseBVars then
                (try isProp dom catch _ => pure false)
              else pure false
            if !skipProof then
              out := out.push arg
          curTy := body.instantiate1 arg
      | _ =>
          out := out.push arg
    return out
  renderCoreApp (tbl : SymbolTable) (head : Name) (args : Array Expr) :
      MetaM (Option (String × Nat)) := do
    let exactBin? (arity : Nat) : Option (Expr × Expr) :=
      if args.size == arity then some (args[arity - 2]!, args[arity - 1]!) else none
    match head with
    | ``Eq =>
        let some (l, r) := exactBin? 3 | return none
        return some (s!"{← recGo 50 l} = {← recGo 50 r}", 50)
    | ``Ne =>
        let some (l, r) := exactBin? 3 | return none
        return some (s!"{← recGo 50 l} \\ne {← recGo 50 r}", 50)
    | ``LE.le =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"{← recGo 50 l} \\le {← recGo 50 r}", 50)
    | ``LT.lt =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"{← recGo 50 l} < {← recGo 50 r}", 50)
    | ``GE.ge =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"{← recGo 50 l} \\ge {← recGo 50 r}", 50)
    | ``GT.gt =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"{← recGo 50 l} > {← recGo 50 r}", 50)
    | ``Iff =>
        let some (l, r) := exactBin? 2 | return none
        return some (s!"{← recGo 20 l} \\iff {← recGo 20 r}", 20)
    | ``And =>
        let some (l, r) := exactBin? 2 | return none
        return some (s!"{← recGo 40 l} \\wedge {← recGo 40 r}", 40)
    | ``Or =>
        let some (l, r) := exactBin? 2 | return none
        return some (s!"{← recGo 35 l} \\vee {← recGo 35 r}", 35)
    | ``Not =>
        if args.size != 1 then return none
        let innerNorm ← normalizeForPresentation args[0]!
        if let some (elem, set) := matchMembershipExpr? innerNorm then
          return some (s!"{← recGo 50 elem} \\notin {← recGo 50 set}", 50)
        return some (s!"\\neg {← recGo 75 args[0]!}", 75)
    | ``HAdd.hAdd =>
        let some (l, r) := exactBin? 6 | return none
        return some (s!"{← recGo 65 l} + {← recGo 65 r}", 65)
    | ``Add.add =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"{← recGo 65 l} + {← recGo 65 r}", 65)
    | ``HSub.hSub =>
        let some (l, r) := exactBin? 6 | return none
        return some (s!"{← recGo 65 l} - {← recGo 66 r}", 65)
    | ``Sub.sub =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"{← recGo 65 l} - {← recGo 66 r}", 65)
    | ``HMul.hMul =>
        let some (l, r) := exactBin? 6 | return none
        return some (s!"{← recGo 70 l} \\cdot {← recGo 70 r}", 70)
    | ``Mul.mul =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"{← recGo 70 l} \\cdot {← recGo 70 r}", 70)
    | ``HDiv.hDiv =>
        let some (l, r) := exactBin? 6 | return none
        return some ("\\frac{" ++ (← recGo 0 l) ++ "}{" ++ (← recGo 0 r) ++ "}", 72)
    | ``Div.div =>
        let some (l, r) := exactBin? 4 | return none
        return some ("\\frac{" ++ (← recGo 0 l) ++ "}{" ++ (← recGo 0 r) ++ "}", 72)
    | ``HPow.hPow =>
        let some (l, r) := exactBin? 6 | return none
        return some ("{" ++ (← recGo 80 l) ++ "}^{" ++ (← recGo 0 r) ++ "}", 78)
    | ``Pow.pow =>
        let some (l, r) := exactBin? 5 | return none
        return some ("{" ++ (← recGo 80 l) ++ "}^{" ++ (← recGo 0 r) ++ "}", 78)
    | ``Neg.neg =>
        if args.size < 3 then return none
        let some a := argFromEnd? args 0 | return none
        return some (s!"-{← recGo 75 a}", 75)
    | ``Min.min =>
        let some (l, r) := exactBin? 4 | return none
        return some ("\\min\\!\\left\\{" ++ (← recGo 0 l) ++ ",\\, " ++ (← recGo 0 r) ++ "\\right\\}", 85)
    | ``Max.max =>
        let some (l, r) := exactBin? 4 | return none
        return some ("\\max\\!\\left\\{" ++ (← recGo 0 l) ++ ",\\, " ++ (← recGo 0 r) ++ "\\right\\}", 85)
    | ``Membership.mem =>
        let some (set, elem) := exactBin? 5 | return none
        return some (s!"{← recGo 50 elem} \\in {← recGo 50 set}", 50)
    | ``HasSubset.Subset =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"{← recGo 50 l} \\subseteq {← recGo 50 r}", 50)
    | ``Singleton.singleton =>
        if args.size < 4 then return none
        let some a := argFromEnd? args 0 | return none
        return some ("\\{" ++ (← recGo 0 a) ++ "\\}", 90)
    | ``Prod =>
        let some (l, r) := exactBin? 2 | return none
        return some (s!"{← recGo 60 l} \\times {← recGo 60 r}", 60)
    | ``Sum =>
        let some (l, r) := exactBin? 2 | return none
        return some (s!"{← recGo 60 l} \\oplus {← recGo 60 r}", 60)
    | ``Prod.mk | ``Sigma.mk | ``PSigma.mk =>
        let some (l, r) := exactBin? 4 | return none
        return some (s!"({← recGo 0 l}, {← recGo 0 r})", 90)
    | ``Prod.fst | ``Prod.snd | ``PProd.fst | ``PProd.snd | ``Sigma.fst | ``Sigma.snd =>
        if args.size ≥ 3 then
          let idxNum :=
            if head == ``Prod.fst || head == ``PProd.fst || head == ``Sigma.fst then 0 else 1
          let idxStr := if idxNum == 0 then "1" else "2"
          let pairExpr := args[2]!
          let structField? : Option String ← try
            let pty ← normalizeForPresentation (← inferType pairExpr)
            match pty.getAppFn.consumeMData with
            | .const sn _ =>
                if sn != ``Prod && sn != ``PProd && sn != ``Sigma then
                  match getStructureInfo? (← getEnv) sn with
                  | some sinfo =>
                      if h : idxNum < sinfo.fieldNames.size then
                        pure (some sinfo.fieldNames[idxNum].toString)
                      else pure none
                  | none => pure none
                else pure none
            | _ => pure none
          catch _ => pure none
          let pairStr ← recGo 90 pairExpr
          let projStr := match structField? with
            | some fname => s!"{pairStr}.\\mathrm\{{escapeLatex fname}}"
            | none => appendSubscript pairStr idxStr
          if args.size == 3 then
            return some (projStr, 90)
          else
            let rest := args.extract 3 args.size
            let renderedArgs ← rest.mapM (recGo 0)
            let argList := String.intercalate ", " renderedArgs.toList
            return some (s!"{projStr}\\!\\left({argList}\\right)", 85)
        return none
    | ``Exists =>
        if args.size ≥ 2 then
          let dom := args[0]!
          let pred := args[1]!
          let (varStr, bodyStr) ← match pred.consumeMData with
            | .lam nm bDom body bi =>
                let freshNm ← chooseUnshadowedBinderName nm #[bDom, body] "x"
                withLocalDecl freshNm bi bDom fun fv => do
                  pure (← recGo 100 fv, ← recGo 10 (body.instantiate1 fv))
            | _ =>
                let freshNm ← freshShadowFreeName `x "x"
                withLocalDecl freshNm .default dom fun fv => do
                  pure (← recGo 100 fv, ← recGo 10 (mkApp pred fv))
          return some (s!"\\exists {varStr},\\; {bodyStr}", 10)
        return none
    | ``Subtype =>
        if args.size ≥ 2 then
          let dom := args[0]!
          let pred := args[1]!
          let domStr ← recGo 0 dom
          let (varStr, predStr) ← match pred.consumeMData with
            | .lam nm bDom body bi =>
                let freshNm ← freshShadowFreeName nm "x"
                withLocalDecl freshNm bi bDom fun fv => do
                  pure (← recGo 100 fv, ← recGo 0 (body.instantiate1 fv))
            | _ =>
                let freshNm ← freshShadowFreeName `x "x"
                withLocalDecl freshNm .default dom fun fv => do
                  pure (← recGo 100 fv, ← recGo 0 (mkApp pred fv))
          return some ("\\{" ++ varStr ++ " \\in " ++ domStr ++ " : " ++ predStr ++ "\\}", 90)
        return none
    | ``Sigma =>
        if args.size ≥ 2 then
          let dom := args[0]!
          let fam := args[1]!
          match fam.consumeMData with
          | .lam nm bDom body bi =>
              if !body.hasLooseBVar 0 then
                return some (s!"{← recGo 60 dom} \\times {← recGo 60 body}", 60)
              let freshNm ← freshShadowFreeName nm "i"
              let (varStr, bodyStr) ← withLocalDecl freshNm bi bDom fun fv => do
                pure (← recGo 100 fv, ← recGo 70 (body.instantiate1 fv))
              return some ("\\bigsqcup_{" ++ varStr ++ "} " ++ bodyStr, 70)
          | _ =>
              let freshNm ← freshShadowFreeName `i "i"
              let (varStr, bodyStr) ← withLocalDecl freshNm .default dom fun fv => do
                pure (← recGo 100 fv, ← recGo 70 (mkApp fam fv))
              return some ("\\bigsqcup_{" ++ varStr ++ "} " ++ bodyStr, 70)
        return none
    | ``ite =>
        if args.size ≥ 5 then
          let cStr ← recGo 0 args[1]!
          let tStr ← recGo 0 args[3]!
          let fStr ← recGo 0 args[4]!
          let casesStr := s!"\\begin\{cases} {tStr} & \\text\{if } {cStr}, \\\\ {fStr} & \\text\{otherwise}\\end\{cases}"
          if args.size == 5 then
            return some (casesStr, 45)
          else
            let rest ← (args.extract 5 args.size).mapM (recGo 0)
            let argList := String.intercalate ", " rest.toList
            return some (s!"\\left({casesStr}\\right)\\!\\left({argList}\\right)", 85)
        return none
    | ``dite =>
        if args.size ≥ 5 then
          let c := args[1]!
          let cStr ← recGo 0 c
          let renderBranch (br : Expr) : MetaM String :=
            match br.consumeMData with
            | .lam nm bDom body bi =>
                if !body.hasLooseBVar 0 then recGo 0 body
                else
                  withLocalDecl nm bi bDom fun fv => recGo 0 (body.instantiate1 fv)
            | _ => recGo 0 br
          let tStr ← renderBranch args[3]!
          let fStr ← renderBranch args[4]!
          let casesStr := s!"\\begin\{cases} {tStr} & \\text\{if } {cStr}, \\\\ {fStr} & \\text\{otherwise}\\end\{cases}"
          if args.size == 5 then
            return some (casesStr, 45)
          else
            let rest ← (args.extract 5 args.size).mapM (recGo 0)
            let argList := String.intercalate ", " rest.toList
            return some (s!"\\left({casesStr}\\right)\\!\\left({argList}\\right)", 85)
        return none
    | _ =>
        let renderBigOp (opCmd : String) (opPrec : Nat) : MetaM (Option (String × Nat)) := do
          if args.size < 5 then return none
          let dom := args[0]!
          let s := args[3]!
          let f := args[4]!
          let isUniv := s.getAppFn.consumeMData.isConstOf `Finset.univ
          let isRange := s.getAppFn.consumeMData.isConstOf `Finset.range && s.getAppArgs.size ≥ 1
          let rangeBound? := if isRange then s.getAppArgs.back? else none
          let sStr? ←
            if isUniv then pure none
            else if let some bnd := rangeBound? then some <$> recGo 0 bnd
            else some <$> recGo 0 s
          let avoidStrings := match sStr? with | some st => #[st] | none => #[]
          let avoidExprs :=
            if isUniv then #[]
            else if let some bnd := rangeBound? then #[bnd]
            else #[s]
          let (varStr, bodyStr) ← match f.consumeMData with
            | .lam nm bDom body bi =>
                let freshNm ← chooseUnshadowedSumBinder tbl nm bDom avoidStrings avoidExprs "i"
                withLocalDecl freshNm bi bDom fun fv => do
                  pure (← recGo 100 fv, ← recGo opPrec (body.instantiate1 fv))
            | _ =>
                let freshNm ← chooseUnshadowedSumBinder tbl `i dom avoidStrings avoidExprs "i"
                withLocalDecl freshNm .default dom fun fv => do
                  pure (← recGo 100 fv, ← recGo opPrec (mkApp f fv))
          let sub :=
            if isUniv then varStr
            else if let some bndStr := sStr? then
              if isRange then s!"{varStr} < {bndStr}" else s!"{varStr} \\in {bndStr}"
            else varStr
          let bigStr := opCmd ++ "_{" ++ sub ++ "} " ++ bodyStr
          if args.size == 5 then return some (bigStr, opPrec)
          else
            let rest ← (args.extract 5 args.size).mapM (recGo 0)
            return some (s!"\\left({bigStr}\\right)\\!\\left({String.intercalate ", " rest.toList}\\right)", 85)
        if head == `Finset.sum then
          return ← renderBigOp "\\sum" 68
        if head == `Finset.prod then
          return ← renderBigOp "\\prod" 71
        if head == `Finset.filter && args.size ≥ 4 then
          let dom := args[0]!
          let pred := args[1]!
          let s := args[3]!
          let isUniv := s.getAppFn.consumeMData.isConstOf `Finset.univ
          let setStr ← if isUniv then recGo 0 dom else recGo 0 s
          let avoidExprs := if isUniv then #[dom] else #[s]
          let (varStr, predStr) ← match pred.consumeMData with
            | .lam nm bDom body bi =>
                let freshNm ← chooseUnshadowedSumBinder tbl nm bDom #[setStr] avoidExprs "x"
                withLocalDecl freshNm bi bDom fun fv => do
                  pure (← recGo 100 fv, ← recGo 0 (body.instantiate1 fv))
            | _ =>
                let freshNm ← chooseUnshadowedSumBinder tbl `x dom #[setStr] avoidExprs "x"
                withLocalDecl freshNm .default dom fun fv => do
                  pure (← recGo 100 fv, ← recGo 0 (mkApp pred fv))
          return some ("\\{" ++ varStr ++ " \\in " ++ setStr ++ " : " ++ predStr ++ "\\}", 90)
        if (head == `setOf || head == `Set.setOf) && args.size ≥ 2 then
          let dom := args[0]!
          let pred := args[1]!
          let domStr ← recGo 0 dom
          let (varStr, predStr) ← match pred.consumeMData with
            | .lam nm bDom body bi =>
                let freshNm ← chooseUnshadowedSumBinder tbl nm bDom #[domStr] #[dom] "x"
                withLocalDecl freshNm bi bDom fun fv => do
                  pure (← recGo 100 fv, ← recGo 0 (body.instantiate1 fv))
            | _ =>
                let freshNm ← chooseUnshadowedSumBinder tbl `x dom #[domStr] #[dom] "x"
                withLocalDecl freshNm .default dom fun fv => do
                  pure (← recGo 100 fv, ← recGo 0 (mkApp pred fv))
          return some ("\\{" ++ varStr ++ " \\in " ++ domStr ++ " : " ++ predStr ++ "\\}", 90)
        if head == `ZMod && args.size ≥ 1 then
          let nTex ← recGo 0 args[0]!
          return some ("\\mathbb{Z}_{" ++ nTex ++ "}", 90)
        if head == `Dvd.dvd then
          let some (a, b) := lastTwo? args | return none
          return some (s!"{← recGo 50 a} \\mid {← recGo 50 b}", 50)
        if head == `List.IsPrefix then
          let some (a, b) := lastTwo? args | return none
          return some (s!"{← recGo 50 a} \\preceq {← recGo 50 b}", 50)
        if head == `abs then
          let some a := argFromEnd? args 0 | return none
          return some (s!"\\left|{← recGo 0 a}\\right|", 90)
        if head == `Nat.choose then
          let some (n, k) := lastTwo? args | return none
          return some ("\\binom{" ++ (← recGo 0 n) ++ "}{" ++ (← recGo 0 k) ++ "}", 85)
        if head == `Fintype.card then
          let some a := args[0]? | return none
          return some (s!"\\left|{← recGo 0 a}\\right|", 90)
        if head == `Finset.card then
          let some a := argFromEnd? args 0 | return none
          return some (s!"\\left|{← recGo 0 a}\\right|", 90)
        if head == `List.length then
          let some a := argFromEnd? args 0 | return none
          return some (s!"\\left|{← recGo 0 a}\\right|", 90)
        if head == ``HXor.hXor then
          let some (l, r) := exactBin? 6 | return none
          return some ((← recGo 65 l) ++ " \\oplus " ++ (← recGo 66 r), 65)
        if head == ``XorOp.xor then
          let some (l, r) := exactBin? 4 | return none
          return some ((← recGo 65 l) ++ " \\oplus " ++ (← recGo 66 r), 65)
        if head == ``List.nil && args.size ≤ 1 then
          return some ("[]", 95)
        if head == ``List.cons && args.size == 3 then
          if let some rest := collectListElems? args[2]! then
            let elems := args[1]! :: rest
            let strs ← elems.mapM (recGo 0)
            return some ("[" ++ String.intercalate ", " strs ++ "]", 95)
          else
            return some ((← recGo 66 args[1]!) ++ " :: " ++ (← recGo 65 args[2]!), 65)
        if head == ``HAppend.hAppend then
          let some (l, r) := exactBin? 6 | return none
          let ty0 ← try withTransparency .reducible (whnf args[0]!) catch _ => pure args[0]!
          if ty0.consumeMData.isAppOf ``List then
            return some ((← recGo 66 l) ++ " \\mathbin{+\\!\\!+} " ++ (← recGo 65 r), 65)
        if head == ``List.append then
          let some (l, r) := exactBin? 3 | return none
          return some ((← recGo 66 l) ++ " \\mathbin{+\\!\\!+} " ++ (← recGo 65 r), 65)
        if head == ``List.sum && args.size == 4 then
          let listArg := args[3]!.consumeMData
          if listArg.getAppFn.consumeMData.isConstOf ``List.map && listArg.getAppArgs.size == 4 then
            let margs := listArg.getAppArgs
            let dom := margs[0]!
            let f := margs[2]!
            let xs := margs[3]!
            let xsStr ← recGo 0 xs
            let (varStr, bodyStr) ← match f.consumeMData with
              | .lam nm bDom body bi =>
                  let freshNm ← chooseUnshadowedSumBinder tbl nm bDom #[xsStr] #[xs] "x"
                  withLocalDecl freshNm bi bDom fun fv => do
                    pure (← recGo 100 fv, ← recGo 68 (body.instantiate1 fv))
              | _ =>
                  let freshNm ← chooseUnshadowedSumBinder tbl `x dom #[xsStr] #[xs] "x"
                  withLocalDecl freshNm .default dom fun fv => do
                    pure (← recGo 100 fv, ← recGo 68 (mkApp f fv))
            return some ("\\sum_{" ++ varStr ++ " \\in " ++ xsStr ++ "} " ++ bodyStr, 68)
        if head == `Nat.descFactorial && args.size == 2 then
          return some ("(" ++ (← recGo 0 args[0]!) ++ ")_{" ++ (← recGo 0 args[1]!) ++ "}", 90)
        if head == ``Function.Injective && args.size == 3 then
          return some ((← recGo 85 args[2]!) ++ " \\text{ is injective}", 45)
        if head == `Probability.Distribution.uniform ||
           head == `Probability.Distribution.ProbDist.uniform ||
           head == `Distribution.uniform then
          if let some info := (← getEnv).find? head then
            let expArgs ← collectExplicitArgs info.type args
            if expArgs.size == 1 then
              return some ("\\mathcal{U}[" ++ (← recGo 0 expArgs[0]!) ++ "]", 90)
            else if expArgs.size == 2 then
              return some ("\\mathcal{U}[" ++ (← recGo 0 expArgs[0]!) ++ "]\\!\\left(" ++ (← recGo 0 expArgs[1]!) ++ "\\right)", 85)
        if head == `Probability.Distribution.mass || head == `Distribution.mass then
          if let some info := (← getEnv).find? head then
            let expArgs ← collectExplicitArgs info.type args
            if expArgs.size == 2 then
              let muStr ← recGo 90 expArgs[0]!
              let evStr ← recGo 0 expArgs[1]!
              return some (muStr ++ "\\!\\left(" ++ evStr ++ "\\right)", 85)
        if head == `Fin then
          let some n := argFromEnd? args 0 | return none
          return some (s!"[{← recGo 0 n}]", 90)
        return none

/-- Public entry point: run the hygiene/normalization firewall, then print 2D LaTeX
with per-call $O(\text{DAG})$ memoization on closed subexpressions. -/
def exprToLatex (e : Expr) (tbl : SymbolTable := {}) (ctxPrec : Nat := 0) : MetaM String := do
  let clean ← normalizeForPresentation e
  let memo ← IO.mkRef ({} : Std.HashMap (Expr × Nat) String)
  renderAuxMemo memo tbl ctxPrec clean

end Informalization.Core.LeanTeX
