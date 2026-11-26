/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Overlay
import Informalization.Core.ContextProfile
import Informalization.Core.Explanation
import Informalization.Core.Register

/-!
# Compositional Ontology & Ambient-Scope Theorem Statement Planner

Implements Kyle Miller's `Entity` / `Noun` / `Adjective` / `Accessory` ontology with:
* domain-extensible type & proposition handlers (registered by `CC/Ontology.lean` and
  downstream profiles without hardcoding domain logic here);
* **exact arity-driven interface inflection** (inspecting `Interface` tensors/ports so
  we emit *"with interface A"* vs. *"with interfaces H and P"*, never `"interface(s)"`);
* **ambient-scope suppression** (factoring shared typeclasses and category telescopes
  out of every theorem/lemma statement once);
* **hygienized Miller goal states** (`GoalState`) with zero `None` hypothesis leaks.
-/

namespace Informalization.Core.Ontology

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Overlay
open Informalization.Core.ContextProfile
open Informalization.Core.Explanation
open Informalization.Core.Register

/-- Semantic description of a mathematical type for entity introductions. -/
structure TypeDescription where
  noun : CountNoun
  adjectives : List String := []
  accessories : List String := []
  /-- Optional extra type annotation printed beside the symbol (e.g. `M \to X^*`). -/
  typeLatex? : Option String := none
  /-- If true, this binder is ambient category/algebra plumbing and belongs in `AmbientSetting`. -/
  isAmbient : Bool := false
  /-- If true, this binder is a proof witness (e.g. an H-coefficient witness) kept in introductions
  even if the witness variable itself does not appear in the conclusion formula. -/
  isWitness : Bool := false
  deriving Repr, Inhabited

/-- Domain-extensible handler mapping a variable's type `Expr` to a `TypeDescription`. -/
structure TypeHandler where
  priority : Nat := 100
  matchType : SymbolTable → Expr → MetaM (Option TypeDescription)

/-- Domain-extensible handler rendering a `Prop` expression into Maurer-style English + LaTeX
(as `Array Inline`) or refining an already-introduced entity with an adjective/accessory. -/
structure PropHandler where
  priority : Nat := 100
  renderProp : SymbolTable → Expr → MetaM (Option (Array Inline))

initialize typeHandlersRef : IO.Ref (Array TypeHandler) ← IO.mkRef #[]
initialize propHandlersRef : IO.Ref (Array PropHandler) ← IO.mkRef #[]

def registerTypeHandler (h : TypeHandler) : IO Unit :=
  typeHandlersRef.modify fun arr =>
    (arr.push h).qsort fun a b => a.priority > b.priority

def registerPropHandler (h : PropHandler) : IO Unit :=
  propHandlersRef.modify fun arr =>
    (arr.push h).qsort fun a b => a.priority > b.priority

/-- Flatten a binary interface tensor (`A ⊗ B` or `Interface.tensor A B`) into its
individual interface components so singular/plural inflection is exact. -/
partial def interfaceComponents (e : Expr) : MetaM (List Expr) := do
  let e ← normalizeForPresentation e
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if let .const name _ := fn then
    if (name == `CategoryTheory.MonoidalCategoryStruct.tensorObj ||
        name == `SystemAlgebra.Interface.tensor) && args.size ≥ 2 then
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      return (← interfaceComponents a) ++ (← interfaceComponents b)
  return [e]

/-- Render an interface expression as an exact singular/plural accessory phrase:
`with interface \(A\)` or `with interfaces \(H\) and \(P\)` (never `"interface(s)"`). -/
def interfaceAccessory (tbl : SymbolTable) (ifaceExpr : Expr) : MetaM String := do
  let comps ← interfaceComponents ifaceExpr
  let rendered ← comps.mapM fun c => do
    let tex ← exprToLatex c tbl
    return s!"\\({tex}\\)"
  return withInterfacesPhrase rendered

/-- Nouns whose codomain is too generic to form `"family of <plural> indexed by X"`;
those arrow types remain `"map"` (or a specialized type such as `"predicate"`). -/
private def isGenericCodomainNoun (nounSingular : String) : Bool :=
  let s := nounSingular.toLower
  s == "set" || s == "proposition" || s == "natural number" || s == "integer" ||
  s == "integer in \\(\\mathbb{n}\\)" || s == "real number" || s == "nonnegative scalar" ||
  s == "nonnegative real" || s == "nonnegative real number" ||
  s == "bit" || s == "function" || s == "map" || s == "pair" || s == "ordered pair" ||
  s == "predicate" || s == "boolean predicate" || s == "event" ||
  s == "key-length profile" || s == "length assignment" ||
  s == "query bound" || s == "query budget" || s == "error function" ||
  s == "resource family" || s == "finite sequence" || s == "finite set" ||
  s == "subset" || s.startsWith "element of " || s.startsWith "family of "

/-- Describe a binder's type using registered domain handlers and checked `informal_noun`
overlays first, then core math fallbacks. -/
partial def describeType (tbl : SymbolTable) (ty : Expr) : MetaM TypeDescription := do
  let ty ← normalizeForPresentation ty
  for h in (← typeHandlersRef.get) do
    if let some desc ← h.matchType tbl ty then
      return desc
  if let .const head _ := ty.getAppFn.consumeMData then
    let env ← getEnv
    if let some (sg, pl) := (getOverlay env head).noun? <|> (Presentation.getMathPresentation env head).interfaceResourceNoun? then
      return { noun := ⟨sg, pl⟩ }
    if let some rule := Presentation.getPaperDescribeRule? env head then
      let mut accessories : List String := []
      if let some qTmpl := rule.qualifierTemplate? then
        if let some info := env.find? head then
          let expArgs ← Presentation.collectExplicitNonPropArgs info.type ty.getAppArgs
          let qual ← Presentation.expandPureTemplate tbl qTmpl expArgs
          if !qual.isEmpty then
            accessories := [qual]
      return { noun := rule.noun, accessories }
  if ty == .sort .zero then
    return { noun := ⟨"proposition", "propositions"⟩ }
  if ty.isSort then
    return { noun := ⟨"set", "sets"⟩ }
  if ty.isAppOf ``Nat || ty == mkConst ``Nat then
    return { noun := ⟨"integer in \\(\\mathbb{N}\\)", "integers in \\(\\mathbb{N}\\)"⟩ }
  if ty.isAppOf ``Int || ty == mkConst ``Int then
    return { noun := ⟨"integer", "integers"⟩ }
  if ty.isAppOf ``Bool || ty == mkConst ``Bool then
    return { noun := ⟨"bit", "bits"⟩ }
  if ty == mkConst `Real then
    return { noun := ⟨"real number", "real numbers"⟩ }
  if ty == mkConst `NNReal || ty == mkConst `ENNReal then
    return { noun := ⟨"nonnegative scalar", "nonnegative scalars"⟩ }
  if let .forallE nm dom body bi := ty then
    if ← isAmbientTypeclass dom then
      if body.hasLooseBVar 0 then
        return ← withLocalDecl nm bi dom fun fv => describeType tbl (body.instantiate1 fv)
      else
        return ← describeType tbl body
    if ← isProp ty then
      return { noun := ⟨"proposition", "propositions"⟩ }
    if !body.hasLooseBVar 0 then
      if dom.isConstOf ``Unit || dom.isConstOf ``PUnit then
        return ← describeType tbl body
      if body == .sort .zero then
        let domTex ← exprToLatex dom tbl
        return { noun := ⟨"predicate", "predicates"⟩, accessories := [s!"on \\({domTex}\\)"] }
      let domClean := dom.consumeMData
      let bodyClean := body.consumeMData
      let domTex ← exprToLatex dom tbl
      if bodyClean.isConstOf ``Bool then
        return { noun := ⟨"Boolean predicate", "Boolean predicates"⟩, accessories := [s!"on \\({domTex}\\)"] }
      if domClean.getAppFn.consumeMData.isConstOf ``Fin && bodyClean.isConstOf ``Nat then
        return { noun := ⟨"key-length profile", "key-length profiles"⟩, accessories := [s!"on \\({domTex}\\)"] }
      if !domClean.isForall && !(← isProp dom) then
        let codDesc ← describeType tbl body
        if !codDesc.isAmbient && !isGenericCodomainNoun codDesc.noun.singular then
          return {
            noun := ⟨s!"family of {codDesc.noun.plural}", s!"families of {codDesc.noun.plural}"⟩
            accessories := [s!"indexed by \\({domTex}\\)"]
          }
      let tyTex ← exprToLatex ty tbl
      return { noun := ⟨"map", "maps"⟩, typeLatex? := some tyTex }
    else
      -- Dependent non-`Prop` arrow `(x : X) → Y x`: indexed family of domain objects when concrete
      let domClean := dom.consumeMData
      if !domClean.isForall && !(← isProp dom) then
        let domTex ← exprToLatex dom tbl
        let famDesc? ← withLocalDecl nm bi dom fun fv => do
          let codDesc ← describeType tbl (body.instantiate1 fv)
          if !codDesc.isAmbient && !isGenericCodomainNoun codDesc.noun.singular then
            return some {
              noun := ⟨s!"family of {codDesc.noun.plural}", s!"families of {codDesc.noun.plural}"⟩
              accessories := [s!"indexed by \\({domTex}\\)"]
            }
          return none
        if let some famDesc := famDesc? then
          return famDesc
      let tyTex ← exprToLatex ty tbl
      return { noun := ⟨"map", "maps"⟩, typeLatex? := some tyTex }
  if ty.isAppOf ``Prod && ty.getAppArgs.size == 2 then
    return { noun := ⟨"pair", "pairs"⟩ }
  let tyTex ← exprToLatex ty tbl
  return { noun := ⟨s!"element of \\({tyTex}\\)", s!"elements of \\({tyTex}\\)"⟩ }

/-- Context-aware 5-level type description resolution (`Core/ContextProfile.lean`), preserving
ambient/witness status and CC structural accessories while enforcing the anti-clobbering lattice. -/
def describeTypeWithContext (tbl : SymbolTable) (profile : PaperContextProfile)
    (fv : Expr) (ty : Expr) (role? : Option SemanticRole)
    (explicitRole? : Option String) (allBinders : Array (FVarId × Expr))
    (visibleExprs : Array Expr) : MetaM TypeDescription := do
  let baseDesc ← describeType tbl ty
  let resolved ← resolveDescription5Level profile fv ty
    baseDesc.noun baseDesc.accessories baseDesc.isAmbient baseDesc.isWitness
    role? explicitRole? allBinders visibleExprs
  return { baseDesc with noun := resolved.noun, accessories := resolved.accessories }

/-- Canonical string key for an `Array Inline` (used to detect identical assumptions across a section). -/
def inlinesCanonicalKey (inls : Array Inline) : String :=
  String.intercalate "" (inls.toList.map Inline.collectText) |>.trimAscii.toString

/-- Fast bounded $O(\text{limit})$ DAG size check so huge expanded `simp` terms don't stall `ppExpr`. -/
private partial def exprDagSmall (e : Expr) (limit : Nat := 220) : Bool :=
  let rec go (cur : Expr) (st : Std.HashSet Expr × Nat) : Std.HashSet Expr × Nat :=
    if st.2 > limit || st.1.contains cur then st
    else
      let st := (st.1.insert cur, st.2 + 1)
      match cur with
      | .app f a => go a (go f st)
      | .lam _ d b _ => go b (go d st)
      | .forallE _ d b _ => go b (go d st)
      | .letE _ t v b _ => go b (go v (go t st))
      | .mdata _ inner => go inner st
      | .proj _ _ s => go s st
      | _ => st
  (go e ({}, 0)).2 ≤ limit

/-- Canonical short math symbol when a quantifier binder's cleaned name collides with its noun
(e.g. `distinguisher : Distinguisher I` -> `D`, avoiding `"for every distinguisher distinguisher"`). -/
private def canonicalQuantBinderName (rawBinder : String) (nounSingular : String) : Option String :=
  let b := rawBinder.toLower
  let n := nounSingular.toLower
  let headNoun := (n.splitOn " \\(").headD n |>.trimAscii.toString
  let matchesNoun :=
    b == n || b == headNoun ||
    (b.length ≥ 4 && (headNoun.splitOn b).length > 1)
  if !matchesNoun then none
  else if (n.splitOn "distinguisher").length > 1 then some "D"
  else if (n.splitOn "adversary").length > 1 then some "A"
  else if (n.splitOn "simulator").length > 1 then some "S"
  else if (n.splitOn "resource").length > 1 then some "R"
  else if (n.splitOn "converter").length > 1 then some "c"
  else if (n.splitOn "solver").length > 1 then some "s"
  else if (n.splitOn "game").length > 1 then some "G"
  else if (n.splitOn "environment").length > 1 then some "E"
  else if (n.splitOn "transcript").length > 1 then some "h"
  else some "x"

/-- Choose an uncolliding quantifier binder `Name`, substituting a canonical symbol when an
unaliased binder repeats its own noun (`"distinguisher"` -> `"D"`). -/
private def resolveQuantBinderName (tbl : SymbolTable) (nm : Name) (nounSingular : String) : Name :=
  let cleanRaw := cleanBinderName nm "x"
  let hasDistinctAlias :=
    match tbl.binderAliases.get? cleanRaw with
    | some al =>
        let alLower := al.toLower
        alLower != cleanRaw.toLower && alLower != ("\\mathrm{" ++ cleanRaw.toLower ++ "}")
    | none => false
  if hasDistinctAlias then nm
  else match canonicalQuantBinderName cleanRaw nounSingular with
    | some sym => Name.mkSimple sym
    | none => nm

private def collectVisiblePredArgs (tbl : SymbolTable) (head : Name) (args : Array Expr) :
    MetaM (Array Expr) := do
  let hidden := tbl.hiddenArgs.getD head []
  let some info := (← getEnv).find? head | return args
  let mut ty := info.type
  let mut visible : Array Expr := #[]
  for i in [:args.size] do
    ty ← whnf ty
    match ty with
    | .forallE _ dom body bi =>
        let isHidden := hidden.contains i
        let isPropArg ← isProp dom
        if bi.isExplicit && !isPropArg && !isHidden then
          visible := visible.push args[i]!
        ty := body.instantiate1 args[i]!
    | _ =>
        if !hidden.contains i then
          visible := visible.push args[i]!
  return visible

private def isBinaryInfixPredPhrase (phrase : String) : Bool :=
  let low := phrase.trimAscii.toString.toLower
  [ " with", " to", " from", " of", " in", " on", " at", " by", " over", " under",
    " against", " between", " into", " onto", " than", " as", " through", " within",
    " across", " for", " equals", " respects", " satisfies", " implements", " realizes",
    " extends", " divides", " contains", " dominates", " precedes"
  ].any fun suf => low.endsWith suf

private def predPhraseStartsWithVerb (phrase : String) : Bool :=
  let first := (phrase.trimAscii.toString.splitOn " ").headD "" |>.toLower
  let clean := ((first.replace "," "").replace "." "").replace ";" ""
  [ "is", "are", "was", "were", "has", "have", "had",
    "can", "may", "must", "does", "do", "did",
    "satisfies", "satisfy", "agrees", "agree", "assigns", "assign",
    "queries", "query", "preserves", "preserve", "respects", "respect",
    "stays", "stay", "holds", "hold", "equals", "equal",
    "lies", "lie", "exceeds", "exceed", "avoids", "avoid",
    "matches", "match", "separates", "separate", "coincides", "coincide",
    "achieves", "achieve", "constructs", "construct", "bounds", "bound",
    "implies", "imply", "ensures", "ensure", "contains", "contain",
    "depends", "depend", "terminates", "terminate"
  ].contains clean

private def hasNumericPlaceholders (phrase : String) (n : Nat) : Bool :=
  (List.range n).any fun i => (phrase.splitOn ("{" ++ toString i ++ "}")).length > 1

/-- True when English prose outside math delimiters (`\(...\)`, `\[...\]`, `$...$`)
contains a comma or semicolon (ignoring commas inside math like `\,` or `f(a, b)`). -/
def proseHasCommaOrSemi (s : String) : Bool := Id.run do
  let arr := s.toList.toArray
  let n := arr.size
  let mut i := 0
  let mut inParenMath := false
  let mut inBracketMath := false
  let mut inDollar := false
  let mut inDoubleDollar := false
  while i < n do
    let c := arr[i]!
    if inParenMath then
      if c == '\\' && i + 1 < n && arr[i + 1]! == ')' then
        inParenMath := false
        i := i + 2
      else
        i := i + 1
    else if inBracketMath then
      if c == '\\' && i + 1 < n && arr[i + 1]! == ']' then
        inBracketMath := false
        i := i + 2
      else
        i := i + 1
    else if inDoubleDollar then
      if c == '$' && i + 1 < n && arr[i + 1]! == '$' then
        inDoubleDollar := false
        i := i + 2
      else
        i := i + 1
    else if inDollar then
      if c == '$' then
        inDollar := false
      i := i + 1
    else
      if c == '\\' && i + 1 < n then
        let nxt := arr[i + 1]!
        if nxt == '(' then
          inParenMath := true; i := i + 2; continue
        else if nxt == '[' then
          inBracketMath := true; i := i + 2; continue
        else if nxt == '$' then
          i := i + 2; continue
      if c == '$' then
        if i + 1 < n && arr[i + 1]! == '$' then
          inDoubleDollar := true; i := i + 2; continue
        else
          inDollar := true; i := i + 1; continue
      if c == ',' || c == ';' then
        return true
      i := i + 1
  return false

/-- True when any non-math prose fragment in `inls` contains a comma or semicolon. -/
def inlinesHasProseCommaOrSemi (inls : Array Inline) : Bool :=
  inls.any fun
    | .text s | .emph s => proseHasCommaOrSemi s
    | .symbol _ d false => proseHasCommaOrSemi d
    | .citation l d => proseHasCommaOrSemi l || proseHasCommaOrSemi d
    | _ => false

private def hasLatexCmd (tex cmd : String) : Bool :=
  let parts := tex.splitOn cmd
  parts.length > 1 &&
    (parts.drop 1).any fun tail =>
      match tail.toList.head? with
      | none => true
      | some c => !c.isAlpha

private def relLatexCmds : List String :=
  [ "\\le", "\\leq", "\\ge", "\\geq", "\\neq", "\\ne", "\\simeq", "\\approx",
    "\\equiv", "\\subseteq", "\\subset", "\\supseteq", "\\supset",
    "\\in", "\\notin", "\\xrightarrow", "\\xleftarrow", "\\preceq",
    "\\implies", "\\iff", "\\forall", "\\exists"
  ]

private def hasRelationalMath (tex : String) : Bool :=
  ["=", "<", ">"].any (fun tok => (tex.splitOn tok).length > 1) ||
    relLatexCmds.any (hasLatexCmd tex)

/-- True when a rendered LaTeX formula already carries a relational verb or quantifier. -/
def hasMathVerbOrRelation (tex : String) : Bool :=
  hasRelationalMath tex ||
    [ "\\mid\\!\\equiv", " \\mid ", "\\perp_{\\mathrm{adm}}",
      "\\text{ is ", "\\text{ are ", "\\text{ holds", "\\text{ satisfies"
    ].any fun tok => (tex.splitOn tok).length > 1

/-- Ensure a rendered proposition forms a grammatical clause when it is a bare symbolic
predicate (such as `\mathsf{AE}\text{-}\mathsf{Sec}(\Pi, \varepsilon)`) without a relational verb. -/
def ensureSymbolicPredClause (inls : Array Inline) : Array Inline :=
  match inls with
  | #[.inlineMath tex] =>
      if hasMathVerbOrRelation tex then inls
      else
        let trimmed := tex.trimAscii.toString
        if trimmed.startsWith "\\neg " &&
           (trimmed.splitOn "\\wedge").length == 1 &&
           (trimmed.splitOn "\\vee").length == 1 then
          let body0 := (trimmed.drop 5).trimAscii.toString
          let body :=
            if body0.startsWith "\\left(" && body0.endsWith "\\right)" then
              ((body0.drop 6).dropEnd 7).toString.trimAscii.toString
            else body0
          #[.inlineMath body, .text " does not hold"]
        else
          #[.inlineMath tex, .text " holds"]
  | _ => inls

private def isDeterministicEnvDesc (dom : Expr) (desc : TypeDescription) : Bool :=
  let nLow := desc.noun.singular.toLower
  let hasEnvWords :=
    (nLow.splitOn "environment").length > 1 &&
    ((nLow.splitOn "deterministic").length > 1 ||
      desc.adjectives.any (·.toLower == "deterministic"))
  let fnName := match dom.getAppFn.consumeMData with
    | .const nm _ => nm.toString
    | _ => ""
  hasEnvWords || fnName.endsWith "DeterministicEnvironment" || fnName.endsWith ".DDE"

private def isPlainNatDesc (dom : Expr) (desc : TypeDescription) : Bool :=
  (dom.consumeMData.isConstOf ``Nat || desc.noun.singular == "integer in \\(\\mathbb{N}\\)") &&
  desc.adjectives.isEmpty && desc.accessories.isEmpty

private def propIsQueryBounded (prop : Expr) (fvN fvE : Expr) : Bool :=
  let fvs := (Lean.collectFVars {} prop).fvarIds
  let usesBoth := fvs.contains fvN.fvarId! && fvs.contains fvE.fvarId!
  let fnOk := match prop.getAppFn.consumeMData with
    | .const nm _ =>
        let s := nm.toString
        s.endsWith "QueryBounded" || s.endsWith "RespectsQueryBudget"
    | _ => false
  usesBoth && fnOk

private def propIsCompatibleWithEnv (prop : Expr) (fvE : Expr) : Bool :=
  let fvs := (Lean.collectFVars {} prop).fvarIds
  let usesEnv := fvs.contains fvE.fvarId!
  let fnOk := match prop.getAppFn.consumeMData with
    | .const nm _ => nm.toString.endsWith "Compatible"
    | _ => false
  usesEnv && fnOk

private def formatGuardChain (guards : Array (Array Inline)) (conclInl : Array Inline) : Array Inline := Id.run do
  if guards.isEmpty then return conclInl
  else if guards.size == 1 then
    return #[.text "if "] ++ guards[0]! ++ #[.text ", then "] ++ conclInl
  else if guards.size == 2 then
    let g0 := guards[0]!
    let g1 := guards[1]!
    let hasPunct := inlinesHasProseCommaOrSemi g0 || inlinesHasProseCommaOrSemi g1
    let sep := if hasPunct then ", and " else " and "
    return #[.text "if "] ++ g0 ++ #[.text sep] ++ g1 ++ #[.text ", then "] ++ conclInl
  else
    let hasPunct := guards.any inlinesHasProseCommaOrSemi
    let sep := if hasPunct then "; " else ", "
    let lastSep := if hasPunct then "; and " else ", and "
    let mut joined : Array Inline := #[]
    for i in [:guards.size] do
      if i > 0 then
        joined := joined.push (.text (if i + 1 == guards.size then lastSep else sep))
      joined := joined ++ guards[i]!
    return #[.text "whenever "] ++ joined ++ #[.text ", we have "] ++ conclInl

private def rewriteCCSubstitutionInlines (inls : Array Inline) : Array Inline := Id.run do
  if inls.size < 4 then return inls
  match inls[0]? with
  | some (.text "the resource ") =>
      let mut out : Array Inline := #[]
      let mut replaced := false
      for i in [1:inls.size] do
        match inls[i]! with
        | .text " can be substituted by " =>
            out := out.push (.text " can be replaced by ")
            replaced := true
        | x => out := out.push x
      if replaced then return out
      else return inls
  | _ => return inls

private def flushQuants (accQuants : Array (Array Inline)) (bodyInl : Array Inline) :
    Array Inline := Id.run do
  if accQuants.isEmpty then return bodyInl
  else if accQuants.size == 1 then
    return #[.text "for "] ++ accQuants[0]! ++ #[.text ", "] ++ bodyInl
  else if accQuants.size == 2 then
    return #[.text "for "] ++ accQuants[0]! ++ #[.text " and "] ++ accQuants[1]! ++ #[.text ", "] ++ bodyInl
  else
    let hasPunct := accQuants.any inlinesHasProseCommaOrSemi
    let sep := if hasPunct then "; " else ", "
    let lastSep := if hasPunct then "; and " else ", and "
    let mut out : Array Inline := #[.text "for "]
    for i in [:accQuants.size] do
      if i > 0 then
        out := out.push (.text (if i + 1 == accQuants.size then lastSep else sep))
      out := out ++ accQuants[i]!
    return out ++ #[.text ", "] ++ bodyInl

private def predHeadTextWithTail (headText varTex : String) (tailText : String := "") : Array Inline :=
  if tailText.isEmpty then #[.text headText, .inlineMath varTex]
  else #[.text headText, .inlineMath varTex, .text tailText]

/-- Render a proposition into natural mathematical English + LaTeX (`Array Inline`),
respecting `CryptoRegister`, consulting registered CC/domain handlers first, folding consecutive
universal quantifiers and negated membership guards cleanly, and falling back to clean `LeanTeX`. -/
partial def renderPropWithQuants (accQuants : Array (Array Inline)) (reg : CryptoRegister)
    (tbl : SymbolTable) (prop : Expr) : MetaM (Array Inline) := do
  let prop ← normalizeForPresentation prop
  if prop.consumeMData.isConstOf ``False then
    return flushQuants accQuants #[.text "a contradiction"]
  if let some (_, symAlias) := tbl.exprAliases.reverse.find? (fun (pat, _) => pat.consumeMData == prop.consumeMData) then
    return flushQuants accQuants #[.inlineMath symAlias]
  for h in (← propHandlersRef.get) do
    if let some out ← h.renderProp tbl prop then
      return flushQuants accQuants (rewriteCCSubstitutionInlines out)
  -- Quantified `∀ x, P x` (with `Prop` domain rendered as implication even when dependent)
  if let .forallE nm dom body bi := prop then
    if ← isAmbientTypeclass dom then
      return ← withLocalDecl nm bi dom fun fv =>
        renderPropWithQuants accQuants reg tbl (body.instantiate1 fv)
    else if ← isProp dom then
      if !body.hasLooseBVar 0 && body.consumeMData.isConstOf ``False then
        let domNorm ← normalizeForPresentation dom
        if let some (elem, setExpr) := matchMembershipExpr? domNorm then
          let eTex ← exprToLatex elem tbl
          let sTex ← exprToLatex setExpr tbl
          return flushQuants accQuants #[.inlineMath s!"{eTex} \\notin {sTex}"]
      let rec collectPropGuards (acc : Array (Array Inline)) (cur : Expr) : MetaM (Array Inline) := do
        let cur ← normalizeForPresentation cur
        match cur with
        | .forallE gNm gDom gBody gBi =>
            if ← isAmbientTypeclass gDom then
              withLocalDecl gNm gBi gDom fun fv => collectPropGuards acc (gBody.instantiate1 fv)
            else if ← isProp gDom then
              let gInl ← renderPropWithQuants #[] reg tbl gDom
              if gBody.hasLooseBVar 0 then
                withLocalDecl gNm gBi gDom fun fv => collectPropGuards (acc.push gInl) (gBody.instantiate1 fv)
              else
                collectPropGuards (acc.push gInl) gBody
            else
              let conclInl ← renderPropWithQuants #[] reg tbl cur
              return formatGuardChain acc conclInl
        | _ =>
            let conclInl ← renderPropWithQuants #[] reg tbl cur
            return formatGuardChain acc conclInl
      let guarded ← collectPropGuards #[] prop
      return flushQuants accQuants guarded
    else
      let desc ← describeType tbl dom
      let domClean := dom.consumeMData
      -- Fold Register C `∀ E (n : ℕ), QueryBounded n E → Compatible A E → P` (either order)
      if body.hasLooseBVar 0 && isDeterministicEnvDesc dom desc then
        let envNm := resolveQuantBinderName tbl nm desc.noun.singular
        let freshEnvNm ← freshShadowFreeName envNm "E"
        let regC? ← withLocalDecl freshEnvNm bi dom fun fvE => do
          let eTex ← exprToLatex fvE tbl
          let rec matchAfterEnv (compatSeen : Bool) (cur : Expr) : MetaM (Option (Array Inline)) := do
            let cur ← normalizeForPresentation cur
            match cur with
            | .forallE cNm cDom cBody cBi =>
                if ← isAmbientTypeclass cDom then
                  withLocalDecl cNm cBi cDom fun fv =>
                    matchAfterEnv compatSeen (cBody.instantiate1 fv)
                else if ← isProp cDom then
                  if !compatSeen && propIsCompatibleWithEnv cDom fvE then
                    if cBody.hasLooseBVar 0 then
                      withLocalDecl cNm cBi cDom fun fv => matchAfterEnv true (cBody.instantiate1 fv)
                    else
                      matchAfterEnv true cBody
                  else pure none
                else
                  let cDesc ← describeType tbl cDom
                  if isPlainNatDesc cDom cDesc && cBody.hasLooseBVar 0 then
                    let nNm := resolveQuantBinderName tbl cNm cDesc.noun.singular
                    let freshNNm ← freshShadowFreeName nNm "n"
                    withLocalDecl freshNNm cBi cDom fun fvN => do
                      let nTex ← exprToLatex fvN tbl
                      let rec matchGuards (qbSeen : Bool) (cpSeen : Bool) (gCur : Expr) :
                          MetaM (Option (Array Inline)) := do
                        let gCur ← normalizeForPresentation gCur
                        if qbSeen && cpSeen then
                          let qHead : Array Inline := #[
                            .text "every compatible ", .inlineMath nTex,
                            .text "-query deterministic environment ", .inlineMath eTex
                          ]
                          return some (← renderPropWithQuants (accQuants.push qHead) reg tbl gCur)
                        match gCur with
                        | .forallE gNm gDom gBody gBi =>
                            if ← isAmbientTypeclass gDom then
                              withLocalDecl gNm gBi gDom fun fv => matchGuards qbSeen cpSeen (gBody.instantiate1 fv)
                            else if ← isProp gDom then
                              if !qbSeen && propIsQueryBounded gDom fvN fvE then
                                if gBody.hasLooseBVar 0 then
                                  withLocalDecl gNm gBi gDom fun fv => matchGuards true cpSeen (gBody.instantiate1 fv)
                                else
                                  matchGuards true cpSeen gBody
                              else if !cpSeen && propIsCompatibleWithEnv gDom fvE then
                                if gBody.hasLooseBVar 0 then
                                  withLocalDecl gNm gBi gDom fun fv => matchGuards qbSeen true (gBody.instantiate1 fv)
                                else
                                  matchGuards qbSeen true gBody
                              else pure none
                            else pure none
                        | _ => pure none
                      matchGuards false compatSeen (cBody.instantiate1 fvN)
                  else pure none
            | _ => pure none
          matchAfterEnv false (body.instantiate1 fvE)
        if let some folded := regC? then
          return folded
      if body.hasLooseBVar 0 && isPlainNatDesc dom desc then
        let nNm := resolveQuantBinderName tbl nm desc.noun.singular
        let freshNNm ← freshShadowFreeName nNm "n"
        let regC? ← withLocalDecl freshNNm bi dom fun fvN => do
          let nTex ← exprToLatex fvN tbl
          let cur ← normalizeForPresentation (body.instantiate1 fvN)
          match cur with
          | .forallE eNm eDom eBody eBi =>
              let eDesc ← describeType tbl eDom
              if !(← isProp eDom) && isDeterministicEnvDesc eDom eDesc && eBody.hasLooseBVar 0 then
                let envNm := resolveQuantBinderName tbl eNm eDesc.noun.singular
                let freshEnvNm ← freshShadowFreeName envNm "E"
                withLocalDecl freshEnvNm eBi eDom fun fvE => do
                  let eTex ← exprToLatex fvE tbl
                  let rec matchGuards (qbSeen : Bool) (cpSeen : Bool) (gCur : Expr) :
                      MetaM (Option (Array Inline)) := do
                    let gCur ← normalizeForPresentation gCur
                    if qbSeen && cpSeen then
                      let qHead : Array Inline := #[
                        .text "every compatible ", .inlineMath nTex,
                        .text "-query deterministic environment ", .inlineMath eTex
                      ]
                      return some (← renderPropWithQuants (accQuants.push qHead) reg tbl gCur)
                    match gCur with
                    | .forallE gNm gDom gBody gBi =>
                        if ← isAmbientTypeclass gDom then
                          withLocalDecl gNm gBi gDom fun fv => matchGuards qbSeen cpSeen (gBody.instantiate1 fv)
                        else if ← isProp gDom then
                          if !qbSeen && propIsQueryBounded gDom fvN fvE then
                            if gBody.hasLooseBVar 0 then
                              withLocalDecl gNm gBi gDom fun fv => matchGuards true cpSeen (gBody.instantiate1 fv)
                            else
                              matchGuards true cpSeen gBody
                          else if !cpSeen && propIsCompatibleWithEnv gDom fvE then
                            if gBody.hasLooseBVar 0 then
                              withLocalDecl gNm gBi gDom fun fv => matchGuards qbSeen true (gBody.instantiate1 fv)
                            else
                              matchGuards qbSeen true gBody
                          else pure none
                        else pure none
                    | _ => pure none
                  matchGuards false false (eBody.instantiate1 fvE)
              else pure none
          | _ => pure none
        if let some folded := regC? then
          return folded
      if body.hasLooseBVar 0 then
        let domTex ← exprToLatex dom tbl
        let rec collectSameDom (firstFv : Expr) (fvIds : Array FVarId) (varTexs : Array String) (cur : Expr) :
            MetaM (Array Inline) := do
          let cur ← normalizeForPresentation cur
          let canJoin ← match cur with
            | .forallE nm' dom' body' _ =>
                if !(← isProp dom') && !(← isAmbientTypeclass dom') && body'.hasLooseBVar 0 then
                  let fvsInDom := (Lean.collectFVars {} dom').fvarIds
                  if fvsInDom.any fvIds.contains then pure none
                  else
                    let desc' ← describeType tbl dom'
                    let domTex' ← exprToLatex dom' tbl
                    if desc'.noun.singular == desc.noun.singular &&
                       desc'.adjectives == desc.adjectives &&
                       desc'.accessories == desc.accessories &&
                       domTex' == domTex then
                      pure (some (nm', dom', body', cur))
                    else pure none
                else pure none
            | _ => pure none
          match canJoin with
          | some (nm', dom', body', _) =>
              let bi' := match cur with | .forallE _ _ _ b => b | _ => .default
              let nmToUse := resolveQuantBinderName tbl nm' desc.noun.singular
              let freshNm ← freshShadowFreeName nmToUse "x"
              withLocalDecl freshNm bi' dom' fun fv' => do
                let vTex ← exprToLatex fv' tbl
                collectSameDom firstFv (fvIds.push fv'.fvarId!) (varTexs.push vTex) (body'.instantiate1 fv')
          | none =>
              if varTexs.size == 1 && !isDeterministicEnvDesc dom desc then
                if let .forallE gNm gDom gBody gBi := cur then
                  if ← isProp gDom then
                    let gDomNorm ← normalizeForPresentation gDom
                    if let some (elem, setExpr) := matchNotMembershipExpr? gDomNorm then
                      if elem.consumeMData == firstFv &&
                         !(Lean.collectFVars {} setExpr).fvarIds.contains firstFv.fvarId! then
                        let setTex ← exprToLatex setExpr tbl
                        let qHead : Array Inline := #[.text "every ", .inlineMath s!"{varTexs[0]!} \\notin {setTex}"]
                        if gBody.hasLooseBVar 0 then
                          return ← withLocalDecl gNm gBi gDom fun fvH =>
                            renderPropWithQuants (accQuants.push qHead) reg tbl (gBody.instantiate1 fvH)
                        else
                          return ← renderPropWithQuants (accQuants.push qHead) reg tbl gBody
              let qHead : Array Inline ← do
                if varTexs.size == 1 then
                  let varTex := varTexs[0]!
                  if desc.noun.singular.startsWith "element of \\(" && desc.noun.singular.endsWith "\\)" then
                    let setTex := ((desc.noun.singular.drop 13).dropEnd 2).toString
                    pure #[.text "every ", .inlineMath s!"{varTex} \\in {setTex}"]
                  else if domClean.isAppOf ``Prod && domClean.getAppArgs.size == 2 && desc.adjectives.isEmpty && desc.accessories.isEmpty then
                    let aTex ← exprToLatex domClean.getAppArgs[0]! tbl
                    let bTex ← exprToLatex domClean.getAppArgs[1]! tbl
                    pure #[.text "every pair ", .inlineMath s!"{varTex} \\in {aTex} \\times {bTex}"]
                  else if desc.noun.singular == "pair" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
                    pure #[.text "every pair ", .inlineMath varTex]
                  else if desc.noun.singular == "integer in \\(\\mathbb{N}\\)" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
                    pure #[.text "every ", .inlineMath s!"{varTex} \\in \\mathbb\{N}"]
                  else if desc.noun.singular == "nonnegative scalar" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
                    pure #[.text "every ", .inlineMath s!"{varTex} \\ge 0"]
                  else
                    let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
                    let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
                    pure (predHeadTextWithTail s!"every {adj}{desc.noun.singular} " varTex acc)
                else
                  let varsTex := String.intercalate ", " varTexs.toList
                  if desc.noun.singular.startsWith "element of \\(" && desc.noun.singular.endsWith "\\)" then
                    let setTex := ((desc.noun.singular.drop 13).dropEnd 2).toString
                    pure #[.text "all ", .inlineMath s!"{varsTex} \\in {setTex}"]
                  else if domClean.isAppOf ``Prod && domClean.getAppArgs.size == 2 && desc.adjectives.isEmpty && desc.accessories.isEmpty then
                    let aTex ← exprToLatex domClean.getAppArgs[0]! tbl
                    let bTex ← exprToLatex domClean.getAppArgs[1]! tbl
                    pure #[.text "all pairs ", .inlineMath s!"{varsTex} \\in {aTex} \\times {bTex}"]
                  else if desc.noun.singular == "pair" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
                    pure #[.text "all pairs ", .inlineMath varsTex]
                  else if desc.noun.singular == "integer in \\(\\mathbb{N}\\)" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
                    pure #[.text "all ", .inlineMath s!"{varsTex} \\in \\mathbb\{N}"]
                  else if desc.noun.singular == "nonnegative scalar" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
                    pure #[.text "all ", .inlineMath s!"{varsTex} \\ge 0"]
                  else if desc.noun.singular == "bitstring" && desc.adjectives.isEmpty && desc.accessories.length == 1 then
                    let acc0 := desc.accessories.head!
                    if acc0.startsWith "of length \\(" && acc0.endsWith "\\)" then
                      let lenTex := ((acc0.drop 12).dropEnd 2).toString.trimAscii.toString
                      let sup := if lenTex.length == 1 then lenTex else "{" ++ lenTex ++ "}"
                      pure #[.text "all ", .inlineMath (varsTex ++ " \\in \\{0,1\\}^" ++ sup)]
                    else
                      let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
                      let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
                      pure (predHeadTextWithTail s!"all {adj}{desc.noun.plural} " varsTex acc)
                  else
                    let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
                    let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
                    pure (predHeadTextWithTail s!"all {adj}{desc.noun.plural} " varsTex acc)
              return ← renderPropWithQuants (accQuants.push qHead) reg tbl cur
        let nmToUse := resolveQuantBinderName tbl nm desc.noun.singular
        let freshNm ← freshShadowFreeName nmToUse "x"
        return ← withLocalDecl freshNm bi dom fun fv => do
          let varTex ← exprToLatex fv tbl
          collectSameDom fv #[fv.fvarId!] #[varTex] (body.instantiate1 fv)
      else
        let qHead : Array Inline ← do
          if domClean.isAppOf ``Prod && domClean.getAppArgs.size == 2 && desc.adjectives.isEmpty && desc.accessories.isEmpty then
            let aTex ← exprToLatex domClean.getAppArgs[0]! tbl
            let bTex ← exprToLatex domClean.getAppArgs[1]! tbl
            pure #[.text "every pair in ", .inlineMath s!"{aTex} \\times {bTex}"]
          else
            let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
            let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
            pure #[.text s!"every {adj}{desc.noun.singular}{acc}"]
        return ← renderPropWithQuants (accQuants.push qHead) reg tbl body
  -- Logical connectives & registered `informal_pred` overlays
  let fn := prop.getAppFn.consumeMData
  let args := prop.getAppArgs
  if let .const head _ := fn then
    let env ← getEnv
    if let some phrase := effectivePredPhrase? env head then
      let glossInl ← do
        let arity? := (Presentation.getMathPresentation env head).explicitNonPropArity?
        if arity? == some 0 then
          pure (parseProseWithMath phrase)
        else
          let visArgs ← collectVisiblePredArgs tbl head args
          if visArgs.isEmpty then
            pure (parseProseWithMath phrase)
          else if hasNumericPlaceholders phrase visArgs.size then
            let mut subPhrase := phrase
            for i in [:visArgs.size] do
              let slot := "{" ++ toString i ++ "}"
              if (subPhrase.splitOn slot).length > 1 then
                let argTex ← exprToLatex visArgs[i]! tbl
                subPhrase := subPhrase.replace slot s!"\\({argTex}\\)"
            pure (parseProseWithMath subPhrase)
          else if visArgs.size == 1 then
            if predPhraseStartsWithVerb phrase then
              let subjTex ← exprToLatex visArgs[0]! tbl
              pure (#[.inlineMath subjTex, .text " "] ++ parseProseWithMath phrase)
            else
              pure (parseProseWithMath phrase)
          else if isBinaryInfixPredPhrase phrase then
            if visArgs.size == 2 then
              let aTex ← exprToLatex visArgs[0]! tbl
              let bTex ← exprToLatex visArgs[1]! tbl
              pure #[.inlineMath aTex, .text (" " ++ phrase ++ " "), .inlineMath bTex]
            else
              let argTexs ← visArgs.mapM fun a => exprToLatex a tbl
              let initTex := String.intercalate ", " argTexs.pop.toList
              let lastTex := argTexs.back!
              pure #[.inlineMath s!"({initTex})", .text (" " ++ phrase ++ " "), .inlineMath lastTex]
          else if predPhraseStartsWithVerb phrase then
            let argTexs ← visArgs.mapM fun a => exprToLatex a tbl
            let tupleTex := String.intercalate ", " argTexs.toList
            pure (#[.inlineMath s!"({tupleTex})", .text " "] ++ parseProseWithMath phrase)
          else
            pure (parseProseWithMath phrase)
      return flushQuants accQuants glossInl
    if head == ``Function.Injective && args.size == 3 then
      let fTex ← exprToLatex args[2]! tbl
      return flushQuants accQuants #[.inlineMath fTex, .text " is injective"]
    if head == ``Not && args.size == 1 then
      let inner := args[0]!.consumeMData
      if inner.getAppFn.consumeMData.isConstOf ``Function.Injective && inner.getAppArgs.size == 3 then
        let fTex ← exprToLatex inner.getAppArgs[2]! tbl
        return flushQuants accQuants #[.inlineMath fTex, .text " is not injective"]
      let innerNorm ← normalizeForPresentation inner
      if let some (elem, setExpr) := matchMembershipExpr? innerNorm then
        let eTex ← exprToLatex elem tbl
        let sTex ← exprToLatex setExpr tbl
        return flushQuants accQuants #[.inlineMath s!"{eTex} \\notin {sTex}"]
    if head == ``And && args.size ≥ 2 then
      -- Flatten chained inequalities `a ≤ b ∧ b ≤ c (∧ c ≤ d)` into `a \le b \le c \le d`
      let rec collectAnds : Expr → Array Expr
        | e =>
            let f := e.getAppFn.consumeMData
            let as := e.getAppArgs
            if f.isConstOf ``And && as.size ≥ 2 then
              collectAnds as[as.size - 2]! ++ collectAnds as[as.size - 1]!
            else #[e]
      let parts := collectAnds prop
      let mut leChain : Option (Array String) := some #[]
      let mut prevRhs? : Option String := none
      for part in parts do
        let p ← normalizeForPresentation part
        let pf := p.getAppFn.consumeMData
        let pa := p.getAppArgs
        if pf.isConstOf ``LE.le && pa.size ≥ 2 then
          let lTex ← exprToLatex pa[pa.size - 2]! tbl
          let rTex ← exprToLatex pa[pa.size - 1]! tbl
          match prevRhs?, leChain with
          | none, some arr =>
              leChain := some (arr.push lTex |>.push rTex)
              prevRhs? := some rTex
          | some prev, some arr =>
              if prev == lTex then
                leChain := some (arr.push rTex)
                prevRhs? := some rTex
              else
                leChain := none
          | _, none => pure ()
        else
          leChain := none
      if let some terms := leChain then
        if terms.size ≥ 3 then
          return flushQuants accQuants #[.inlineMath (String.intercalate " \\le " terms.toList)]
      let a ← renderPropWithQuants #[] reg tbl args[args.size - 2]!
      let b ← renderPropWithQuants #[] reg tbl args[args.size - 1]!
      let andInl := match a, b with
        | #[.inlineMath aTex], #[.inlineMath bTex] =>
            if hasRelationalMath aTex || hasRelationalMath bTex then
              #[.inlineMath aTex, .text " and ", .inlineMath bTex]
            else
              #[.inlineMath s!"{aTex} \\wedge {bTex}"]
        | _, _ =>
            let sep := if inlinesHasProseCommaOrSemi a || inlinesHasProseCommaOrSemi b then ", and " else " and "
            a ++ #[.text sep] ++ b
      return flushQuants accQuants andInl
    if head == ``Iff && args.size ≥ 2 then
      let a ← renderPropWithQuants #[] reg tbl args[args.size - 2]!
      let b ← renderPropWithQuants #[] reg tbl args[args.size - 1]!
      return flushQuants accQuants (a ++ #[.text " if and only if "] ++ b)
    if head == ``Exists && args.size ≥ 2 then
      if let .lam nm dom body bi := args[args.size - 1]! then
        let desc ← describeType tbl dom
        let domClean := dom.consumeMData
        let nmToUse := resolveQuantBinderName tbl nm desc.noun.singular
        let freshNm ← chooseUnshadowedBinderName nmToUse #[dom, body] "x"
        let exInl ← withLocalDecl freshNm bi dom fun fv => do
          let varTex ← exprToLatex fv tbl
          let bodyInl ← renderPropWithQuants #[] reg tbl (body.instantiate1 fv)
          if desc.noun.singular.startsWith "element of \\(" && desc.noun.singular.endsWith "\\)" then
            let setTex := ((desc.noun.singular.drop 13).dropEnd 2).toString
            return #[.text "there exists ", .inlineMath s!"{varTex} \\in {setTex}",
                     .text " such that "] ++ bodyInl
          if domClean.isAppOf ``Prod && domClean.getAppArgs.size == 2 && desc.adjectives.isEmpty && desc.accessories.isEmpty then
            let aTex ← exprToLatex domClean.getAppArgs[0]! tbl
            let bTex ← exprToLatex domClean.getAppArgs[1]! tbl
            return #[.text "there exists a pair ", .inlineMath s!"{varTex} \\in {aTex} \\times {bTex}",
                     .text " such that "] ++ bodyInl
          if desc.noun.singular == "pair" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
            return #[.text "there exists a pair ", .inlineMath varTex,
                     .text " such that "] ++ bodyInl
          if desc.noun.singular == "integer in \\(\\mathbb{N}\\)" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
            return #[.text "there exists ", .inlineMath s!"{varTex} \\in \\mathbb\{N}",
                     .text " such that "] ++ bodyInl
          if desc.noun.singular == "nonnegative scalar" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
            return #[.text "there exists ", .inlineMath s!"{varTex} \\ge 0",
                     .text " such that "] ++ bodyInl
          let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
          let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
          let art := article (adj ++ desc.noun.singular)
          return #[.text s!"there exists {art} {adj}{desc.noun.singular} ", .inlineMath varTex,
                   .text s!"{acc} such that "] ++ bodyInl
        return flushQuants accQuants exInl
  -- Default: clean 2D LaTeX formula
  let tex ← exprToLatex prop tbl
  return flushQuants accQuants #[.inlineMath tex]

/-- Render a proposition into natural mathematical English + LaTeX (`Array Inline`),
respecting `CryptoRegister`, consulting registered CC/domain handlers first, and falling back to clean `LeanTeX`. -/
partial def renderPropositionAux (reg : CryptoRegister) (tbl : SymbolTable) (prop : Expr) : MetaM (Array Inline) :=
  renderPropWithQuants #[] reg tbl prop

/-- Render a proposition into natural mathematical English + LaTeX (`Array Inline`)
using the default constructive register. -/
partial def renderProposition (tbl : SymbolTable) (prop : Expr) : MetaM (Array Inline) :=
  renderPropositionAux .constructive tbl prop

/-- Cached local-context entry for `buildGoalState` so unchanged parameters/hypotheses
are not re-described across hundreds of proof nodes in the same declaration. -/
private inductive CachedGoalDecl where
  | suppressed
  | largePropUnrendered
  | ready (entry : ContextEntry) (alwaysShow : Bool)

private initialize goalCtxDeclCacheRef :
    IO.Ref (Std.HashMap (FVarId × UInt64) CachedGoalDecl) ← IO.mkRef {}

/-- Clear the per-declaration `buildGoalState` local-context cache. -/
def clearGoalCtxCache : IO Unit :=
  goalCtxDeclCacheRef.set {}

/-- Build a clean Kyle Miller `GoalState` from a live local context and target `Expr`.
Suppresses ambient typeclasses and implementation details, and never prints `None`. -/
def buildGoalState (tbl : SymbolTable) (target : Expr) (onlyUsed : Bool := false) : MetaM GoalState := do
  let lctx ← getLCtx
  let targetClean ← normalizeForPresentation target
  let targetFVars := (Lean.collectFVars {} targetClean).fvarIds
  let aliasTag : UInt64 :=
    tbl.exprAliases.foldl (init := hash tbl.exprAliases.size) fun a (pat, s) =>
      mixHash a (mixHash (hash pat) (hash s))
  let mut cache ← goalCtxDeclCacheRef.get
  if cache.size ≥ 4096 then
    cache := {}
  let mut cacheDirty := false
  let mut entries : Array ContextEntry := #[]
  for decl in lctx do
    let used := targetFVars.contains decl.fvarId
    let key := (decl.fvarId, aliasTag)
    match cache.get? key with
    | some .suppressed => continue
    | some (.ready entry alwaysShow) =>
        if (!onlyUsed && alwaysShow) || used then
          entries := entries.push { entry with usedInGoal := used }
    | some .largePropUnrendered =>
        if !used then continue
        let propTex ← exprToLatex decl.type tbl
        let entry : ContextEntry := {
          name? := cleanBinderName? decl.userName
          description := s!"\\({propTex}\\)"
          isHypothesis := true
          usedInGoal := true
        }
        cache := cache.insert key (.ready entry false)
        cacheDirty := true
        entries := entries.push entry
    | none =>
        if onlyUsed && !used then
          continue
        if ← isSuppressedLocalDecl decl then
          cache := cache.insert key .suppressed
          cacheDirty := true
          continue
        if ← isProp decl.type then
          let isSmall := exprDagSmall decl.type 160
          if !used && !isSmall then
            cache := cache.insert key .largePropUnrendered
            cacheDirty := true
            continue
          let propTex ← exprToLatex decl.type tbl
          let entry : ContextEntry := {
            name? := cleanBinderName? decl.userName
            description := s!"\\({propTex}\\)"
            isHypothesis := true
            usedInGoal := used
          }
          cache := cache.insert key (.ready entry isSmall)
          cacheDirty := true
          entries := entries.push entry
        else
          let desc ← describeType tbl decl.type
          let sym ← exprToLatex decl.toExpr tbl
          let roleText :=
            if desc.noun.singular == "integer in \\(\\mathbb{N}\\)" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
              "is in \\(\\mathbb{N}\\)"
            else if desc.noun.singular == "nonnegative scalar" && desc.adjectives.isEmpty && desc.accessories.isEmpty then
              "is in \\(\\mathbb{R}_{\\ge 0}\\)"
            else
              let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
              let art := article (adj ++ desc.noun.singular)
              let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
              s!"is {art} {adj}{desc.noun.singular}{acc}"
          let entry : ContextEntry := {
            name? := some s!"\\({sym}\\)"
            description := roleText
            isHypothesis := false
            usedInGoal := used
          }
          cache := cache.insert key (.ready entry true)
          cacheDirty := true
          entries := entries.push entry
  if cacheDirty then
    goalCtxDeclCacheRef.set cache
  let targetLatex ← exprToLatex targetClean tbl
  let rawTarget := stripMacroScopesExpr (← instantiateMVars target)
  let rawTarget? ←
    if !rawTarget.hasLooseBVars && exprDagSmall rawTarget 240 then
      pure (some (← ppExpr rawTarget).pretty)
    else
      pure none
  return {
    context := entries
    targetLatex
    rawLeanGoal? := rawTarget?
  }

/-- Format a concise capitalized role description for a type `ty` (with optional adjectives such as `"finite"`). -/
def formatParameterRole (tbl : SymbolTable) (ty : Expr) (adjectives : List String := []) : MetaM String := do
  let desc ← describeType tbl ty
  let mergedAdjs := adjectives.foldl (init := desc.adjectives) fun acc a =>
    if acc.contains a then acc else a :: acc
  if desc.noun.singular == "integer in \\(\\mathbb{N}\\)" && mergedAdjs.isEmpty && desc.accessories.isEmpty then
    return "Integer parameter in \\(\\mathbb{N}\\)."
  if desc.noun.singular == "nonnegative scalar" && mergedAdjs.isEmpty && desc.accessories.isEmpty then
    return "Nonnegative scalar (\\(\\ge 0\\))."
  let adj := if mergedAdjs.isEmpty then "" else String.intercalate " " mergedAdjs ++ " "
  let art := article (adj ++ desc.noun.singular)
  let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
  return capitalizeFirst (ensurePeriod s!"{art} {adj}{desc.noun.singular}{acc}")

/-- Section-fixed context passed into `parseTheoremStatement` so already-fixed parameters
and assumptions are omitted from individual theorem statements in that section. -/
structure HoistedContext where
  paramSyms : Std.HashSet String := {}
  hypKeys : Std.HashSet String := {}
  sectionId? : Option String := none
  sectionNumber? : Option Nat := none
  deriving Inhabited

/-- Checked metadata for a theorem-local shorthand (`Write c₁ = …` or `let R = …`). -/
structure LocalShorthandInfo where
  sym : String
  rhsLatex : String
  leanType : String
  roleDescription : String
  deriving Repr, Inhabited

/-- Checked parameter metadata extracted while its `FVarId` is live in `LocalContext`. -/
structure SigParam where
  sym : String
  cleanName : String
  typeKey : String
  intro : Intro
  roleDescription : String
  leanType : String
  isDomainConfig : Bool
  depSyms : Array String
  deriving Repr, Inhabited

/-- Checked hypothesis metadata extracted while its `FVarId` is live in `LocalContext`. -/
structure SigHyp where
  key : String
  inlines : Array Inline
  depSyms : Array String
  deriving Repr, Inhabited

/-- Extracted visible signature of one declaration for section-context hoisting analysis. -/
structure SignatureSummary where
  params : Array SigParam := #[]
  hyps : Array SigHyp := #[]
  deriving Inhabited

/-- Structured decomposition of a theorem's top-level signature for Maurer-style presentation. -/
structure ParsedStatement where
  ambient? : Option AmbientSetting
  paragraphs : Array (Array Inline)
  conclusion : Expr
  localShorthands : Array LocalShorthandInfo := #[]
  notationInspectors : Array SymbolInspector := #[]
  deriving Inhabited

/-- Approximate AST size of an expression (used for generic repeated-subexpression factoring). -/
private partial def exprSize : Expr → Nat
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ d b _ => 1 + exprSize d + exprSize b
  | .forallE _ d b _ => 1 + exprSize d + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e => exprSize e
  | .proj _ _ s => 1 + exprSize s
  | _ => 1

/-- Collect non-Prop, visible (explicit, non-hidden, non-typeclass) application subexpressions
occurring across `exprs` to automatically factor heavy repeated terms into crisp shorthands. -/
private partial def collectCandidateSubexprs (tbl : SymbolTable) (e : Expr)
    (counts : Std.HashMap Expr Nat) : MetaM (Std.HashMap Expr Nat) := do
  let e ← normalizeForPresentation e
  if tbl.exprAliases.any (fun (pat, _) => pat.consumeMData == e.consumeMData) then
    return counts
  match e with
  | .app .. =>
      let mut m := counts
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs
      let headName? := fn.constName?
      if let some hn := headName? then
        if tbl.zeroArgConsts.contains hn then
          return m
      if !e.hasLooseBVars then
        let sz := exprSize e
        if sz ≥ 6 && sz ≤ 48 then
          let isP ← try isProp e catch _ => pure true
          let isTyOrInst ← try
            let ty ← inferType e
            if ty.isSort then pure true
            else isAmbientTypeclass ty
          catch _ => pure true
          let isInstConst := match headName? with
            | some hn => (shortConstName hn).startsWith "inst" || hn == ``OfNat.ofNat
            | none => false
          if !isP && !isTyOrInst && !isInstConst then
            m := m.insert e ((m.getD e 0) + 1)
      -- Recurse ONLY into explicit, non-hidden arguments (never implicit typeclasses/interfaces!)
      let recurseArgs ←
        match headName? with
        | some hn => do
            try
              let info ← getConstInfo hn
              let mut curTy := info.type
              let mut vis : Array Expr := #[]
              let mut expIdx := 0
              let hidden := tbl.hiddenArgs.getD hn []
              for a in args do
                let f ← match curTy.consumeMData with
                  | x@(.forallE ..) => pure x
                  | other => withTransparency .reducible (whnf other)
                match f.consumeMData with
                | .forallE _ _ body bi =>
                    if bi.isExplicit then
                      if !hidden.contains expIdx then
                        vis := vis.push a
                      expIdx := expIdx + 1
                    curTy := body.instantiate1 a
                | _ => vis := vis.push a
              pure vis
            catch _ => pure args
        | none => pure args
      for a in recurseArgs do
        m ← collectCandidateSubexprs tbl a m
      return m
  | .forallE _ d b _ =>
      let m ← collectCandidateSubexprs tbl d counts
      if !b.hasLooseBVars then collectCandidateSubexprs tbl b m else return m
  | _ => return counts

/-- Approximate visible glyph length of rendered LaTeX (excluding markup macros like `\mathrm{`
and `\left` / `\right`) so short terms such as `system(scheme)` or `Δ(fixedBit(false), sampledBit)`
are never pointlessly replaced by `c₁`. -/
private def visibleMathLength (tex : String) : Nat :=
  let s := tex
    |>.replace "@@CADMO_W_0@@" "c1" |>.replace "@@CADMO_W_1@@" "c2" |>.replace "@@CADMO_W_2@@" "c3"
    |>.replace "\\mathrm{" "" |>.replace "\\mathsf{" "" |>.replace "\\mathcal{" ""
    |>.replace "\\mathbf{" "" |>.replace "\\mathbb{" "" |>.replace "\\text{" ""
    |>.replace "\\left" "" |>.replace "\\right" ""
    |>.replace "\\!" "" |>.replace "\\," " " |>.replace "\\;" " "
    |>.replace "{" "" |>.replace "}" ""
    |>.replace "\\Delta" "Δ" |>.replace "\\varepsilon" "ε" |>.replace "\\epsilon" "ε"
    |>.replace "\\times" "×" |>.replace "\\cdot" "·" |>.replace "\\parallel" "∥"
    |>.replace "\\otimes" "⊗" |>.replace "\\le" "≤" |>.replace "\\ge" "≥"
  s.trimAscii.toString.length

/-- Extract inline math strings embedded as `\(...\)` inside an English prose string. -/
private def extractEmbeddedMath (s : String) : Array String := Id.run do
  let parts := s.splitOn "\\("
  let mut out : Array String := #[]
  for part in parts.drop 1 do
    match part.splitOn "\\)" with
    | m :: _ => out := out.push m
    | [] => pure ()
  return out

private def collectInlineMathStrings (inls : Array Inline) : Array String :=
  inls.flatMap fun
    | .text s | .emph s => extractEmbeddedMath s
    | .inlineMath s => #[s]
    | .displayMath s _ => #[s]
    | .symbol _ d true => #[d]
    | _ => #[]

/-- Factor up to 3 heavy repeated visible subexpressions across `exprs` into crisp local
abbreviations using collision-free placeholder tokens until final non-colliding display symbols
are allocated. -/
private def factorRepeatedSubexprs (tbl : SymbolTable) (exprs : Array Expr) :
    MetaM (SymbolTable × Array (String × Expr)) := do
  let mut counts : Std.HashMap Expr Nat := {}
  for ex in exprs do
    counts ← collectCandidateSubexprs tbl ex counts
  let mut cands : Array (Expr × Nat × Nat) := #[]
  for (ex, cnt) in counts.toList do
    if cnt ≥ 2 then
      cands := cands.push (ex, cnt, exprSize ex)
  let sorted := cands.qsort fun (_, c1, s1) (_, c2, s2) =>
    if s1 != s2 then s1 > s2 else c1 > c2
  let mut curTbl := tbl
  let mut defs : Array (String × Expr) := #[]
  let mut chosenExprs : Array Expr := #[]
  for (ex, _, _) in sorted do
    if defs.size ≥ 3 then break
    if chosenExprs.any (fun prev => prev == ex) then continue
    let tex ← exprToLatex ex curTbl
    if visibleMathLength tex < 34 || (tex.splitOn "inst").length > 1 then continue
    let sym := "@@CADMO_W_" ++ toString defs.size ++ "@@"
    defs := defs.push (sym, ex)
    chosenExprs := chosenExprs.push ex
    curTbl := curTbl.withExprAlias ex sym
  return (curTbl, defs)

/-- Choose `count` fresh subscripted shorthand symbols (`c_1, c_2, ...` or `w_1, w_2, ...`)
such that neither the bare prefix nor any subscripted symbol collides with `usedNames` or
already-visible statement math. -/
private def pickFreshShorthandFamily (used : Std.HashSet String) (visibleMath : Array String)
    (count : Nat) : Array String := Id.run do
  let isFree (tok : String) : Bool :=
    !used.contains tok && !mathDispAppearsIn visibleMath tok
  let prefixes := #["c", "w", "u", "v", "z", "t", "y", "a", "b"]
  for pfx in prefixes do
    let syms := (Array.range count).map fun i => s!"{pfx}_\{{i + 1}}"
    if isFree pfx && syms.all isFree then
      return syms
  let mut out : Array String := #[]
  let mut idx := 1
  while out.size < count do
    let cand := s!"s_\{{idx}}"
    if isFree cand && !out.contains cand then
      out := out.push cand
    idx := idx + 1
  return out

/-- Helper: check if `sub` appears inside any `Inline` of `inls`. -/
private def inlinesContain (inls : Array Inline) (needle : String) : Bool :=
  inls.any fun
    | .text s | .emph s | .inlineMath s => (s.splitOn needle).length > 1
    | .displayMath s _ => (s.splitOn needle).length > 1
    | .symbol _ d _ => (d.splitOn needle).length > 1
    | .citation _ _ => false

/-- Helper: replace a shorthand token (e.g. `c_{2}` → `c_{1}`) across `Array Inline`. -/
private def replaceInInline (old new : String) : Inline → Inline
  | .text s => .text (s.replace old new)
  | .emph s => .emph (s.replace old new)
  | .inlineMath s => .inlineMath (s.replace old new)
  | .displayMath s p => .displayMath (s.replace old new) p
  | .symbol k d t => .symbol k (d.replace old new) t
  | .citation l t => .citation l t

private def replaceInInlines (old new : String) (inls : Array Inline) : Array Inline :=
  inls.map (replaceInInline old new)

/-- Continuation-passing hoist of leading `let x := v; body` bindings out of a theorem's
conclusion so `fv` stays live in the `LocalContext` throughout factoring and rendering,
and display equations never print `let ... in let ... in`. Preserves distinct source names
and avoids colliding with already-used binder display names in `tbl.usedNames`. -/
private partial def withHoistedConclusionLets {α : Type} (tbl : SymbolTable) (e : Expr)
    (acc : Array (String × Expr × Expr) := #[])
    (k : SymbolTable → Array (String × Expr × Expr) → Expr → MetaM α) : MetaM α := do
  match e.consumeMData with
  | .letE nm ty val body _ =>
      let isP ← try isProp ty catch _ => pure false
      if isP then k tbl acc e
      else
        withLetDecl nm ty val fun fv => do
          let rawTex ← exprToLatex fv tbl
          let nmTex := pickFreshLocalSymbol tbl.usedNames rawTex
          let tbl' := (tbl.withExprAlias fv nmTex).withUsedName nmTex
          withHoistedConclusionLets tbl' (body.instantiate1 fv) (acc.push (nmTex, ty, val)) k
  | _ => k tbl acc e

/-- Render `Expr` to a clean, macro-scope-free Lean type string. -/
private def cleanTypeString (ty : Expr) : MetaM String := do
  let ty ← normalizeForPresentation ty
  return (← ppExpr ty).pretty (width := 100)

/-- Decide whether `ty` represents a structured domain configuration / CC object
eligible for majority-based section hoisting (excluding bare scalars `ℕ`, `ℤ`, `Bool`,
`Type`, functions, and lists). -/
private def isDomainConfigExpr (env : Environment) (desc : TypeDescription) (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  let isScalarOrContainer :=
    ty.isSort || ty == mkConst ``Nat || ty == mkConst ``Int || ty == mkConst ``Bool ||
    ty == mkConst `Real || ty == mkConst `NNReal || ty == mkConst `ENNReal ||
    ty.isAppOf ``List || ty.isAppOf ``Fin || ty.isAppOf ``Option || ty.isAppOf `Equiv.Perm ||
    ty.isForall
  if isScalarOrContainer then false
  else
    let hasNoun := match ty.getAppFn.consumeMData with
      | .const head _ => (effectiveNoun? env head).isSome
      | _ => false
    hasNoun || ["interface", "resource", "converter", "specification",
                "game", "distinguisher"].contains desc.noun.singular

private def propHeadName? (prop : Expr) : MetaM (Option Name) := do
  if let .const h _ := prop.consumeMData.getAppFn.consumeMData then
    return some h
  let norm ← normalizeForPresentation prop
  if let .const h _ := norm.consumeMData.getAppFn.consumeMData then
    return some h
  return none

/-- Extract visible parameters and hypotheses from `theoremType` for section-context hoisting. -/
def extractSignatureSummary (tbl : SymbolTable) (theoremType : Expr) (declName : Name := .anonymous) :
    MetaM SignatureSummary := do
  let env ← getEnv
  forallTelescope theoremType fun fvars _ => do
    let mut finiteSets : List String := []
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      if ← isAmbientTypeclass decl.type then
        let head := decl.type.getAppFn.consumeMData
        if let .const hName _ := head then
          if hName == `Fintype || hName == `Finite then
            if let some carrier := decl.type.getAppArgs.back? then
              if let .fvar cid := carrier.consumeMData then
                let cdecl ← cid.getDecl
                finiteSets := (cleanBinderName cdecl.userName) :: finiteSets
    let mut params : Array SigParam := #[]
    let mut hyps : Array SigHyp := #[]
    let mut fvarToSym : Std.HashMap FVarId String := {}
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      if ← isSuppressedLocalDecl decl then continue
      if ← isProp decl.type then
        if !declName.isAnonymous then
          let pHead? ← propHeadName? decl.type
          if pHead?.any (isPredicateSuppressedInSection env declName) then
            continue
        let hInl ← renderProposition tbl decl.type
        let key := inlinesCanonicalKey hInl
        let depIds := (Lean.collectFVars {} decl.type).fvarIds
        let mut depSyms : Array String := #[]
        for id in depIds do
          if let some s := fvarToSym.get? id then
            if !depSyms.contains s then
              depSyms := depSyms.push s
        hyps := hyps.push { key, inlines := hInl, depSyms }
      else
        let desc ← describeType tbl decl.type
        if desc.isAmbient then continue
        let clean := cleanBinderName decl.userName
        let sym ← exprToLatex fv tbl
        if !declName.isAnonymous then
          if isBinderSuppressedInSection env declName clean ||
             isBinderSuppressedInSection env declName sym ||
             isBinderSuppressedInSection env declName decl.userName.toString then
            continue
        fvarToSym := fvarToSym.insert decl.fvarId sym
        let adjs :=
          if finiteSets.contains clean && !desc.adjectives.contains "finite" then
            "finite" :: desc.adjectives
          else desc.adjectives
        let depIds := (Lean.collectFVars {} decl.type).fvarIds
        let depNames ← depIds.toList.mapM fun id => do
          let d ← id.getDecl
          let s ← exprToLatex d.toExpr tbl
          return s!"\\({s}\\)"
        let mut depSyms : Array String := #[]
        for id in depIds do
          if let some s := fvarToSym.get? id then
            if !depSyms.contains s then
              depSyms := depSyms.push s
        let typeTex ← exprToLatex decl.type tbl
        let typeKey := s!"{typeTex}|{String.intercalate "," adjs}"
        let intro : Intro := {
          name := s!"\\({sym}\\)"
          noun := desc.noun
          adjectives := adjs
          accessories := desc.accessories
          subjunctive := true
          typeStr := desc.typeLatex?.getD ""
          mentions := depNames
        }
        let roleDescription ← formatParameterRole tbl decl.type
          (if finiteSets.contains clean then ["finite"] else [])
        let leanType ← cleanTypeString decl.type
        let isDomCfg := isDomainConfigExpr env desc decl.type
        params := params.push {
          sym, cleanName := clean, typeKey, intro, roleDescription, leanType,
          isDomainConfig := isDomCfg, depSyms
        }
    return { params, hyps }

private def stripInlineMathDelims (s : String) : String :=
  let t := s.trimAscii.toString
  if t.startsWith "\\(" && t.endsWith "\\)" then
    ((t.drop 2).dropEnd 2).toString.trimAscii.toString
  else
    t

private def isPlainNatIntro (x : Intro) : Bool :=
  x.noun.singular == "integer in \\(\\mathbb{N}\\)" && x.adjectives.isEmpty && x.accessories.isEmpty

private def isPlainNonnegIntro (x : Intro) : Bool :=
  x.noun.singular == "nonnegative scalar" && x.adjectives.isEmpty && x.accessories.isEmpty

private def elementOfSet? (x : Intro) : Option String :=
  if x.noun.singular.startsWith "element of \\(" && x.noun.singular.endsWith "\\)" &&
     x.adjectives.isEmpty && x.accessories.isEmpty then
    some ((x.noun.singular.drop 13).dropEnd 2).toString
  else
    none

private def isPlainRealIntro (x : Intro) : Bool :=
  x.noun.singular == "real number" && x.adjectives.isEmpty && x.accessories.isEmpty

private def stripIntroLeadAndPeriod (s : String) : String :=
  let s1 := if s.startsWith "Let " then (s.drop 4).toString else lowercaseFirst s
  let s2 := s1.trimAscii.toString
  if s2.endsWith "." then (s2.dropEnd 1).toString else s2

/-- Realize `Intro` items while compacting plain `Nat` parameters (`$q, W, P \in \mathbb{N}$`),
plain set elements (`$x, y \in S$`), real scalars (`$x \in \mathbb{R}$`), and nonnegative
scalar parameters (`$\varepsilon_1, \varepsilon_2 \ge 0$`) per Quantifier Economy (`Q3`, `Q5`).
Joins 2 binder groups cleanly with `, and let ` (never `; and `), and reserves `; ` / `; and `
strictly for 3+ clauses that contain internal English commas or semicolons. -/
def realizeGroupedIntros (intros : List Intro) : String := Id.run do
  if intros.isEmpty then return ""
  let natIntros := intros.filter isPlainNatIntro
  let nonnegIntros := intros.filter isPlainNonnegIntro
  let realIntros := intros.filter isPlainRealIntro
  let mut rawClauses : List (Bool × Bool × String) := []
  let mut otherRun : List Intro := []
  let mut emittedNat := false
  let mut emittedNonneg := false
  let mut emittedReal := false
  let mut emittedSets : List String := []
  let flushOther (run : List Intro) (acc : List (Bool × Bool × String)) :
      List (Bool × Bool × String) :=
    if run.isEmpty then acc
    else
      let parts := (mergeGroups run).map realizeIntroClause |>.filter (!·.isEmpty)
      let tagged := parts.mapIdx fun idx c => (false, idx == 0, c)
      acc ++ tagged
  for x in intros do
    if isPlainNatIntro x then
      if !emittedNat then
        rawClauses := flushOther otherRun rawClauses
        otherRun := []
        let names := String.intercalate ", " (natIntros.map (stripInlineMathDelims ·.name))
        rawClauses := rawClauses ++ [(true, true, s!"\\({names} \\in \\mathbb\{N}\\)")]
        emittedNat := true
    else if isPlainNonnegIntro x then
      if !emittedNonneg then
        rawClauses := flushOther otherRun rawClauses
        otherRun := []
        let names := String.intercalate ", " (nonnegIntros.map (stripInlineMathDelims ·.name))
        rawClauses := rawClauses ++ [(true, true, s!"\\({names} \\ge 0\\)")]
        emittedNonneg := true
    else if isPlainRealIntro x then
      if !emittedReal then
        rawClauses := flushOther otherRun rawClauses
        otherRun := []
        let names := String.intercalate ", " (realIntros.map (stripInlineMathDelims ·.name))
        rawClauses := rawClauses ++ [(true, true, s!"\\({names} \\in \\mathbb\{R}\\)")]
        emittedReal := true
    else if let some setTex := elementOfSet? x then
      if !emittedSets.contains setTex then
        rawClauses := flushOther otherRun rawClauses
        otherRun := []
        let matching := intros.filter (fun y => elementOfSet? y == some setTex)
        let names := String.intercalate ", " (matching.map (stripInlineMathDelims ·.name))
        rawClauses := rawClauses ++ [(true, true, s!"\\({names} \\in {setTex}\\)")]
        emittedSets := setTex :: emittedSets
    else
      otherRun := otherRun ++ [x]
  rawClauses := flushOther otherRun rawClauses
  -- Coalesce adjacent compact math clauses (`q ∈ ℕ` + `ε ≥ 0` -> `\(q \in \mathbb{N}\) and \(\varepsilon \ge 0\)`)
  let mut clauses : List (Bool × Bool × String) := []
  for (m, isHead, c) in rawClauses do
    match clauses.reverse with
    | (true, prevHead, prev) :: revTail =>
        if m then clauses := revTail.reverse ++ [(true, prevHead, s!"{prev} and {c}")]
        else clauses := clauses ++ [(m, isHead, c)]
    | _ =>
        clauses := clauses ++ [(m, isHead, c)]
  match clauses with
  | [] => ""
  | [(_, _, c)] => s!"Let {c}."
  | [(_, _, c0), (_, _, c1)] =>
      s!"Let {c0}, and let {c1}."
  | (_, _, c0) :: rest =>
      let tailStrs := rest.map fun (isMath, isHead, c) =>
        if isMath || isHead then s!"let {c}" else c
      let allStrs := c0 :: tailStrs
      let initStrs := allStrs.dropLast
      let lastStr := allStrs.getLast!
      let hasInternalPunct := allStrs.any proseHasCommaOrSemi
      let body :=
        if hasInternalPunct then
          String.intercalate "; " initStrs ++ "; and " ++ lastStr
        else
          String.intercalate ", " initStrs ++ ", and " ++ lastStr
      s!"Let {body}."

/-- Format hoisted section-fixed parameters and assumptions into a calm archival Section Context
paragraph (*"Throughout this section, let … [and assume that …]."*). -/
def formatSectionContextParagraphs (intros : List Intro) (hyps : Array (Array Inline)) :
    Array (Array Inline) := Id.run do
  if intros.isEmpty && hyps.isEmpty then return #[]
  let mut para : Array Inline := #[]
  let mut hasMultiIntro := false
  if !intros.isEmpty then
    let introSentence := realizeGroupedIntros intros
    let rawBody :=
      if introSentence.startsWith "Let " then
        "Throughout this section, let " ++ (introSentence.drop 4).toString
      else
        "Throughout this section, " ++ lowercaseFirst introSentence
    if !hyps.isEmpty then
      let trimmed := if rawBody.endsWith "." then (rawBody.dropEnd 1).toString else rawBody
      hasMultiIntro := proseHasCommaOrSemi trimmed
      para := para.push (.text (if hasMultiIntro then trimmed ++ "." else trimmed))
    else
      para := para.push (.text rawBody)
  if !hyps.isEmpty then
    let lead :=
      if para.isEmpty then "Throughout this section, assume that "
      else if hasMultiIntro then " Assume throughout that "
      else " and assume that "
    para := para.push (.text lead)
    let hypsHaveProsePunct := hyps.any inlinesHasProseCommaOrSemi
    for i in [:hyps.size] do
      if i > 0 then
        let sep :=
          if hyps.size == 2 then
            if hypsHaveProsePunct then ", and " else " and "
          else if i + 1 == hyps.size then
            if hypsHaveProsePunct then "; and " else ", and "
          else
            if hypsHaveProsePunct then "; " else ", "
        para := para.push (.text sep)
      para := para ++ hyps[i]!
    para := para.push (.text ".")
  return #[para]

private def kvGetStr? (kv : MData) (k : Name) : Option String :=
  match kv.find k with
  | some (.ofString s) => if s.isEmpty then none else some s
  | _ => none

initialize topProofRoleHookRef : IO.Ref (Expr → Array Expr → MetaM (Std.HashMap FVarId String)) ←
  IO.mkRef (fun _ _ => pure {})

initialize topProofNotationHookRef : IO.Ref (Expr → Array Expr → MetaM (Array (Expr × String × Option String))) ←
  IO.mkRef (fun _ _ => pure #[])

def registerTopProofRoleHook (f : Expr → Array Expr → MetaM (Std.HashMap FVarId String)) : IO Unit :=
  topProofRoleHookRef.set f

def registerTopProofNotationHook (f : Expr → Array Expr → MetaM (Array (Expr × String × Option String))) : IO Unit :=
  topProofNotationHookRef.set f

/-- Extract top-level `With notation` / `Let ... denote ... as ...` expression aliases from a
checked proof body instantiated against `fvars`, so theorem statements share the exact same
paper symbols as their proofs. -/
private partial def collectTopProofNotations (proofBody? : Option Expr) (fvars : Array Expr) :
    MetaM (Array (Expr × String × Option String)) := do
  let some rawVal := proofBody? | return #[]
  let mut cur := rawVal
  for fv in fvars do
    match cur.consumeMData with
    | .lam _ _ b _ => cur := b.instantiate1 fv
    | _ => break
  let spineNotations ← (← topProofNotationHookRef.get) cur fvars
  let rec scan (e : Expr) (fuel : Nat := 48) : Array (Expr × String × Option String) :=
    if fuel == 0 then #[]
    else match e with
    | .mdata kv inner =>
        match kvGetStr? kv `ccVerboseKind with
        | some "with_notation" =>
            let sym? := kvGetStr? kv `ccVerboseLabel
            let gloss? := kvGetStr? kv `ccVerboseReason
            match inner.consumeMData with
            | .app fn val =>
                match fn.consumeMData with
                | .lam _ _ body _ =>
                    let rest := scan (body.instantiate1 val) (fuel - 1)
                    match sym? with
                    | some sym => #[(val, sym, gloss?)] ++ rest
                    | none => rest
                | _ => scan inner (fuel - 1)
            | _ => scan inner (fuel - 1)
        | some "with_notation_let" =>
            let sym? := kvGetStr? kv `ccVerboseLabel
            let gloss? := kvGetStr? kv `ccVerboseReason
            match inner.consumeMData with
            | .letE _ _ val body _ =>
                let rest := scan (body.instantiate1 val) (fuel - 1)
                match sym? with
                | some sym => #[(val, sym, gloss?)] ++ rest
                | none => rest
            | _ => scan inner (fuel - 1)
        | some "write" | some "hybrid" | some "define_game" | some "let_adv" =>
            match inner.consumeMData with
            | .letE _ _ val body _ => scan (body.instantiate1 val) (fuel - 1)
            | _ => scan inner (fuel - 1)
        | some "proof_overview" | some "paragraph" | some "define_game_note" | some "with_role" =>
            scan inner (fuel - 1)
        | _ => scan inner (fuel - 1)
    | _ => #[]
  return spineNotations ++ scan cur

/-- Extract top-level `With role` binder overrides from a checked proof body instantiated
against `fvars`. -/
private partial def collectTopProofRoles (proofBody? : Option Expr) (fvars : Array Expr) :
    MetaM (Std.HashMap FVarId String) := do
  let some rawVal := proofBody? | return {}
  let mut cur := rawVal
  for fv in fvars do
    match cur.consumeMData with
    | .lam _ _ b _ => cur := b.instantiate1 fv
    | _ => break
  let mut out ← (← topProofRoleHookRef.get) cur fvars
  let rec collectFVarRoles (e : Expr) (m : Std.HashMap FVarId String) (fuel : Nat := 48) :
      MetaM (Std.HashMap FVarId String) := do
    if fuel == 0 then return m
    match e with
    | .mdata kv inner =>
        let mut m' := m
        if kvGetStr? kv `ccVerboseKind == some "with_role" then
          if let (some bNm, some rStr) := (kvGetStr? kv `ccVerboseLabel, kvGetStr? kv `ccVerboseReason) then
            for fv in fvars do
              let d ← fv.fvarId!.getDecl
              if (cleanBinderName d.userName) == bNm || d.userName.toString == bNm then
                let merged := mergeRoleStrings m'[fv.fvarId!]? rStr
                m' := m'.insert fv.fvarId! merged
        match inner.consumeMData with
        | .letE _ _ val body _ => collectFVarRoles (body.instantiate1 val) m' (fuel - 1)
        | .app (.lam _ _ body _) val => collectFVarRoles (body.instantiate1 val) m' (fuel - 1)
        | _ => collectFVarRoles inner m' (fuel - 1)
    | _ => return m
  out ← collectFVarRoles cur out
  return out

private def endsWithSentencePunct (inls : Array Inline) : Bool :=
  match inls.back? with
  | some (.text s) =>
      let t := s.trimAscii.toString
      t.endsWith "." || t.endsWith "!" || t.endsWith "?"
  | some (.displayMath _ p) => !p.trimAscii.toString.isEmpty
  | _ => false

/-- Parse a theorem's full `Expr` type into:
1. factored-out ambient setting (none when only routine typeclasses were suppressed);
2. aggregated entity introductions (`Let … be …`), omitting any already-fixed section parameters;
3. automatic local shorthand definitions for genuinely used repeated subexpressions + hoisted `let`s;
4. explicit mathematical assumptions (`Assume that …`), omitting any already-fixed section assumptions;
5. the concluding claim (displayed cleanly, promoted to display math when substantial). -/
def parseTheoremStatement (tbl : SymbolTable) (theoremType : Expr)
    (hoisted? : Option HoistedContext := none)
    (proofBody? : Option Expr := none)
    (theoremNotations : Array (Nat × Expr × String × Option String) := #[])
    (declName : Name := .anonymous) : MetaM ParsedStatement := do
  let hoisted := hoisted?.getD {}
  let env ← getEnv
  let reg := effectiveRegister env declName
  let profile :=
    match getEffectiveContextProfileName? env declName with
    | some _ => getEffectiveContextProfile env declName
    | none =>
        match reg with
        | .gameBased => resolveProfile env `GameBasedContext
        | .constructive | .randomSystems => getEffectiveContextProfile env declName
  forallTelescope theoremType fun fvars rawConclusion => do
    let fvarRoles ← inferTheoremSemanticRoles fvars rawConclusion
    let explicitRoles ← collectTopProofRoles proofBody? fvars
    -- Apply declaration-level and top-of-proof scoped paper notations (`With notation`)
    let mut rawNotations : Array (Expr × String × Option String) := #[]
    for (nBind, closedPat, sym, gloss?) in theoremNotations do
      if nBind ≤ fvars.size then
        rawNotations := rawNotations.push (closedPat.instantiateRev (fvars.extract 0 nBind), sym, gloss?)
    let proofNotations ← collectTopProofNotations proofBody? fvars
    rawNotations := rawNotations ++ proofNotations
    let mut tbl := tbl
    let mut notationInspectors : Array SymbolInspector := #[]
    for (patRaw, sym, gloss?) in rawNotations do
      if !patRaw.hasLooseBVars && !patRaw.hasExprMVar then
        let patNorm ← normalizeForPresentation patRaw
        let rhsTex ← exprToLatex patNorm { tbl with exprAliases := tbl.exprAliases.filter (·.2 != sym) }
        let (leanTy, roleDesc) ← try
          let pty ← inferType patNorm
          pure (← cleanTypeString pty, ← formatParameterRole tbl pty)
        catch _ =>
          pure ("", "Local paper notation.")
        let desc := gloss?.getD roleDesc
        let ins : SymbolInspector := {
          key := s!"notation:{declName}:{sym}"
          display := sym
          kind := .localShorthand s!"{sym} = {rhsTex}" desc
          leanName? := none
          leanType := leanTy
          roleBadge? := some "notation"
        }
        if let some existingIdx := notationInspectors.findIdx? (·.display == sym) then
          if gloss?.isSome then
            notationInspectors := notationInspectors.set! existingIdx ins
        else
          notationInspectors := notationInspectors.push ins
        tbl := tbl.withExprAlias patNorm sym
        tbl := tbl.withUsedName sym
    for ins in notationInspectors do
      tbl := tbl.withUsedName ins.display
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      if !(← isSuppressedLocalDecl decl) && !(← isProp decl.type) then
        let sym ← exprToLatex fv tbl
        tbl := tbl.withUsedName sym
        tbl := tbl.withUsedName (cleanBinderName decl.userName)
    -- Hoist leading `let R := ...; let S := ...; body` out of the conclusion in CPS
    withHoistedConclusionLets tbl rawConclusion #[] fun tbl letRawDefs conclusion => do
      let mut suppressed : Array String := #[]
      let mut finiteSets : List String := []
      -- First pass: collect `Fintype` / `Nonempty` modifiers attached to carrier variables
      for fv in fvars do
        let decl ← fv.fvarId!.getDecl
        if ← isAmbientTypeclass decl.type then
          let head := decl.type.getAppFn.consumeMData
          if let .const hName _ := head then
            suppressed := suppressed.push (shortConstName hName)
            if hName == `Fintype || hName == `Finite then
              if let some carrier := decl.type.getAppArgs.back? then
                if let .fvar cid := carrier.consumeMData then
                  let cdecl ← cid.getDecl
                  finiteSets := (cleanBinderName cdecl.userName) :: finiteSets
      -- Collect candidate non-ambient, non-hoisted parameter binders and visible hypotheses,
      -- then filter out any unused ambient binders (both AST-unused and unreferenced in rendered
      -- conclusion/hypotheses/retained binders) via backwards dependency closure.
      let mut rawNonPropFVars : Array (Expr × Expr × String × String) := #[]
      let mut allBinders : Array (FVarId × Expr) := #[]
      let mut keptPropTypes : Array Expr := #[]
      for fv in fvars do
        let decl ← fv.fvarId!.getDecl
        if ← isSuppressedLocalDecl decl then continue
        if ← isProp decl.type then
          let pHead? ← propHeadName? decl.type
          if pHead?.any (isPredicateSuppressedInSection env declName) then
            continue
          let hInl ← renderPropositionAux reg tbl decl.type
          if !hoisted.hypKeys.contains (inlinesCanonicalKey hInl) then
            keptPropTypes := keptPropTypes.push decl.type
        else
          allBinders := allBinders.push (fv.fvarId!, decl.type)
          let clean := cleanBinderName decl.userName
          let sym ← exprToLatex fv tbl
          rawNonPropFVars := rawNonPropFVars.push (fv, decl.type, clean, sym)
      let isProbDistDomain (dom : Expr) : Bool :=
        rawNonPropFVars.any fun (_, pty, _, _) =>
          let pClean := pty.consumeMData
          let isPD := match pClean.getAppFn.consumeMData with
            | .const nm _ => nm == `ProbDist || nm.toString.endsWith ".ProbDist"
            | _ => false
          isPD && pClean.getAppArgs.any (·.consumeMData == dom.consumeMData)
      let visibleStmtExprs : Array Expr := #[conclusion] ++ keptPropTypes
      let mut candBinders : Array (Expr × TypeDescription × String × String) := #[]
      for (fv, bty, clean, sym) in rawNonPropFVars do
        let decl ← fv.fvarId!.getDecl
        let mut desc ← describeTypeWithContext tbl profile fv bty
          (fvarRoles.get? fv.fvarId!) (explicitRoles.get? fv.fvarId!)
          allBinders visibleStmtExprs
        if reg == .gameBased && desc.noun.singular == "predicate" then
          if let .forallE _ dom _ _ := bty.consumeMData then
            if isProbDistDomain dom then
              desc := { desc with noun := ⟨"event", "events"⟩ }
        if desc.isAmbient then
          suppressed := suppressed.push clean
          continue
        if hoisted.paramSyms.contains sym then continue
        if isBinderSuppressedInSection env declName clean ||
           isBinderSuppressedInSection env declName sym ||
           isBinderSuppressedInSection env declName decl.userName.toString then
          suppressed := suppressed.push clean
          continue
        candBinders := candBinders.push (fv, desc, clean, sym)
      -- Stage 1 (AST backwards closure): keep binders referenced in conclusion, visible hyps,
      -- `letRawDefs`, or another retained binder's type (unless marked `isWitness`).
      let mut astNeeded : Std.HashSet FVarId := {}
      for id in (Lean.collectFVars {} conclusion).fvarIds do
        astNeeded := astNeeded.insert id
      for pt in keptPropTypes do
        for id in (Lean.collectFVars {} pt).fvarIds do
          astNeeded := astNeeded.insert id
      for (_, lty, lval) in letRawDefs do
        for id in (Lean.collectFVars {} lty).fvarIds do
          astNeeded := astNeeded.insert id
        for id in (Lean.collectFVars {} lval).fvarIds do
          astNeeded := astNeeded.insert id
      -- Also keep dependencies of hoisted parameters/hyps? No, hoisted params are already omitted,
      -- except a non-hoisted binder referenced by a retained binder's type stays via the reverse walk.
      let mut stage1Rev : Array (Expr × TypeDescription × String × String) := #[]
      for item in candBinders.reverse do
        let (fv, desc, _, _) := item
        let decl ← fv.fvarId!.getDecl
        if desc.isWitness || astNeeded.contains fv.fvarId! then
          stage1Rev := stage1Rev.push item
          for id in (Lean.collectFVars {} decl.type).fvarIds do
            astNeeded := astNeeded.insert id
        else
          suppressed := suppressed.push (cleanBinderName decl.userName)
      let stage1Binders := stage1Rev.reverse

      -- Collect ONLY retained non-hoisted parameter types, non-hoisted hypotheses, hoisted `let` values,
      -- and conclusion for repeated-subexpression factoring (never emit unused `c_k` from dropped binders!).
      let mut factorExprs : Array Expr := #[]
      for (fv, _, _, _) in stage1Binders do
        let decl ← fv.fvarId!.getDecl
        factorExprs := factorExprs.push decl.type
      for pt in keptPropTypes do
        factorExprs := factorExprs.push pt
      for (_, _, lval) in letRawDefs do
        factorExprs := factorExprs.push lval
      factorExprs := factorExprs.push conclusion
      let (tbl, _) ← factorRepeatedSubexprs tbl factorExprs

      let mut hyps : Array (Array Inline) := #[]
      for pt in keptPropTypes do
        hyps := hyps.push (← renderPropositionAux reg tbl pt)
      let mut letDefsRendered : Array (String × String × String × String) := #[]
      for (nmTex, tyExpr, valExpr) in letRawDefs do
        let valTex ← exprToLatex valExpr tbl
        let leanTy ← cleanTypeString tyExpr
        let roleDesc ← formatParameterRole tbl tyExpr
        letDefsRendered := letDefsRendered.push (nmTex, valTex, leanTy, roleDesc)
      let mut conclInl ← renderPropositionAux reg tbl conclusion

      -- Build candidate `Intro`s for `stage1Binders`
      let mut stage1Intros : Array (Expr × TypeDescription × String × Intro) := #[]
      for (fv, desc, clean, sym) in stage1Binders do
        let decl ← fv.fvarId!.getDecl
        let adjs :=
          if finiteSets.contains clean && !desc.adjectives.contains "finite" then
            "finite" :: desc.adjectives
          else desc.adjectives
        let depFVars := (Lean.collectFVars {} decl.type).fvarIds
        let depNames ← depFVars.toList.mapM fun id => do
          let d ← id.getDecl
          let s ← exprToLatex d.toExpr tbl
          return s!"\\({s}\\)"
        let intro : Intro := {
          name := s!"\\({sym}\\)"
          noun := desc.noun
          adjectives := adjs
          accessories := desc.accessories
          subjunctive := true
          typeStr := desc.typeLatex?.getD ""
          mentions := depNames
        }
        stage1Intros := stage1Intros.push (fv, desc, sym, intro)

      -- Stage 2 (Rendered-visibility backwards closure): drop binders like unused `C : Type u`
      -- or implicit-only `q : Port → ℕ` whose symbol never appears visibly in the rendered
      -- conclusion, hypotheses, let-defs, or any retained binder's accessories/type!
      let mut visibleMath : Array String :=
        hyps.flatMap collectInlineMathStrings ++ collectInlineMathStrings conclInl
      for (_, valTex, _, _) in letDefsRendered do
        visibleMath := visibleMath.push valTex
      -- Include expanded RHS of any expression alias referenced in visible statement pieces so
      -- variables appearing inside a notation or shorthand definition are recognized as visibly used.
      for (pat, aliasSym) in tbl.exprAliases do
        let usedInStmt :=
          visibleMath.any (fun seg => (seg.splitOn aliasSym).length > 1) ||
          stage1Intros.any fun (_, _, _, intr) =>
            (intr.typeStr.splitOn aliasSym).length > 1 ||
            intr.accessories.any (fun a => (a.splitOn aliasSym).length > 1)
        if usedInStmt then
          let rhs ← exprToLatex pat { tbl with exprAliases := tbl.exprAliases.filter (·.2 != aliasSym) }
          visibleMath := visibleMath.push rhs
      let mut stage2Rev : Array Intro := #[]
      for (fv, desc, sym, intro) in stage1Intros.reverse do
        let usedVisibly :=
          desc.isWitness || mathDispAppearsIn visibleMath sym
        if usedVisibly then
          stage2Rev := stage2Rev.push intro
          if !intro.typeStr.isEmpty then
            visibleMath := visibleMath.push intro.typeStr
          visibleMath := visibleMath ++ extractEmbeddedMath intro.noun.singular
          for acc in intro.accessories do
            visibleMath := visibleMath ++ extractEmbeddedMath acc
        else
          let decl ← fv.fvarId!.getDecl
          suppressed := suppressed.push (cleanBinderName decl.userName)
      let mut intros : List Intro := stage2Rev.reverse.toList
      -- Keep ONLY auto-factored shorthands transitively referenced by hypotheses, `let`s, or conclusion,
      -- ordered leaf-first (no forward references) and named cleanly without colliding with any binder.
      let allVisibleInls := hyps.foldl (· ++ ·) #[] ++ conclInl
      let introRendered := if intros.isEmpty then "" else realizeGroupedIntros intros
      let replaceInIntro (src dst : String) (x : Intro) : Intro := {
        x with
        accessories := x.accessories.map (·.replace src dst)
        typeStr := x.typeStr.replace src dst
      }
      let strContains (hay needle : String) : Bool :=
        !needle.isEmpty && (hay.splitOn needle).length > 1
      let mut allCDefs : Array (String × String × String × String) := #[]
      for (pat, sym) in tbl.exprAliases do
        if sym.startsWith "@@CADMO_W_" then
          let rhs ← exprToLatex pat { tbl with exprAliases := tbl.exprAliases.filter (·.2 != sym) }
          let patMeta ← try
            let pty ← inferType pat
            pure (← cleanTypeString pty, ← formatParameterRole tbl pty)
          catch _ =>
            pure ("", "Local abbreviation.")
          allCDefs := allCDefs.push (sym, rhs, patMeta.1, patMeta.2)
      let mut usedSyms : Std.HashSet String := {}
      for (sym, _, _, _) in allCDefs do
        let usedInMain := inlinesContain allVisibleInls sym
        let usedInIntro := strContains introRendered sym
        let usedInLet := letDefsRendered.any fun (_, rhs, _, rd) =>
          strContains rhs sym || strContains rd sym
        if usedInMain || usedInIntro || usedInLet then
          usedSyms := usedSyms.insert sym
      -- Fixed-point transitive closure (checking both RHS and roleDescription)
      for _ in [:allCDefs.size] do
        for (sym, rhs, _, rd) in allCDefs do
          if usedSyms.contains sym then
            for (otherSym, _, _, _) in allCDefs do
              if otherSym != sym && (strContains rhs otherSym || strContains rd otherSym) then
                usedSyms := usedSyms.insert otherSym
      let activeWriteDefs := allCDefs.filter (fun (sym, _, _, _) => usedSyms.contains sym)
      -- Order leaf-first: reverse `sorted` (which was largest-first) so subexpressions are defined before use
      let orderedWriteDefs := activeWriteDefs.reverse
      let allMathForCollision := visibleMath ++ (allCDefs.map (·.2.1))
      let finalSyms := pickFreshShorthandFamily tbl.usedNames allMathForCollision orderedWriteDefs.size
      let mut workWriteDefs := orderedWriteDefs
      for i in [:orderedWriteDefs.size] do
        let (oldSym, _, _, _) := orderedWriteDefs[i]!
        let newSym := finalSyms[i]!
        intros := intros.map (replaceInIntro oldSym newSym)
        hyps := hyps.map (replaceInInlines oldSym newSym)
        conclInl := replaceInInlines oldSym newSym conclInl
        letDefsRendered := letDefsRendered.map fun (n, r, lt, rd) =>
          (n, r.replace oldSym newSym, lt, rd.replace oldSym newSym)
        workWriteDefs := workWriteDefs.map fun (n, r, lt, rd) =>
          (n, r.replace oldSym newSym, lt, rd.replace oldSym newSym)
      let mut renumberedWriteDefs : Array (String × String × String × String) := #[]
      for i in [:workWriteDefs.size] do
        let (_, rhs, lt, rd) := workWriteDefs[i]!
        renumberedWriteDefs := renumberedWriteDefs.push (finalSyms[i]!, rhs, lt, rd)
      let allWriteDefs := renumberedWriteDefs ++ letDefsRendered
      let mut localShorthands : Array LocalShorthandInfo := #[]
      for (sym, rhs, lt, rd) in allWriteDefs do
        localShorthands := localShorthands.push {
          sym, rhsLatex := rhs, leanType := lt, roleDescription := rd
        }
      let mut paragraphs : Array (Array Inline) := #[]
      if !intros.isEmpty then
        paragraphs := paragraphs.push #[.text (realizeGroupedIntros intros)]
      if !allWriteDefs.isEmpty then
        let mut inl : Array Inline := #[.text "Write "]
        for i in [:allWriteDefs.size] do
          let (sym, rhs, _, _) := allWriteDefs[i]!
          if i > 0 then
            inl := inl.push (.text (if i + 1 == allWriteDefs.size then " and " else ", "))
          inl := inl.push (.inlineMath s!"{sym} = {rhs}")
        inl := inl.push (.text ".")
        paragraphs := paragraphs.push inl
      if !hyps.isEmpty then
        let mut assumeInl : Array Inline := #[.text "Assume that "]
        let hypsHavePunct := hyps.any inlinesHasProseCommaOrSemi
        for i in [:hyps.size] do
          if i > 0 then
            let sep :=
              if hyps.size == 2 then (if hypsHavePunct then ", and " else " and ")
              else if i + 1 == hyps.size then (if hypsHavePunct then "; and " else ", and ")
              else (if hypsHavePunct then "; " else ", ")
            assumeInl := assumeInl.push (.text sep)
          assumeInl := assumeInl ++ hyps[i]!
        if !endsWithSentencePunct assumeInl then
          assumeInl := assumeInl.push (.text ".")
        paragraphs := paragraphs.push assumeInl
      let rawConclCount := conclInl.size
      conclInl := ensureSymbolicPredClause conclInl
      let addedVerb := conclInl.size > rawConclCount
      let lead := if hyps.isEmpty && intros.isEmpty && allWriteDefs.isEmpty then "We have " else "Then "
      let capConcl (inls : Array Inline) : Array Inline :=
        match inls[0]? with
        | some (Inline.text t) => inls.set! 0 (.text (capitalizeFirst t))
        | _ => inls
      let isStandaloneProseClause : Bool :=
        match conclInl[0]? with
        | some (Inline.text t) =>
            let low := t.trimAsciiStart.toString.toLower
            low.startsWith "the distinguishing advantage between " ||
            (low.startsWith "the " &&
              (let txt := (inlinesCanonicalKey conclInl).toLower
               [" is ", " are ", " can ", " holds", " constructs ", " satisfies ", " agrees ", " match ", " separate ", " avoid ", " coincide"].any fun v =>
                 (txt.splitOn v).length > 1))
        | _ => false
      let conclPara : Array Inline :=
        match conclInl with
        | #[.inlineMath tex] =>
            if tex.length ≥ 36 then
              #[.text lead, .displayMath tex "."]
            else
              #[.text lead, .inlineMath tex, .text "."]
        | _ =>
            let body :=
              if lead == "We have " && isStandaloneProseClause then
                capConcl conclInl
              else if lead == "We have " && addedVerb then
                #[.text "We have that "] ++ conclInl
              else
                #[.text lead] ++ conclInl
            if endsWithSentencePunct body then body
            else body ++ #[.text "."]
      paragraphs := paragraphs.push conclPara
      let ambient? : Option AmbientSetting := none
      let _ := suppressed
      return { ambient?, paragraphs, conclusion := rawConclusion, localShorthands, notationInspectors }

end Informalization.Core.Ontology
