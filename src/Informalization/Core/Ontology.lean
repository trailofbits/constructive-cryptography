/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Overlay
import Informalization.Core.Explanation

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
open Informalization.Core.Explanation

/-- Semantic description of a mathematical type for entity introductions. -/
structure TypeDescription where
  noun : CountNoun
  adjectives : List String := []
  accessories : List String := []
  /-- Optional extra type annotation printed beside the symbol (e.g. `M \to X^*`). -/
  typeLatex? : Option String := none
  /-- If true, this binder is ambient category/algebra plumbing and belongs in `AmbientSetting`. -/
  isAmbient : Bool := false
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

/-- Describe a binder's type using registered domain handlers and checked `informal_noun`
overlays first, then core math fallbacks. -/
def describeType (tbl : SymbolTable) (ty : Expr) : MetaM TypeDescription := do
  let ty ← normalizeForPresentation ty
  for h in (← typeHandlersRef.get) do
    if let some desc ← h.matchType tbl ty then
      return desc
  if let .const head _ := ty.getAppFn.consumeMData then
    let env ← getEnv
    if let some (sg, pl) := (getOverlay env head).noun? then
      return { noun := ⟨sg, pl⟩ }
  if ty.isSort then
    return { noun := ⟨"set", "sets"⟩ }
  if ty.isAppOf ``Nat || ty == mkConst ``Nat then
    return { noun := ⟨"natural number", "natural numbers"⟩ }
  if ty.isAppOf ``Int || ty == mkConst ``Int then
    return { noun := ⟨"integer", "integers"⟩ }
  if ty.isAppOf ``Bool || ty == mkConst ``Bool then
    return { noun := ⟨"bit", "bits"⟩ }
  if ty == mkConst `Real then
    return { noun := ⟨"real number", "real numbers"⟩ }
  if ty == mkConst `NNReal then
    return { noun := ⟨"nonnegative real number", "nonnegative real numbers"⟩ }
  if ty == mkConst `ENNReal then
    return { noun := ⟨"extended nonnegative real", "extended nonnegative reals"⟩ }
  if let .forallE _ dom body _ := ty then
    if !body.hasLooseBVar 0 then
      if body == .sort .zero then
        let domTex ← exprToLatex dom tbl
        return { noun := ⟨"predicate", "predicates"⟩, accessories := [s!"on \\({domTex}\\)"] }
      else
        let tyTex ← exprToLatex ty tbl
        return { noun := ⟨"function", "functions"⟩, typeLatex? := some tyTex }
  let tyTex ← exprToLatex ty tbl
  return { noun := ⟨s!"element of \\({tyTex}\\)", s!"elements of \\({tyTex}\\)"⟩ }

/-- Render a proposition into natural mathematical English + LaTeX (`Array Inline`),
consulting registered CC/domain handlers first and falling back to clean `LeanTeX`. -/
partial def renderProposition (tbl : SymbolTable) (prop : Expr) : MetaM (Array Inline) := do
  let prop ← normalizeForPresentation prop
  for h in (← propHandlersRef.get) do
    if let some out ← h.renderProp tbl prop then
      return out
  -- Quantified `∀ x, P x`
  if let .forallE nm dom body bi := prop then
    if body.hasLooseBVar 0 then
      if ← isAmbientTypeclass dom then
        return ← withLocalDecl nm bi dom fun fv => renderProposition tbl (body.instantiate1 fv)
      return ← withLocalDecl nm bi dom fun fv => do
        let desc ← describeType tbl dom
        let varTex ← exprToLatex fv tbl
        let bodyInl ← renderProposition tbl (body.instantiate1 fv)
        if desc.noun.singular.startsWith "element of \\(" && desc.noun.singular.endsWith "\\)" then
          let setTex := ((desc.noun.singular.drop 13).dropEnd 2).toString
          return #[.text "for every ", .inlineMath s!"{varTex} \\in {setTex}", .text ", "] ++ bodyInl
        let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
        let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
        return #[.text s!"for every {adj}{desc.noun.singular} ", .inlineMath varTex,
                 .text s!"{acc}, "] ++ bodyInl
    else if ← isProp dom then
      let pInl ← renderProposition tbl dom
      let qInl ← renderProposition tbl body
      return #[.text "if "] ++ pInl ++ #[.text ", then "] ++ qInl
  -- Logical connectives & registered `informal_pred` overlays
  let fn := prop.getAppFn.consumeMData
  let args := prop.getAppArgs
  if let .const head _ := fn then
    let env ← getEnv
    if let some phrase := (getOverlay env head).predPhrase? then
      if let some subject := args.back? then
        let subjTex ← exprToLatex subject tbl
        return #[.inlineMath subjTex, .text (" " ++ phrase)]
      return #[.text phrase]
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
          return #[.inlineMath (String.intercalate " \\le " terms.toList)]
      let a ← renderProposition tbl args[args.size - 2]!
      let b ← renderProposition tbl args[args.size - 1]!
      return a ++ #[.text ", and "] ++ b
    if head == ``Iff && args.size ≥ 2 then
      let a ← renderProposition tbl args[args.size - 2]!
      let b ← renderProposition tbl args[args.size - 1]!
      return a ++ #[.text " if and only if "] ++ b
    if head == ``Exists && args.size ≥ 2 then
      if let .lam nm dom body bi := args[args.size - 1]! then
        return ← withLocalDecl nm bi dom fun fv => do
          let desc ← describeType tbl dom
          let varTex ← exprToLatex fv tbl
          let bodyInl ← renderProposition tbl (body.instantiate1 fv)
          let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
          let art := article (adj ++ desc.noun.singular)
          return #[.text s!"there exists {art} {adj}{desc.noun.singular} ", .inlineMath varTex,
                   .text " such that "] ++ bodyInl
  -- Default: clean 2D LaTeX formula
  let tex ← exprToLatex prop tbl
  return #[.inlineMath tex]

/-- Build a clean Kyle Miller `GoalState` from a live local context and target `Expr`.
Suppresses ambient typeclasses and implementation details, and never prints `None`. -/
def buildGoalState (tbl : SymbolTable) (target : Expr) : MetaM GoalState := do
  let lctx ← getLCtx
  let targetClean ← normalizeForPresentation target
  let targetFVars := (Lean.collectFVars {} targetClean).fvarIds
  let mut entries : Array ContextEntry := #[]
  for decl in lctx do
    if ← isSuppressedLocalDecl decl then continue
    let used := targetFVars.contains decl.fvarId
    if ← isProp decl.type then
      let propTex ← exprToLatex decl.type tbl
      entries := entries.push {
        name? := cleanBinderName? decl.userName
        description := s!"\\({propTex}\\)"
        isHypothesis := true
        usedInGoal := used
      }
    else
      let desc ← describeType tbl decl.type
      let sym ← exprToLatex decl.toExpr tbl
      let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
      let art := article (adj ++ desc.noun.singular)
      let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
      entries := entries.push {
        name? := some s!"\\({sym}\\)"
        description := s!"is {art} {adj}{desc.noun.singular}{acc}"
        isHypothesis := false
        usedInGoal := used
      }
  let targetLatex ← exprToLatex targetClean tbl
  let rawTarget ← ppExpr target
  return {
    context := entries
    targetLatex
    rawLeanGoal? := some rawTarget.pretty
  }

/-- Structured decomposition of a theorem's top-level signature for Maurer-style presentation. -/
structure ParsedStatement where
  ambient? : Option AmbientSetting
  paragraphs : Array (Array Inline)
  conclusion : Expr
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
                curTy ← whnfD curTy
                match curTy with
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

/-- Factor up to 3 heavy repeated visible subexpressions across `exprs` into crisp local
abbreviations (`c₁, c₂, …`), keeping ONLY shorthands that visibly shorten the statement. -/
private def factorRepeatedSubexprs (tbl : SymbolTable) (exprs : Array Expr) :
    MetaM (SymbolTable × Option (Array Inline)) := do
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
  let mut defs : Array (String × String) := #[]
  let mut chosenExprs : Array Expr := #[]
  for (ex, _, _) in sorted do
    if defs.size ≥ 3 then break
    if chosenExprs.any (fun prev => prev == ex) then continue
    let tex ← exprToLatex ex curTbl
    if tex.length < 22 || (tex.splitOn "inst").length > 1 then continue
    let sym := "c_{" ++ toString (defs.size + 1) ++ "}"
    defs := defs.push (sym, tex)
    chosenExprs := chosenExprs.push ex
    curTbl := curTbl.withExprAlias ex sym
  if defs.isEmpty then
    return (curTbl, none)
  let mut inl : Array Inline := #[.text "Write "]
  for i in [:defs.size] do
    let (sym, rhs) := defs[i]!
    if i > 0 then
      inl := inl.push (.text (if i + 1 == defs.size then " and " else ", "))
    inl := inl.push (.inlineMath s!"{sym} = {rhs}")
  inl := inl.push (.text ".")
  return (curTbl, some inl)

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
and display equations never print `let ... in let ... in`. -/
private partial def withHoistedConclusionLets {α : Type} (tbl : SymbolTable) (e : Expr)
    (acc : Array (String × Expr) := #[])
    (k : SymbolTable → Array (String × Expr) → Expr → MetaM α) : MetaM α := do
  match e.consumeMData with
  | .letE nm ty val body _ =>
      let isP ← try isProp ty catch _ => pure false
      if isP then k tbl acc e
      else
        withLetDecl nm ty val fun fv => do
          let nmTex ← exprToLatex fv tbl
          let tbl' := tbl.withExprAlias fv nmTex
          withHoistedConclusionLets tbl' (body.instantiate1 fv) (acc.push (nmTex, val)) k
  | _ => k tbl acc e

/-- Parse a theorem's full `Expr` type into:
1. factored-out ambient setting (suppressed typeclasses & category boilerplate);
2. aggregated entity introductions (`Let … be …`);
3. automatic local shorthand definitions for genuinely used repeated subexpressions + hoisted `let`s;
4. explicit mathematical assumptions (`Assume that …`);
5. the concluding claim (displayed cleanly, promoted to display math when substantial). -/
def parseTheoremStatement (tbl : SymbolTable) (theoremType : Expr) : MetaM ParsedStatement := do
  forallTelescope theoremType fun fvars rawConclusion => do
    -- Hoist leading `let R := ...; let S := ...; body` out of the conclusion in CPS
    withHoistedConclusionLets tbl rawConclusion #[] fun tbl letRawDefs conclusion => do
      -- Collect prop assumptions, hoisted `let` values, & conclusion for subexpr factoring
      let mut factorExprs : Array Expr := #[]
      for fv in fvars do
        let decl ← fv.fvarId!.getDecl
        if ← isSuppressedLocalDecl decl then continue
        if ← isProp decl.type then
          factorExprs := factorExprs.push decl.type
      for (_, lval) in letRawDefs do
        factorExprs := factorExprs.push lval
      factorExprs := factorExprs.push conclusion
      let (tbl, _writePara?) ← factorRepeatedSubexprs tbl factorExprs

      let mut intros : List Intro := []
      let mut hyps : Array (Array Inline) := #[]
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
      -- Second pass: classify visible binders into entity introductions vs. assumptions
      for fv in fvars do
        let decl ← fv.fvarId!.getDecl
        if ← isSuppressedLocalDecl decl then continue
        if ← isProp decl.type then
          let hInl ← renderProposition tbl decl.type
          hyps := hyps.push hInl
        else
          let desc ← describeType tbl decl.type
          if desc.isAmbient then
            suppressed := suppressed.push (cleanBinderName decl.userName)
            continue
          let clean := cleanBinderName decl.userName
          let sym ← exprToLatex fv tbl
          let adjs :=
            if finiteSets.contains clean && !desc.adjectives.contains "finite" then
              "finite" :: desc.adjectives
            else desc.adjectives
          let depFVars := (Lean.collectFVars {} decl.type).fvarIds
          let depNames ← depFVars.toList.mapM fun id => do
            let d ← id.getDecl
            let s ← exprToLatex d.toExpr tbl
            return s!"\\({s}\\)"
          intros := intros ++ [{
            name := s!"\\({sym}\\)"
            noun := desc.noun
            adjectives := adjs
            accessories := desc.accessories
            subjunctive := true
            typeStr := desc.typeLatex?.getD ""
            mentions := depNames
          }]
      let mut letDefsRendered : Array (String × String) := #[]
      for (nmTex, valExpr) in letRawDefs do
        let valTex ← exprToLatex valExpr tbl
        letDefsRendered := letDefsRendered.push (nmTex, valTex)
      let mut conclInl ← renderProposition tbl conclusion
      -- Keep ONLY `c_k` shorthands transitively referenced by hypotheses, `let`s, or conclusion,
      -- ordered leaf-first (no forward references) and renumbered densely `c_1, c_2, …`.
      let allVisibleInls := hyps.foldl (· ++ ·) #[] ++ conclInl
      let mut allCDefs : Array (String × String) := #[]
      for (pat, sym) in tbl.exprAliases do
        if sym.startsWith "c_{" then
          let rhs ← exprToLatex pat { tbl with exprAliases := tbl.exprAliases.filter (·.2 != sym) }
          allCDefs := allCDefs.push (sym, rhs)
      let mut usedSyms : Std.HashSet String := {}
      for (sym, _) in allCDefs do
        let usedInMain := inlinesContain allVisibleInls sym
        let usedInLet := letDefsRendered.any fun (_, rhs) => (rhs.splitOn sym).length > 1
        if usedInMain || usedInLet then
          usedSyms := usedSyms.insert sym
      -- Fixed-point transitive closure (at most 3 shorthands)
      for _ in [:allCDefs.size] do
        for (sym, rhs) in allCDefs do
          if usedSyms.contains sym then
            for (otherSym, _) in allCDefs do
              if otherSym != sym && (rhs.splitOn otherSym).length > 1 then
                usedSyms := usedSyms.insert otherSym
      let activeWriteDefs := allCDefs.filter (fun (sym, _) => usedSyms.contains sym)
      -- Order leaf-first: reverse `sorted` (which was largest-first) so subexpressions are defined before use
      let orderedWriteDefs := activeWriteDefs.reverse
      -- Two-phase collision-free renumbering (`oldSym` -> `__TMP_i__` -> `c_{i+1}`)
      let mut tmpWriteDefs := orderedWriteDefs
      for i in [:orderedWriteDefs.size] do
        let (oldSym, _) := orderedWriteDefs[i]!
        let tmpTok := "__CADMO_C_" ++ toString i ++ "__"
        hyps := hyps.map (replaceInInlines oldSym tmpTok)
        conclInl := replaceInInlines oldSym tmpTok conclInl
        letDefsRendered := letDefsRendered.map fun (n, r) => (n, r.replace oldSym tmpTok)
        tmpWriteDefs := tmpWriteDefs.map fun (n, r) => (n, r.replace oldSym tmpTok)
      let mut renumberedWriteDefs : Array (String × String) := #[]
      for i in [:tmpWriteDefs.size] do
        let tmpTok := "__CADMO_C_" ++ toString i ++ "__"
        let newSym := "c_{" ++ toString (i + 1) ++ "}"
        hyps := hyps.map (replaceInInlines tmpTok newSym)
        conclInl := replaceInInlines tmpTok newSym conclInl
        letDefsRendered := letDefsRendered.map fun (n, r) => (n, r.replace tmpTok newSym)
        tmpWriteDefs := tmpWriteDefs.map fun (n, r) => (n, r.replace tmpTok newSym)
      for i in [:tmpWriteDefs.size] do
        let (_, rhs) := tmpWriteDefs[i]!
        renumberedWriteDefs := renumberedWriteDefs.push ("c_{" ++ toString (i + 1) ++ "}", rhs)
      let allWriteDefs := renumberedWriteDefs ++ letDefsRendered
      let mut paragraphs : Array (Array Inline) := #[]
      if !intros.isEmpty then
        paragraphs := paragraphs.push #[.text (realizeIntros intros)]
      if !allWriteDefs.isEmpty then
        let mut inl : Array Inline := #[.text "Write "]
        for i in [:allWriteDefs.size] do
          let (sym, rhs) := allWriteDefs[i]!
          if i > 0 then
            inl := inl.push (.text (if i + 1 == allWriteDefs.size then " and " else ", "))
          inl := inl.push (.inlineMath s!"{sym} = {rhs}")
        inl := inl.push (.text ".")
        paragraphs := paragraphs.push inl
      if !hyps.isEmpty then
        let mut assumeInl : Array Inline := #[.text "Assume that "]
        for i in [:hyps.size] do
          if i > 0 then
            assumeInl := assumeInl.push (.text (if i + 1 == hyps.size then ", and " else "; "))
          assumeInl := assumeInl ++ hyps[i]!
        assumeInl := assumeInl.push (.text ".")
        paragraphs := paragraphs.push assumeInl
      let lead := if hyps.isEmpty && intros.isEmpty then "We have " else "Then "
      let conclPara : Array Inline :=
        match conclInl with
        | #[.inlineMath tex] =>
            if tex.length ≥ 36 then
              #[.text (lead.trimAscii.toString), .displayMath tex "."]
            else
              #[.text lead, .inlineMath tex, .text "."]
        | _ =>
            #[.text lead] ++ conclInl ++ #[.text "."]
      paragraphs := paragraphs.push conclPara
      let ambient? :=
        if suppressed.isEmpty then none
        else
          let uniq := suppressed.toList.eraseDups.toArray
          some {
            summary := #[.text "We work in the Constructive Cryptography framework over finite alphabets and compatible distinguishing metrics."]
            suppressedTypeclasses := uniq
          }
      return { ambient?, paragraphs, conclusion := rawConclusion }

end Informalization.Core.Ontology
