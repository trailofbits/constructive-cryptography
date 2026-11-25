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
    return { noun := ⟨"nonnegative real", "nonnegative reals"⟩ }
  if let .forallE _ dom body _ := ty then
    if !body.hasLooseBVar 0 then
      if dom.isConstOf ``Unit || dom.isConstOf ``PUnit then
        return ← describeType tbl body
      if body == .sort .zero then
        let domTex ← exprToLatex dom tbl
        return { noun := ⟨"predicate", "predicates"⟩, accessories := [s!"on \\({domTex}\\)"] }
      else
        let tyTex ← exprToLatex ty tbl
        return { noun := ⟨"function", "functions"⟩, typeLatex? := some tyTex }
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

/-- Render a proposition into natural mathematical English + LaTeX (`Array Inline`),
consulting registered CC/domain handlers first and falling back to clean `LeanTeX`. -/
partial def renderProposition (tbl : SymbolTable) (prop : Expr) : MetaM (Array Inline) := do
  let prop ← normalizeForPresentation prop
  if let some (_, symAlias) := tbl.exprAliases.reverse.find? (fun (pat, _) => pat.consumeMData == prop.consumeMData) then
    return #[.inlineMath symAlias]
  for h in (← propHandlersRef.get) do
    if let some out ← h.renderProp tbl prop then
      return out
  -- Quantified `∀ x, P x` (with `Prop` domain rendered as implication even when dependent)
  if let .forallE nm dom body bi := prop then
    if ← isAmbientTypeclass dom then
      return ← withLocalDecl nm bi dom fun fv => renderProposition tbl (body.instantiate1 fv)
    else if ← isProp dom then
      let pInl ← renderProposition tbl dom
      let qInl ←
        if body.hasLooseBVar 0 then
          withLocalDecl nm bi dom fun fv => renderProposition tbl (body.instantiate1 fv)
        else
          renderProposition tbl body
      return #[.text "if "] ++ pInl ++ #[.text ", then "] ++ qInl
    else if body.hasLooseBVar 0 then
      let freshNm ← freshShadowFreeName nm "x"
      return ← withLocalDecl freshNm bi dom fun fv => do
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
  -- Logical connectives & registered `informal_pred` overlays
  let fn := prop.getAppFn.consumeMData
  let args := prop.getAppArgs
  if let .const head _ := fn then
    let env ← getEnv
    if let some phrase := effectivePredPhrase? env head then
      let glossInl ← do
        let arity? := (Presentation.getMathPresentation env head).explicitNonPropArity?
        if arity? == some 0 then
          pure #[.text phrase]
        else if let some subject := args.back? then
          let subjTex ← exprToLatex subject tbl
          pure #[.inlineMath subjTex, .text (" " ++ phrase)]
        else
          pure #[.text phrase]
      if Presentation.isPredPreserveFormula env head then
        if let some unfolded ← withTransparency .default (Meta.unfoldDefinition? prop) then
          let uClean ← normalizeForPresentation unfolded
          if uClean != prop && exprDagSmall uClean 180 then
            let headRecurses := uClean.foldConsts false fun n acc => acc || n == head
            let formulaInl ←
              if headRecurses then
                pure #[.inlineMath (← exprToLatex uClean tbl)]
              else
                renderProposition tbl uClean
            if inlinesCanonicalKey formulaInl != inlinesCanonicalKey glossInl then
              return glossInl ++ #[.text " (i.e., "] ++ formulaInl ++ #[.text ")"]
      return glossInl
    if head == ``Function.Injective && args.size == 3 then
      let fTex ← exprToLatex args[2]! tbl
      return #[.inlineMath fTex, .text " is injective"]
    if head == ``Not && args.size == 1 then
      let inner := args[0]!.consumeMData
      if inner.getAppFn.consumeMData.isConstOf ``Function.Injective && inner.getAppArgs.size == 3 then
        let fTex ← exprToLatex inner.getAppArgs[2]! tbl
        return #[.inlineMath fTex, .text " is not injective"]
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
      match a, b with
      | #[.inlineMath aTex], #[.inlineMath bTex] =>
          return #[.inlineMath s!"{aTex} \\wedge {bTex}"]
      | _, _ =>
          let aTxt := inlinesCanonicalKey a
          let bTxt := inlinesCanonicalKey b
          let sep := if aTxt.contains ',' || bTxt.contains ',' then "; and " else " and "
          return a ++ #[.text sep] ++ b
    if head == ``Iff && args.size ≥ 2 then
      let a ← renderProposition tbl args[args.size - 2]!
      let b ← renderProposition tbl args[args.size - 1]!
      return a ++ #[.text " if and only if "] ++ b
    if head == ``Exists && args.size ≥ 2 then
      if let .lam nm dom body bi := args[args.size - 1]! then
        let freshNm ← chooseUnshadowedBinderName nm #[dom, body] "x"
        return ← withLocalDecl freshNm bi dom fun fv => do
          let desc ← describeType tbl dom
          let varTex ← exprToLatex fv tbl
          let bodyInl ← renderProposition tbl (body.instantiate1 fv)
          if desc.noun.singular.startsWith "element of \\(" && desc.noun.singular.endsWith "\\)" then
            let setTex := ((desc.noun.singular.drop 13).dropEnd 2).toString
            return #[.text "there exists ", .inlineMath s!"{varTex} \\in {setTex}",
                     .text " such that "] ++ bodyInl
          let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
          let art := article (adj ++ desc.noun.singular)
          return #[.text s!"there exists {art} {adj}{desc.noun.singular} ", .inlineMath varTex,
                   .text " such that "] ++ bodyInl
  -- Default: clean 2D LaTeX formula
  let tex ← exprToLatex prop tbl
  return #[.inlineMath tex]

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
          let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
          let art := article (adj ++ desc.noun.singular)
          let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
          let entry : ContextEntry := {
            name? := some s!"\\({sym}\\)"
            description := s!"is {art} {adj}{desc.noun.singular}{acc}"
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
abbreviations (`c₁, c₂, …`), keeping ONLY shorthands that visibly shorten the statement. -/
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
    let sym := "c_{" ++ toString (defs.size + 1) ++ "}"
    defs := defs.push (sym, ex)
    chosenExprs := chosenExprs.push ex
    curTbl := curTbl.withExprAlias ex sym
  return (curTbl, defs)

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
    (acc : Array (String × Expr × Expr) := #[])
    (k : SymbolTable → Array (String × Expr × Expr) → Expr → MetaM α) : MetaM α := do
  match e.consumeMData with
  | .letE nm ty val body _ =>
      let isP ← try isProp ty catch _ => pure false
      if isP then k tbl acc e
      else
        withLetDecl nm ty val fun fv => do
          let nmTex ← exprToLatex fv tbl
          let tbl' := tbl.withExprAlias fv nmTex
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

/-- Extract visible parameters and hypotheses from `theoremType` for section-context hoisting. -/
def extractSignatureSummary (tbl : SymbolTable) (theoremType : Expr) : MetaM SignatureSummary := do
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

/-- Format hoisted section-fixed parameters and assumptions into a calm archival Section Context
paragraph (*"Throughout this section, let … [and assume that …]."*). -/
def formatSectionContextParagraphs (intros : List Intro) (hyps : Array (Array Inline)) :
    Array (Array Inline) := Id.run do
  if intros.isEmpty && hyps.isEmpty then return #[]
  let mut para : Array Inline := #[]
  let mut hasMultiIntro := false
  if !intros.isEmpty then
    let introSentence := realizeIntros intros
    let rawBody :=
      if introSentence.startsWith "Let " then
        "Throughout this section, let " ++ (introSentence.drop 4).toString
      else
        "Throughout this section, " ++ lowercaseFirst introSentence
    if !hyps.isEmpty then
      let trimmed := if rawBody.endsWith "." then (rawBody.dropEnd 1).toString else rawBody
      hasMultiIntro := trimmed.contains ',' || trimmed.contains ';'
      para := para.push (.text (if hasMultiIntro then trimmed ++ "." else trimmed))
    else
      para := para.push (.text rawBody)
  if !hyps.isEmpty then
    let lead :=
      if para.isEmpty then "Throughout this section, assume that "
      else if hasMultiIntro then " Assume throughout that "
      else " and assume that "
    para := para.push (.text lead)
    for i in [:hyps.size] do
      if i > 0 then
        let sep :=
          if hyps.size == 2 then " and "
          else if i + 1 == hyps.size then "; and "
          else "; "
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
  let profile := getEffectiveContextProfile env declName
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
          let hInl ← renderProposition tbl decl.type
          if !hoisted.hypKeys.contains (inlinesCanonicalKey hInl) then
            keptPropTypes := keptPropTypes.push decl.type
        else
          allBinders := allBinders.push (fv.fvarId!, decl.type)
          let clean := cleanBinderName decl.userName
          let sym ← exprToLatex fv tbl
          rawNonPropFVars := rawNonPropFVars.push (fv, decl.type, clean, sym)
      let visibleStmtExprs : Array Expr := #[conclusion] ++ keptPropTypes
      let mut candBinders : Array (Expr × TypeDescription × String × String) := #[]
      for (fv, bty, clean, sym) in rawNonPropFVars do
        let desc ← describeTypeWithContext tbl profile fv bty
          (fvarRoles.get? fv.fvarId!) (explicitRoles.get? fv.fvarId!)
          allBinders visibleStmtExprs
        if desc.isAmbient then
          suppressed := suppressed.push clean
          continue
        if hoisted.paramSyms.contains sym then continue
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
        hyps := hyps.push (← renderProposition tbl pt)
      let mut letDefsRendered : Array (String × String × String × String) := #[]
      for (nmTex, tyExpr, valExpr) in letRawDefs do
        let valTex ← exprToLatex valExpr tbl
        let leanTy ← cleanTypeString tyExpr
        let roleDesc ← formatParameterRole tbl tyExpr
        letDefsRendered := letDefsRendered.push (nmTex, valTex, leanTy, roleDesc)
      let mut conclInl ← renderProposition tbl conclusion

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
      -- Keep ONLY `c_k` shorthands transitively referenced by hypotheses, `let`s, or conclusion,
      -- ordered leaf-first (no forward references) and renumbered densely `c_1, c_2, …`.
      let allVisibleInls := hyps.foldl (· ++ ·) #[] ++ conclInl
      let introRendered := if intros.isEmpty then "" else realizeIntros intros
      let replaceInIntro (src dst : String) (x : Intro) : Intro := {
        x with
        accessories := x.accessories.map (·.replace src dst)
        typeStr := x.typeStr.replace src dst
      }
      let strContains (hay needle : String) : Bool :=
        !needle.isEmpty && (hay.splitOn needle).length > 1
      let mut allCDefs : Array (String × String × String × String) := #[]
      for (pat, sym) in tbl.exprAliases do
        if sym.startsWith "c_{" then
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
      -- Two-phase collision-free renumbering (`oldSym` -> `__TMP_i__` -> `c_{i+1}`)
      let mut tmpWriteDefs := orderedWriteDefs
      for i in [:orderedWriteDefs.size] do
        let (oldSym, _, _, _) := orderedWriteDefs[i]!
        let tmpTok := "__CADMO_C_" ++ toString i ++ "__"
        intros := intros.map (replaceInIntro oldSym tmpTok)
        hyps := hyps.map (replaceInInlines oldSym tmpTok)
        conclInl := replaceInInlines oldSym tmpTok conclInl
        letDefsRendered := letDefsRendered.map fun (n, r, lt, rd) =>
          (n, r.replace oldSym tmpTok, lt, rd.replace oldSym tmpTok)
        tmpWriteDefs := tmpWriteDefs.map fun (n, r, lt, rd) =>
          (n, r.replace oldSym tmpTok, lt, rd.replace oldSym tmpTok)
      let mut renumberedWriteDefs : Array (String × String × String × String) := #[]
      for i in [:tmpWriteDefs.size] do
        let tmpTok := "__CADMO_C_" ++ toString i ++ "__"
        let newSym := "c_{" ++ toString (i + 1) ++ "}"
        intros := intros.map (replaceInIntro tmpTok newSym)
        hyps := hyps.map (replaceInInlines tmpTok newSym)
        conclInl := replaceInInlines tmpTok newSym conclInl
        letDefsRendered := letDefsRendered.map fun (n, r, lt, rd) =>
          (n, r.replace tmpTok newSym, lt, rd.replace tmpTok newSym)
        tmpWriteDefs := tmpWriteDefs.map fun (n, r, lt, rd) =>
          (n, r.replace tmpTok newSym, lt, rd.replace tmpTok newSym)
      for i in [:tmpWriteDefs.size] do
        let (_, rhs, lt, rd) := tmpWriteDefs[i]!
        renumberedWriteDefs := renumberedWriteDefs.push ("c_{" ++ toString (i + 1) ++ "}", rhs, lt, rd)
      let allWriteDefs := renumberedWriteDefs ++ letDefsRendered
      let mut localShorthands : Array LocalShorthandInfo := #[]
      for (sym, rhs, lt, rd) in allWriteDefs do
        localShorthands := localShorthands.push {
          sym, rhsLatex := rhs, leanType := lt, roleDescription := rd
        }
      let mut paragraphs : Array (Array Inline) := #[]
      if !intros.isEmpty then
        paragraphs := paragraphs.push #[.text (realizeIntros intros)]
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
        for i in [:hyps.size] do
          if i > 0 then
            assumeInl := assumeInl.push (.text (if i + 1 == hyps.size then ", and " else "; "))
          assumeInl := assumeInl ++ hyps[i]!
        assumeInl := assumeInl.push (.text ".")
        paragraphs := paragraphs.push assumeInl
      let lead := if hyps.isEmpty && intros.isEmpty && allWriteDefs.isEmpty then "We have " else "Then "
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
      let ambient? : Option AmbientSetting := none
      let _ := suppressed
      return { ambient?, paragraphs, conclusion := rawConclusion, localShorthands, notationInspectors }

end Informalization.Core.Ontology
