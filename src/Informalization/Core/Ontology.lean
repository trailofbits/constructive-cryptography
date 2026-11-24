/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
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

/-- Describe a binder's type using registered domain handlers first, then core math fallbacks. -/
def describeType (tbl : SymbolTable) (ty : Expr) : MetaM TypeDescription := do
  let ty ← normalizeForPresentation ty
  for h in (← typeHandlersRef.get) do
    if let some desc ← h.matchType tbl ty then
      return desc
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
  -- Logical connectives
  let fn := prop.getAppFn.consumeMData
  let args := prop.getAppArgs
  if let .const head _ := fn then
    if head == ``And && args.size ≥ 2 then
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

/-- Parse a theorem's full `Expr` type into:
1. factored-out ambient setting (suppressed typeclasses & category boilerplate);
2. aggregated entity introductions (`Let … be …`);
3. explicit mathematical assumptions (`Assume that …`);
4. the concluding claim (displayed prominently). -/
def parseTheoremStatement (tbl : SymbolTable) (theoremType : Expr) : MetaM ParsedStatement := do
  forallTelescope theoremType fun fvars conclusion => do
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
    let mut paragraphs : Array (Array Inline) := #[]
    if !intros.isEmpty then
      paragraphs := paragraphs.push #[.text (realizeIntros intros)]
    if !hyps.isEmpty then
      let mut assumeInl : Array Inline := #[.text "Assume that "]
      for i in [:hyps.size] do
        if i > 0 then
          assumeInl := assumeInl.push (.text (if i + 1 == hyps.size then ", and " else "; "))
        assumeInl := assumeInl ++ hyps[i]!
      assumeInl := assumeInl.push (.text ".")
      paragraphs := paragraphs.push assumeInl
    let conclInl ← renderProposition tbl conclusion
    let conclPara :=
      if hyps.isEmpty && intros.isEmpty then
        #[.text "We have "] ++ conclInl ++ #[.text "."]
      else
        #[.text "Then "] ++ conclInl ++ #[.text "."]
    paragraphs := paragraphs.push conclPara
    let ambient? :=
      if suppressed.isEmpty then none
      else
        let uniq := suppressed.toList.eraseDups.toArray
        some {
          summary := #[.text "We work in the Constructive Cryptography framework over finite alphabets and compatible distinguishing metrics."]
          suppressedTypeclasses := uniq
        }
    return { ambient?, paragraphs, conclusion }

end Informalization.Core.Ontology
