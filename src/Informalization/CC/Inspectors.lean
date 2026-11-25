/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Rendering.CCWidget
import Rendering.Export
import Rendering.Widget
import Rendering.Instances
import Rendering.Proofs
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Ontology
import Informalization.Core.ProofGraph
import Informalization.Core.Routine
import Informalization.Core.Explanation
import Informalization.CC.Registry
import Informalization.CC.Ontology

/-!
# Type-Aware CC Symbol Inspectors & Live `Rendering` Diagram Hooks

Connects `Rendering`'s deterministic box-and-wire diagrams, interface port tables,
and parser-recorded DSL pseudocode cards into `Informalization.Core.ProofGraph`:

1. **`ccDiagramHook`** (`ProofGraph.registerDiagramHook`): projects CC expressions,
   judgments, and proof witnesses via `CCWidget.viewExprCore` / `CCWidget.renderJudgment` /
   `CCWidget.panel` / `CCWidget.staticHtml` into static HTML embedded directly inside
   `Entry.diagramHtml?` and `ProofNode.diagramHtml?`.
2. **`collectCCInspectors`** (`ProofGraph.registerInspectorCollector`): inspects every
   named symbol (free variables and project constants) appearing in a theorem statement
   and dispatches by type to the best human-first `SymbolInspector`:
   * **`Interface`** → `InspectorKind.interfaceTable` (Port / Query / Reply / Domain via
     `CCWidget.interfacePorts` and `CCWidget.interfaceProjections`);
   * **DSL `converter` / `system`** → `InspectorKind.dslPseudocode` (exact parser-recorded
     slices from `SystemAlgebra.DSL.sourceDocuments`);
   * **CC assembly** → `InspectorKind.ccDiagram` (static `Rendering` box-and-wire HTML);
   * **`HCoefficient` / `Implication` witness** → `InspectorKind.witnessCard`;
   * **Project mathematical definition** → ambient-suppressed `InspectorKind.mathDefinition`;
   * **Named parameter** → `InspectorKind.parameter`.
-/

namespace Informalization.CC.Inspectors

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.ProofGraph
open Informalization.Core.Routine
open Informalization.Core.Explanation
open Informalization.CC.Registry

/-! ## 1. Static Box-and-Wire Diagram Hook (`Rendering` Integration) -/

/-- Render a checked Lean expression or CC judgment to self-contained static HTML using
`Rendering`'s deterministic projection (`CCWidget.viewExprCore`, `CCWidget.renderJudgment`,
`CCWidget.panel`, `CCWidget.staticHtml`). Returns `none` for non-CC expressions. -/
def renderCCDiagramHtml? (e : Expr) : MetaM (Option String) := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasSorry || e.hasLevelMVar then
    return none
  try
    if let some (j, _) ← CCWidget.viewExprCore e false then
      let html := CCWidget.panel (CCWidget.renderJudgment j #[])
      match CCWidget.staticHtml html with
      | .ok rendered => return some rendered
      | .error _ => return none
  catch _ =>
    pure ()
  try
    if let some viewHtml ← CCWidget.proofViewHtml? e false then
      match CCWidget.staticHtml (CCWidget.proofPanel viewHtml) with
      | .ok rendered => return some rendered
      | .error _ => return none
  catch _ =>
    pure ()
  return none

/-! ## 2. Type-Aware Symbol Inspector Builders -/

/-- Source location `(moduleName?, line?)` for a resolved constant, when recorded by Lean. -/
private def declLocation (env : Environment) (declName : Name) : MetaM (Option String × Option Nat) := do
  let mod? := (env.getModuleIdxFor? declName).map fun idx =>
    (env.header.moduleNames[idx.toNat]?.map (·.toString)).getD ""
  let mod? := mod?.bind fun s => if s.isEmpty then none else some s
  let line? ← try
    let ranges? ← Lean.findDeclarationRanges? declName
    pure (ranges?.map fun r => r.range.pos.line)
  catch _ =>
    pure none
  return (mod?, line?)

/-- Clean pretty-printed type string with macro scopes stripped. -/
private def cleanLeanTypeStr (ty : Expr) : MetaM String := do
  let ty ← normalizeForPresentation ty
  return (← ppExpr ty).pretty (width := 100)

/-- Build an `InspectorKind.interfaceTable` from `CCWidget.interfacePorts` and
`CCWidget.interfaceProjections` when `e` is an interface expression with registered schema. -/
private def buildInterfaceTable? (tbl : SymbolTable) (e : Expr) :
    MetaM (Option InspectorKind) := do
  let projections ← try CCWidget.interfaceProjections e catch _ => pure #[]
  if projections.isEmpty then
    return none
  let rawPorts ← try CCWidget.interfacePorts e catch _ => pure #[]
  let mut rows : Array PortRow := #[]
  for (portLabel, _, inputExpr, outputExpr) in rawPorts do
    let qTex ← try exprToLatex inputExpr tbl catch _ => pure (← CCWidget.typeNotation inputExpr).text
    let rTex ← try exprToLatex outputExpr tbl catch _ => pure (← CCWidget.typeNotation outputExpr).text
    rows := rows.push {
      port := portLabel
      queryLatex := qTex
      replyLatex := rTex
    }
  let mut domainLatex := ""
  for (sym, _, valExpr) in projections do
    if sym == "D" then
      domainLatex ← try CCWidget.domainNotation valExpr catch _ => exprToLatex valExpr tbl
  let budgetNote ← do
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    if fn.isConstOf interfaceQueryBudgetName && !args.isEmpty then
      let qTex ← exprToLatex args.back! tbl
      pure s!"Total query budget: \\({qTex}\\)"
    else if fn.isConstOf interfacePortBudgetName && !args.isEmpty then
      let qTex ← exprToLatex args.back! tbl
      pure s!"Per-port query budget: \\({qTex}\\)"
    else
      pure ""
  return some (.interfaceTable rows domainLatex budgetNote)

/-- Build an `InspectorKind.dslPseudocode` card from `SystemAlgebra.DSL.sourceDocuments`. -/
private def buildDslPseudocode? (env : Environment) (declName : Name) : Option InspectorKind :=
  match (SystemAlgebra.DSL.sourceDocuments.getState env).find? declName with
  | none => none
  | some doc =>
      let bodyParts := doc.sections.filterMap fun sec =>
        if sec.proof then none else some (sec.header ++ sec.body)
      let body := String.intercalate "\n" bodyParts.toList |>.trimAscii.toString
      some (.dslPseudocode doc.header body doc.source)

/-- Build an `InspectorKind.witnessCard` for an `HCoefficient` or `Implication` witness type. -/
private def buildWitnessCard? (tbl : SymbolTable) (ty : Expr) : MetaM (Option InspectorKind) := do
  let ty ← normalizeForPresentation ty
  if isHCoefficientType ty then
    let args := ty.getAppArgs
    let mut rows : Array (String × String) := #[]
    if args.size ≥ 3 then
      let rTex ← exprToLatex args[args.size - 3]! tbl
      let sTex ← exprToLatex args[args.size - 2]! tbl
      let errTex ← exprToLatex args[args.size - 1]! tbl
      rows := rows.push ("Real system", s!"\\({rTex}\\)")
      rows := rows.push ("Ideal system", s!"\\({sTex}\\)")
      rows := rows.push ("Error bound", s!"\\({errTex}\\)")
    rows := rows.push ("Structure", "Sample law, real/ideal reveals, transcript classes, pointwise ratio, and expected error bound")
    return some (.witnessCard "H-coefficient witness" rows)
  if isImplicationType ty then
    let args := ty.getAppArgs
    let mut rows : Array (String × String) := #[]
    if args.size ≥ 1 then
      let usesTex ← exprToLatex args.back! tbl
      rows := rows.push ("Additional steps", s!"\\({usesTex}\\)")
    rows := rows.push ("Structure", "Counted substitution chain with exact endpoint and link equalities")
    return some (.witnessCard "Substitution chain witness" rows)
  return none

/-- Build an ambient-suppressed `InspectorKind.mathDefinition` for a project `defnInfo`. -/
private def buildMathDefinition (tbl : SymbolTable) (declName : Name) (info : DefinitionVal) :
    MetaM InspectorKind := do
  let (eqLatex, proseSummary) ←
    forallTelescope info.type fun fvars bodyTy => do
      let mut explicitParams : Array String := #[]
      for fv in fvars do
        let d ← fv.fvarId!.getDecl
        if ← isSuppressedLocalDecl d then continue
        if !d.binderInfo.isExplicit then continue
        explicitParams := explicitParams.push (← exprToLatex fv tbl)
      let desc ← describeType tbl bodyTy
      let lhsHead := formatMathIdent (shortConstName declName)
      let lhs :=
        if explicitParams.isEmpty then lhsHead
        else s!"{lhsHead}\\!\\left({String.intercalate ", " explicitParams.toList}\\right)"
      -- Instantiate the definition body with the same telescope fvars (stripping leading lambdas)
      let mut rhs := info.value
      for fv in fvars do
        match rhs.consumeMData with
        | .lam _ _ b _ => rhs := b.instantiate1 fv
        | _ => break
      let rhsTex ← exprToLatex rhs tbl
      let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
      let art := article (adj ++ desc.noun.singular)
      let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
      let summary := ensurePeriod s!"Defined as {art} {adj}{desc.noun.singular}{acc}"
      return (s!"{lhs} := {rhsTex}", summary)
  return .mathDefinition eqLatex proseSummary

/-- Internal Lean/category/plumbing constants that add noise rather than mathematical value
to a human reader's glossary. -/
private def isInspectorNoise (n : Name) : Bool :=
  let s := n.toString
  let leaf := shortConstName n
  leaf.startsWith "inst" ||
  leaf.startsWith "match_" ||
  ["casesOn", "below", "brecOn", "noConfusion", "noConfusionType", "binductionOn", "rec", "recOn"].contains leaf ||
  s.startsWith "CategoryTheory." ||
  s.endsWith ".toCategoryStruct" ||
  s.endsWith ".toQuiver" ||
  s.endsWith ".absorb" ||
  s.endsWith ".ClosedUnder" ||
  n == `SystemAlgebra.TypedSystem ||
  n == `SystemAlgebra.TypedConverter ||
  n == `SystemAlgebra.TypedDistinguisher ||
  n == `SystemAlgebra.TypedSystem.sample ||
  n == `SystemAlgebra.TypedSystem.ofFunction ||
  n == `SystemAlgebra.TypedSystem.ofConditional

private def isLibraryModuleRoot (root : Name) : Bool :=
  [`Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `ProofWidgets].contains root

/-- Filter out Lean core, Mathlib, typeclass plumbing, and internal compiler helpers. -/
private def isLibraryConstant (env : Environment) (n : Name) : Bool :=
  if isCoreOrMathlib n || ambientTypeclassHeads.contains n || isInspectorNoise n then true
  else match env.getModuleIdxFor? n with
    | some idx =>
        match env.header.moduleNames[idx.toNat]? with
        | some modName => isLibraryModuleRoot modName.getRoot
        | none => false
    | none => false

/-- Strip fenced code blocks, markdown emphasis/backticks, and extra whitespace from docstrings,
dropping any upstream docstring containing Lean-isms flagged by the zero-leakage gate. -/
private def cleanDocString? (env : Environment) (declName : Name) : IO (Option String) := do
  let some raw ← Lean.findDocString? env declName | return none
  -- Drop fenced code blocks (```text ... ``` etc.); formal equations are already rendered via `equationLatex`
  let normalized := raw.replace "\r\n" "\n" |>.replace "\r" "\n" |>.replace "\t" " "
  let fenceParts := normalized.splitOn "```"
  let mut proseParts : Array String := #[]
  for i in [:fenceParts.length] do
    if i % 2 == 0 then
      let part := fenceParts[i]!
      proseParts := proseParts.push part
  let joined := String.intercalate " " proseParts.toList
  let cleanedChars := (joined.replace "**" "" |>.replace "`" "" |>.replace "--" "–")
  let words := (cleanedChars.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty)
  let s := (String.intercalate " " words).trimAscii.toString
  -- Fix dangling `:` at end of lead-in right before stripped code block
  let s :=
    if s.endsWith ":" then (s.dropEnd 1).toString ++ "."
    else s
  if s.isEmpty then return none
  let lower := s.toLower
  let bannedCI := [
    "at interface", "whiskering", "interface(s)", "admissibility closure",
    "visible system", "user(s)", "query(s)", "resource(s)"
  ]
  if bannedCI.any (fun pat => (lower.splitOn pat).length > 1) then
    return none
  if !(auditZeroLeakage #[s]).isEmpty then
    return none
  return some s

/-- Detect compiler-generated `match_1` / `match_2` helpers inside an `Expr` in $O(\text{DAG})$ time. -/
private def containsMatchHelper (e : Expr) : Bool :=
  e.foldConsts (init := false) fun n acc =>
    acc || (shortConstName n).startsWith "match_"

/-- Fast bounded $O(\text{limit})$ DAG size check so pathological permutation tables never stall elaboration. -/
private partial def exprSizeBounded (e : Expr) (limit : Nat := 160) : Bool :=
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

/-- Split conjunction chains `A ∧ B ∧ C` into individual `Expr` clauses. -/
private partial def splitAndClauses (e : Expr) : MetaM (Array Expr) := do
  let e ← normalizeForPresentation e
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf ``And && args.size ≥ 2 then
    return (← splitAndClauses args[args.size - 2]!) ++ (← splitAndClauses args[args.size - 1]!)
  return #[e]

/-- Unwrap `TypedSystem.sample` layers and extract clean sampling clauses `\pi \sim \mathrm{uniform}(...)`. -/
private partial def extractSampleClauses (tbl : SymbolTable) (e : Expr) :
    MetaM (Array String × Expr) := do
  let e ← normalizeForPresentation e
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf `SystemAlgebra.TypedSystem.sample && args.size ≥ 5 then
    let lawRaw := args[args.size - 3]!
    let lawClean := match lawRaw.consumeMData with
      | .letE _ _ val (.bvar 0) _ => val
      | other => other
    let lawTex ← exprToLatex lawClean tbl
    let bodyFn := args[args.size - 1]!.consumeMData
    match bodyFn with
    | .lam nm dom body bi =>
        withLocalDecl nm bi dom fun fv => do
          let varTex ← exprToLatex fv tbl
          let (restClauses, innerBody) ← extractSampleClauses tbl (body.instantiate1 fv)
          let clause := s!"\\text\{Sample } {varTex} \\sim {lawTex}"
          return (#[clause] ++ restClauses, innerBody)
    | _ =>
        return (#[s!"\\text\{Sample from } {lawTex}"], e)
  else
    return (#[], e)

/-- Unwrap `{R | P R}` (`setOf` / `Set.setOf` or lambda into `Prop`) for specification comprehensions. -/
private def unwrapSetComprehension? (tbl : SymbolTable) (e : Expr) :
    MetaM (Option (String × Array String)) := do
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let lamExpr? :=
    if fn.isConstOf `Set.setOf || fn.isConstOf `setOf then e.getAppArgs.back?
    else match e with | .lam .. => some e | _ => none
  let some (.lam nm dom body bi) := lamExpr? | return none
  withLocalDecl nm bi dom fun fv => do
    let varTex ← exprToLatex fv tbl
    let pred := body.instantiate1 fv
    let isP ← try isProp pred catch _ => pure false
    if !isP then return none
    let rawClauses ← splitAndClauses pred
    let mut renderedClauses : Array String := #[]
    for c in rawClauses do
      renderedClauses := renderedClauses.push (← exprToLatex c tbl)
    let predTex ← exprToLatex pred tbl
    let setTex := "\\left\\{ " ++ varTex ++ " \\;\\middle|\\; " ++ predTex ++ " \\right\\}"
    return some (setTex, renderedClauses)

/-- Build a concise role description and role badge for a local parameter using `Ontology.describeType`. -/
private def buildParameterRoleAndBadge (tbl : SymbolTable) (ty : Expr) :
    MetaM (String × String) := do
  let desc ← describeType tbl ty
  let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
  let art := article (adj ++ desc.noun.singular)
  let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
  let role := capitalizeFirst (ensurePeriod s!"{art} {adj}{desc.noun.singular}{acc}")
  let badge :=
    if ["interface", "resource", "converter", "specification", "game", "distinguisher"].contains desc.noun.singular then
      desc.noun.singular
    else "parameter"
  return (role, badge)

/-- Build an ambient-suppressed `InspectorKind.mathDefinition` plus `(roleBadge, clauses)`
for a project `defnInfo`. -/
private def buildMathDefinitionRich (tbl : SymbolTable) (declName : Name) (info : DefinitionVal) :
    MetaM (InspectorKind × String × Array String) := do
  let env ← getEnv
  forallTelescope info.type fun fvars bodyTy => do
    let mut explicitParams : Array String := #[]
    let mut explicitFVars : Array Expr := #[]
    let mut domainNouns : List String := []
    let mut expIdx := 0
    let hidden := tbl.hiddenArgs.getD declName []
    let isProj := env.isProjectionFn declName
    for fv in fvars do
      let d ← fv.fvarId!.getDecl
      if ← isSuppressedLocalDecl d then continue
      if !d.binderInfo.isExplicit then continue
      explicitFVars := explicitFVars.push fv
      let pTex ←
        if isProj && cleanBinderName d.userName == "self" then pure "p"
        else exprToLatex fv tbl
      if !hidden.contains expIdx then
        explicitParams := explicitParams.push pTex
      if !(← isProp d.type) then
        let pd ← describeType tbl d.type
        if !pd.noun.singular.startsWith "element of" then
          domainNouns := domainNouns ++ [pd.noun.plural]
      expIdx := expIdx + 1
    let bodyTyClean ← normalizeForPresentation bodyTy
    let desc ← describeType tbl bodyTyClean
    let isPredicate := bodyTyClean == .sort .zero
    let badge ←
      if isPredicate then pure "predicate"
      else if (← resourceInterface? bodyTyClean).isSome then pure "resource"
      else if (← converterInterfaces? bodyTyClean).isSome then pure "converter"
      else if (← specificationInterface? bodyTyClean).isSome then pure "specification"
      else if (← isInterfaceType bodyTyClean) then pure "interface"
      else if isProj then pure "parameter field"
      else pure "definition"
    let lhsHead := tbl.constAliases.getD declName (formatMathIdent (shortConstName declName))
    let lhs :=
      if explicitParams.isEmpty then lhsHead
      else s!"{lhsHead}\\!\\left({String.intercalate ", " explicitParams.toList}\\right)"
    -- Instantiate the definition body with the same telescope fvars (stripping leading lambdas)
    let mut rhs := info.value
    for fv in fvars do
      match rhs.consumeMData with
      | .lam _ _ b _ => rhs := b.instantiate1 fv
      | _ => break
    let rhsTbl :=
      if isProj && explicitFVars.size == 1 then tbl.withExprAlias explicitFVars[0]! "p"
      else tbl
    if rhs.approxDepth > 22 || !exprSizeBounded rhs 160 then
      let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
      let art := article (adj ++ desc.noun.singular)
      let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
      let summary :=
        if isProj then
          s!"Projection field {shortConstName declName} ({art} {adj}{desc.noun.singular}{acc})."
        else
          ensurePeriod s!"Defined as {art} {adj}{desc.noun.singular}{acc}"
      return (.mathDefinition "" summary, badge, #[])
    let rhsNorm ← normalizeForPresentation rhs
    -- 1. Predicate (`→ Prop`): unfold conjunct clauses cleanly!
    if isPredicate then
      let rawClauses ← splitAndClauses rhsNorm
      let mut clauses : Array String := #[]
      for c in rawClauses do
        clauses := clauses.push (← exprToLatex c rhsTbl)
      let summary :=
        if let some firstDom := domainNouns.head? then
          s!"Predicate on {firstDom}."
        else
          "Checked mathematical predicate."
      let eqLatex ←
        if clauses.isEmpty then do
          pure s!"{lhs} := {← exprToLatex rhsNorm rhsTbl}"
        else
          pure s!"{lhs} \\iff {String.intercalate " \\wedge " clauses.toList}"
      return (.mathDefinition eqLatex summary, badge, clauses)
    -- 2. Specification set comprehension (`Set (TypedSystem ...)`): extract membership condition!
    if badge == "specification" then
      if let some (setTex, clauses) ← unwrapSetComprehension? rhsTbl rhsNorm then
        let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
        let summary := ensurePeriod s!"{capitalizeFirst desc.noun.singular}{acc}"
        return (.mathDefinition s!"{lhs} = {setTex}" summary, badge, clauses)
    -- 3. Resource with `TypedSystem.sample` / `TypedSystem.ofFunction` (`match_1` clean handling!)
    if badge == "resource" then
      let (sampleClauses, innerBody) ← extractSampleClauses rhsTbl rhsNorm
      let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
      let summary := ensurePeriod s!"{capitalizeFirst desc.noun.singular}{acc}"
      if !sampleClauses.isEmpty || containsMatchHelper rhsNorm then
        let ifaceStr ← match ← resourceInterface? bodyTyClean with
          | some iface => do
              let itex ← exprToLatex iface rhsTbl
              pure s!"\\text\{Port behavior at } {itex}"
          | none => pure "\\text{Deterministic port evaluation}"
        let finalClauses ←
          if containsMatchHelper innerBody then
            pure (sampleClauses.push ifaceStr)
          else do
            let bodyTex ← exprToLatex innerBody rhsTbl
            pure (sampleClauses.push bodyTex)
        return (.mathDefinition "" summary, badge, finalClauses)
    -- 4. Standard definition / projection
    let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
    let art := article (adj ++ desc.noun.singular)
    let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
    let summary :=
      if isProj then
        s!"Projection field {shortConstName declName} ({art} {adj}{desc.noun.singular}{acc})."
      else
        ensurePeriod s!"Defined as {art} {adj}{desc.noun.singular}{acc}"
    let eqLatex ←
      if containsMatchHelper rhsNorm then pure ""
      else pure s!"{lhs} := {← exprToLatex rhsNorm rhsTbl}"
    return (.mathDefinition eqLatex summary, badge, #[])

/-- Collect explicit project constants referenced inside `e` in $O(\text{DAG})$ time (excluding
core/Mathlib, implicit typeclass arguments, ambient typeclass heads, and internal instance plumbing). -/
private partial def collectExplicitProjectConstants (env : Environment) (e : Expr) :
    MetaM (Array Name) := do
  let rec go (cur : Expr) (acc : NameSet × Array Name × Std.HashSet Expr) :
      MetaM (NameSet × Array Name × Std.HashSet Expr) := do
    if acc.2.2.contains cur then return acc
    let seenE := acc.2.2.insert cur
    let acc := (acc.1, acc.2.1, seenE)
    match cur with
    | .const n _ =>
        if acc.1.contains n || isLibraryConstant env n then return acc
        if env.contains n then return (acc.1.insert n, acc.2.1.push n, seenE)
        else return acc
    | .app .. =>
        let fn := cur.getAppFn.consumeMData
        let args := cur.getAppArgs
        let mut curAcc ← go fn acc
        let visArgs ←
          if cur.hasLooseBVars then pure args
          else match fn.constName? with
          | some hn =>
              try
                let info ← getConstInfo hn
                let mut curTy := info.type
                let mut res : Array Expr := #[]
                for a in args do
                  if curTy.hasLooseBVars then
                    res := res.push a
                  else
                    curTy ← whnfD curTy
                    match curTy with
                    | .forallE _ dom body bi =>
                        if bi.isExplicit && (dom.hasLooseBVars || !(← isAmbientTypeclass dom)) then
                          res := res.push a
                        curTy := body.instantiate1 a
                    | _ => res := res.push a
                pure res
              catch _ => pure args
          | none => pure args
        for a in visArgs do
          curAcc ← go a curAcc
        return curAcc
    | .lam _ d b _ =>
        let acc1 ← go d acc
        go b acc1
    | .forallE _ d b _ =>
        let acc1 ← go d acc
        go b acc1
    | .letE _ t v b _ =>
        let acc1 ← go t acc
        let acc2 ← go v acc1
        go b acc2
    | .mdata _ inner => go inner acc
    | .proj _ _ s => go s acc
    | _ => return acc
  let (_, res, _) ← go e ({}, #[], {})
  return res

/-- Fast $O(\text{DAG})$ scan of a proof term collecting non-theorem project definitions/interfaces. -/
private def collectProofDefConstants (env : Environment) (e : Expr) : Array Name :=
  let (_, out) := e.foldConsts (init := (({} : NameSet), (#[] : Array Name))) fun n (visited, out) =>
    if visited.contains n || isLibraryConstant env n then (visited, out)
    else
      match env.find? n with
      | some (.defnInfo _) | some (.opaqueInfo _) => (visited.insert n, out.push n)
      | _ => (visited.insert n, out)
  out

/-- Special operator display/metadata overrides for CC primitives whose 2D LaTeX comes from
registered `AppHandler`s rather than `constAliases`. -/
private def specialCCOperatorMeta? (declName : Name) : Option (String × String × String) :=
  if declName == distanceName || declName == transcriptDistanceName then
    some ("\\Delta", "metric",
      "Distinguishing distance: supremum of distinguishing advantages over all compatible distinguishers.")
  else if declName == advantageDistanceName || declName == distinguisherAdvantageValName then
    some ("\\Delta", "advantage",
      "Distinguishing advantage between two resources or systems.")
  else if declName == rsWinProbabilityName || declName == typedSolverWinProbabilityName then
    some ("\\Gamma", "win probability",
      "Game winning probability achieved by a solver or distinguisher.")
  else if declName == constructsName || declName == constructsWithinName then
    some ("\\xrightarrow{\\pi}", "construction",
      "Constructive Cryptography realization relation between source and target specifications.")
  else if declName == substitutesWithinName then
    some ("\\simeq", "substitution",
      "Admissible-distinguisher substitution relation between resources within an error bound.")
  else
    none

/-- Inspect a single constant declaration in the environment and produce a rich, type-aware
`SymbolInspector`. -/
private def inspectConstant? (tbl : SymbolTable) (declName : Name) :
    MetaM (Option SymbolInspector) := do
  let env ← getEnv
  if isLibraryConstant env declName then return none
  let some info := env.find? declName | return none
  if ← isAmbientTypeclass info.type then return none
  let key := declName.toString
  let leanType ← cleanLeanTypeStr info.type
  let (sourceFile?, sourceLine?) ← declLocation env declName
  let docString? ← cleanDocString? env declName
  if let some (disp, badge, summary) := specialCCOperatorMeta? declName then
    return some {
      key, display := disp, kind := .mathDefinition "" summary,
      leanName? := some key, leanType, sourceFile?, sourceLine?,
      roleBadge? := some badge, docString?
    }
  let display ← exprToLatex (mkConst declName) tbl
  -- 1. DSL `converter` / `system` recorded by parser
  if let some dslKind := buildDslPseudocode? env declName then
    let badge ← forallTelescope info.type fun _ bodyTy => do
      if (← converterInterfaces? bodyTy).isSome then pure "converter"
      else if (← resourceInterface? bodyTy).isSome then pure "resource"
      else pure "system / converter"
    return some {
      key, display, kind := dslKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?, roleBadge? := some badge, docString?
    }
  -- 2. Closed `Interface` definition -> Port / Query / Reply / Domain table
  let cExpr := mkConst declName (info.levelParams.map Level.param)
  if info.type.consumeMData == mkConst interfaceName then
    if let some tableKind ← buildInterfaceTable? tbl cExpr then
      return some {
        key, display, kind := tableKind, leanName? := some key, leanType,
        sourceFile?, sourceLine?, roleBadge? := some "interface", docString?
      }
  -- 3. `HCoefficient` or `Implication` witness constant
  if let some witnessKind ← buildWitnessCard? tbl info.type then
    return some {
      key, display, kind := witnessKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?, roleBadge? := some "witness", docString?
    }
  -- 4. CC resource / converter / specification assembly -> live box-and-wire diagram
  if let .defnInfo dinfo := info then
    let (isRes, isConv, isSpec) ← forallTelescope info.type fun _ bodyTy => do
      let isRes := (← resourceInterface? bodyTy).isSome
      let isConv := (← converterInterfaces? bodyTy).isSome
      let isSpec := (← specificationInterface? bodyTy).isSome
      pure (isRes, isConv, isSpec)
    if (isRes || isConv || isSpec) && !info.type.isForall then
      if let some diagHtml ← renderCCDiagramHtml? dinfo.value then
        let sumTex ← exprToLatex dinfo.value tbl
        let badge := if isConv then "converter" else if isSpec then "specification" else "resource"
        return some {
          key, display, kind := .ccDiagram diagHtml sumTex,
          leanName? := some key, leanType, sourceFile?, sourceLine?,
          roleBadge? := some badge, docString?
        }
    -- 5. Ambient-suppressed mathematical definition / predicate / resource / projection
    let (defKind, badge, clauses) ← buildMathDefinitionRich tbl declName dinfo
    return some {
      key, display, kind := defKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?, roleBadge? := some badge, clauses, docString?
    }
  return none

/-- Collect constant inspectors from an arbitrary array of expressions (used e.g. for Section Contexts). -/
def collectExprInspectors (tbl : SymbolTable) (exprs : Array Expr) : MetaM (Array SymbolInspector) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut out : Array SymbolInspector := #[]
  for e in exprs do
    for cn in (← collectExplicitProjectConstants env e) do
      if !seen.contains cn then
        seen := seen.insert cn
        try
          if let some ins ← inspectConstant? tbl cn then
            out := out.push ins
        catch _ => pure ()
  return out

/-- Inspect a theorem statement's local non-hoisted parameters AND referenced constants from both
`theoremType` and `proofBody?` (+ `extraOriginDecls`), returning
`(localParamInspectors, typeConstInspectors, proofConstInspectors)`. -/
def collectScopedCCInspectors (tbl : SymbolTable) (declName : Name) (theoremType : Expr)
    (proofBody? : Option Expr) (hoistedParamSyms : Std.HashSet String)
    (extraOriginDecls : Array Name := #[]) :
    MetaM (Array SymbolInspector × Array SymbolInspector × Array SymbolInspector) := do
  let env ← getEnv
  let pushUnique (acc : Array SymbolInspector) (seen : Std.HashSet String) (ins : SymbolInspector) :
      Array SymbolInspector × Std.HashSet String :=
    if seen.contains ins.key then (acc, seen)
    else (acc.push ins, seen.insert ins.key)
  let (fvOut, typeConsts) ← forallTelescope theoremType fun fvars conclusion => do
    let mut fvOut : Array SymbolInspector := #[]
    let mut consts : Array Name := #[]
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      if ← isSuppressedLocalDecl decl then continue
      if ← isProp decl.type then
        consts := consts ++ (← collectExplicitProjectConstants env decl.type)
        continue
      let desc ← describeType tbl decl.type
      if desc.isAmbient then continue
      consts := consts ++ (← collectExplicitProjectConstants env decl.type)
      let clean := cleanBinderName decl.userName
      let display ← exprToLatex fv tbl
      if hoistedParamSyms.contains display then
        continue
      let leanType ← cleanLeanTypeStr decl.type
      let key := s!"param:{declName}:{clean}"
      let (kind, badge) : InspectorKind × String ← do
        if let some tableKind ← buildInterfaceTable? tbl fv then
          pure (tableKind, "interface")
        else if let some witnessKind ← buildWitnessCard? tbl decl.type then
          pure (witnessKind, "witness")
        else
          let isRes := (← resourceInterface? decl.type).isSome
          let isConv := (← converterInterfaces? decl.type).isSome
          let isSpec := (← specificationInterface? decl.type).isSome
          if isRes || isConv || isSpec then
            let b := if isConv then "converter" else if isSpec then "specification" else "resource"
            match ← renderCCDiagramHtml? fv with
            | some html => pure (.ccDiagram html display, b)
            | none =>
                let (role, _) ← buildParameterRoleAndBadge tbl decl.type
                pure (.parameter role, b)
          else
            let (role, b) ← buildParameterRoleAndBadge tbl decl.type
            pure (.parameter role, b)
      fvOut := fvOut.push {
        key, display, kind, leanName? := none, leanType, roleBadge? := some badge
      }
    consts := consts ++ (← collectExplicitProjectConstants env conclusion)
    return (fvOut, consts)
  let mut typeIns : Array SymbolInspector := #[]
  let mut seenTypeKeys : Std.HashSet String := {}
  for cn in typeConsts do
    if !seenTypeKeys.contains cn.toString then
      try
        if let some ins ← inspectConstant? tbl cn then
          (typeIns, seenTypeKeys) := pushUnique typeIns seenTypeKeys ins
      catch _ => pure ()
  let mut proofConsts : Array Name := match proofBody? with
    | some body => collectProofDefConstants env body
    | none => #[]
  for od in extraOriginDecls do
    if let some oinfo := env.find? od then
      proofConsts := proofConsts ++ (← collectExplicitProjectConstants env oinfo.type)
  let mut proofIns : Array SymbolInspector := #[]
  let mut seenProofKeys := seenTypeKeys
  for cn in proofConsts do
    if !seenProofKeys.contains cn.toString then
      try
        if let some ins ← inspectConstant? tbl cn then
          (proofIns, seenProofKeys) := pushUnique proofIns seenProofKeys ins
      catch _ => pure ()
  return (fvOut, typeIns, proofIns)

/-- Legacy flat collector compatibility wrapper. -/
def collectCCInspectors (tbl : SymbolTable) (theoremType : Expr) :
    MetaM (Array SymbolInspector) := do
  let (fvOut, typeIns, _) ← collectScopedCCInspectors tbl .anonymous theoremType none {}
  return fvOut ++ typeIns

/-! ## 3. Module Initialization (Auto-Registration) -/

/-- Register the CC diagram hook and type-aware symbol inspector collectors with `ProofGraph`. -/
def registerAll : IO Unit := do
  registerDiagramHook renderCCDiagramHtml?
  registerInspectorCollector collectCCInspectors
  registerScopedInspectorCollector fun tbl declName theoremType proofBody? hoistedParamSyms extra =>
    collectScopedCCInspectors tbl declName theoremType proofBody? hoistedParamSyms extra

initialize registerAll

end Informalization.CC.Inspectors
