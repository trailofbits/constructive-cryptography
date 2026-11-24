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

/-- Build a concise role description for a local parameter using `Ontology.describeType`. -/
private def buildParameterRole (tbl : SymbolTable) (ty : Expr) : MetaM String := do
  let desc ← describeType tbl ty
  let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
  let art := article (adj ++ desc.noun.singular)
  let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
  return capitalizeFirst (ensurePeriod s!"{art} {adj}{desc.noun.singular}{acc}")

/-- Internal Lean/category/plumbing constants that add noise rather than mathematical value
to a human reader's glossary. -/
private def isInspectorNoise (n : Name) : Bool :=
  let s := n.toString
  let leaf := shortConstName n
  leaf.startsWith "inst" ||
  s.startsWith "CategoryTheory." ||
  s.endsWith ".toCategoryStruct" ||
  s.endsWith ".toQuiver" ||
  s.endsWith ".absorb" ||
  s.endsWith ".ClosedUnder" ||
  n == `SystemAlgebra.TypedSystem ||
  n == `SystemAlgebra.TypedConverter ||
  n == `SystemAlgebra.TypedDistinguisher

/-- Collect all project-level constants referenced inside `e` (excluding core/Mathlib,
ambient typeclass heads, and internal instance/category plumbing). -/
private partial def collectProjectConstants (env : Environment) (e : Expr) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut out : Array Name := #[]
  let rec go (cur : Expr) (acc : NameSet × Array Name) : NameSet × Array Name :=
    match cur with
    | .const n _ =>
        if acc.1.contains n || isCoreOrMathlib n || ambientTypeclassHeads.contains n ||
            isInspectorNoise n then acc
        else if env.contains n then (acc.1.insert n, acc.2.push n)
        else acc
    | .app f a => go a (go f acc)
    | .lam _ d b _ => go b (go d acc)
    | .forallE _ d b _ => go b (go d acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ inner => go inner acc
    | .proj _ _ s => go s acc
    | _ => acc
  (visited, out) := go e (visited, out)
  return out

/-- Inspect a single constant declaration in the environment and produce a type-aware
`SymbolInspector`. -/
private def inspectConstant? (tbl : SymbolTable) (declName : Name) :
    MetaM (Option SymbolInspector) := do
  let env ← getEnv
  let some info := env.find? declName | return none
  if ← isAmbientTypeclass info.type then return none
  let key := declName.toString
  let display ← exprToLatex (mkConst declName) tbl
  let leanType ← cleanLeanTypeStr info.type
  let (sourceFile?, sourceLine?) ← declLocation env declName
  -- 1. DSL `converter` / `system` recorded by parser
  if let some dslKind := buildDslPseudocode? env declName then
    return some {
      key, display, kind := dslKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?
    }
  -- 2. Closed `Interface` definition -> Port / Query / Reply / Domain table
  let cExpr := mkConst declName (info.levelParams.map Level.param)
  if info.type.consumeMData == mkConst interfaceName then
    if let some tableKind ← buildInterfaceTable? tbl cExpr then
      return some {
        key, display, kind := tableKind, leanName? := some key, leanType,
        sourceFile?, sourceLine?
      }
  -- 3. `HCoefficient` or `Implication` witness constant
  if let some witnessKind ← buildWitnessCard? tbl info.type then
    return some {
      key, display, kind := witnessKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?
    }
  -- 4. CC resource / converter / specification assembly -> live box-and-wire diagram
  if let .defnInfo dinfo := info then
    let isCCObj ← forallTelescope info.type fun _ bodyTy => do
      let isRes := (← resourceInterface? bodyTy).isSome
      let isConv := (← converterInterfaces? bodyTy).isSome
      let isSpec := (← specificationInterface? bodyTy).isSome
      pure (isRes || isConv || isSpec)
    if isCCObj && !info.type.isForall then
      if let some diagHtml ← renderCCDiagramHtml? dinfo.value then
        let sumTex ← exprToLatex dinfo.value tbl
        return some {
          key, display, kind := .ccDiagram diagHtml sumTex,
          leanName? := some key, leanType, sourceFile?, sourceLine?
        }
    -- 5. Ambient-suppressed mathematical definition
    let defKind ← buildMathDefinition tbl declName dinfo
    return some {
      key, display, kind := defKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?
    }
  return none

/-- Inspect a theorem statement's free variables and referenced project constants, returning
a deduplicated array of type-aware `SymbolInspector`s. -/
def collectCCInspectors (tbl : SymbolTable) (theoremType : Expr) :
    MetaM (Array SymbolInspector) := do
  let env ← getEnv
  let mut out : Array SymbolInspector := #[]
  let mut seenKeys : Std.HashSet String := {}
  let pushUnique (acc : Array SymbolInspector) (seen : Std.HashSet String) (ins : SymbolInspector) :
      Array SymbolInspector × Std.HashSet String :=
    if seen.contains ins.key then (acc, seen)
    else (acc.push ins, seen.insert ins.key)
  -- Walk the theorem signature in live `MetaM` context
  let (fvarInspectors, constNames) ← forallTelescope theoremType fun fvars conclusion => do
    let mut fvOut : Array SymbolInspector := #[]
    let mut consts : Array Name := #[]
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      if ← isSuppressedLocalDecl decl then continue
      if ← isProp decl.type then
        consts := consts ++ collectProjectConstants env decl.type
        continue
      let desc ← describeType tbl decl.type
      if desc.isAmbient then continue
      consts := consts ++ collectProjectConstants env decl.type
      let clean := cleanBinderName decl.userName
      let display ← exprToLatex fv tbl
      let leanType ← cleanLeanTypeStr decl.type
      let key := s!"param:{clean}"
      -- Dispatch free variable by type
      let kind : InspectorKind ← do
        if let some tableKind ← buildInterfaceTable? tbl fv then
          pure tableKind
        else if let some witnessKind ← buildWitnessCard? tbl decl.type then
          pure witnessKind
        else
          let isCCObj :=
            (← resourceInterface? decl.type).isSome ||
            (← converterInterfaces? decl.type).isSome ||
            (← specificationInterface? decl.type).isSome
          if isCCObj then
            match ← renderCCDiagramHtml? fv with
            | some html => pure (.ccDiagram html display)
            | none => pure (.parameter (← buildParameterRole tbl decl.type))
          else
            pure (.parameter (← buildParameterRole tbl decl.type))
      fvOut := fvOut.push {
        key, display, kind, leanName? := none, leanType
      }
    consts := consts ++ collectProjectConstants env conclusion
    return (fvOut, consts)
  for ins in fvarInspectors do
    (out, seenKeys) := pushUnique out seenKeys ins
  for cn in constNames do
    if !seenKeys.contains cn.toString then
      try
        if let some ins ← inspectConstant? tbl cn then
          (out, seenKeys) := pushUnique out seenKeys ins
      catch _ =>
        pure ()
  return out

/-! ## 3. Module Initialization (Auto-Registration) -/

/-- Register the CC diagram hook and type-aware symbol inspector collector with `ProofGraph`. -/
def registerAll : IO Unit := do
  registerDiagramHook renderCCDiagramHtml?
  registerInspectorCollector collectCCInspectors

initialize registerAll

end Informalization.CC.Inspectors
