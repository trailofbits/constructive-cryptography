/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Overlay
import Informalization.Core.Ontology
import Informalization.Core.Routine
import Informalization.Core.Explanation

/-!
# Cross-Lemma Recursive Proof Decompiler (90% Pure Kyle Miller Engine)

Decompiles any checked Lean declaration directly from its kernel proof term (and live `MetaM`
context) into the single unified recursive `Explanation.ProofNode` tree:
* Recognizes `calc` / `cc_calc` chains (`Trans.trans`, `Eq.trans`, `LE.le.trans`,
  `SubstitutesWithin.trans`) and displays them as crisp aligned paper calculations.
* Recurses seamlessly across project lemmas (`ConstructiveCryptography.*`, `Examples.*`,
  `SequenceHash.*`, …), stopping cleanly at Lean/Mathlib leaves or `informal_opaque` stops.
* **Smart wrapper auto-inlining:** marks trivial 1-step forwarding/cast/rewrite bridge lemmas
  with `isWrapper := true` so Paper mode surfaces genuine mathematical joints immediately while
  Auditor mode preserves every declaration boundary.
* **Sibling deduplication:** never prints 15 identical copies of the same helper invocation.
* **Extensible CC family explainers:** consults registered domain explainers (`CC/Families/*`)
  before falling back to clean generic Miller decompilation in Maurer's voice.
-/

namespace Informalization.Core.ProofGraph

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Overlay
open Informalization.Core.Ontology
open Informalization.Core.Routine
open Informalization.Core.Explanation

/-- Configuration for one informalization run. -/
structure Config where
  maxLemmaDepth : Nat := 4
  maxTermFuel : Nat := 96
  /-- Package/module root namespaces considered "local project" for cross-lemma expansion
  (empty = expand any non-Mathlib/core theorem). -/
  projectNamespaces : Array Name := #[]
  deriving Inhabited

/-- Context threaded through proof decompilation. -/
structure DecompCtx where
  config : Config
  tbl : SymbolTable
  seenDecls : NameSet := {}
  lemmaDepth : Nat := 0
  /-- Most recently introduced `have` fact (for causal vs. independent discourse transitions). -/
  lastFactFVar? : Option FVarId := none
  /-- Count of sequential `have` steps at the current block level. -/
  factIndex : Nat := 0
  /-- True when proving the top-level theorem conclusion (suppresses verbatim restatement). -/
  atRootConclusion : Bool := true

/-- Callback allowing domain explainers to recursively decompile child proof terms. -/
abbrev DecompileChild := DecompCtx → Expr → Expr → StateRefT DiscourseState MetaM (Array ProofNode)

/-- Extensible explainer for a domain proof rule (e.g., CC constructions, `cc_calc`,
indifferentiability composition, H-coefficient witnesses, games). -/
structure RuleExplainer where
  priority : Nat := 100
  explain : DecompCtx → DecompileChild → Expr → Expr →
    StateRefT DiscourseState MetaM (Option (Array ProofNode))

/-- Optional diagram hook (registered by `CC/Inspectors.lean` using `Rendering`) that turns
a recognized CC expression or judgment into static HTML. -/
initialize diagramHookRef : IO.Ref (Expr → MetaM (Option String)) ←
  IO.mkRef (fun _ => pure none)

/-- Optional type-aware symbol inspector collector (populated by `CC/Inspectors.lean`). -/
initialize inspectorCollectorRef :
    IO.Ref (SymbolTable → Expr → MetaM (Array SymbolInspector)) ←
  IO.mkRef (fun _ _ => pure #[])

/-- Scoped inspector collector returning
`(localParamInspectors, typeConstInspectors, proofConstInspectors)`
for a declaration, excluding parameters already hoisted into the section context. -/
initialize scopedInspectorCollectorRef :
    IO.Ref (SymbolTable → Name → Expr → Option Expr → Std.HashSet String → Array Name →
      MetaM (Array SymbolInspector × Array SymbolInspector × Array SymbolInspector)) ←
  IO.mkRef fun tbl _ ty _ _ _ => do
    let all ← (← inspectorCollectorRef.get) tbl ty
    return (#[], all, #[])

initialize ruleExplainersRef : IO.Ref (Array RuleExplainer) ← IO.mkRef #[]

def registerRuleExplainer (e : RuleExplainer) : IO Unit :=
  ruleExplainersRef.modify fun arr =>
    (arr.push e).qsort fun a b => a.priority > b.priority

def registerDiagramHook (f : Expr → MetaM (Option String)) : IO Unit :=
  diagramHookRef.set f

def registerInspectorCollector (f : SymbolTable → Expr → MetaM (Array SymbolInspector)) : IO Unit :=
  inspectorCollectorRef.set f

def registerScopedInspectorCollector
    (f : SymbolTable → Name → Expr → Option Expr → Std.HashSet String → Array Name →
      MetaM (Array SymbolInspector × Array SymbolInspector × Array SymbolInspector)) : IO Unit :=
  scopedInspectorCollectorRef.set f

/-- Extract binary relation `(relLatex, lhs, rhs)` if `prop` is a recognized chainable relation. -/
def splitBinaryRelation? (tbl : SymbolTable) (prop : Expr) :
    MetaM (Option (String × Expr × Expr)) := do
  let prop ← normalizeForPresentation prop
  let fn := prop.getAppFn.consumeMData
  let args := prop.getAppArgs
  let some head := fn.constName? | return none
  if args.size < 2 then return none
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  match head with
  | ``Eq => return some ("=", lhs, rhs)
  | ``LE.le => return some ("\\le", lhs, rhs)
  | ``LT.lt => return some ("<", lhs, rhs)
  | `ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin =>
      if args.size ≥ 3 then
        let err := args[args.size - 3]!
        let errTex ← exprToLatex err tbl
        return some ("\\simeq_{" ++ errTex ++ "}", lhs, rhs)
      return some ("\\simeq", lhs, rhs)
  | `ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs =>
      if args.size ≥ 3 then
        let conv := args[args.size - 3]!
        let convTex ← exprToLatex conv tbl
        return some ("\\xrightarrow{" ++ convTex ++ "}", lhs, rhs)
      return none
  | `ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin =>
      if args.size ≥ 4 then
        let conv := args[args.size - 4]!
        let err := args[args.size - 1]!
        let src := args[args.size - 3]!
        let tgt := args[args.size - 2]!
        let convTex ← exprToLatex conv tbl
        let errTex ← exprToLatex err tbl
        return some ("\\xrightarrow{" ++ convTex ++ ";\\," ++ errTex ++ "}", src, tgt)
      return none
  | _ => return none

/-- Detect if a proof term is a transitivity step (from `calc`, `cc_calc`, `Eq.trans`,
`LE.le.trans`, `Trans.trans`, or `SubstitutesWithin.trans`) and split it into its two
checked sub-proofs `(leftProof, leftType, rightProof, rightType)`. -/
private def splitTransProof? (proof : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let fn := proof.getAppFn.consumeMData
  let args := proof.getAppArgs
  let some head := fn.constName? | return none
  let isTrans :=
    head == ``Eq.trans || head == `LE.le.trans || head == `LT.lt.trans ||
    head == ``Trans.trans || head == `LE.le.trans_eq || head == `Eq.trans_le ||
    head.toString.endsWith ".trans" || head.toString.endsWith ".trans_eq" ||
    head.toString.endsWith "substitutesWithin_trans" ||
    head.toString.endsWith "substitutesWithin_of_eq_left" ||
    head.toString.endsWith "substitutesWithin_of_eq_right"
  if !isTrans then return none
  -- Collect proof-valued arguments (typically the last two propositions proved)
  let mut proofArgs : Array (Expr × Expr) := #[]
  for arg in args do
    try
      let ty ← inferType arg
      if ← isProp ty then
        proofArgs := proofArgs.push (arg, ty)
    catch _ => pure ()
  if proofArgs.size == 2 then
    let (p1, t1) := proofArgs[0]!
    let (p2, t2) := proofArgs[1]!
    return some (p1, t1, p2, t2)
  return none

/-- Flatten a chain of transitivity steps into ordered `(stepProof, stepType)` pairs. -/
private partial def flattenCalcChain (proof expected : Expr) (fuel : Nat := 32) :
    MetaM (Array (Expr × Expr)) := do
  if fuel == 0 then return #[(proof, expected)]
  match ← splitTransProof? proof with
  | some (p1, t1, p2, t2) =>
      let left ← flattenCalcChain p1 t1 (fuel - 1)
      let right ← flattenCalcChain p2 t2 (fuel - 1)
      return left ++ right
  | none => return #[(proof, expected)]

/-- Should we recurse into project lemma `declName`'s body? -/
private def shouldExpandLemma (env : Environment) (ctx : DecompCtx) (declName : Name) : Bool :=
  if ctx.lemmaDepth ≥ ctx.config.maxLemmaDepth then false
  else if ctx.seenDecls.contains declName then false
  else if isCoreOrMathlib declName then false
  else if (getOverlay env declName).isOpaqueLeaf then false
  else if ctx.config.projectNamespaces.isEmpty then
    match env.find? declName with
    | some (.thmInfo _) => true
    | _ => false
  else
    ctx.config.projectNamespaces.any (fun p => p.isPrefixOf declName)

/-- Extract the proof-valued arguments of an application `f a₁ … aₙ`. -/
private def proofValuedArgs (term : Expr) : MetaM (Array (Expr × Expr)) := do
  let mut out : Array (Expr × Expr) := #[]
  for arg in term.getAppArgs do
    try
      let ty ← inferType arg
      if ← isProp ty then
        out := out.push (arg, ty)
    catch _ => pure ()
  return out

/-- Format a readable human label for a theorem/lemma name (respecting `informal_title`
overlay if present, otherwise clean spaced words). -/
def humanLemmaLabel (env : Environment) (declName : Name) : String :=
  match (getOverlay env declName).title? with
  | some t => t.trimAscii.toString
  | none =>
      let short := shortConstName declName
      let words := (short.replace "_" " ").splitOn " " |>.filter (!·.isEmpty)
      String.intercalate " " words

/-- Heuristic detector for trivial 1-step forwarding/cast wrapper lemmas so Paper mode can
auto-inline them cleanly (while Auditor mode still shows them). -/
private def isTrivialWrapperBody (env : Environment) (declName : Name) (body : Expr) : Bool :=
  if (getOverlay env declName).isProofJoint then false
  else
    let rec stripLams : Expr → Expr
      | .lam _ _ b _ => stripLams b
      | .mdata _ b => stripLams b
      | e => e
    let core := stripLams body
    match core.getAppFn.consumeMData with
    | .const head _ =>
        -- Single direct call to another non-Mathlib theorem or trivial `rfl`/`Eq.mp` wrapper
        head == ``Eq.refl || head == ``Eq.mp || head == ``Eq.mpr ||
        (!isCoreOrMathlib head && core.getAppArgs.size ≤ 16)
    | _ => false

/-- Recursively deduplicate repeated identical sibling proof nodes (preventing 15× spam)
and coalesce duplicate `routineReceipt` siblings of the same kind into one counted receipt
at every level of the proof tree, including nodes built by domain `RuleExplainer`s. -/
private partial def dedupSiblings (nodes : Array ProofNode) : Array ProofNode := Id.run do
  let rec cleanNode : ProofNode → ProofNode
    | .step id content children goal? diag origin isWrap defExp =>
        .step id content (dedupSiblings children) goal? diag origin isWrap defExp
    | .calcChain id intro steps goal? origin =>
        .calcChain id intro (steps.map fun (s, ch) => (s, dedupSiblings ch)) goal? origin
    | .routineReceipt id summary count details goal? =>
        .routineReceipt id summary count (dedupSiblings details) goal?
    | other => other
  let mut seen : Std.HashSet String := {}
  let mut seenRoutineIdx : Std.HashMap String Nat := {}
  let mut out : Array ProofNode := #[]
  for raw in nodes do
    let n := cleanNode raw
    match n with
    | .routineReceipt id summary count details goal? =>
        if let some idx := seenRoutineIdx.get? summary then
          if let .routineReceipt oid osum ocount odet ogoal := out[idx]! then
            out := out.set! idx (.routineReceipt oid osum (ocount + count) (dedupSiblings (odet ++ details)) ogoal)
        else
          seenRoutineIdx := seenRoutineIdx.insert summary out.size
          out := out.push (.routineReceipt id summary count details goal?)
    | _ =>
        let visibleKey : String :=
          match n with
          | .step _ content _ _ _ _ _ _ =>
              let parts := content.map fun
                | .text s => s
                | .emph s => s
                | .inlineMath s => s
                | .displayMath s p => s ++ p
                | .symbol _ d _ => d
                | .citation l d => l ++ " " ++ d
              String.intercalate "|" parts.toList
          | _ => String.intercalate "|" (n.collectAllText.toList)
        if !visibleKey.isEmpty && seen.contains visibleKey then
          continue
        seen := seen.insert visibleKey
        out := out.push n
  return out

/-- Core recursive decompiler: `(ctx, expectedProp, proofTerm) → Array ProofNode`. -/
partial def decompileProof (ctx : DecompCtx) (expected proof : Expr)
    (fuel : Nat := 96) : StateRefT DiscourseState MetaM (Array ProofNode) := do
  if fuel == 0 then return #[]
  let expected ← instantiateMVars expected
  let proof ← instantiateMVars proof
  let env ← getEnv

  -- 1. Check domain-registered CC family explainers first
  for exp in (← ruleExplainersRef.get) do
    if let some nodes ← exp.explain ctx (fun c e p => decompileProof c e p (fuel - 1)) expected proof then
      return dedupSiblings nodes

  -- 2. Check routine algebra / casts / reflexivity (fail-closed)
  if let some rkind := classifyRoutine? env proof then
    let goal ← buildGoalState ctx.tbl expected
    return #[.routineReceipt s!"routine-{fuel}" rkind.label 1 #[] (some goal)]

  -- 3. Unwrap leading binders (`intro`) transparently into the live `LocalContext`
  match expected, proof with
  | .forallE nm dom body bi, .lam pnm _ pbody _ =>
      let useName := if (cleanBinderName? pnm).isSome then pnm else nm
      return ← withLocalDecl useName bi dom fun fv =>
        decompileProof ctx (body.instantiate1 fv) (pbody.instantiate1 fv) (fuel - 1)
  | _, .mdata _ inner =>
      return ← decompileProof ctx expected inner (fuel - 1)
  | _, .letE nm ty val body _ =>
      let isP ← isProp ty
      if isP then
        -- Local intermediate fact (`have h : P := ...`): choose causal vs. parallel transition!
        let usesPrev := match ctx.lastFactFVar? with
          | some prevId => (Lean.collectFVars {} val).fvarIds.contains prevId
          | none => false
        let factNodes ← decompileProof { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false } ty val (fuel - 1)
        let goal ← buildGoalState ctx.tbl ty
        let factInl ← renderProposition ctx.tbl ty
        let opener ← do
          let st ← get
          if usesPrev then
            let (op, st') := st.pickOpener .consequence
            set st'
            pure op
          else if ctx.factIndex == 0 then
            pure "First,"
          else
            let parallelOps := #["Next,", "Moreover,", "In addition,", "Similarly,"]
            pure (parallelOps[(ctx.factIndex - 1) % parallelOps.size]!)
        let headerStep : ProofNode :=
          .step s!"have-{fuel}"
            (#[.text s!"{opener} "] ++ factInl ++ #[.text "."])
            factNodes (some goal)
        let rest ← withLetDecl nm ty val fun fv =>
          let nextCtx := { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1 }
          decompileProof nextCtx expected (body.instantiate1 fv) (fuel - 1)
        return dedupSiblings (#[headerStep] ++ rest)
      else
        return ← withLetDecl nm ty val fun fv =>
          decompileProof ctx expected (body.instantiate1 fv) (fuel - 1)
  | _, _ => pure ()

  -- 3a. Fold `funext` into natural pointwise prose instead of "Applying funext, ..."
  if let .const head _ := proof.getAppFn.consumeMData then
    if head == ``funext || head == `Function.funext then
      if let some (.lam pnm dom pbody bi) := proof.getAppArgs.back? then
        return ← withLocalDecl pnm bi dom fun fv => do
          let xTex ← exprToLatex fv ctx.tbl
          let bodyExpr := pbody.instantiate1 fv
          let bodyTy ← inferType bodyExpr
          let subNodes ← decompileProof { ctx with lastFactFVar? := none, factIndex := 0 } bodyTy bodyExpr (fuel - 1)
          let bodyInl ← renderProposition ctx.tbl bodyTy
          let goal ← buildGoalState ctx.tbl expected
          return #[.step s!"funext-{fuel}"
            (#[.text "Evaluating pointwise at ", .inlineMath xTex, .text ", "] ++ bodyInl ++ #[.text "."])
            subNodes (some goal)]

  -- 3b. Transparently unwrap kernel cast/rewrite transport wrappers (`Eq.mp`, `Eq.mpr`,
  -- `Iff.mp`, `Iff.mpr`, `id`) so Paper mode lands directly on genuine mathematical joints.
  if let .const head _ := proof.getAppFn.consumeMData then
    if head == ``Eq.mp || head == ``Eq.mpr || head == ``Iff.mp || head == ``Iff.mpr ||
       head == ``id then
      let args := proof.getAppArgs
      if let some inner := args.back? then
        try
          let innerTy ← inferType inner
          if ← isProp innerTy then
            return ← decompileProof ctx innerTy inner (fuel - 1)
        catch _ => pure ()

  -- 3c. Split `And.intro p q` into two flowing sub-arguments (never collapsed as routine!)
  if let .const head _ := proof.getAppFn.consumeMData then
    if head == ``And.intro then
      let args := proof.getAppArgs
      if args.size ≥ 4 then
        let pTy := args[args.size - 4]!
        let qTy := args[args.size - 3]!
        let pPf := args[args.size - 2]!
        let qPf := args[args.size - 1]!
        let subCtx := { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false }
        let pNodes ← decompileProof subCtx pTy pPf (fuel - 1)
        let qNodes ← decompileProof subCtx qTy qPf (fuel - 1)
        let pInl ← renderProposition ctx.tbl pTy
        let qInl ← renderProposition ctx.tbl qTy
        let pGoal ← buildGoalState ctx.tbl pTy
        let qGoal ← buildGoalState ctx.tbl qTy
        let bothLe := pTy.getAppFn.consumeMData.isConstOf ``LE.le &&
          (qTy.getAppFn.consumeMData.isConstOf ``LE.le || qTy.getAppFn.consumeMData.isConstOf ``And)
        let lead1 := if bothLe then "For the lower bound, " else "First, "
        let lead2 := if bothLe then "For the upper bound, " else "Second, "
        let step1 : ProofNode := .step s!"andL-{fuel}" (#[.text lead1] ++ pInl ++ #[.text "."]) pNodes (some pGoal)
        let step2 : ProofNode := .step s!"andR-{fuel}" (#[.text lead2] ++ qInl ++ #[.text "."]) qNodes (some qGoal)
        return dedupSiblings #[step1, step2]

  -- 4. Detect `calc` / `cc_calc` chains (`Trans.trans` / `Eq.trans` / `LE.le.trans` / `SubstitutesWithin`)
  let chain ← flattenCalcChain proof expected
  if chain.size ≥ 2 then
    let mut calcSteps : Array (CalcStep × Array ProofNode) := #[]
    let mut allParsed := true
    for (sp, st) in chain do
      match ← splitBinaryRelation? ctx.tbl st with
      | some (rel, lhs, rhs) =>
          let lhsTex ← exprToLatex lhs ctx.tbl
          let rhsTex ← exprToLatex rhs ctx.tbl
          let subNodes ← decompileProof ctx st sp (fuel - 1)
          let reason : Array Inline ←
            match sp.getAppFn.consumeMData with
            | .const cn _ =>
                if isCoreOrMathlib cn then pure #[.text "by elementary algebra"]
                else pure #[.text s!"by {humanLemmaLabel env cn}"]
            | .fvar id => do
                let ldecl ← id.getDecl
                match cleanBinderName? ldecl.userName with
                | some hn => pure #[.text "by hypothesis ", .inlineMath (formatMathIdent hn)]
                | none => pure #[.text "by assumption"]
            | _ => pure #[.text "by the checked subargument"]
          let diagHtml ← (← diagramHookRef.get) st
          let cs : CalcStep := {
            lhsLatex := lhsTex
            relationLatex := rel
            rhsLatex := rhsTex
            reason
            diagramHtml? := diagHtml
          }
          calcSteps := calcSteps.push (cs, subNodes)
      | none => allParsed := false
    if allParsed && !calcSteps.isEmpty then
      let goal ← buildGoalState ctx.tbl expected
      let st ← get
      let (opener, st') := st.pickOpener .elaboration
      set st'
      let intro : Array Inline := #[.text s!"{opener} chaining the intermediate steps yields"]
      return #[.calcChain s!"calc-{fuel}" intro calcSteps (some goal)]

  -- 5. Direct hypothesis (`assumption`)
  if let .fvar id := proof.consumeMData then
    let decl ← id.getDecl
    let goal ← buildGoalState ctx.tbl expected
    let nameStr := match cleanBinderName? decl.userName with
      | some hn => s!"the assumption \\({formatMathIdent hn}\\)"
      | none => "the preceding assumption"
    return #[.step s!"hyp-{fuel}" #[.text s!"This holds directly by {nameStr}."] #[] (some goal)]

  -- 6. Application of a named theorem/lemma (with cross-lemma recursion & wrapper detection!)
  if let .const declName _ := proof.getAppFn.consumeMData then
    let pArgs ← proofValuedArgs proof
    let mut premiseNodes : Array ProofNode := #[]
    let subCtx := { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false }
    for (ap, aty) in pArgs do
      let sub ← decompileProof subCtx aty ap (fuel - 1)
      premiseNodes := premiseNodes ++ sub
    let mut expandedBody : Array ProofNode := #[]
    let mut isWrap := false
    if shouldExpandLemma env ctx declName then
      if let some (.thmInfo info) := env.find? declName then
        isWrap := isTrivialWrapperBody env declName info.value
        let childCtx : DecompCtx := {
          ctx with
          seenDecls := ctx.seenDecls.insert declName
          lemmaDepth := ctx.lemmaDepth + 1
          lastFactFVar? := none
          factIndex := 0
          atRootConclusion := false
        }
        expandedBody ← forallTelescope info.type fun _ innerTarget =>
          decompileProof childCtx innerTarget info.value (fuel - 1)
    let ov := getOverlay env declName
    let mut allChildren : Array ProofNode := #[]
    if let some fb := ov.flowBefore? then
      allChildren := allChildren.push (.flowNote s!"flow-pre-{declName}" fb "margin")
    allChildren := allChildren ++ dedupSiblings (premiseNodes ++ expandedBody)
    if let some fa := ov.flowAfter? then
      allChildren := allChildren.push (.flowNote s!"flow-post-{declName}" fa "margin")
    let goal ← buildGoalState ctx.tbl expected
    let diagHtml ← (← diagramHookRef.get) expected
    let label := humanLemmaLabel env declName
    let st ← get
    let (opener, st') := st.pickOpener .justification
    set st'
    -- Avoid the "restatement reflex": at the root conclusion, never re-quote the whole theorem!
    let content : Array Inline ←
      if ctx.atRootConclusion then
        if isCoreOrMathlib declName then
          pure #[.text s!"The claim follows directly by {label}."]
        else if premiseNodes.isEmpty then
          pure #[.text "The claim follows from ", .emph label, .text "."]
        else
          pure #[.text "Applying ", .emph label, .text " to the checked premises establishes the claim."]
      else
        let conclInl ← renderProposition ctx.tbl expected
        if isCoreOrMathlib declName then
          pure (#[.text s!"{opener} {label}, "] ++ conclInl ++ #[.text "."])
        else
          pure (#[.text s!"{opener} ", .emph label, .text ", "] ++ conclInl ++ #[.text "."])
    return #[.step s!"app-{declName}-{fuel}" content allChildren (some goal)
      diagHtml (some declName.toString) isWrap]

  -- 7. Fallback: checked goal statement
  let goal ← buildGoalState ctx.tbl expected
  let conclInl ← renderProposition ctx.tbl expected
  return #[.step s!"step-{fuel}" (#[.text "We obtain "] ++ conclInl ++ #[.text "."]) #[] (some goal)]

/-- Collect the exact axiom footprint of a declaration (`propext`, `Classical.choice`,
`Quot.sound`, flagging any `sorryAx`). -/
def auditAxioms (declName : Name) : MetaM AxiomAudit := do
  let axioms ← Lean.collectAxioms declName
  let names := axioms.map (·.toString)
  let hasSorry := axioms.contains ``sorryAx
  return { axioms := names, hasSorry }

/-- Collect all math LaTeX strings inside an array of `Inline`s and `ProofNode`s so we know
which proof-only definitions actually appear visibly in the informalized document. -/
private partial def collectProofNodeMath : ProofNode → Array String
  | .step _ content children _ _ _ _ _ =>
      let own := content.filterMap fun
        | .inlineMath s => some s
        | .displayMath s _ => some s
        | .symbol _ d true => some d
        | _ => none
      own ++ children.flatMap collectProofNodeMath
  | .calcChain _ intro steps _ _ =>
      let introM := intro.filterMap fun
        | .inlineMath s => some s
        | .displayMath s _ => some s
        | .symbol _ d true => some d
        | _ => none
      let stepM := steps.flatMap fun (cs, ch) =>
        let r := cs.reason.filterMap fun
          | .inlineMath s => some s
          | .displayMath s _ => some s
          | .symbol _ d true => some d
          | _ => none
        #[cs.lhsLatex, cs.relationLatex, cs.rhsLatex] ++ r ++ ch.flatMap collectProofNodeMath
      introM ++ stepM
  | .routineReceipt _ _ _ details _ => details.flatMap collectProofNodeMath
  | .flowNote _ _ _ => #[]
  | .figure _ caption _ =>
      caption.filterMap fun
        | .inlineMath s => some s
        | .displayMath s _ => some s
        | .symbol _ d true => some d
        | _ => none

/-- Collect distinct `originDecl` names appearing anywhere in a `ProofNode` tree. -/
private partial def collectOriginDecls : ProofNode → Array Name
  | .step _ _ children _ _ origin? _ _ =>
      let own := match origin? with | some s => #[s.toName] | none => #[]
      own ++ children.flatMap collectOriginDecls
  | .calcChain _ _ steps _ origin? =>
      let own := match origin? with | some s => #[s.toName] | none => #[]
      own ++ steps.flatMap fun (_, ch) => ch.flatMap collectOriginDecls
  | .routineReceipt _ _ _ details _ => details.flatMap collectOriginDecls
  | _ => #[]

/-- Check whether `disp` appears as a rendered math token inside `mathSegs`. -/
private def mathDispAppearsIn (mathSegs : Array String) (disp : String) : Bool :=
  if disp.isEmpty then false
  else if disp.length ≥ 2 then
    mathSegs.any fun seg => (seg.splitOn disp).length > 1
  else
    let ch := disp.toList.head!
    mathSegs.any fun seg =>
      let chars := seg.toList
      let rec check (prevAlpha : Bool) : List Char → Bool
        | [] => false
        | c :: rest =>
            let nextAlpha := match rest with | d :: _ => d.isAlpha | [] => false
            if c == ch && !prevAlpha && !nextAlpha then true
            else check (c.isAlpha || c == '\\') rest
      check false chars

/-- Top-level entry point with optional section-fixed context hoisting:
informalizes a checked Lean declaration into an `Explanation.Entry` (with scoped local
shorthands & parameter inspectors) plus all referenced constant `SymbolInspector`s. -/
def informalizeDeclarationWithContext (declName : Name) (config : Config := {})
    (hoisted? : Option HoistedContext := none) : MetaM (Entry × Array SymbolInspector) := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "informalize: declaration `{declName}` not found in environment"
  let ov := getOverlay env declName
  let tbl := buildSymbolTable env declName
  let parsed ← parseTheoremStatement tbl info.type hoisted?
  let diagHtml ← (← diagramHookRef.get) info.type
  let header := match ov.entryKind? with
    | some k => k
    | none =>
      match info with
      | .thmInfo _ => "Theorem"
      | .defnInfo _ => "Definition"
      | _ => "Declaration"
  let mut proofNodes : Array ProofNode := #[]
  if let some fb := ov.flowBefore? then
    proofNodes := proofNodes.push (.flowNote s!"doc-flow-pre-{declName}" fb "inline")
  let proofBody? : Option Expr :=
    match info with
    | .thmInfo tinfo => some tinfo.value
    | _ => none
  if let .thmInfo tinfo := info then
    let ctx : DecompCtx := {
      config
      tbl
      seenDecls := ({} : NameSet).insert declName
      lemmaDepth := 0
      atRootConclusion := true
    }
    let (nodes, _) ← (decompileProof ctx info.type tinfo.value config.maxTermFuel).run {}
    proofNodes := dedupSiblings (proofNodes ++ nodes)
  if let some fa := ov.flowAfter? then
    proofNodes := proofNodes.push (.flowNote s!"doc-flow-post-{declName}" fa "inline")
  let hoistedSyms := match hoisted? with
    | some h => h.paramSyms
    | none => {}
  let originDecls := proofNodes.flatMap collectOriginDecls
  let (localParamInspectors, typeConstInspectors, proofConstInspectors) ←
    (← scopedInspectorCollectorRef.get) tbl declName info.type proofBody? hoistedSyms originDecls
  let shorthandInspectors : Array SymbolInspector :=
    parsed.localShorthands.map fun sh => {
      key := s!"local:{declName}:{sh.sym}"
      display := sh.sym
      kind := .localShorthand s!"{sh.sym} = {sh.rhsLatex}" sh.roleDescription
      leanName? := none
      leanType := sh.leanType
      roleBadge? := some "local shorthand"
    }
  let localInspectors := localParamInspectors ++ shorthandInspectors
  let statementMath : Array String := parsed.paragraphs.flatMap fun para =>
    para.filterMap fun
      | .inlineMath s => some s
      | .displayMath s _ => some s
      | .symbol _ d true => some d
      | _ => none
  let allMathSegs := statementMath ++ proofNodes.flatMap collectProofNodeMath
  let mut seenConstKeys : Std.HashSet String := {}
  let mut constInspectors : Array SymbolInspector := #[]
  for ins in typeConstInspectors do
    if !seenConstKeys.contains ins.key then
      seenConstKeys := seenConstKeys.insert ins.key
      constInspectors := constInspectors.push ins
  for ins in proofConstInspectors do
    if !seenConstKeys.contains ins.key && mathDispAppearsIn allMathSegs ins.display then
      seenConstKeys := seenConstKeys.insert ins.key
      constInspectors := constInspectors.push ins
  let axioms ← auditAxioms declName
  let referencedKeys := constInspectors.map (·.key)
  let entry : Entry := {
    header
    title? := ov.title? <|> some (humanLemmaLabel env declName)
    declaration := declName.toString
    sectionTitle? := ov.sectionTitle?
    sectionIntro? := ov.sectionIntro?
    sectionId? := hoisted?.bind (·.sectionId?)
    ambient? := parsed.ambient?
    statement := parsed.paragraphs
    localInspectors
    referencedKeys
    diagramHtml? := diagHtml
    proof := proofNodes
    axioms
  }
  return (entry, constInspectors)

/-- Informalize a single standalone checked Lean declaration (no section hoisting). -/
def informalizeDeclaration (declName : Name) (config : Config := {}) :
    MetaM (Entry × Array SymbolInspector) :=
  informalizeDeclarationWithContext declName config none

end Informalization.Core.ProofGraph
