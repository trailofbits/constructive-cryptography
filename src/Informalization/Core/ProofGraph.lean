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

initialize ruleExplainersRef : IO.Ref (Array RuleExplainer) ← IO.mkRef #[]

def registerRuleExplainer (e : RuleExplainer) : IO Unit :=
  ruleExplainersRef.modify fun arr =>
    (arr.push e).qsort fun a b => a.priority > b.priority

def registerDiagramHook (f : Expr → MetaM (Option String)) : IO Unit :=
  diagramHookRef.set f

def registerInspectorCollector (f : SymbolTable → Expr → MetaM (Array SymbolInspector)) : IO Unit :=
  inspectorCollectorRef.set f

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
  | some t => t
  | none =>
      let short := shortConstName declName
      short.replace "_" " "

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

/-- Deduplicate adjacent/repeated identical sibling proof nodes (preventing the 15× spam bug). -/
private def dedupSiblings (nodes : Array ProofNode) : Array ProofNode := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array ProofNode := #[]
  for n in nodes do
    let key := String.intercalate "|" (n.collectAllText.toList)
    if !key.isEmpty && seen.contains key then
      continue
    seen := seen.insert key
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
        -- Local intermediate fact (`have h : P := ...`) -> visible Maurer proof step!
        let factNodes ← decompileProof ctx ty val (fuel - 1)
        let goal ← buildGoalState ctx.tbl ty
        let factInl ← renderProposition ctx.tbl ty
        let st ← get
        let (opener, st') := st.pickOpener .consequence
        set st'
        let headerStep : ProofNode :=
          .step s!"have-{fuel}"
            (#[.text s!"{opener} "] ++ factInl ++ #[.text "."])
            factNodes (some goal)
        let rest ← withLetDecl nm ty val fun fv =>
          decompileProof ctx expected (body.instantiate1 fv) (fuel - 1)
        return dedupSiblings (#[headerStep] ++ rest)
      else
        return ← withLetDecl nm ty val fun fv =>
          decompileProof ctx expected (body.instantiate1 fv) (fuel - 1)
  | _, _ => pure ()

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
    for (ap, aty) in pArgs do
      let sub ← decompileProof ctx aty ap (fuel - 1)
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
    let conclInl ← renderProposition ctx.tbl expected
    let goal ← buildGoalState ctx.tbl expected
    let diagHtml ← (← diagramHookRef.get) expected
    let label := humanLemmaLabel env declName
    let st ← get
    let (opener, st') := st.pickOpener .justification
    set st'
    let content : Array Inline :=
      if isCoreOrMathlib declName then
        #[.text s!"{opener} {label}, "] ++ conclInl ++ #[.text "."]
      else
        #[.text s!"{opener} ", .emph label, .text ", "] ++ conclInl ++ #[.text "."]
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

/-- Top-level entry point: informalize a checked Lean declaration into an `Explanation.Entry`
plus all collected type-aware `SymbolInspector`s. -/
def informalizeDeclaration (declName : Name) (config : Config := {}) :
    MetaM (Entry × Array SymbolInspector) := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "informalize: declaration `{declName}` not found in environment"
  let ov := getOverlay env declName
  let tbl := buildSymbolTable env declName
  let parsed ← parseTheoremStatement tbl info.type
  let diagHtml ← (← diagramHookRef.get) info.type
  let inspectors ← (← inspectorCollectorRef.get) tbl info.type
  let header := match info with
    | .thmInfo _ => "Theorem"
    | .defnInfo _ => "Definition"
    | _ => "Declaration"
  let mut proofNodes : Array ProofNode := #[]
  if let some fb := ov.flowBefore? then
    proofNodes := proofNodes.push (.flowNote s!"doc-flow-pre-{declName}" fb "inline")
  if let .thmInfo tinfo := info then
    let ctx : DecompCtx := {
      config
      tbl
      seenDecls := ({} : NameSet).insert declName
      lemmaDepth := 0
    }
    let (nodes, _) ← (decompileProof ctx info.type tinfo.value config.maxTermFuel).run {}
    proofNodes := proofNodes ++ nodes
  if let some fa := ov.flowAfter? then
    proofNodes := proofNodes.push (.flowNote s!"doc-flow-post-{declName}" fa "inline")
  let axioms ← auditAxioms declName
  let entry : Entry := {
    header
    title? := ov.title? <|> some (humanLemmaLabel env declName)
    declaration := declName.toString
    ambient? := parsed.ambient?
    statement := parsed.paragraphs
    diagramHtml? := diagHtml
    proof := proofNodes
    axioms
  }
  return (entry, inspectors)

end Informalization.Core.ProofGraph
