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
  docDecls : NameSet := {}
  lemmaDepth : Nat := 0
  /-- Most recently introduced `have` fact (for causal vs. independent discourse transitions). -/
  lastFactFVar? : Option FVarId := none
  /-- Count of sequential `have` steps at the current block level. -/
  factIndex : Nat := 0
  /-- True when proving the top-level theorem conclusion (suppresses verbatim restatement). -/
  atRootConclusion : Bool := true
  /-- True when the next emitted sentence will be the very first sentence of the proof. -/
  isProofStart : Bool := true
  /-- Free variables peeled along leading lambdas (for instantiating `theoremNotations`). -/
  peeledFVars : Array Expr := #[]
  /-- Declaration-level `informal_theorem_notation` entries `(nBinders, closedPat, latex, gloss?)`. -/
  pendingNotations : Array (Nat × Expr × String × Option String) := #[]
  /-- True once `It_suffices_to_show` / `By ... it suffices to show` reduced the root conclusion. -/
  isClosingGoal : Bool := false

/-- Per-declaration collector for proof-local notation & hybrid/game/adversary hover inspectors. -/
initialize extraNotationInspectorsRef : IO.Ref (Array SymbolInspector) ← IO.mkRef #[]

def registerProofNotationInspector (ins : SymbolInspector) : IO Unit :=
  extraNotationInspectorsRef.modify fun arr =>
    if arr.any (fun x => x.display == ins.display && x.key == ins.key) then arr
    else arr.push ins

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
initialize diagramHookRef : IO.Ref (SymbolTable → Expr → MetaM (Option String)) ←
  IO.mkRef (fun _ _ => pure none)

/-- Optional hook to clear per-declaration diagram caches when starting a new declaration. -/
initialize clearDiagramCacheHookRef : IO.Ref (IO Unit) ←
  IO.mkRef (pure ())

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

def registerDiagramHook (f : SymbolTable → Expr → MetaM (Option String)) : IO Unit :=
  diagramHookRef.set f

def registerClearDiagramCacheHook (f : IO Unit) : IO Unit :=
  clearDiagramCacheHookRef.set f

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

/-- Fast O(1) syntactic check whether `ty` is a Lean/Mathlib/CC typeclass (`Prop`-valued
or `Type`-valued), including quantified instances, without running `whnf`/`isClass?`. -/
def isTypeclassProp (ty : Expr) : MetaM Bool := do
  let env ← getEnv
  let rec headExpr : Expr → Expr
    | .forallE _ _ b _ => headExpr b
    | .mdata _ b => headExpr b
    | e => e
  let checkHead (e : Expr) : Bool :=
    match e.getAppFn.consumeMData with
    | .const cn _ => ambientTypeclassHeads.contains cn || Lean.isClass env cn
    | _ => false
  return checkHead ty || checkHead (headExpr ty)

/-- Fast binder-driven extractor for non-typeclass proof-valued arguments `(arg, propType)`.
Walks `fn`'s type telescope first so huge `Fintype` / automaton data arguments never trigger
redundant kernel `inferType` checks. -/
private def fastProofValuedArgs (term : Expr) : MetaM (Array (Expr × Expr)) := do
  let args := term.getAppArgs
  if args.isEmpty then return #[]
  let fn := term.getAppFn.consumeMData
  let fnTy? : Option Expr ← match fn with
    | .const cn levels =>
        try
          let info ← getConstInfo cn
          pure <| some (if levels.length == info.levelParams.length
            then info.type.instantiateLevelParams info.levelParams levels
            else info.type)
        catch _ => pure none
    | .fvar id =>
        try pure <| some (← id.getDecl).type
        catch _ => pure none
    | _ => pure none
  let mut out : Array (Expr × Expr) := #[]
  match fnTy? with
  | some initTy =>
      let mut curTy := initTy
      for idx in [:args.size] do
        let arg := args[idx]!
        let tyStep? ← match curTy.consumeMData with
          | f@(.forallE ..) => pure (some f)
          | other =>
              let w ← try withTransparency .reducible (whnf other) catch _ => pure other
              match w.consumeMData with
              | f@(.forallE ..) => pure (some f)
              | _ => pure none
        match tyStep? with
        | some (.forallE _ dom body bi) =>
            if bi != .instImplicit then
              let isP ← try isProp dom catch _ => pure false
              if isP && !(← isTypeclassProp dom) then
                out := out.push (arg, dom)
            curTy := body.instantiate1 arg
        | _ =>
            for j in [idx:args.size] do
              let a := args[j]!
              try
                let ty ← inferType a
                if (← isProp ty) && !(← isTypeclassProp ty) then
                  out := out.push (a, ty)
              catch _ => pure ()
            return out
      return out
  | none =>
      for arg in args do
        try
          let ty ← inferType arg
          if (← isProp ty) && !(← isTypeclassProp ty) then
            out := out.push (arg, ty)
        catch _ => pure ()
      return out

/-- Detect if a proof term is a transitivity step (from `calc`, `cc_calc`, `Eq.trans`,
`LE.le.trans`, `le_trans`, `Trans.trans`, or `SubstitutesWithin.trans`) and split it into its two
checked sub-proofs `(leftProof, leftType, rightProof, rightType)`. -/
private def splitTransProof? (proof : Expr) :
    MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let fn := proof.getAppFn.consumeMData
  let some head := fn.constName? | return none
  let isTrans :=
    head == ``Eq.trans || head == `LE.le.trans || head == `LT.lt.trans ||
    head == `le_trans || head == `lt_trans ||
    head == ``Trans.trans || head == `LE.le.trans_eq || head == `Eq.trans_le ||
    head.toString.endsWith ".trans" || head.toString.endsWith ".trans_eq" ||
    head.toString.endsWith "substitutesWithin_trans" ||
    head.toString.endsWith "substitutesWithin_of_eq_left" ||
    head.toString.endsWith "substitutesWithin_of_eq_right"
  if !isTrans then return none
  let proofArgs ← fastProofValuedArgs proof
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

private def isNeverExpandedConst (declName : Name) : Bool :=
  let s := declName.toString
  let short := shortConstName declName
  s.endsWith ".ext" || s.endsWith ".ext_iff" || s.endsWith ".casesOn" ||
  s.endsWith ".rec" || s.endsWith ".recOn" ||
  s.startsWith "congr" || short == "ext" ||
  declName == ``funext || declName == ``propext || declName == ``Subtype.ext ||
  declName == ``Quotient.sound || declName == ``Exists.intro ||
  declName == ``False.elim || declName == ``absurd ||
  declName == ``Or.elim || declName == ``Or.inl || declName == ``Or.inr ||
  declName == ``Eq.rec || declName == ``Eq.ndrec || declName == `Eq.drec ||
  declName == `of_eq_true || declName == `eq_self ||
  declName == ``Eq.refl || declName == ``rfl

/-- Should we recurse into project lemma `declName`'s body?
In legacy non-Spine mode, do NOT recursively expand `private` declarations unless explicitly
marked `informal_joint`, preventing exponential blowup on SHA-3 helper DAGs while still citing
the private lemma cleanly by name instead of swallowing it as routine. -/
private def shouldExpandLemma (env : Environment) (ctx : DecompCtx) (declName : Name) : Bool :=
  let expandAttr := Informalization.Core.Presentation.isInformalExpand env declName
  if ctx.lemmaDepth ≥ ctx.config.maxLemmaDepth then false
  else if ctx.seenDecls.contains declName then false
  else if ctx.docDecls.contains declName then false
  else if ctx.lemmaDepth ≥ 1 && effectiveIsProofJoint env declName && !expandAttr then false
  else if declName == ``sorryAx then false
  else if isCoreOrMathlibIn env declName then false
  else if isNeverExpandedConst declName then false
  else if effectiveIsOpaqueLeaf env declName && !expandAttr then false
  else if Lean.isPrivateName declName && !effectiveIsProofJoint env declName && !expandAttr then false
  else if expandAttr then
    match env.find? declName with
    | some (.thmInfo _) => true
    | _ => false
  else if ctx.config.projectNamespaces.isEmpty then
    match env.find? declName with
    | some (.thmInfo _) => true
    | _ => false
  else
    ctx.config.projectNamespaces.any (fun p => p.isPrefixOf declName)

/-- Extract all non-typeclass proof-valued arguments `(arg, propType)` of an application `f a₁ … aₙ`. -/
def proofValuedArgs (term : Expr) : MetaM (Array (Expr × Expr)) :=
  fastProofValuedArgs term

/-- If `e` is a bare local hypothesis `.fvar id` (possibly wrapped in `Expr.mdata`,
a constant unused lambda `fun _ => h`, or a trivial cast `Eq.mp`/`Eq.mpr`/`Iff.mp`/`Iff.mpr`/`id`/`of_eq_true`),
return `some id`. -/
def unwrapHypothesisFVar? : Expr → Option FVarId
  | .mdata _ inner => unwrapHypothesisFVar? inner
  | .fvar id => some id
  | .lam _ _ b _ => if !b.hasLooseBVar 0 then unwrapHypothesisFVar? b else none
  | .app fn inner =>
      match fn.getAppFn.consumeMData with
      | .const head _ =>
          if head == ``Eq.mp || head == ``Eq.mpr || head == ``Iff.mp ||
             head == ``Iff.mpr || head == ``id || head == `of_eq_true then
            unwrapHypothesisFVar? inner
          else none
      | _ => none
  | _ => none

/-- Render a direct hypothesis `.fvar id` using its mathematical content (when concise) rather
than printing an unintroduced Lean identifier (`hk`, `hR`, `this`, `hp`, `hred`). -/
def renderHypothesisStep (tbl : SymbolTable) (expected : Expr) (id : FVarId)
    (nodeId : String) (isWrap : Bool := false) (onlyUsed : Bool := false) : MetaM ProofNode := do
  let decl ← id.getDecl
  let goal? ← if isWrap then pure none else some <$> buildGoalState tbl expected onlyUsed
  let hypInl ← renderProposition tbl decl.type
  let hypLen := (inlinesCanonicalKey hypInl).length
  let head := decl.type.getAppFn.consumeMData
  let content : Array Inline :=
    if hypLen > 0 && hypLen ≤ 60 then
      if head.isConstOf ``LE.le || head.isConstOf ``LT.lt then
        #[.text "This holds by the assumed bound "] ++ hypInl ++ #[.text "."]
      else
        #[.text "This holds by the assumption that "] ++ hypInl ++ #[.text "."]
    else
      #[.text "This holds by the assumed hypothesis."]
  return .step nodeId content #[] goal? none none isWrap false

/-- Decompile every non-typeclass proof-valued argument of `proof`, marking trivial bare
hypothesis-passthroughs with `isWrapper := true` so Paper mode stays clean while Auditor mode
retains every premise edge. -/
def decompilePremiseArgs (ctx : DecompCtx) (decompileChild : DecompileChild)
    (proof : Expr) : StateRefT DiscourseState MetaM (Array ProofNode) := do
  let pArgs ← proofValuedArgs proof
  let subCtx := { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
  let mut out : Array ProofNode := #[]
  for idx in [:pArgs.size] do
    let (ap, aty) := pArgs[idx]!
    if let some fvid := unwrapHypothesisFVar? ap then
      let node ← renderHypothesisStep ctx.tbl aty fvid s!"hyp-prem-{idx}-{fvid.name}-{aty.hash}"
        (isWrap := true) (onlyUsed := (ctx.lemmaDepth ≥ 1))
      out := out.push node
    else
      let sub ← decompileChild subCtx aty ap
      out := out ++ sub
  return out

private def cryptoAcronyms : List (String × String) :=
  [ ("prg", "PRG"), ("aead", "AEAD"), ("ind", "IND"), ("cca", "CCA"),
    ("cpa", "CPA"), ("ptxt", "PTXT"), ("ctxt", "CTXT"), ("int", "INT"),
    ("mbo", "MBO"), ("mac", "MAC"), ("sha3", "SHA-3"), ("sha", "SHA"),
    ("urf", "URF"), ("urp", "URP"), ("prf", "PRF"), ("cc", "CC"),
    ("cr", "CR"), ("pdg", "PDG"), ("pds", "PDS"), ("dde", "DDE"),
    ("ddd", "DDD"), ("dsl", "DSL"), ("iv", "IV"), ("h", "H") ]

private def minorTitleWords : List String :=
  [ "of", "from", "and", "or", "via", "by", "for", "in", "to", "on", "with", "as", "the", "a", "an" ]

private def splitCamelCaseToken (tok : String) : List String := Id.run do
  let chars := tok.toList
  if chars.isEmpty then return []
  let mut words : Array String := #[]
  let mut cur : Array Char := #[]
  for i in [:chars.length] do
    let c := chars[i]!
    let prev? := if i > 0 then some chars[i - 1]! else none
    let next? := if i + 1 < chars.length then some chars[i + 1]! else none
    let isBoundary := match prev?, next? with
      | some p, some n => (p.isLower && c.isUpper) || (p.isUpper && c.isUpper && n.isLower)
      | some p, none => p.isLower && c.isUpper
      | _, _ => false
    if isBoundary && !cur.isEmpty then
      words := words.push (String.ofList cur.toList)
      cur := #[c]
    else
      cur := cur.push c
  if !cur.isEmpty then
    words := words.push (String.ofList cur.toList)
  return words.toList

private def humanizeDeclWords (declName : Name) : List String :=
  let short0 := shortConstName declName
  let short :=
    if short0.endsWith "_verbose" then (short0.dropEnd 8).toString
    else if short0.endsWith "Verbose" then (short0.dropEnd 7).toString
    else short0
  let rawTokens := (short.replace "_" " ").splitOn " " |>.filter (!·.isEmpty)
  rawTokens.flatMap splitCamelCaseToken

/-- Format an inline human label for a cited theorem/lemma name (respecting `informal_title`
overlay if present, otherwise splitting camelCase/underscores cleanly). -/
def humanLemmaLabel (env : Environment) (declName : Name) : String :=
  match (getOverlay env declName).title? with
  | some t => t.trimAscii.toString
  | none =>
      let words := humanizeDeclWords declName |>.map fun w =>
        let low := w.toLower
        match cryptoAcronyms.find? (·.1 == low) with
        | some (_, acr) => acr
        | none => low
      let raw := String.intercalate " " words
      raw.replace "transcript distance" "distinguishing advantage"
         |>.replace "distinguishing distance" "distinguishing advantage"

/-- Format a Title-Cased fallback entry/document title for a declaration (respecting
`informal_title`, stripping `_verbose`, splitting camelCase, and preserving acronyms). -/
def humanDeclarationTitle (env : Environment) (declName : Name) : String :=
  match (getOverlay env declName).title? with
  | some t => t.trimAscii.toString
  | none =>
      let words := humanizeDeclWords declName
      let formatted := words.mapIdx fun idx w =>
        let low := w.toLower
        match cryptoAcronyms.find? (·.1 == low) with
        | some (_, acr) => acr
        | none =>
            if idx > 0 && minorTitleWords.contains low then low
            else capitalizeFirst w
      let raw := String.intercalate " " formatted
      raw.replace "Transcript Distance" "Distinguishing Advantage"
         |>.replace "Distinguishing Distance" "Distinguishing Advantage"
         |>.replace "transcript distance" "distinguishing advantage"
         |>.replace "distinguishing distance" "distinguishing advantage"

/-- Beta-instantiate a called theorem's `type` and `value` with the caller's actual `args`
(and universe levels), so expanded sub-proofs always use the caller's exact symbols.
Returns `none` if `info.value` lacks matching leading lambdas for `args`. -/
private partial def betaInstantiateTheorem (info : TheoremVal) (levels : List Level)
    (args : Array Expr) : MetaM (Option (Expr × Expr)) := do
  let ty0 :=
    if levels.length == info.levelParams.length then
      info.type.instantiateLevelParams info.levelParams levels
    else info.type
  let val0 :=
    if levels.length == info.levelParams.length then
      info.value.instantiateLevelParams info.levelParams levels
    else info.value
  let rec go (i : Nat) (ty val : Expr) : MetaM (Option (Expr × Expr)) := do
    if h : i < args.size then
      match val.consumeMData with
      | .lam _ _ vbody _ =>
          let tyW ← match ty.consumeMData with
            | .forallE .. => pure ty.consumeMData
            | _ =>
                let r ← withTransparency .reducible (whnf ty)
                if r.consumeMData.isForall then pure r else whnfD ty
          match tyW with
          | .forallE _ _ tbody _ =>
              let a := args[i]
              go (i + 1) (tbody.instantiate1 a) (vbody.instantiate1 a)
          | _ => return none
      | _ => return none
    else
      return some (ty, val)
  go 0 ty0 val0

/-- Heuristic detector for trivial 1-step forwarding/cast wrapper lemmas so Paper mode can
auto-inline them cleanly (while Auditor mode still shows them). -/
private def isTrivialWrapperBody (env : Environment) (declName : Name) (body : Expr) : Bool :=
  if effectiveIsProofJoint env declName then false
  else if effectiveIsWrapper env declName then true
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
        (!isCoreOrMathlibIn env head && core.getAppArgs.size ≤ 16)
    | _ => false

/-- Cap `diagramHtml?` emission on `ProofNode`s at nesting `depth ≤ maxDepth` (default `1`)
so deeply nested child trees never duplicate multi-MB diagram HTML payloads. -/
private partial def capDiagramHtmlDepth (maxDepth : Nat := 1) : Nat → ProofNode → ProofNode
  | depth, .step id content children goal? diag origin isWrap defExp sp lh tr im =>
      let keepDiag := if depth ≤ maxDepth then diag else none
      .step id content (children.map (capDiagramHtmlDepth maxDepth (depth + 1)))
        goal? keepDiag origin isWrap defExp sp lh tr im
  | depth, .calcChain id intro steps goal? origin =>
      let keepStep (s : CalcStep) : CalcStep :=
        if depth ≤ maxDepth then s else { s with diagramHtml? := none }
      let nextSteps := steps.map fun (s, ch) =>
        (keepStep s, ch.map (capDiagramHtmlDepth maxDepth (depth + 1)))
      .calcChain id intro nextSteps goal? origin
  | depth, .routineReceipt id summary count details goal? =>
      .routineReceipt id summary count
        (details.map (capDiagramHtmlDepth maxDepth (depth + 1))) goal?
  | _, other => other

/-- Recursively deduplicate repeated identical sibling proof nodes (preventing 15× spam)
and coalesce duplicate `routineReceipt` siblings of the same kind into one counted receipt
at every level of the proof tree, including nodes built by domain `RuleExplainer`s. -/
private partial def dedupSiblings (nodes : Array ProofNode) : Array ProofNode := Id.run do
  let rec cleanNode : ProofNode → ProofNode
    | .step id content children goal? diag origin isWrap defExp sp lh tr im =>
        .step id content (dedupSiblings children) goal? diag origin isWrap defExp sp lh tr im
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
          | .step _ content _ _ _ _ _ _ _ _ _ _ =>
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

/-- Collect all math LaTeX strings inside an array of `Inline`s and `ProofNode`s so we know
which proof-only definitions or bound variables actually appear visibly in the document. -/
private partial def collectProofNodeMath : ProofNode → Array String
  | .step _ content children _ _ _ _ _ _ _ _ _ =>
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
  | .pseudocodeBox _ _ _ lines _ _ =>
      lines.flatMap fun l => l.inlines.filterMap fun
        | .inlineMath s => some s
        | .displayMath s _ => some s
        | .symbol _ d true => some d
        | _ => none

private def normalizeMathToken (s : String) : String :=
  let words := (s.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty)
  let joined := (String.intercalate " " words).trimAscii.toString
  if joined.endsWith "." || joined.endsWith "," then
    (joined.dropEnd 1).toString.trimAscii.toString
  else
    joined

private def extractNormalizedMath (inls : Array Inline) : Array String :=
  inls.filterMap fun
    | .inlineMath s =>
        let n := normalizeMathToken s
        if n.isEmpty then none else some n
    | .displayMath s _ =>
        let n := normalizeMathToken s
        if n.isEmpty then none else some n
    | .symbol _ d true =>
        let n := normalizeMathToken d
        if n.isEmpty then none else some n
    | _ => none

private def normalizeProseForComparison (inls : Array Inline) : String := Id.run do
  let raw := String.intercalate "" (inls.toList.map Inline.collectText)
  let words := (raw.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty)
  let stripTrailingPunct (x : String) : String :=
    let x := x.trimAscii.toString
    if x.endsWith "." || x.endsWith "," || x.endsWith ";" || x.endsWith ":" then
      (x.dropEnd 1).toString.trimAscii.toString
    else x
  let mut s := stripTrailingPunct ((String.intercalate " " words).trimAscii.toString.toLower)
  let prefixes := [
    "we obtain ", "we claim that ", "we claim ", "next, we claim that ", "next, we claim ",
    "first, observe that ", "moreover, note that ", "therefore, ", "hence, ", "thus, ",
    "consequently, ", "accordingly, ", "from this, ", "combining the preceding bounds, ",
    "since the assumption holds, ", "by non-expansion, ", "by monotonicity, ",
    "by extensionality, ", "by function extensionality, ", "unpacking the hypothesis yields "
  ]
  for _ in [:2] do
    let mut matched := false
    for p in prefixes do
      if s.startsWith p then
        s := (s.drop p.length).toString.trimAscii.toString
        matched := true
        break
    if !matched && s.startsWith "by " then
      let commaParts := s.splitOn ", "
      if commaParts.length ≥ 2 then
        let headPart := commaParts.headD ""
        if !headPart.contains '$' && !headPart.contains '\\' then
          s := (String.intercalate ", " (commaParts.drop 1)).trimAscii.toString
  return stripTrailingPunct s

private def isBareSingleSentenceRestatement (parentContent childContent : Array Inline) : Bool := Id.run do
  let proseOnly := (String.intercalate "" (childContent.toList.filterMap fun
    | .text t => some t
    | .emph t => some t
    | _ => none)).trimAscii.toString
  if (proseOnly.splitOn ". ").length > 1 then
    return false
  let childRawWords :=
    ((String.intercalate "" (childContent.toList.map Inline.collectText)).replace "\n" " ").splitOn " "
      |>.filter (!·.isEmpty)
  let childLow := (String.intercalate " " childRawWords).trimAscii.toString.toLower
  if childLow.startsWith "this holds by the assumed " then
    return true
  let parentMath := extractNormalizedMath parentContent
  let childMath := extractNormalizedMath childContent
  let allChildMathInParent := childMath.all fun cm =>
    parentMath.any fun pm => pm == cm || (cm.length ≥ 4 && (pm.splitOn cm).length > 1)
  if !allChildMathInParent then
    return false
  let childNorm := normalizeProseForComparison childContent
  let parentNorm := normalizeProseForComparison parentContent
  if !childNorm.isEmpty && childNorm == parentNorm then
    return true
  if childLow.startsWith "the claim follows from " ||
     childLow.startsWith "the claim follows directly by " then
    return true
  if childLow.startsWith "we obtain " || childLow.startsWith "therefore, " ||
     childLow.startsWith "hence, " || childLow.startsWith "thus, " then
    return !childMath.isEmpty
  if childLow.startsWith "proceeding by " then
    return !childMath.isEmpty
  if childLow.startsWith "by " || childLow.startsWith "from " then
    let commaParts := childLow.splitOn ", "
    if commaParts.length ≥ 2 then
      if !childMath.isEmpty then return true
      let rhsNorm := normalizeProseForComparison #[.text (String.intercalate ", " (commaParts.drop 1))]
      if !rhsNorm.isEmpty && (rhsNorm == parentNorm || (parentNorm.splitOn rhsNorm).length > 1) then
        return true
  return false

/-- Eliminate tautological 1-child `⊕` leaves whose single child merely restates the parent's
claim or formula without introducing new mathematics, diagrams, or sub-children, while
preserving `origin? := origin? <|> cOrigin?` provenance. -/
partial def collapseTautologicalSingleChild : ProofNode → ProofNode
  | .step id content children goal? diag? origin? isWrap defExp startsPara leadHead? trust? inlineMeta =>
      let children' := children.map collapseTautologicalSingleChild
      let collapsed :=
        if !isWrap && children'.size == 1 then
          match children'[0]! with
          | c@(.step _ cContent cChildren _ cDiag? cOrigin? _ _ _ _ _ _) =>
              let hasSorry := c.collectAllText.any fun t => (t.splitOn "[UNPROVED: sorry]").length > 1
              if cChildren.isEmpty && cDiag?.isNone && !hasSorry &&
                 isBareSingleSentenceRestatement content cContent then
                some cOrigin?
              else
                none
          | _ => none
        else
          none
      match collapsed with
      | some cOrigin? =>
          .step id content #[] goal? diag? (origin? <|> cOrigin?) isWrap defExp startsPara leadHead? trust? inlineMeta
      | none =>
          .step id content children' goal? diag? origin? isWrap defExp startsPara leadHead? trust? inlineMeta
  | .calcChain id intro steps goal? origin? =>
      .calcChain id intro (steps.map fun (cs, ch) => (cs, ch.map collapseTautologicalSingleChild)) goal? origin?
  | .routineReceipt id summary count details goal? =>
      .routineReceipt id summary count (details.map collapseTautologicalSingleChild) goal?
  | other => other

private def isStructuralCongrOrCast (head : Name) : Bool :=
  let s := head.toString
  isCompilerAuxDecl head ||
  head == ``congrArg || head == ``congrFun || head == `congrFun' || head == ``congr ||
  head == ``propext || head == `eq_self || head == ``Eq.refl || head == ``rfl ||
  head == ``Eq.subst || head == ``Eq.symm ||
  head == ``Eq.ndrec || head == ``Eq.rec || head == `Eq.drec ||
  head == `eq_iff_iff || head == `and_congr || head == `and_congr_left ||
  head == `and_congr_right || head == `and_congr_left_eq || head == `and_congr_right_eq ||
  head == `or_congr || head == `or_congr_left || head == `or_congr_right ||
  head == `imp_congr || head == `imp_congr_left || head == `imp_congr_right ||
  head == `imp_congr_ctx || head == `iff_congr || head == `forall_congr ||
  head == `forall_congr' || head == `exists_congr || head == `not_congr ||
  s.endsWith "_congr" || s.endsWith "_congr_left" || s.endsWith "_congr_right"

/-- Unwrap transparent kernel cast/transport wrappers (`Eq.mp`, `Eq.mpr`, `Iff.mp`, `Iff.mpr`,
`Eq.rec`, `Eq.ndrec`, `id`, `of_eq_true`, `mdata`, unused lambdas) to expose the underlying proof head. -/
private partial def unwrapCastProof (e : Expr) (fuel : Nat := 16) : Expr :=
  if fuel == 0 then e
  else match e with
  | .mdata _ inner => unwrapCastProof inner (fuel - 1)
  | .lam _ _ b _ => if !b.hasLooseBVar 0 then unwrapCastProof b (fuel - 1) else e
  | .app .. =>
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs
      match fn with
      | .const head _ =>
          if (head == ``Eq.mp || head == ``Eq.mpr || head == ``Iff.mp || head == ``Iff.mpr) && args.size == 4 then
            unwrapCastProof args[3]! (fuel - 1)
          else if (head == ``Eq.mp || head == ``Eq.mpr || head == ``Iff.mp || head == ``Iff.mpr) && args.size > 4 then
            unwrapCastProof ((args[3]!).beta (args.extract 4 args.size)) (fuel - 1)
          else if head == ``id && args.size == 2 then
            unwrapCastProof args[1]! (fuel - 1)
          else if head == ``id && args.size > 2 then
            unwrapCastProof ((args[1]!).beta (args.extract 2 args.size)) (fuel - 1)
          else if (head == ``Eq.rec || head == ``Eq.ndrec) && args.size ≥ 6 then
            unwrapCastProof ((args[3]!).beta (args.extract 6 args.size)) (fuel - 1)
          else if head == `of_eq_true && args.size ≥ 1 then
            unwrapCastProof args.back! (fuel - 1)
          else e
      | _ => e
  | _ => e

/-- Core recursive decompiler: `(ctx, expectedProp, proofTerm) → Array ProofNode`. -/
partial def decompileProof (ctx : DecompCtx) (expected proof : Expr)
    (fuel : Nat := 96) : StateRefT DiscourseState MetaM (Array ProofNode) := do
  if fuel == 0 then return #[]
  let expected ← instantiateMVars expected
  let proof ← instantiateMVars proof
  let env ← getEnv

  -- 0. Never render Prop-valued typeclass instances (`PosMulMono`, `AddLeftMono`, etc.)
  if ← isTypeclassProp expected then
    return #[]

  -- 1. Check domain-registered CC family explainers first
  for exp in (← ruleExplainersRef.get) do
    if let some nodes ← exp.explain ctx (fun c e p => decompileProof c e p (fuel - 1)) expected proof then
      return dedupSiblings nodes

  -- 2. Check routine algebra / casts / reflexivity (fail-closed)
  if proof.getAppFn.consumeMData.isConstOf ``sorryAx then
    let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
    return #[.step s!"sorry-{fuel}" #[.text "[UNPROVED: sorry]"] #[] (some goal)]

  if let some rkind := classifyRoutine? env proof then
    return #[.routineReceipt s!"routine-{fuel}" rkind.label 1 #[] none]

  -- 3. Unwrap leading binders (`intro`) transparently into the live `LocalContext`,
  -- avoiding macro-scoped shadow collisions (`x` -> `w'`) and introducing arbitrary variables
  -- inside subgoal universal quantifiers.
  let chooseBinderName (nm pnm : Name) : MetaM Name := do
    let base :=
      if !pnm.hasMacroScopes && (cleanBinderName? pnm).isSome then pnm
      else if (cleanBinderName? nm).isSome then nm
      else pnm
    freshShadowFreeName base "x"
  let maybePrefixIntroVar (varTex : String) (nodes : Array ProofNode) : Array ProofNode := Id.run do
    if nodes.isEmpty then return nodes
    let allMath := nodes.flatMap collectProofNodeMath
    if !mathDispAppearsIn allMath varTex then return nodes
    let pre : Array Inline := #[.text "Fix any ", .inlineMath varTex, .text ". "]
    for idx in [:nodes.size] do
      match nodes[idx]! with
      | .step id content ch goal diag orig false defExp sp lh tr im =>
          return nodes.set! idx (.step id (pre ++ content) ch goal diag orig false defExp sp lh tr im)
      | .calcChain id intro steps goal orig =>
          return nodes.set! idx (.calcChain id (pre ++ intro) steps goal orig)
      | _ => pure ()
    return nodes
  let instantiatePendingNotations (baseCtx : DecompCtx) (fv : Expr) : MetaM DecompCtx := do
    let fvs := baseCtx.peeledFVars.push fv
    let mut tbl := baseCtx.tbl
    for (nBind, closedPat, sym, _) in baseCtx.pendingNotations do
      if nBind == fvs.size then
        let instPat := closedPat.instantiateRev fvs
        if !instPat.hasLooseBVars && !instPat.hasExprMVar then
          let patNorm ← normalizeForPresentation instPat
          tbl := tbl.withExprAlias patNorm sym
    return { baseCtx with tbl, peeledFVars := fvs }
  match expected.consumeMData, proof with
  | .forallE nm dom body bi, .lam pnm _ pbody _ =>
      let useName ← chooseBinderName nm pnm
      let needIntro ←
        if !ctx.atRootConclusion && bi == .default && body.hasLooseBVar 0 then
          pure (!(← isProp dom) && !(← isAmbientTypeclass dom))
        else pure false
      return ← withLocalDecl useName bi dom fun fv => do
        let nextCtx ← instantiatePendingNotations ctx fv
        let nodes ← decompileProof nextCtx (body.instantiate1 fv) (pbody.instantiate1 fv) (fuel - 1)
        if needIntro then
          let varTex ← exprToLatex fv nextCtx.tbl
          return maybePrefixIntroVar varTex nodes
        return nodes
  | _, .mdata _ inner =>
      return ← decompileProof ctx expected inner (fuel - 1)
  | _, .lam pnm _ pbody _ =>
      let expR ← withTransparency .reducible (whnf expected.consumeMData)
      let expW ← if expR.consumeMData.isForall then pure expR else whnfD expected.consumeMData
      if let .forallE nm dom body bi := expW.consumeMData then
        let useName ← chooseBinderName nm pnm
        let needIntro ←
          if !ctx.atRootConclusion && bi == .default && body.hasLooseBVar 0 then
            pure (!(← isProp dom) && !(← isAmbientTypeclass dom))
          else pure false
        return ← withLocalDecl useName bi dom fun fv => do
          let nextCtx ← instantiatePendingNotations ctx fv
          let nodes ← decompileProof nextCtx (body.instantiate1 fv) (pbody.instantiate1 fv) (fuel - 1)
          if needIntro then
            let varTex ← exprToLatex fv nextCtx.tbl
            return maybePrefixIntroVar varTex nodes
          return nodes
      else pure ()
  | _, .letE nm ty val body _ =>
      let isP ← isProp ty
      if isP then
        -- Local intermediate fact (`have h : P := ...`): choose causal vs. parallel transition!
        let usesPrev := match ctx.lastFactFVar? with
          | some prevId => (Lean.collectFVars {} val).fvarIds.contains prevId
          | none => false
        let factNodes ← decompileProof { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false } ty val (fuel - 1)
        let goal ← buildGoalState ctx.tbl ty (ctx.lemmaDepth ≥ 1)
        let factInl ← renderProposition ctx.tbl ty
        let opener ← do
          let st ← get
          if usesPrev && !(ctx.isProofStart && ctx.factIndex == 0 && st.stepCounter == 0) then
            let (op, st') := st.pickOpener .consequence
            set st'
            pure op
          else if ctx.factIndex == 0 then
            modify (·.markEmitted (some "First,"))
            pure "First,"
          else
            let parallelOps := #["Next,", "Moreover,", "In addition,", "Similarly,"]
            let op := parallelOps[(ctx.factIndex - 1) % parallelOps.size]!
            modify (·.markEmitted (some op))
            pure op
        let headerStep : ProofNode :=
          .step s!"have-{fuel}"
            (#[.text s!"{opener} "] ++ factInl ++ #[.text "."])
            factNodes (some goal)
        let rest ← withLetDecl nm ty val fun fv =>
          let nextCtx := { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
          decompileProof nextCtx expected (body.instantiate1 fv) (fuel - 1)
        return dedupSiblings (#[headerStep] ++ rest)
      else
        return ← withLetDecl nm ty val fun fv =>
          decompileProof ctx expected (body.instantiate1 fv) (fuel - 1)
  | _, _ => pure ()

  -- 3a. Fold `funext` into natural pointwise prose instead of "By funext, ..."
  if let .const head _ := proof.getAppFn.consumeMData then
    if head == ``funext || head == `Function.funext then
      if let some back := proof.getAppArgs.back? then
        if let .lam pnm dom pbody bi := back.consumeMData then
          modify (·.markEmitted)
          let useName ← freshShadowFreeName pnm "x"
          return ← withLocalDecl useName bi dom fun fv => do
            let xTex ← exprToLatex fv ctx.tbl
            let bodyExpr := pbody.instantiate1 fv
            let bodyTy ← inferType bodyExpr
            let subNodes ← decompileProof { ctx with lastFactFVar? := none, factIndex := 0, isProofStart := false } bodyTy bodyExpr (fuel - 1)
            let bodyInl ← renderProposition ctx.tbl bodyTy
            let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
            return #[.step s!"funext-{fuel}"
              (#[.text "Evaluating pointwise at ", .inlineMath xTex, .text ", "] ++ bodyInl ++ #[.text "."])
              subNodes (some goal)]
      modify (·.markEmitted)
      let subNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
      let conclInl ← renderProposition ctx.tbl expected
      let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      return #[.step s!"funext-{fuel}"
        (#[.text "By function extensionality, "] ++ conclInl ++ #[.text "."])
        subNodes (some goal)]

  -- 3b. Transparently unwrap kernel cast/rewrite transport wrappers (`Eq.mp`, `Eq.mpr`,
  -- `Iff.mp`, `Iff.mpr`, `Eq.rec`, `Eq.ndrec`, `id`, `of_eq_true`)
  if let .const head _ := proof.getAppFn.consumeMData then
    let args := proof.getAppArgs
    let tryUnwrapInner (inner : Expr) : StateRefT DiscourseState MetaM (Option (Array ProofNode)) := do
      try
        let innerTy ← inferType inner
        if ← isProp innerTy then
          return some (← decompileProof ctx innerTy inner (fuel - 1))
        return none
      catch _ => return none
    if (head == ``Eq.mp || head == ``Iff.mp) && args.size ≥ 4 then
      if args.size == 4 then
        let innerTy := args[0]!
        if ← (try isProp innerTy catch _ => pure false) then
          return ← decompileProof ctx innerTy args[3]! (fuel - 1)
      else if let some res ← tryUnwrapInner ((args[3]!).beta (args.extract 4 args.size)) then
        return res
    if (head == ``Eq.mpr || head == ``Iff.mpr) && args.size ≥ 4 then
      if args.size == 4 then
        let innerTy := args[1]!
        if ← (try isProp innerTy catch _ => pure false) then
          return ← decompileProof ctx innerTy args[3]! (fuel - 1)
      else if let some res ← tryUnwrapInner ((args[3]!).beta (args.extract 4 args.size)) then
        return res
    if head == ``id && args.size ≥ 2 then
      if args.size == 2 then
        let innerTy := args[0]!
        if ← (try isProp innerTy catch _ => pure false) then
          return ← decompileProof ctx innerTy args[1]! (fuel - 1)
      else if let some res ← tryUnwrapInner ((args[1]!).beta (args.extract 2 args.size)) then
        return res
    if (head == ``Eq.rec || head == ``Eq.ndrec) && args.size ≥ 6 then
      if let some res ← tryUnwrapInner ((args[3]!).beta (args.extract 6 args.size)) then
        return res
    if head == `of_eq_true then
      if let some inner := args.back? then
        if let some res ← tryUnwrapInner inner then
          return res

  -- 3c. Split `And.intro p q` and `Iff.intro mp mpr` into two flowing sub-arguments
  if let .const head _ := proof.getAppFn.consumeMData then
    if head == ``And.intro then
      let args := proof.getAppArgs
      if args.size ≥ 4 then
        modify (·.markEmitted)
        let pTy := args[args.size - 4]!
        let qTy := args[args.size - 3]!
        let pPf := args[args.size - 2]!
        let qPf := args[args.size - 1]!
        let subCtx := { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
        let pNodes ← decompileProof subCtx pTy pPf (fuel - 1)
        let qNodes ← decompileProof subCtx qTy qPf (fuel - 1)
        let pInl ← renderProposition ctx.tbl pTy
        let qInl ← renderProposition ctx.tbl qTy
        let pGoal ← buildGoalState ctx.tbl pTy (ctx.lemmaDepth ≥ 1)
        let qGoal ← buildGoalState ctx.tbl qTy (ctx.lemmaDepth ≥ 1)
        let pClean ← normalizeForPresentation pTy
        let qClean ← normalizeForPresentation qTy
        let bothLe ←
          if pClean.getAppFn.consumeMData.isConstOf ``LE.le && pClean.getAppArgs.size == 4 &&
             qClean.getAppFn.consumeMData.isConstOf ``LE.le && qClean.getAppArgs.size == 4 then
            let x1 ← normalizeForPresentation pClean.getAppArgs[3]!
            let x2 ← normalizeForPresentation qClean.getAppArgs[2]!
            pure (x1 == x2)
          else
            pure false
        let lead1 := if bothLe then "For the lower bound, " else "First, "
        let lead2 := if bothLe then "For the upper bound, " else "Second, "
        let step1 : ProofNode := .step s!"andL-{fuel}" (#[.text lead1] ++ pInl ++ #[.text "."]) pNodes (some pGoal)
        let step2 : ProofNode := .step s!"andR-{fuel}" (#[.text lead2] ++ qInl ++ #[.text "."]) qNodes (some qGoal)
        return dedupSiblings #[step1, step2]
    if head == ``Iff.intro then
      let args := proof.getAppArgs
      if args.size ≥ 4 then
        modify (·.markEmitted)
        let aTy := args[0]!
        let bTy := args[1]!
        let mpPf := args[2]!
        let mprPf := args[3]!
        let subCtx := { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
        let fwdTy := mkForall `h .default aTy bTy
        let revTy := mkForall `h .default bTy aTy
        let pNodes ← decompileProof subCtx fwdTy mpPf (fuel - 1)
        let qNodes ← decompileProof subCtx revTy mprPf (fuel - 1)
        let pInl ← renderProposition ctx.tbl aTy
        let qInl ← renderProposition ctx.tbl bTy
        let pGoal ← buildGoalState ctx.tbl fwdTy (ctx.lemmaDepth ≥ 1)
        let qGoal ← buildGoalState ctx.tbl revTy (ctx.lemmaDepth ≥ 1)
        let step1 : ProofNode := .step s!"iffL-{fuel}" (#[.text "For the forward direction, assuming "] ++ pInl ++ #[.text ", we show "] ++ qInl ++ #[.text "."]) pNodes (some pGoal)
        let step2 : ProofNode := .step s!"iffR-{fuel}" (#[.text "Conversely, assuming "] ++ qInl ++ #[.text ", we show "] ++ pInl ++ #[.text "."]) qNodes (some qGoal)
        return dedupSiblings #[step1, step2]

  -- 3d. Handle `Exists.intro w h` cleanly ("Taking x := w, …")
  if let .const head _ := proof.getAppFn.consumeMData then
    if head == ``Exists.intro then
      let args := proof.getAppArgs
      if args.size ≥ 4 then
        modify (·.markEmitted)
        let witness := args[args.size - 2]!
        let bodyProof := args[args.size - 1]!
        let bodyTy ← inferType bodyProof
        let wTex ← exprToLatex witness ctx.tbl
        let binderInfo? : Option (Name × Expr) :=
          let fromPred (p : Expr) : Option (Name × Expr) :=
            match p.consumeMData with
            | .lam nm d _ _ => if (cleanBinderName? nm).isSome then some (nm, d) else none
            | _ => none
          let expClean := expected.consumeMData
          let fromExp :=
            if expClean.isAppOf ``Exists && expClean.getAppArgs.size ≥ 2 then
              fromPred expClean.getAppArgs[1]!
            else none
          fromExp <|> fromPred args[args.size - 3]!
        let binderTex? ← match binderInfo? with
          | some (nm, dom) =>
              withLocalDecl nm .default dom fun fv => do
                pure (some (← exprToLatex fv ctx.tbl))
          | none => pure none
        let subCtx := { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
        let subNodes ← decompileProof subCtx bodyTy bodyProof (fuel - 1)
        let bodyInl ← renderProposition ctx.tbl bodyTy
        let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
        let leadInl : Array Inline := match binderTex? with
          | some bTex =>
              if bTex == wTex then #[.text "Taking witness ", .inlineMath wTex, .text ", "]
              else #[.text "Taking ", .inlineMath s!"{bTex} := {wTex}", .text ", "]
          | none => #[.text "Taking witness ", .inlineMath wTex, .text ", "]
        return #[.step s!"exists-{fuel}" (leadInl ++ bodyInl ++ #[.text "."]) subNodes (some goal)]

  -- 3e. Handle `False.elim` and `absurd` cleanly ("This yields a contradiction.")
  if let .const head _ := proof.getAppFn.consumeMData then
    if head == ``False.elim || head == ``absurd then
      modify (·.markEmitted)
      let subNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
      let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      return #[.step s!"contra-{fuel}" #[.text "This yields a contradiction."] subNodes (some goal)]

  -- 3f. Never emit compiler aux decls (`_simp_1`, `_proof_1`, ...) or structural congruence/cast
  -- combinators (`congr*`, `and_congr*`, `propext`, `Eq.ndrec`, ...) as named mathematical lemmas.
  if let .const head _ := proof.getAppFn.consumeMData then
    if isStructuralCongrOrCast head then
      let subNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
      if subNodes.isEmpty then
        let rk := if head == `eq_self || head == ``Eq.refl || head == ``rfl then
          RoutineKind.reflexivity.label else RoutineKind.congruenceAndExt.label
        return #[.routineReceipt s!"routine-{fuel}" rk 1 #[] none]
      else
        let conclInl ← renderProposition ctx.tbl expected
        let verb := if isCompilerAuxDecl head then "By simplification, " else "By substitution of equals, "
        return #[.step s!"wrap-congr-{fuel}"
          (#[.text verb] ++ conclInl ++ #[.text "."])
          subNodes none none none true false]

  -- 4. Detect `calc` / `cc_calc` chains (`Trans.trans` / `Eq.trans` / `LE.le.trans` / `le_trans` / `SubstitutesWithin`)
  let chain ← flattenCalcChain proof expected
  if chain.size ≥ 2 then
    let st ← get
    let (opener, st') := st.pickOpener .elaboration
    set st'
    let mut calcSteps : Array (CalcStep × Array ProofNode) := #[]
    let mut allParsed := true
    for (sp, stProp) in chain do
      match ← splitBinaryRelation? ctx.tbl stProp with
      | some (rel, lhs, rhs) =>
          let lhsTex ← exprToLatex lhs ctx.tbl
          let rhsTex ← exprToLatex rhs ctx.tbl
          let subCtx := { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
          let subNodes ← decompileProof subCtx stProp sp (fuel - 1)
          let spUnwrapped := unwrapCastProof sp
          let isNonAlgebraicRel :=
            rel.startsWith "\\simeq" || rel.startsWith "\\approx" ||
            rel.startsWith "\\preceq" || rel.startsWith "\\xrightarrow"
          let reason : Array Inline ←
            if exprContainsSorryAx sp then pure #[.text "[UNPROVED: sorry]"]
            else match spUnwrapped.getAppFn.consumeMData with
            | .const cn _ =>
                if cn == ``dite || cn == ``ite || cn == ``Decidable.byCases || cn == `Classical.byCases then
                  pure #[.text "by case analysis"]
                else if isCoreOrMathlibIn env cn then
                  if isNonAlgebraicRel then pure #[.text "by the checked subargument"]
                  else pure #[.text "by elementary algebra"]
                else
                  pure #[.text s!"by {humanLemmaLabel env cn}"]
            | .fvar _ => pure #[.text "by assumption"]
            | _ => pure #[.text "by the checked subargument"]
          let diagHtml ← if ctx.lemmaDepth ≤ 1 then (← diagramHookRef.get) ctx.tbl stProp else pure none
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
      let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      let intro : Array Inline := #[.text s!"{opener} chaining the intermediate steps yields"]
      return #[.calcChain s!"calc-{fuel}" intro calcSteps (some goal)]

  -- 5. Direct hypothesis (`assumption`) or application headed by a local hypothesis `.fvar id`
  if let .fvar id := proof.consumeMData then
    modify (·.markEmitted)
    return #[← renderHypothesisStep ctx.tbl expected id s!"hyp-{fuel}-{id.name}"
      (isWrap := false) (onlyUsed := (ctx.lemmaDepth ≥ 1))]

  if let .fvar id := proof.getAppFn.consumeMData then
    modify (·.markEmitted)
    let decl ← id.getDecl
    let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
    let subNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
    let hypInl ← renderProposition ctx.tbl decl.type
    let hypLen := (inlinesCanonicalKey hypInl).length
    let conclInl ← renderProposition ctx.tbl expected
    let lead : Array Inline :=
      if hypLen > 0 && hypLen ≤ 60 then
        #[.text "By the assumption that "] ++ hypInl ++ #[.text ", "]
      else
        #[.text "By the assumed hypothesis, "]
    let conclPhrase : Array Inline :=
      if expected.consumeMData.isConstOf ``False then #[.text "this yields a contradiction."]
      else conclInl ++ #[.text "."]
    return #[.step s!"hypapp-{fuel}-{id.name}" (lead ++ conclPhrase) subNodes (some goal)]

  -- 6. Application of a named theorem/lemma (with beta-instantiated cross-lemma recursion & wrapper detection!)
  if let .const declName levels := proof.getAppFn.consumeMData then
    let st ← get
    let (opener, st') := st.pickOpener .justification
    set st'
    let premiseNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
    let mut expandedBody : Array ProofNode := #[]
    let mut isWrap := false
    if shouldExpandLemma env ctx declName then
      if let some (.thmInfo info) := env.find? declName then
        if let some (instTy, instVal) ← betaInstantiateTheorem info levels proof.getAppArgs then
          isWrap := isTrivialWrapperBody env declName instVal
          let childCtx : DecompCtx := {
            ctx with
            seenDecls := ctx.seenDecls.insert declName
            lemmaDepth := ctx.lemmaDepth + 1
            lastFactFVar? := none
            factIndex := 0
            atRootConclusion := false
            isProofStart := false
          }
          expandedBody ← decompileProof childCtx instTy instVal (fuel - 1)
    let ov := getOverlay env declName
    let mut allChildren : Array ProofNode := #[]
    if let some fb := ov.flowBefore? then
      allChildren := allChildren.push (.flowNote s!"flow-pre-{declName}" fb "margin")
    allChildren := allChildren ++ dedupSiblings (premiseNodes ++ expandedBody)
    if let some fa := ov.flowAfter? then
      allChildren := allChildren.push (.flowNote s!"flow-post-{declName}" fa "margin")
    let hasSorry := exprContainsSorryAx proof
    let isCore := isCoreOrMathlibIn env declName
    let isOrderMono :=
      declName == `add_le_add || declName == `mul_le_mul_of_nonneg_left ||
      declName == `mul_le_mul_of_nonneg_right || declName == `le_trans ||
      declName == `le_add_of_nonneg_left || declName == `le_add_of_nonneg_right ||
      declName == `sub_le_sub || declName == `sub_le_sub_left ||
      declName == `div_le_div_of_nonneg_left || declName == `add_pos'
    let sName := shortConstName declName
    let isNonnegHelper :=
      !effectiveIsProofJoint env declName && !ctx.docDecls.contains declName &&
      (sName.endsWith "_nonNeg" || sName.endsWith "_nonneg" ||
       sName == "zero_le" || sName.endsWith ".zero_le" || sName.endsWith "_zero_le")
    let onlyRoutine := allChildren.all fun
      | .routineReceipt .. => true
      | _ => false
    if !hasSorry && (((isCore && isOrderMono) && allChildren.isEmpty) || (isNonnegHelper && onlyRoutine)) then
      return #[.routineReceipt s!"routine-{fuel}" RoutineKind.algebraAndOrder.label 1 #[] none]
    let label := humanLemmaLabel env declName
    let isCaseSplit := declName == ``Or.elim || declName == ``Or.casesOn ||
      declName == ``Bool.rec || declName == ``Option.rec || declName == ``Sum.rec || declName == ``Or.rec ||
      declName == ``dite || declName == ``ite || declName == ``Decidable.byCases ||
      declName == `Classical.byCases || declName == ``Decidable.casesOn
    let isDisjInj := declName == ``Or.inl || declName == ``Or.inr
    let isCasesDestruct := !isCaseSplit &&
      (declName.toString.endsWith ".casesOn" || declName == ``Exists.elim)
    let isInductionRec :=
      !isCaseSplit && !isCasesDestruct && !declName.toString.startsWith "Eq." &&
      (declName == ``Nat.rec || declName == `Nat.recAux || declName == ``Nat.recOn ||
       declName == ``List.rec || declName == ``List.recOn ||
       declName.toString.endsWith ".rec" || declName.toString.endsWith ".recOn" ||
       declName.toString.endsWith ".recAux")
    let isExt := !isCore && (declName.toString.endsWith ".ext" || declName == ``Subtype.ext)
    if isOrderMono || isDisjInj || isCasesDestruct then
      isWrap := true
    let goal? ←
      if isWrap && !hasSorry then pure none
      else some <$> buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
    if hasSorry &&
       !allChildren.any (fun n => n.collectAllText.any (fun t => (t.splitOn "[UNPROVED: sorry]").length > 1)) then
      let sorryGoal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      allChildren := allChildren.push (.step s!"sorry-child-{fuel}" #[.text "[UNPROVED: sorry]"] #[] (some sorryGoal))
    let diagHtml ← if ctx.lemmaDepth ≤ 1 then (← diagramHookRef.get) ctx.tbl expected else pure none
    -- Avoid the "restatement reflex": at the root conclusion, never re-quote the whole theorem!
    let hasVisibleNonWrap := allChildren.any fun
      | .step _ _ _ _ _ _ w _ _ _ _ _ => !w
      | _ => true
    let conclInl ← renderProposition ctx.tbl expected
    let citeInline : Inline :=
      let isCitableThm :=
        !isCore && !Lean.isPrivateName declName &&
        (ctx.docDecls.contains declName || ov.title?.isSome || effectiveIsProofJoint env declName) &&
        (match env.find? declName with | some (.thmInfo _) => true | _ => false)
      if isCitableThm then .symbol declName.toString label false
      else .emph label
    let content : Array Inline ←
      if isCaseSplit then
        pure (#[.text "Proceeding by case analysis, "] ++ conclInl ++ #[.text "."])
      else if isInductionRec then
        pure (#[.text "Proceeding by structural induction, "] ++ conclInl ++ #[.text "."])
      else if isDisjInj then
        pure (#[.text "By the corresponding alternative, "] ++ conclInl ++ #[.text "."])
      else if isCasesDestruct then
        pure (#[.text "Unpacking the hypothesis yields "] ++ conclInl ++ #[.text "."])
      else if isOrderMono then
        pure (#[.text "By monotonicity, "] ++ conclInl ++ #[.text "."])
      else if isExt || declName == ``Subtype.ext then
        pure (#[.text "By extensionality, "] ++ conclInl ++ #[.text "."])
      else if ctx.atRootConclusion then
        if isCore then
          pure #[.text s!"The claim follows directly by {label}."]
        else if !hasVisibleNonWrap then
          pure #[.text "The claim follows from ", citeInline, .text "."]
        else
          pure #[.text "Applying ", citeInline, .text " to the checked premises establishes the claim."]
      else
        if isCore then
          pure (#[.text s!"{opener} {label}, "] ++ conclInl ++ #[.text "."])
        else
          pure (#[.text s!"{opener} ", citeInline, .text ", "] ++ conclInl ++ #[.text "."])
    return #[.step s!"app-{declName}-{fuel}" content allChildren goal?
      diagHtml (some declName.toString) isWrap]

  -- 7. Fallback: checked goal statement (flagging any unexpanded `sorryAx`)
  let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
  if exprContainsSorryAx proof then
    return #[.step s!"sorry-fallback-{fuel}" #[.text "[UNPROVED: sorry]"] #[] (some goal)]
  let conclInl ← renderProposition ctx.tbl expected
  return #[.step s!"step-{fuel}" (#[.text "We obtain "] ++ conclInl ++ #[.text "."]) #[] (some goal)]

/-- Collect the exact axiom footprint of a declaration (`propext`, `Classical.choice`,
`Quot.sound`, flagging any `sorryAx`). -/
def auditAxioms (declName : Name) : MetaM AxiomAudit := do
  let axioms ← Lean.collectAxioms declName
  let names := axioms.map (·.toString)
  let hasSorry := axioms.contains ``sorryAx
  return { axioms := names, hasSorry }

/-- Collect distinct `originDecl` names appearing anywhere in a `ProofNode` tree. -/
private partial def collectOriginDecls : ProofNode → Array Name
  | .step _ _ children _ _ origin? _ _ _ _ _ _ =>
      let own := match origin? with | some s => #[s.toName] | none => #[]
      own ++ children.flatMap collectOriginDecls
  | .calcChain _ _ steps _ origin? =>
      let own := match origin? with | some s => #[s.toName] | none => #[]
      own ++ steps.flatMap fun (_, ch) => ch.flatMap collectOriginDecls
  | .routineReceipt _ _ _ details _ => details.flatMap collectOriginDecls
  | .pseudocodeBox _ _ _ _ _ origin? =>
      match origin? with | some s => #[s.toName] | none => #[]
  | _ => #[]

/-- Collect all `dataKey` / `.symbol` keys referenced inside an array of `Inline`s and optional `inlineMeta`. -/
private def collectInlineDataKeys (inls : Array Inline)
    (metas : Array (Option ProseTrust × Option String) := #[]) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [:inls.size] do
    match inls[i]! with
    | .symbol k _ _ =>
        if !k.isEmpty then out := out.push k
    | _ => pure ()
    if let some (_, some dk) := metas[i]? then
      if !dk.isEmpty then out := out.push dk
  return out

/-- Collect all `dataKey` / `.symbol` keys referenced anywhere inside a `ProofNode` tree. -/
private partial def collectProofNodeDataKeys : ProofNode → Array String
  | .step _ content children _ _ _ _ _ _ _ _ inlineMeta =>
      collectInlineDataKeys content inlineMeta ++ children.flatMap collectProofNodeDataKeys
  | .calcChain _ intro steps _ _ =>
      collectInlineDataKeys intro ++
      steps.flatMap fun (cs, ch) =>
        collectInlineDataKeys cs.reason ++ ch.flatMap collectProofNodeDataKeys
  | .routineReceipt _ _ _ details _ => details.flatMap collectProofNodeDataKeys
  | .flowNote _ _ _ => #[]
  | .figure _ caption _ => collectInlineDataKeys caption
  | .pseudocodeBox _ _ _ lines _ _ =>
      lines.flatMap fun l => collectInlineDataKeys l.inlines

/-- Top-level entry point with optional section-fixed context hoisting:
informalizes a checked Lean declaration into an `Explanation.Entry` (with scoped local
shorthands & parameter inspectors) plus all referenced constant `SymbolInspector`s. -/
def informalizeDeclarationWithContext (declName : Name) (config : Config := {})
    (hoisted? : Option HoistedContext := none)
    (docDecls : NameSet := {}) : MetaM (Entry × Array SymbolInspector) := do
  clearGoalCtxCache
  (← clearDiagramCacheHookRef.get)
  let env ← getEnv
  let some info := env.find? declName
    | throwError "informalize: declaration `{declName}` not found in environment"
  let ov := getOverlay env declName
  let tbl := buildSymbolTable env declName
  let proofBody? : Option Expr :=
    match info with
    | .thmInfo tinfo => some tinfo.value
    | _ => none
  let parsed ← parseTheoremStatement tbl info.type hoisted? proofBody? ov.theoremNotations declName
  let diagHtml ← (← diagramHookRef.get) tbl info.type
  let rawHeader := match ov.entryKind? with
    | some k => k
    | none =>
      match info with
      | .thmInfo _ => "Theorem"
      | .defnInfo _ => "Definition"
      | _ => "Declaration"
  let header := capitalizeFirst rawHeader.trimAscii.toString
  let mut proofNodes : Array ProofNode := #[]
  if let some fb := ov.flowBefore? then
    proofNodes := proofNodes.push (.flowNote s!"doc-flow-pre-{declName}" fb "inline")
  extraNotationInspectorsRef.set #[]
  if let .thmInfo tinfo := info then
    let ctx : DecompCtx := {
      config
      tbl
      seenDecls := ({} : NameSet).insert declName
      docDecls
      lemmaDepth := 0
      atRootConclusion := true
      pendingNotations := ov.theoremNotations
      isClosingGoal := true
    }
    let (nodes, _) ← (decompileProof ctx info.type tinfo.value config.maxTermFuel).run {}
    proofNodes := ((dedupSiblings (proofNodes ++ nodes)).map collapseTautologicalSingleChild).map
      (capDiagramHtmlDepth 1 0)
  let extraProofNotations ← extraNotationInspectorsRef.get
  extraNotationInspectorsRef.set #[]
  if let some fa := ov.flowAfter? then
    proofNodes := proofNodes.push (.flowNote s!"doc-flow-post-{declName}" fa "inline")
  let hoistedSyms := match hoisted? with
    | some h => h.paramSyms
    | none => {}
  let originDecls := proofNodes.flatMap collectOriginDecls
  let dataKeyStrings :=
    parsed.paragraphs.flatMap (collectInlineDataKeys ·) ++ proofNodes.flatMap collectProofNodeDataKeys
  let mut dataKeySet : Std.HashSet String := {}
  let mut dataKeyDecls : Array Name := #[]
  for dk in dataKeyStrings do
    if !dataKeySet.contains dk then
      dataKeySet := dataKeySet.insert dk
      let nm := dk.toName
      if !nm.isAnonymous then
        dataKeyDecls := dataKeyDecls.push nm
  let (localParamInspectors, typeConstInspectors, proofConstInspectors) ←
    (← scopedInspectorCollectorRef.get) tbl declName info.type proofBody? hoistedSyms (originDecls ++ dataKeyDecls)
  let shorthandInspectors : Array SymbolInspector :=
    parsed.localShorthands.map fun sh => {
      key := s!"local:{declName}:{sh.sym}"
      display := sh.sym
      kind := .localShorthand s!"{sh.sym} = {sh.rhsLatex}" sh.roleDescription
      leanName? := none
      leanType := sh.leanType
      roleBadge? := some "local shorthand"
    }
  let mut mergedNotations : Array SymbolInspector := parsed.notationInspectors
  for ins in extraProofNotations do
    if !mergedNotations.any (fun x => x.display == ins.display) then
      mergedNotations := mergedNotations.push ins
  let localInspectors := mergedNotations ++ localParamInspectors ++ shorthandInspectors
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
    let keep :=
      if ins.roleBadge? == some "theorem" then
        dataKeySet.contains ins.key
      else
        dataKeySet.contains ins.key || mathDispAppearsIn allMathSegs ins.display
    if !seenConstKeys.contains ins.key && keep then
      seenConstKeys := seenConstKeys.insert ins.key
      constInspectors := constInspectors.push ins
  let axioms ← auditAxioms declName
  let referencedKeys := constInspectors.map (·.key)
  let entry : Entry := {
    header
    title? := ov.title? <|> some (humanDeclarationTitle env declName)
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
