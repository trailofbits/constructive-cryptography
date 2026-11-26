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
import Informalization.Core.Register

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
open Informalization.Core.Register

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

private def isPlumbingNameStr (s : String) : Bool :=
  s.startsWith "match_" || (s.splitOn ".match_").length > 1 || (s.splitOn "_match_").length > 1 ||
  (s.splitOn "IsDDCFrom").length > 1 || (s.splitOn "isDDCFrom").length > 1 ||
  (s.splitOn "ofPDS").length > 1 || (s.splitOn "ofDDC").length > 1 ||
  (s.splitOn "of_pds").length > 1 || (s.splitOn "of_ddc").length > 1 ||
  (s.splitOn "associator").length > 1 ||
  (s.splitOn "getElem!").length > 1 || (s.splitOn "getElem?").length > 1 ||
  (s.splitOn "toBitVec").length > 1 || (s.splitOn "ByteArray").length > 1

private def isAstPlumbingHead (declName : Name) : Bool :=
  let s := declName.toString
  isCompilerAuxDecl declName || isPlumbingNameStr s ||
  declName == ``Prod.casesOn || declName == ``PProd.casesOn ||
  declName == ``Sigma.casesOn || declName == ``PSigma.casesOn ||
  declName == ``Sum.inl || declName == ``Sum.inr ||
  declName == ``Or.inl || declName == ``Or.inr ||
  declName == ``And.left || declName == ``And.right ||
  declName == ``Prod.fst || declName == ``Prod.snd ||
  declName == ``PProd.fst || declName == ``PProd.snd ||
  declName == `Set.mem_image || declName == `Set.mem_image2 ||
  declName == `Set.mem_singleton_iff || declName == `Set.mem_singleton ||
  declName == `Equiv.refl || declName == ``Eq.rec || declName == ``Eq.ndrec || declName == `Eq.drec ||
  declName == ``Nat.rec || declName == `Nat.recAux || declName == ``Nat.recOn ||
  declName == ``congrArg || declName == ``congrFun || declName == `congrFun' || declName == ``congr ||
  declName == ``funext || declName == ``propext ||
  declName == `CategoryTheory.MonoidalCategory.associator ||
  declName == `List.getElem! || declName == `List.getElem? ||
  declName == `GetElem.getElem || declName == `GetElem?.getElem? ||
  declName == `ByteArray.toBitVec

private def exprHasRawPlumbing (e : Expr) : Bool :=
  e.foldConsts (init := false) fun cn acc =>
    if acc then true
    else
      let s := cn.toString
      isCompilerAuxDecl cn || isPlumbingNameStr s ||
      cn == ``Prod.casesOn || cn == ``PProd.casesOn ||
      cn == ``Sum.inl || cn == ``Sum.inr ||
      cn == `Equiv.refl || cn == ``Eq.rec || cn == ``Eq.ndrec || cn == `Eq.drec ||
      cn == ``Nat.rec || cn == `Nat.recAux || cn == ``Nat.recOn ||
      cn == `CategoryTheory.MonoidalCategory.associator ||
      cn == `List.getElem! || cn == `List.getElem? ||
      cn == `GetElem.getElem || cn == `GetElem?.getElem? ||
      cn == `ByteArray.toBitVec

private def isNeverExpandedConst (declName : Name) : Bool :=
  let s := declName.toString
  let short := shortConstName declName
  s.endsWith ".ext" || s.endsWith ".ext_iff" || s.endsWith ".casesOn" ||
  s.endsWith ".rec" || s.endsWith ".recOn" || s.endsWith ".recAux" ||
  s.startsWith "congr" || short == "ext" || isAstPlumbingHead declName ||
  declName == ``Quotient.sound || declName == ``Exists.intro ||
  declName == ``False.elim || declName == ``absurd ||
  declName == ``Or.elim ||
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
  else
    let typeClean := match env.find? declName with
      | some (.thmInfo info) => !exprHasRawPlumbing info.type
      | _ => false
    if !typeClean then false
    else if expandAttr then true
    else if ctx.config.projectNamespaces.isEmpty then true
    else ctx.config.projectNamespaces.any (fun p => p.isPrefixOf declName)

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

private def isVacuousRenderedEq (tbl : SymbolTable) (prop : Expr) : MetaM Bool := do
  let p ← normalizeForPresentation prop
  match p.eq? with
  | some (_, lhs, rhs) =>
      let lhsTex ← exprToLatex lhs tbl
      let rhsTex ← exprToLatex rhs tbl
      return lhsTex == rhsTex
  | none => return false

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
    if !exprContainsSorryAx ap && (← isVacuousRenderedEq ctx.tbl aty) then
      continue
    if let some fvid := unwrapHypothesisFVar? ap then
      let decl ← fvid.getDecl
      let hypInl ← renderProposition ctx.tbl decl.type
      let hypLen := (inlinesCanonicalKey hypInl).length
      if hypLen > 0 && hypLen ≤ 60 then
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

private def coreLemmaTitles : NameMap String :=
  [ (`ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.DominatedByDistance.advantage_le_distance,
      "the advantage-to-distance bound"),
    (`AuthenticatedEncryption.hybrid_ideal_distance_le,
      "the hybrid-to-ideal distance bound"),
    (`ConstructiveCryptography.CompatiblePseudoMetric.edist_smul_le,
      "converter contractivity"),
    (`ConstructiveCryptography.CryptographicAlgebra.distance_attach_le,
      "the converter attachment distance bound"),
    (`GameExamples.collision_win_le,
      "the collision winning-probability bound"),
    (`ConstructiveCryptography.DistinctionGames.solvers_winner,
      "the solver winning criterion"),
    (`ConstructiveCryptography.DistinctionGames.advantage_le_win,
      "the conditional-equivalence advantage bound"),
    (`ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le,
      "parallel non-expansion"),
    (`ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le,
      "left-parallel non-expansion"),
    (`ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le,
      "right-parallel non-expansion"),
    (`SystemAlgebra.Interface.distance_parallel_le,
      "parallel non-expansion"),
    (`SystemAlgebra.Interface.distance_parallel_left_le,
      "left-parallel non-expansion"),
    (`SystemAlgebra.Interface.distance_parallel_right_le,
      "right-parallel non-expansion"),
    (`ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.trans,
      "transitivity of substitution"),
    (`ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance,
      "the distinguishing advantage bound"),
    (`ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical,
      "the statistical distance bound"),
    (`ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_context,
      "context absorption under substitution"),
    (`ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_attach,
      "converter-attachment substitution"),
    (`SystemAlgebra.TypedConverter.substitutesWithin_attach,
      "converter-attachment substitution"),
    (`SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability,
      "the conditional-equivalence advantage bound"),
    (`GameExamples.hybrid_ideal_advantage_le,
      "the hybrid-to-ideal advantage bound"),
    (`AuthenticatedEncryption.real_ideal_distance_le,
      "the AEAD hybrid distance bound"),
    (`Examples.PRGLengthExtension.prgReal_H_eq,
      "the length-extension attachment identity"),
    (`Examples.PRGLengthExtension.𝓡₁_smul_prgRand,
      "the first-call converter identity"),
    (`Examples.PRGLengthExtension.𝓡₂_smul_prgRand,
      "the second-call converter identity"),
    (`Probability.Distribution.isProbDist_single,
      "point-mass normalization"),
    (`Probability.Distribution.ProbDist.single.eq_1,
      "the point-mass distribution identity"),
    (`SystemAlgebra.RandomSystem.transcriptDistance_le_one,
      "the unit distance bound"),
    (`SystemAlgebra.Domain.Distinguisher.advantage_le_transcriptDistance,
      "the distinguisher advantage-to-distance bound"),
    (`SystemAlgebra.Domain.DistinguisherBehavior.advantage_le_transcriptDistance,
      "the distinguisher advantage-to-distance bound"),
    (``And.left, "conjunction elimination"),
    (``And.right, "conjunction elimination"),
    (``Prod.fst, "projection"),
    (``Prod.snd, "projection"),
    (``Or.inl, "disjunction introduction"),
    (``Or.inr, "disjunction introduction"),
    (``Sum.inl, "sum injection"),
    (``Sum.inr, "sum injection"),
    (``Eq.refl, "reflexivity"),
    (``rfl, "reflexivity")
  ].foldl (init := {}) fun m (n, t) => m.insert n t

private def sanitizeRawLemmaLabel (declName : Name) (raw : String) : String :=
  let s := raw.trimAscii.toString
  let low := s.toLower
  let short := (shortConstName declName).toLower
  if low == "with public port attach" then
    "the public-port wiring identity"
  else if (low.splitOn "ddc").length > 1 || (low.splitOn "pds").length > 1 ||
          (low.splitOn "call converter").length > 1 || (low.splitOn "associator").length > 1 ||
          (short.splitOn "ddc").length > 1 || (short.splitOn "pds").length > 1 then
    "the wiring identity"
  else if (low.splitOn "injective").length > 1 || (low.splitOn "injectivity").length > 1 ||
          short.endsWith "_inj" || short.endsWith "injective" then
    "injectivity"
  else if low == "not bound of lower bound" || low.startsWith "not bound of " then
    "the lower bound"
  else if low.startsWith "of real" || (low.splitOn "of real").length > 1 ||
          (low.splitOn "real bound").length > 1 ||
          short.startsWith "of_real" || short.startsWith "ofreal" then
    "the auxiliary bound"
  else if low == "mass or bound" || low.endsWith " or bound" then
    "the probability bound"
  else if low == "bound min" || low == "min bound" then
    "the minimum bound"
  else if low == "transitivity strict bound" then
    "transitivity"
  else if low == "capacity card bound state" then
    "the state-space bound"
  else if low == "bound refined error bound" then
    "the refined error bound"
  else if low.startsWith "of " || short.startsWith "of_" ||
          (low.splitOn " of fn").length > 1 || (low.splitOn " of val").length > 1 ||
          (low.splitOn " of coe").length > 1 || (low.splitOn " of eq").length > 1 ||
          (low.splitOn " of ne").length > 1 then
    if (low.splitOn "bound").length > 1 || (low.splitOn "strict").length > 1 then
      "the auxiliary bound"
    else if (low.splitOn "identity").length > 1 || (low.splitOn "equivalence").length > 1 then
      "the auxiliary identity"
    else
      "the auxiliary lemma"
  else
    let ws := s.splitOn " " |>.filter (!·.isEmpty)
    if ws.length ≥ 2 && ws.head?.map (·.toLower) == some "bound" &&
       ws.getLast?.map (·.toLower) == some "bound" then
      String.intercalate " " ws.tail!
    else
      s

private def rewriteMathSuffixWords (words : List String) : List String := Id.run do
  let mapped := words.map fun w =>
    match w with
    | "smul" => "attachment"
    | "edist" => "distance"
    | "mono" => "monotonicity"
    | "symm" => "symmetry"
    | "trans" => "transitivity"
    | "refl" | "rfl" => "reflexivity"
    | "nonneg" => "nonnegativity"
    | "inj" => "injectivity"
    | _ => w
  let rec collapseAdj : List String → List String
    | [] => []
    | [x] => [x]
    | x :: y :: rest =>
        if x == y then collapseAdj (x :: rest) else x :: collapseAdj (y :: rest)
  let rev := mapped.reverse
  let rev := match rev with
    | "le" :: r => if r.head? == some "bound" then r else "bound" :: r
    | "lt" :: r => "bound" :: "strict" :: r
    | "ge" :: r => "bound" :: "lower" :: r
    | "gt" :: r => "bound" :: "lower" :: r
    | "eq" :: r => if r.head? == some "identity" then r else "identity" :: r
    | "iff" :: r => "equivalence" :: r
    | n :: "eq" :: r =>
        if n.all Char.isDigit then "identity" :: "defining" :: r
        else n :: "eq" :: r
    | _ => rev
  let out := rev.reverse.map fun w =>
    match w with
    | "le" => "bound"
    | "lt" => "strict"
    | "eq" => "identity"
    | _ => w
  return collapseAdj out

/-- Format an inline human label for a cited theorem/lemma name (respecting `informal_title`
overlay if present, then core CC/game titles, otherwise splitting camelCase/underscores cleanly). -/
def humanLemmaLabel (env : Environment) (declName : Name) : String :=
  match (getOverlay env declName).title? with
  | some t => t.trimAscii.toString
  | none =>
      match coreLemmaTitles.find? declName with
      | some t => t
      | none =>
          let words0 := humanizeDeclWords declName |>.map fun w =>
            let low := w.toLower
            match cryptoAcronyms.find? (·.1 == low) with
            | some (_, acr) => acr
            | none => low
          let words := rewriteMathSuffixWords words0
          let raw := (String.intercalate " " words)
            |>.replace "transcript distance" "distinguishing advantage"
            |>.replace "distinguishing distance" "distinguishing advantage"
          sanitizeRawLemmaLabel declName raw

/-- Format a Title-Cased fallback entry/document title for a declaration (respecting
`informal_title`, stripping `_verbose`, splitting camelCase, and preserving acronyms). -/
def humanDeclarationTitle (env : Environment) (declName : Name) : String :=
  match (getOverlay env declName).title? with
  | some t => t.trimAscii.toString
  | none =>
      let words0 := humanizeDeclWords declName
      let words := rewriteMathSuffixWords (words0.map fun w =>
        let low := w.toLower
        match cryptoAcronyms.find? (·.1 == low) with
        | some (_, acr) => acr
        | none => low)
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

/-- Strip `diagramHtml?` from ALL `ProofNode`s (`steps` and `calcSteps`), keeping figures
strictly at the entry level so `⊕` expansions stay clean and diagram-free. -/
private partial def capDiagramHtmlDepth (_maxDepth : Nat := 0) (_parentDiag? : Option String := none) :
    Nat → ProofNode → ProofNode
  | depth, .step id content children goal? _ origin isWrap defExp sp lh tr im =>
      .step id content (children.map (capDiagramHtmlDepth 0 none (depth + 1)))
        goal? none origin isWrap defExp sp lh tr im
  | depth, .calcChain id intro steps goal? origin =>
      let nextSteps := steps.map fun (s, ch) =>
        ({ s with diagramHtml? := none }, ch.map (capDiagramHtmlDepth 0 none (depth + 1)))
      .calcChain id intro nextSteps goal? origin
  | depth, .routineReceipt id summary count details goal? =>
      .routineReceipt id summary count
        (details.map (capDiagramHtmlDepth 0 none (depth + 1))) goal?
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

private def containsSorryText (n : ProofNode) : Bool :=
  n.collectAllText.any fun t => (t.splitOn "[UNPROVED: sorry]").length > 1

private def isVacuousHypOrRoutineChild (n : ProofNode) : Bool :=
  if containsSorryText n then false
  else match n with
  | .routineReceipt _ summary _ details _ =>
      if !details.isEmpty then false
      else
        let low := summary.trimAscii.toString.toLower
        low.startsWith "reflexiv" || low.startsWith "definitional" ||
        low.startsWith "trivial" || low.startsWith "assumed" ||
        low.startsWith "cast" || low.startsWith "coercion" ||
        low.startsWith "congruence" || low.startsWith "extensional" ||
        low.startsWith "elementary arithmetic" || low.startsWith "elementary algebra" ||
        low.startsWith "low-level wiring" || low.startsWith "algebra"
  | .step _ cContent cChildren _ cDiag? _ isWrap _ _ _ _ _ =>
      if !cChildren.isEmpty || cDiag?.isSome then false
      else
        let raw := String.intercalate "" (cContent.toList.map Inline.collectText)
        let words := (raw.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty)
        let low := (String.intercalate " " words).trimAscii.toString.toLower
        let lowNoDot :=
          if low.endsWith "." || low.endsWith "," then (low.dropEnd 1).toString.trimAscii.toString
          else low
        let hasMath := !(extractNormalizedMath cContent).isEmpty
        low.startsWith "this holds by the assumed " ||
        lowNoDot == "by definitional equality" ||
        lowNoDot == "by reflexivity" ||
        lowNoDot == "by definition" ||
        lowNoDot == "by extensionality and substitution of equals" ||
        lowNoDot == "by elementary algebra and inequalities" ||
        lowNoDot == "by elementary algebra" ||
        lowNoDot == "by substitution of equals" ||
        (!hasMath && (low.startsWith "by definitional" || low.startsWith "by reflexivity" ||
          low.startsWith "by extensionality" || low.startsWith "by elementary algebra")) ||
        (isWrap && low.startsWith "this holds by the assumption")
  | _ => false

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
  let childNoDot :=
    if childLow.endsWith "." || childLow.endsWith "," then
      (childLow.dropEnd 1).toString.trimAscii.toString
    else childLow
  if childNoDot == "by definitional equality" || childNoDot == "by reflexivity" ||
     childNoDot == "by extensionality and substitution of equals" ||
     childNoDot == "by elementary algebra and inequalities" then
    return true
  let parentMath := extractNormalizedMath parentContent
  let childMath := extractNormalizedMath childContent
  let allChildMathInParent := childMath.all fun cm =>
    parentMath.any fun pm => pm == cm || (cm.length ≥ 4 && (pm.splitOn cm).length > 1)
  if !allChildMathInParent then
    return false
  if childLow.startsWith "this holds by the assumption that " then
    return true
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
  if childLow.startsWith "proceeding by " || childLow.startsWith "by case analysis, " ||
     childLow.startsWith "by structural induction, " then
    return !childMath.isEmpty
  if childLow.startsWith "by " || childLow.startsWith "from " || childLow.startsWith "applying " then
    let commaParts := childLow.splitOn ", "
    if commaParts.length ≥ 2 then
      if !childMath.isEmpty then return true
      let rhsNorm := normalizeProseForComparison #[.text (String.intercalate ", " (commaParts.drop 1))]
      if !rhsNorm.isEmpty && (rhsNorm == parentNorm || (parentNorm.splitOn rhsNorm).length > 1) then
        return true
  return false

private def isCalcStepRestatement (cs : CalcStep) (child : ProofNode) : Bool :=
  if isVacuousHypOrRoutineChild child then true
  else match child with
  | .step _ cContent cChildren _ cDiag? _ _ _ _ _ _ _ =>
      if !cChildren.isEmpty || cDiag?.isSome || containsSorryText child then false
      else
        let proseOnly := (String.intercalate "" (cContent.toList.filterMap fun
          | .text t => some t
          | .emph t => some t
          | _ => none)).trimAscii.toString
        if (proseOnly.splitOn ". ").length > 1 then false
        else
          let lhsNorm := normalizeMathToken cs.lhsLatex
          let rhsNorm := normalizeMathToken cs.rhsLatex
          let reasonMath := extractNormalizedMath cs.reason
          let allowedMath := #[lhsNorm, rhsNorm] ++ reasonMath
          let cMath := extractNormalizedMath cContent
          if cMath.isEmpty then false
          else
            cMath.all fun cm =>
              let parts :=
                if (cm.splitOn " = ").length == 2 then cm.splitOn " = "
                else if (cm.splitOn " \\le ").length == 2 then cm.splitOn " \\le "
                else if (cm.splitOn " \\simeq ").length == 2 then cm.splitOn " \\simeq "
                else if (cm.splitOn " \\approx ").length == 2 then cm.splitOn " \\approx "
                else [cm]
              parts.all fun p =>
                let pn := normalizeMathToken p
                allowedMath.any fun am =>
                  !am.isEmpty && (am == pn || (pn.length ≥ 4 && (am.splitOn pn).length > 1))
  | _ => false

private def isL9TrivialCalcReason (reason : Array Inline) : Bool :=
  let raw := String.intercalate "" (reason.toList.map Inline.collectText)
  let words := (raw.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty)
  let low := (String.intercalate " " words).trimAscii.toString.toLower
  low.startsWith "by reflexivity" || low.startsWith "by definition" ||
  low.startsWith "by rfl" || low.startsWith "by eq.refl" ||
  low.startsWith "by le_refl" || low.startsWith "by le_rfl" ||
  low.startsWith "by non-expansion"

/-- Eliminate tautological 1-child `⊕` leaves and vacuous hypothesis/routine children whose
contents merely restate the parent's claim or formula without introducing new mathematics,
diagrams, or sub-children, while preserving `origin?` provenance and `L9` `vcc-calc` subproofs. -/
partial def collapseTautologicalSingleChild : ProofNode → ProofNode
  | .step id content children goal? diag? origin? isWrap defExp startsPara leadHead? trust? inlineMeta =>
      let children0 := children.map collapseTautologicalSingleChild
      let nonVac := children0.filter (!isVacuousHypOrRoutineChild ·)
      let children' :=
        if !isWrap && !nonVac.isEmpty then nonVac
        else children0
      let allVacuous := !isWrap && !children'.isEmpty && children'.all isVacuousHypOrRoutineChild
      let collapsed : Option (Option String) :=
        if allVacuous then
          let firstOrig := children'.findSome? fun
            | .step _ _ _ _ _ o _ _ _ _ _ _ => o
            | _ => none
          some firstOrig
        else if !isWrap && children'.size == 1 then
          match children'[0]! with
          | c@(.step _ cContent cChildren _ cDiag? cOrigin? _ _ _ _ _ _) =>
              if cChildren.isEmpty && cDiag?.isNone && !containsSorryText c &&
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
      let isCCCalc := id.startsWith "vcc-calc" || id.startsWith "vcc-hybrid-chain"
      let steps' := steps.map fun (cs, ch) =>
        let ch0 := ch.map collapseTautologicalSingleChild
        let nonVac := ch0.filter (!isVacuousHypOrRoutineChild ·)
        let ch1 := if !nonVac.isEmpty then nonVac else ch0
        let canEmpty := !isCCCalc || isL9TrivialCalcReason cs.reason
        let chFinal :=
          if canEmpty && !ch1.isEmpty && ch1.all isVacuousHypOrRoutineChild then #[]
          else if canEmpty && ch1.size == 1 && isCalcStepRestatement cs ch1[0]! then #[]
          else ch1
        (cs, chFinal)
      .calcChain id intro steps' goal? origin?
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

private def kvStr? (kv : MData) (k : Name) : Option String :=
  match kv.find k with
  | some (DataValue.ofString s) => some s
  | _ => none

private partial def unwrapAnyByLeafMData? (e : Expr) : Option (String × String × Expr) :=
  match unwrapByLeafMData? e with
  | some hit => some hit
  | none =>
      match e with
      | .mdata kv inner =>
          if (kvStr? kv `ccVerboseKind).isSome then
            none
          else
            match unwrapAnyByLeafMData? inner with
            | some (k, s, inner') => some (k, s, .mdata kv inner')
            | none => none
      | .lam nm ty b bi =>
          if !b.hasLooseBVar 0 then
            match unwrapAnyByLeafMData? b with
            | some (k, s, inner') => some (k, s, .lam nm ty inner' bi)
            | none => none
          else none
      | _ => none

private def isFalseGoalExpr (e : Expr) : Bool :=
  e.consumeMData.isConstOf ``False

private def lowercaseForClause (s : String) : String :=
  match s.toList with
  | c1 :: c2 :: rest =>
      if c1.isUpper && c2.isLower then
        String.ofList (c1.toLower :: c2 :: rest)
      else s
  | _ => s

private def isGerundOpener (s : String) : Bool :=
  let words := (s.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  match words with
  | w0 :: w1 :: _ =>
      let l0 := w0.toLower
      let l1 := w1.toLower
      let gerundVerbs := [
        "multiplying", "dividing", "adding", "subtracting", "summing", "combining",
        "applying", "substituting", "rewriting", "unfolding", "rearranging",
        "factoring", "simplifying", "canceling", "cancelling", "expanding",
        "telescoping", "averaging", "integrating", "taking", "replacing",
        "lifting", "pushing", "pulling", "composing", "attaching", "bounding",
        "comparing", "dropping", "keeping", "splitting", "grouping", "collecting",
        "using", "chaining", "evaluating", "restricting", "conditioning", "inverting"
      ]
      gerundVerbs.contains l0 ||
      (l0.endsWith "ing" && (l1 == "both" || l1 == "over" || l1 == "by" || l1 == "the" ||
        l1 == "two" || l1 == "each" || l1 == "all" || l1 == "out"))
  | _ => false

private def startsWithPreposition (s : String) : Bool :=
  let low := s.trimAscii.toString.toLower
  low.startsWith "by " || low.startsWith "from " || low.startsWith "via " ||
  low.startsWith "since " || low.startsWith "using " || low.startsWith "applying " ||
  low.startsWith "under " || low.startsWith "through " || low.startsWith "after " ||
  low.startsWith "with "

private def containsFiniteVerb (s : String) : Bool :=
  let words := (s.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  words.any fun w =>
    let clean := ((w.replace "," "").replace "." "").replace ";" "" |>.toLower
    clean == "gives" || clean == "shows" || clean == "yields" || clean == "implies" ||
    clean == "establishes" || clean == "proves" || clean == "forces" || clean == "ensures" ||
    clean == "entails" || clean == "holds" || clean == "follows"

private def endsWithTransitiveVerb (s : String) : Bool :=
  let words := (s.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  match words.getLast? with
  | some w =>
      let clean := ((w.replace "," "").replace "." "").replace ";" "" |>.toLower
      clean == "gives" || clean == "shows" || clean == "yields" || clean == "implies" ||
      clean == "establishes" || clean == "proves" || clean == "forces" || clean == "ensures" ||
      clean == "entails" || clean == "that"
  | none => false

private def formatCalcReasonText (label : String) : String :=
  let s := label.trimAscii.toString
  let low := s.toLower
  if low == "reflexivity" || low == "eq.refl" || low == "rfl" then
    "by definition"
  else if startsWithPreposition s || isGerundOpener s || containsFiniteVerb s then
    s
  else
    s!"by {s}"

private def leafHasGerundLead (low : String) : Bool :=
  [ "counting ", "summing ", "multiplying ", "dividing ", "rewriting ",
    "applying ", "absorbing ", "combining ", "substituting ", "partitioning ",
    "conditioning ", "unfolding ", "expanding ", "bounding ", "comparing ",
    "splitting ", "checking ", "verifying ", "tracing ", "inducting "
  ].any fun g => low.startsWith g

private def leafHasFiniteVerb (low : String) : Bool :=
  let padded := " " ++ low ++ " "
  [ " is ", " are ", " was ", " were ", " has ", " have ", " had ",
    " does ", " do ", " did ", " can ", " may ", " must ", " will ", " shall ",
    " holds ", " hold ", " follows ", " follow ", " gives ", " give ",
    " yields ", " yield ", " establishes ", " establish ", " implies ", " imply ",
    " shows ", " show ", " satisfies ", " satisfy ", " agrees ", " agree ",
    " contradicts ", " contradict ", " reduces ", " reduce ", " vanishes ", " vanish ",
    " equals ", " equal ", " remains ", " remain ", " ensures ", " ensure "
  ].any fun v => (padded.splitOn v).length > 1

private def leafSmartLowerFirst (s : String) : String :=
  if s.startsWith "The " then "the " ++ (s.drop 4).toString
  else if s.startsWith "A " then "a " ++ (s.drop 2).toString
  else if s.startsWith "An " then "an " ++ (s.drop 3).toString
  else
    let firstWord := (s.splitOn " ").headD s
    let keepProper :=
      [ "Markov", "Chernoff", "Hoeffding", "Bernstein", "Chebyshev", "Jensen",
        "Bayes", "Keccak", "Sponge", "Boneh", "Shoup" ].any fun p => firstWord.startsWith p
    if keepProper then s
    else match s.toList with
      | c1 :: c2 :: _ =>
          if c1.isUpper && c2.isLower then lowercaseFirst s else s
      | _ => s

private def stripApplyingLead (s : String) : String :=
  let low := s.toLower
  if low.startsWith "applying the " || low.startsWith "applying a " || low.startsWith "applying an " then
    (s.drop 9).trimAscii.toString
  else s

private def formatByLeafInlines (summary : String) (conclInl : Array Inline) : Array Inline :=
  let s0 := summary.trimAscii.toString
  let s := if s0.endsWith "," then (s0.dropEnd 1).trimAscii.toString else s0
  let hadTrailingComma := s0.endsWith ","
  if s.isEmpty then
    #[.text "Direct verification yields "] ++ conclInl ++ #[.text "."]
  else if !hadTrailingComma && (s.endsWith "." || s.endsWith "!" || s.endsWith "?") then
    let parsed := parseProseWithMath s
    match parsed[0]? with
    | some (Inline.text t) => parsed.set! 0 (.text (capitalizeFirst t))
    | _ => parsed
  else
    let parsed : Array Inline := parseProseWithMath s
    let parsedCap : Array Inline := match parsed[0]? with
      | some (Inline.text t) => parsed.set! 0 (.text (capitalizeFirst t))
      | _ => parsed
    let conclHasPunct := match conclInl.back? with
      | some (.text t) =>
          let tt := t.trimAscii.toString
          tt.endsWith "." || tt.endsWith "!" || tt.endsWith "?"
      | some (.displayMath _ p) => p == "." || p == "!" || p == "?"
      | _ => false
    let conclSuffix := if conclHasPunct then conclInl else conclInl ++ #[.text "."]
    let low := s.toLower
    let isSubordLead :=
      low.startsWith "by " || low.startsWith "since " || low.startsWith "from " ||
      low.startsWith "using " || low.startsWith "via " || low.startsWith "because " ||
      low.startsWith "under "
    if hadTrailingComma then
      parsedCap ++ #[.text ", "] ++ conclSuffix
    else if isSubordLead then
      if (low.splitOn ",").length > 1 && leafHasFiniteVerb low then
        parsedCap ++ #[.text "."]
      else
        parsedCap ++ #[.text ", "] ++ conclSuffix
    else if leafHasGerundLead low then
      if leafHasFiniteVerb low then
        parsedCap ++ #[.text "."]
      else
        let core := stripApplyingLead s
        parseProseWithMath ("By " ++ leafSmartLowerFirst core ++ ", ") ++ conclSuffix
    else if leafHasFiniteVerb low then
      parsedCap ++ #[.text "."]
    else
      parseProseWithMath ("By " ++ leafSmartLowerFirst s ++ ", ") ++ conclSuffix

private def applyNotationsAtCount (tbl : SymbolTable) (fvs : Array Expr)
    (pending : Array (Nat × Expr × String × Option String))
    (targetCount : Nat) : MetaM SymbolTable := do
  let mut out := tbl
  for (nBind, closedPat, sym, _) in pending do
    if nBind == targetCount && nBind ≤ fvs.size then
      let instPat := closedPat.instantiateRev (fvs.extract 0 nBind)
      if !instPat.hasLooseBVars && !instPat.hasExprMVar then
        let patNorm ← normalizeForPresentation instPat
        out := out.withExprAlias patNorm sym
  return out

private def isSetMembershipHead (e : Expr) : Bool :=
  let clean := e.consumeMData
  clean.isAppOf ``Membership.mem || clean.isAppOf `Set.mem

private def hasSetMemLeafConst (e : Expr) : Bool :=
  e.foldConsts (init := false) fun cn acc =>
    acc ||
    cn == `Set.mem_image || cn == `Set.mem_image2 ||
    cn == `Set.mem_singleton_iff || cn == `Set.mem_singleton ||
    cn == `Set.mem_setOf_eq || cn == `Set.mem_setOf

private def collectConciseProofHyps (tbl : SymbolTable) (proof : Expr) :
    MetaM (Array (Array Inline)) := do
  let fvarIds := (Lean.collectFVars {} proof).fvarIds
  let lctx ← getLCtx
  let mut out : Array (Array Inline) := #[]
  let mut seen : Std.HashSet String := {}
  for fid in fvarIds do
    if let some d := lctx.find? fid then
      if d.isAuxDecl || d.isImplementationDetail then continue
      if !(← isProp d.type) || (← isAmbientTypeclass d.type) then continue
      if exprHasRawPlumbing d.type then continue
      if ← isVacuousRenderedEq tbl d.type then continue
      let hypInl ← renderProposition tbl d.type
      let key := inlinesCanonicalKey hypInl
      if key.length > 0 && key.length ≤ 60 && !seen.contains key then
        seen := seen.insert key
        out := out.push hypInl
        if out.size ≥ 2 then break
  return out

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

  -- 0a. Preserve local `With notation` (`with_notation` / `with_notation_let`) shorthands
  -- throughout the entire recursive proof tree before anything else consumes `.mdata`.
  if let .mdata kv inner := proof then
    match kvStr? kv `ccVerboseKind with
    | some "with_notation" =>
        if let (some sym, .app fn val) := (kvStr? kv `ccVerboseLabel, inner.consumeMData) then
          if let .lam _ _ body _ := fn.consumeMData then
            let mut nextTbl := ctx.tbl
            nextTbl := nextTbl.withExprAlias val.consumeMData sym
            let valNorm ← normalizeForPresentation val
            nextTbl := nextTbl.withExprAlias valNorm sym
            return ← decompileProof { ctx with tbl := nextTbl } expected (body.instantiate1 val) (fuel - 1)
        return ← decompileProof ctx expected inner (fuel - 1)
    | some "with_notation_let" =>
        if let (some sym, .letE nm ty val body _) := (kvStr? kv `ccVerboseLabel, inner.consumeMData) then
          return ← withLetDecl nm ty val fun fv => do
            let mut nextTbl := ctx.tbl
            nextTbl := nextTbl.withExprAlias fv sym
            nextTbl := nextTbl.withExprAlias val.consumeMData sym
            let valNorm ← normalizeForPresentation val
            nextTbl := nextTbl.withExprAlias valNorm sym
            decompileProof { ctx with tbl := nextTbl } expected (body.instantiate1 fv) (fuel - 1)
        return ← decompileProof ctx expected inner (fuel - 1)
    | _ => pure ()

  -- 0b. Peel leading non-Prop `let` bindings on `expected` (e.g., `Write R = ... and S = ...`
  -- hoisted in the theorem statement) so paper shorthands persist through the whole proof tree.
  if let .letE nm ty val body _ := expected.consumeMData then
    if !(← isProp ty) then
      return ← withLetDecl nm ty val fun fv => do
        let mut nextTbl := ctx.tbl
        if !(← isAmbientTypeclass ty) then
          let symOpt? :=
            match cleanBinderName? nm with
            | some s => some s
            | none => if !nm.isAnonymous && !nm.hasMacroScopes then some nm.toString else none
          if symOpt?.isSome then
            let rawSymTex ← exprToLatex fv nextTbl
            let symTex :=
              if !nextTbl.usedNames.contains rawSymTex then rawSymTex
              else
                let cands := #[rawSymTex ++ "'", rawSymTex ++ "''"] ++
                  (#["w", "z", "u", "v", "t", "y"].flatMap fun p =>
                    (Array.range 5).map fun i => s!"{p}_\{{i + 1}}")
                (cands.find? (!nextTbl.usedNames.contains ·)).getD (rawSymTex ++ "'")
            nextTbl := nextTbl.withUsedName symTex
            nextTbl := nextTbl.withExprAlias val.consumeMData symTex
            let valNorm ← normalizeForPresentation val
            nextTbl := nextTbl.withExprAlias valNorm symTex
            nextTbl := nextTbl.withExprAlias fv symTex
        let nextProof ← match proof.consumeMData with
          | .letE _ pty pval pbody _ =>
              let same ← try
                if ← isProp pty then pure false
                else withTransparency .reducible (isDefEq pval val)
              catch _ => pure false
              pure (if same then pbody.instantiate1 fv else proof)
          | _ => pure proof
        decompileProof { ctx with tbl := nextTbl } (body.instantiate1 fv) nextProof (fuel - 1)

  -- 0c. Honor `by_leaf` (`unwrapByLeafMData?`): stop recursion immediately and emit one clean leaf
  -- step using the author summary (while preserving `sorryAx` honestly).
  if let some (_, summary, inner) := unwrapAnyByLeafMData? proof then
    if exprContainsSorryAx inner then
      let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      return #[.step s!"sorry-leaf-{fuel}" #[.text "[UNPROVED: sorry]"] #[] (some goal)]
    if !ctx.atRootConclusion && (← isVacuousRenderedEq ctx.tbl expected) then
      return #[]
    modify (·.markEmitted)
    let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
    let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
    let content :=
      if isFalseGoalExpr expected then #[.text "This contradicts the assumed bound."]
      else formatByLeafInlines summary conclInl
    return #[.step s!"byleaf-{fuel}" content #[] (some goal)]

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

  -- 2b. Collapse pure `Set.mem_image` / `Set.mem_singleton_iff` proofs (`Sσ ∈ S*`) into a single
  -- mathematical sentence instead of 6 nested existential/conjunction steps (`B4`), and apply the
  -- hard AST opacity wall against raw plumbing terms inside expanded sub-lemmas (`lemmaDepth ≥ 1`).
  if !exprContainsSorryAx proof && !exprContainsSorryAx expected then
    if isSetMembershipHead expected && hasSetMemLeafConst proof then
      modify (·.markEmitted)
      let conclInl ← renderProposition ctx.tbl expected
      let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      let hyps ← collectConciseProofHyps ctx.tbl proof
      let content : Array Inline :=
        match hyps.toList with
        | [h0] => #[.text "Since "] ++ h0 ++ #[.text ", "] ++ conclInl ++ #[.text "."]
        | h0 :: h1 :: _ => #[.text "Since "] ++ h0 ++ #[.text " and "] ++ h1 ++ #[.text ", "] ++ conclInl ++ #[.text "."]
        | [] => #[.text "By definition, "] ++ conclInl ++ #[.text "."]
      return #[.step s!"mem-{fuel}" content #[] (some goal)]
    if ctx.lemmaDepth ≥ 1 && exprHasRawPlumbing expected then
      return #[.routineReceipt s!"routine-{fuel}" "low-level wiring and representation verification" 1 #[] none]

  -- 3. Unwrap leading binders (`intro`) transparently into the live `LocalContext`,
  -- avoiding macro-scoped shadow collisions (`x` -> `w'`) and introducing arbitrary variables
  -- inside subgoal universal quantifiers without repetitive "Fix any ".
  let chooseBinderName (nm pnm : Name) : MetaM Name := do
    let base :=
      if !pnm.hasMacroScopes && (cleanBinderName? pnm).isSome then pnm
      else if (cleanBinderName? nm).isSome then nm
      else pnm
    freshShadowFreeName base "x"
  let joinIntroWithNext (varTex : String) (nodes : Array ProofNode) : Array ProofNode := Id.run do
    if nodes.isEmpty then return nodes
    let allMath := nodes.flatMap collectProofNodeMath
    if !mathDispAppearsIn allMath varTex then return nodes
    for idx in [:nodes.size] do
      match nodes[idx]! with
      | .step id content ch goal diag orig false defExp sp lh tr im =>
          let newContent : Array Inline :=
            match content[0]? with
            | some (Inline.text "For any ") =>
                #[.text "For any ", .inlineMath varTex, .text ", "] ++ content.extract 1 content.size
            | some (Inline.text t) =>
                #[.text "For any ", .inlineMath varTex, .text ", "] ++
                  content.set! 0 (.text (lowercaseForClause t))
            | _ =>
                #[.text "For any ", .inlineMath varTex, .text ", "] ++ content
          return nodes.set! idx (.step id newContent ch goal diag orig false defExp sp lh tr im)
      | .calcChain id intro steps goal orig =>
          let newIntro : Array Inline :=
            match intro[0]? with
            | some (Inline.text "For any ") =>
                #[.text "For any ", .inlineMath varTex, .text ", "] ++ intro.extract 1 intro.size
            | some (Inline.text t) =>
                #[.text "For any ", .inlineMath varTex, .text ", "] ++
                  intro.set! 0 (.text (lowercaseForClause t))
            | _ =>
                #[.text "For any ", .inlineMath varTex, .text ", "] ++ intro
          return nodes.set! idx (.calcChain id newIntro steps goal orig)
      | _ => pure ()
    return nodes
  let instantiatePendingNotations (baseCtx : DecompCtx) (fv : Expr) : MetaM DecompCtx := do
    let fvs := baseCtx.peeledFVars.push fv
    let tbl ← applyNotationsAtCount baseCtx.tbl fvs baseCtx.pendingNotations fvs.size
    return { baseCtx with tbl, peeledFVars := fvs }
  match expected.consumeMData, proof with
  | .forallE nm dom body bi, .lam pnm _ pbody _ =>
      let useName ← chooseBinderName nm pnm
      let needIntro ←
        if !ctx.atRootConclusion && bi == .default && body.hasLooseBVar 0 then
          pure (!(← isProp dom) && !(← isAmbientTypeclass dom))
        else pure false
      return ← withLocalDecl useName bi dom fun fv => do
        let varTex ← exprToLatex fv ctx.tbl
        let nextCtx ← instantiatePendingNotations { ctx with tbl := ctx.tbl.withUsedName varTex } fv
        let nodes ← decompileProof nextCtx (body.instantiate1 fv) (pbody.instantiate1 fv) (fuel - 1)
        if needIntro then
          return joinIntroWithNext varTex nodes
        return nodes
  | _, .mdata _ inner =>
      return ← decompileProof ctx expected inner (fuel - 1)
  | _, .lam pnm _ pbody _ =>
      let expR ← withTransparency .reducible (whnf expected.consumeMData)
      let expW ← if expR.consumeMData.isForall then pure expR else whnfD expected.consumeMData
      if let .forallE nm dom body bi := expW.consumeMData then
        let useName ← chooseBinderName nm pnm
        let expNotForall := !expected.consumeMData.isForall
        let needIntro ←
          if (!ctx.atRootConclusion || expNotForall) && bi == .default && body.hasLooseBVar 0 then
            pure (!(← isProp dom) && !(← isAmbientTypeclass dom))
          else pure false
        return ← withLocalDecl useName bi dom fun fv => do
          let varTex ← exprToLatex fv ctx.tbl
          let nextCtx ← instantiatePendingNotations { ctx with tbl := ctx.tbl.withUsedName varTex } fv
          let nodes ← decompileProof nextCtx (body.instantiate1 fv) (pbody.instantiate1 fv) (fuel - 1)
          if needIntro then
            return joinIntroWithNext varTex nodes
          return nodes
      else pure ()
  | _, .letE nm ty val body _ =>
      let isP ← isProp ty
      if isP then
        if body == .bvar 0 then
          return ← decompileProof ctx ty val (fuel - 1)
        if !exprContainsSorryAx val && (← isVacuousRenderedEq ctx.tbl ty) then
          return ← withLetDecl nm ty val fun fv =>
            decompileProof ctx expected (body.instantiate1 fv) (fuel - 1)
        -- Local intermediate fact (`have h : P := ...`): choose causal vs. parallel transition
        -- without emitting `"To prove the claim,"`.
        let usesPrev := match ctx.lastFactFVar? with
          | some prevId => (Lean.collectFVars {} val).fvarIds.contains prevId
          | none => false
        let factNodes ← decompileProof { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false } ty val (fuel - 1)
        let goal ← buildGoalState ctx.tbl ty (ctx.lemmaDepth ≥ 1)
        let factInl := ensureSymbolicPredClause (← renderProposition ctx.tbl ty)
        let opener ← do
          let st ← get
          if usesPrev && !(ctx.isProofStart && ctx.factIndex == 0 && st.stepCounter == 0) then
            let causalOps := #["Hence,", "Therefore,", "Consequently,", "Thus,"]
            let op := causalOps[(ctx.factIndex + st.stepCounter) % causalOps.size]!
            modify (·.markEmitted (some op))
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
        return ← withLetDecl nm ty val fun fv => do
          let symOpt? :=
            if !(← isAmbientTypeclass ty) then
              match cleanBinderName? nm with
              | some s => some s
              | none => if !nm.isAnonymous && !nm.hasMacroScopes then some nm.toString else none
            else none
          let mut nextTbl := ctx.tbl
          let mut symTex? : Option String := none
          if symOpt?.isSome then
            let rawTex ← exprToLatex fv nextTbl
            let sTex := pickFreshLocalSymbol nextTbl.usedNames rawTex
            symTex? := some sTex
            nextTbl := nextTbl.withUsedName sTex
            nextTbl := nextTbl.withExprAlias fv sTex
            nextTbl := nextTbl.withExprAlias val.consumeMData sTex
            let valNorm ← normalizeForPresentation val
            nextTbl := nextTbl.withExprAlias valNorm sTex
          let rest ← decompileProof { ctx with tbl := nextTbl } expected (body.instantiate1 fv) (fuel - 1)
          match symTex? with
          | some symTex =>
              if !exprHasRawPlumbing val && !val.consumeMData.isFVar then
                let allMath := rest.flatMap collectProofNodeMath
                if mathDispAppearsIn allMath symTex then
                  let valTex ← exprToLatex val ctx.tbl
                  if !valTex.isEmpty && valTex != symTex then
                    let defStep : ProofNode :=
                      .step s!"let-{fuel}"
                        #[.text "Define ", .inlineMath s!"{symTex} := {valTex}", .text "."]
                        #[] none none none false
                    return #[defStep] ++ rest
              return rest
          | none => return rest
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
            let bodyInl := ensureSymbolicPredClause (← renderProposition ctx.tbl bodyTy)
            let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
            return #[.step s!"funext-{fuel}"
              (#[.text "Evaluating pointwise at ", .inlineMath xTex, .text ", "] ++ bodyInl ++ #[.text "."])
              subNodes (some goal)]
      modify (·.markEmitted)
      let subNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
      let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
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
        let pInl := ensureSymbolicPredClause (← renderProposition ctx.tbl pTy)
        let qInl := ensureSymbolicPredClause (← renderProposition ctx.tbl qTy)
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
        let pInl := ensureSymbolicPredClause (← renderProposition ctx.tbl aTy)
        let qInl := ensureSymbolicPredClause (← renderProposition ctx.tbl bTy)
        let pGoal ← buildGoalState ctx.tbl fwdTy (ctx.lemmaDepth ≥ 1)
        let qGoal ← buildGoalState ctx.tbl revTy (ctx.lemmaDepth ≥ 1)
        let step1 : ProofNode := .step s!"iffL-{fuel}" (#[.text "Assume first that "] ++ pInl ++ #[.text "; we show "] ++ qInl ++ #[.text "."]) pNodes (some pGoal)
        let step2 : ProofNode := .step s!"iffR-{fuel}" (#[.text "Conversely, assume "] ++ qInl ++ #[.text "; we show "] ++ pInl ++ #[.text "."]) qNodes (some qGoal)
        return dedupSiblings #[step1, step2]

  -- 3c2. Handle kernel structure projections (`.proj` for `And.left`/`And.right`/`Prod.fst`/`Prod.snd`)
  -- with `"In particular, ..."` rather than `"By right,"` / `"By left,"`.
  if let .proj _ _ inner := proof.consumeMData then
    if !ctx.atRootConclusion && !exprContainsSorryAx proof && (← isVacuousRenderedEq ctx.tbl expected) then
      return #[]
    modify (·.markEmitted)
    if isFalseGoalExpr expected then
      let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      return #[.step s!"proj-{fuel}" #[.text "This contradicts the assumed bound."] #[] (some goal)]
    let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
    let hasSorry := exprContainsSorryAx proof
    let goal? ←
      if ctx.atRootConclusion || hasSorry then
        some <$> buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      else pure none
    if !hasSorry && (unwrapHypothesisFVar? inner).isSome then
      return #[.step s!"proj-{fuel}" (#[.text "In particular, "] ++ conclInl ++ #[.text "."]) #[] goal? none none (!ctx.atRootConclusion)]
    let subNodes ← try
      let innerTy ← inferType inner
      if ← isProp innerTy then
        decompileProof { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false } innerTy inner (fuel - 1)
      else pure #[]
    catch _ => pure #[]
    return #[.step s!"proj-{fuel}" (#[.text "In particular, "] ++ conclInl ++ #[.text "."]) subNodes goal? none none (!ctx.atRootConclusion)]

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
        let bodyInl := ensureSymbolicPredClause (← renderProposition ctx.tbl bodyTy)
        let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
        let leadInl : Array Inline := match binderTex? with
          | some bTex =>
              if bTex == wTex then #[.text "Taking witness ", .inlineMath wTex, .text ", "]
              else #[.text "Taking ", .inlineMath s!"{bTex} := {wTex}", .text ", "]
          | none => #[.text "Taking witness ", .inlineMath wTex, .text ", "]
        return #[.step s!"exists-{fuel}" (leadInl ++ bodyInl ++ #[.text "."]) subNodes (some goal)]

  -- 3e. Handle `False.elim` and `absurd` cleanly (never emit `⊥` in paper prose)
  if let .const head _ := proof.getAppFn.consumeMData then
    if head == ``False.elim || head == ``absurd then
      modify (·.markEmitted)
      let subNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
      let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      let msg :=
        if isFalseGoalExpr expected then "This contradicts the assumed bound."
        else "This yields a contradiction."
      return #[.step s!"contra-{fuel}" #[.text msg] subNodes (some goal)]

  -- 3f. Never emit compiler aux decls (`_simp_1`, `_proof_1`, ...) or structural congruence/cast
  -- combinators (`congr*`, `and_congr*`, `propext`, `Eq.ndrec`, ...) as named mathematical lemmas.
  if let .const head _ := proof.getAppFn.consumeMData then
    if isStructuralCongrOrCast head then
      if ctx.lemmaDepth ≥ 1 && !exprContainsSorryAx proof && exprHasRawPlumbing expected then
        return #[.routineReceipt s!"routine-{fuel}" "low-level wiring and representation verification" 1 #[] none]
      let subNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
      if subNodes.isEmpty then
        let rk := if head == `eq_self || head == ``Eq.refl || head == ``rfl then
          RoutineKind.reflexivity.label else RoutineKind.congruenceAndExt.label
        return #[.routineReceipt s!"routine-{fuel}" rk 1 #[] none]
      else if isFalseGoalExpr expected then
        return #[.step s!"wrap-congr-{fuel}" #[.text "This contradicts the assumed bound."]
          subNodes none none none true false]
      else
        let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
        let verb := if isCompilerAuxDecl head then "By simplification, " else "By substitution of equals, "
        return #[.step s!"wrap-congr-{fuel}"
          (#[.text verb] ++ conclInl ++ #[.text "."])
          subNodes none none none true false]

  -- 4. Detect `calc` / `cc_calc` chains (`Trans.trans` / `Eq.trans` / `LE.le.trans` / `le_trans` / `SubstitutesWithin`)
  let chain ← flattenCalcChain proof expected
  if chain.size ≥ 2 then
    let mut calcSteps : Array (CalcStep × Array ProofNode) := #[]
    let mut survivingChain : Array (Expr × Expr) := #[]
    let mut allParsed := true
    for (sp, stProp) in chain do
      match ← splitBinaryRelation? ctx.tbl stProp with
      | some (rel, lhs, rhs) =>
          let lhsTex ← exprToLatex lhs ctx.tbl
          let rhsTex ← exprToLatex rhs ctx.tbl
          if rel == "=" && lhsTex == rhsTex && !exprContainsSorryAx sp then
            continue
          survivingChain := survivingChain.push (sp, stProp)
          let subCtx := { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
          let spUnwrapped := unwrapCastProof sp
          let isTrivCalcSubproof := !exprContainsSorryAx sp &&
            (spUnwrapped.consumeMData.isFVar ||
             spUnwrapped.getAppFn.consumeMData.isConstOf ``Eq.refl ||
             spUnwrapped.getAppFn.consumeMData.isConstOf ``rfl)
          let subNodes ←
            if isTrivCalcSubproof then pure #[]
            else decompileProof subCtx stProp sp (fuel - 1)
          let isNonAlgebraicRel :=
            rel.startsWith "\\simeq" || rel.startsWith "\\approx" ||
            rel.startsWith "\\preceq" || rel.startsWith "\\xrightarrow"
          let reason : Array Inline ←
            if exprContainsSorryAx sp then pure #[.text "[UNPROVED: sorry]"]
            else match spUnwrapped.getAppFn.consumeMData with
            | .const cn _ =>
                if cn == ``dite || cn == ``ite || cn == ``Decidable.byCases || cn == `Classical.byCases then
                  pure #[.text "by case analysis"]
                else if cn == ``Eq.refl || cn == ``rfl || cn == ``funext || cn == `Function.funext || cn == ``propext then
                  pure #[.text "by definition"]
                else if isCoreOrMathlibIn env cn then
                  if isNonAlgebraicRel then pure #[.text "by the checked subargument"]
                  else if rel == "=" then pure #[.text "by calculation"]
                  else pure #[.text "by algebra"]
                else
                  pure #[.text (formatCalcReasonText (humanLemmaLabel env cn))]
            | .fvar _ => pure #[.text "by assumption"]
            | _ => pure #[.text "by definition"]
          let cs : CalcStep := {
            lhsLatex := lhsTex
            relationLatex := rel
            rhsLatex := rhsTex
            reason
            diagramHtml? := none
          }
          calcSteps := calcSteps.push (cs, subNodes)
      | none => allParsed := false
    if allParsed then
      if calcSteps.size == 1 then
        let (sp1, stProp1) := survivingChain[0]!
        return ← decompileProof ctx stProp1 sp1 (fuel - 1)
      else if calcSteps.isEmpty && !ctx.atRootConclusion && !exprContainsSorryAx proof then
        return #[.routineReceipt s!"routine-{fuel}" RoutineKind.reflexivity.label 1 #[] none]
      else if !calcSteps.isEmpty then
        let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
        let allEq := calcSteps.all fun (cs, _) => cs.relationLatex == "="
        let eqIntros := #["We compute:", "Direct calculation gives:", "We obtain:"]
        let boundIntros := #["By the triangle inequality:", "Chaining the bounds gives:", "We obtain:"]
        let st ← get
        let introStr :=
          if allEq then eqIntros[st.stepCounter % eqIntros.size]!
          else boundIntros[st.stepCounter % boundIntros.size]!
        modify (·.markEmitted (some introStr))
        let intro : Array Inline := #[.text introStr]
        return #[.calcChain s!"calc-{fuel}" intro calcSteps (some goal)]

  -- 5. Direct hypothesis (`assumption`) or application headed by a local hypothesis `.fvar id`
  if let .fvar id := proof.consumeMData then
    if !ctx.atRootConclusion && !exprContainsSorryAx proof && (← isVacuousRenderedEq ctx.tbl expected) then
      return #[]
    modify (·.markEmitted)
    if isFalseGoalExpr expected then
      let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      return #[.step s!"hyp-{fuel}-{id.name}" #[.text "This contradicts the assumed bound."] #[] (some goal)]
    return #[← renderHypothesisStep ctx.tbl expected id s!"hyp-{fuel}-{id.name}"
      (isWrap := false) (onlyUsed := (ctx.lemmaDepth ≥ 1))]

  if let .fvar id := proof.getAppFn.consumeMData then
    if !ctx.atRootConclusion && !exprContainsSorryAx proof && (← isVacuousRenderedEq ctx.tbl expected) then
      return #[]
    modify (·.markEmitted)
    let decl ← id.getDecl
    let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
    let subNodes ← decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
    let hypInl ← renderProposition ctx.tbl decl.type
    let hypLen := (inlinesCanonicalKey hypInl).length
    let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
    let lead : Array Inline :=
      if hypLen > 0 && hypLen ≤ 60 then
        #[.text "By the assumption that "] ++ hypInl ++ #[.text ", "]
      else
        #[.text "By the assumed hypothesis, "]
    let conclPhrase : Array Inline :=
      if isFalseGoalExpr expected then #[.text "this contradicts the assumed bound."]
      else conclInl ++ #[.text "."]
    return #[.step s!"hypapp-{fuel}-{id.name}" (lead ++ conclPhrase) subNodes (some goal)]

  -- 6. Application of a named theorem/lemma (with beta-instantiated cross-lemma recursion & opacity walls!)
  if let .const declName levels := proof.getAppFn.consumeMData then
    let st ← get
    modify (·.markEmitted)
    let hasSorry := exprContainsSorryAx proof
    let isCore := isCoreOrMathlibIn env declName
    let isOrderMono :=
      declName == `add_le_add || declName == `mul_le_mul_of_nonneg_left ||
      declName == `mul_le_mul_of_nonneg_right || declName == `le_trans ||
      declName == `le_add_of_nonneg_left || declName == `le_add_of_nonneg_right ||
      declName == `sub_le_sub || declName == `sub_le_sub_left ||
      declName == `div_le_div_of_nonneg_left || declName == `add_pos'
    let isCaseSplit := declName == ``Or.elim || declName == ``Or.casesOn ||
      declName == ``Bool.rec || declName == ``Option.rec || declName == ``Sum.rec || declName == ``Or.rec ||
      declName == ``dite || declName == ``ite || declName == ``Decidable.byCases ||
      declName == `Classical.byCases || declName == ``Decidable.casesOn
    let isProj := declName == ``And.left || declName == ``And.right ||
      declName == ``Prod.fst || declName == ``Prod.snd ||
      declName == ``PProd.fst || declName == ``PProd.snd
    let isDisjInj := declName == ``Or.inl || declName == ``Or.inr ||
      declName == ``Sum.inl || declName == ``Sum.inr
    let isCasesDestruct := !isCaseSplit && !isProj && !isDisjInj &&
      (declName.toString.endsWith ".casesOn" || declName == ``Exists.elim)
    let isInductionRec :=
      !isCaseSplit && !isCasesDestruct && !declName.toString.startsWith "Eq." &&
      (declName == ``Nat.rec || declName == `Nat.recAux || declName == ``Nat.recOn ||
       declName == ``List.rec || declName == ``List.recOn ||
       declName.toString.endsWith ".rec" || declName.toString.endsWith ".recOn" ||
       declName.toString.endsWith ".recAux")
    let isExt := !isCore && (declName.toString.endsWith ".ext" || declName == ``Subtype.ext)
    if !hasSorry && !isProj && !isDisjInj && !isCaseSplit && !isInductionRec && !isCasesDestruct then
      if isAstPlumbingHead declName || (ctx.lemmaDepth ≥ 1 && exprHasRawPlumbing expected) then
        return #[.routineReceipt s!"routine-{fuel}" "low-level wiring and representation verification" 1 #[] none]
    let premiseNodes ←
      if isProj && !hasSorry then pure #[]
      else decompilePremiseArgs ctx (fun c e p => decompileProof c e p (fuel - 1)) proof
    let ov := getOverlay env declName
    let mut expandedBody : Array ProofNode := #[]
    let mut isWrap := false
    if shouldExpandLemma env ctx declName then
      if let some (.thmInfo info) := env.find? declName then
        if let some (instTy, instVal) ← betaInstantiateTheorem info levels proof.getAppArgs then
          isWrap := isTrivialWrapperBody env declName instVal
          let childTbl ← applyNotationsAtCount ctx.tbl #[] ov.theoremNotations 0
          let childCtx : DecompCtx := {
            ctx with
            tbl := childTbl
            seenDecls := ctx.seenDecls.insert declName
            lemmaDepth := ctx.lemmaDepth + 1
            lastFactFVar? := none
            factIndex := 0
            atRootConclusion := false
            isProofStart := false
            peeledFVars := #[]
            pendingNotations := ov.theoremNotations
          }
          expandedBody ← decompileProof childCtx instTy instVal (fuel - 1)
    let mut allChildren : Array ProofNode := #[]
    if let some fb := ov.flowBefore? then
      allChildren := allChildren.push (.flowNote s!"flow-pre-{declName}" fb "margin")
    allChildren := allChildren ++ dedupSiblings (premiseNodes ++ expandedBody)
    if let some fa := ov.flowAfter? then
      allChildren := allChildren.push (.flowNote s!"flow-post-{declName}" fa "margin")
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
    if isOrderMono || isDisjInj || isCasesDestruct || (isProj && !ctx.atRootConclusion) then
      isWrap := true
    let goal? ←
      if isWrap && !hasSorry then pure none
      else some <$> buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
    if hasSorry &&
       !allChildren.any (fun n => n.collectAllText.any (fun t => (t.splitOn "[UNPROVED: sorry]").length > 1)) then
      let sorryGoal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
      allChildren := allChildren.push (.step s!"sorry-child-{fuel}" #[.text "[UNPROVED: sorry]"] #[] (some sorryGoal))
    let hasVisibleNonWrap := allChildren.any fun
      | .step _ _ _ _ _ _ w _ _ _ _ _ => !w
      | _ => true
    let rawConclInl ← renderProposition ctx.tbl expected
    let conclInl := ensureSymbolicPredClause rawConclInl
    let addedHoldVerb := conclInl.size > rawConclInl.size
    let isCitableThm :=
      !isCore && !Lean.isPrivateName declName &&
      (ctx.docDecls.contains declName || ov.title?.isSome || effectiveIsProofJoint env declName) &&
      (match env.find? declName with | some (.thmInfo _) => true | _ => false)
    let mkCite (lbl : String) : Inline :=
      if isCitableThm then .symbol declName.toString lbl false
      else .emph lbl
    let capLabel := capitalizeFirst label.trimAscii.toString
    let content : Array Inline ←
      if isFalseGoalExpr expected then
        pure #[.text "This contradicts the assumed bound."]
      else if isProj then
        pure (#[.text "In particular, "] ++ conclInl ++ #[.text "."])
      else if isCaseSplit then
        pure (#[.text "By case analysis, "] ++ conclInl ++ #[.text "."])
      else if isInductionRec then
        pure (#[.text "By induction, "] ++ conclInl ++ #[.text "."])
      else if isDisjInj then
        pure (#[.text "Hence, "] ++ conclInl ++ #[.text "."])
      else if isCasesDestruct then
        pure (#[.text "From the hypothesis, "] ++ conclInl ++ #[.text "."])
      else if isOrderMono then
        pure (#[.text "By monotonicity, "] ++ conclInl ++ #[.text "."])
      else if isExt || declName == ``Subtype.ext then
        pure (#[.text "By extensionality, "] ++ conclInl ++ #[.text "."])
      else if ctx.atRootConclusion then
        if isCore then
          if startsWithPreposition label then
            pure #[.text s!"{capLabel}, the claim holds."]
          else if containsFiniteVerb label then
            let endPhrase := if endsWithTransitiveVerb label then " the claim." else "."
            pure #[.text s!"{capLabel}{endPhrase}"]
          else
            pure #[.text s!"The claim follows from {label}."]
        else if !hasVisibleNonWrap then
          pure #[.text "This follows from ", mkCite label, .text "."]
        else
          pure #[.text "By ", mkCite label, .text ", the claim holds."]
      else if startsWithPreposition label then
        if isCore then
          pure (#[.text s!"{capLabel}, "] ++ conclInl ++ #[.text "."])
        else
          pure (#[mkCite capLabel, .text ", "] ++ conclInl ++ #[.text "."])
      else if isGerundOpener label then
        let link :=
          if addedHoldVerb then " shows that "
          else match (conclInl[0]? : Option Inline) with
            | some (.inlineMath _) | some (.symbol _ _ true) => " gives "
            | _ => " shows that "
        if isCore then
          pure (#[.text s!"{capLabel}{link}"] ++ conclInl ++ #[.text "."])
        else
          pure (#[mkCite capLabel, .text link] ++ conclInl ++ #[.text "."])
      else if containsFiniteVerb label then
        let sep :=
          if endsWithTransitiveVerb label then (if addedHoldVerb then " that " else " ")
          else ", so "
        if isCore then
          pure (#[.text s!"{capLabel}{sep}"] ++ conclInl ++ #[.text "."])
        else
          pure (#[mkCite capLabel, .text sep] ++ conclInl ++ #[.text "."])
      else
        let prep := if st.stepCounter % 2 == 0 then "By " else "From "
        if isCore then
          pure (#[.text s!"{prep}{label}, "] ++ conclInl ++ #[.text "."])
        else
          pure (#[.text prep, mkCite label, .text ", "] ++ conclInl ++ #[.text "."])
    return #[.step s!"app-{declName}-{fuel}" content allChildren goal?
      none (some declName.toString) isWrap]

  -- 7. Fallback: checked goal statement (flagging any unexpanded `sorryAx`)
  if exprContainsSorryAx proof then
    let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
    return #[.step s!"sorry-fallback-{fuel}" #[.text "[UNPROVED: sorry]"] #[] (some goal)]
  if !ctx.atRootConclusion && (← isVacuousRenderedEq ctx.tbl expected) then
    return #[]
  let goal ← buildGoalState ctx.tbl expected (ctx.lemmaDepth ≥ 1)
  if isFalseGoalExpr expected then
    return #[.step s!"step-{fuel}" #[.text "This contradicts the assumed bound."] #[] (some goal)]
  let rawConclInl ← renderProposition ctx.tbl expected
  let conclInl := ensureSymbolicPredClause rawConclInl
  let lead := if conclInl.size > rawConclInl.size then "We obtain that " else "We obtain "
  return #[.step s!"step-{fuel}" (#[.text lead] ++ conclInl ++ #[.text "."]) #[] (some goal)]

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
  let tbl0 := buildSymbolTable env declName
  let tbl1 ← applyNotationsAtCount tbl0 #[] ov.theoremNotations 0
  let tbl ← forallTelescope info.type fun fvars _ => do
    let mut t := tbl1
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      if !(← isSuppressedLocalDecl decl) && !(← isProp decl.type) then
        let sym ← exprToLatex fv t
        t := t.withUsedName sym
        t := t.withUsedName (cleanBinderName decl.userName)
    return t
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
      (capDiagramHtmlDepth 0 none 0)
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
