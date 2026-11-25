/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Ontology
import Informalization.Core.Routine
import Informalization.Core.Explanation
import Informalization.Core.ProofGraph
import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
import ConstructiveCryptography.CryptographicAlgebra.Star
import ConstructiveCryptography.Instances.Algebra
import ConstructiveCryptography.Instances.Game
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Game.MBO
import RandomSystems.Game.UntilBad

/-!
# Zero-Cost `Expr.mdata` Trace Markers & Maurer-Voice Proof Decompiler

Provides kernel-transparent `Expr.mdata` tags (`ccVerboseKind`, `ccVerboseLabel`,
`ccVerboseReason`, `ccVerboseRole`, `ccVerboseCount`) emitted by `Informalization.Verbose.Syntax`,
together with a high-priority `ProofGraph.RuleExplainer` (`priority := 500`) registered at
module initialization.

* **Zero trust-base impact:** `Expr.mdata` is ignored by the Lean 4 kernel (`isDefEq`, `inferType`,
  and `#print axioms` remain strictly within `{propext, Classical.choice, Quot.sound}`).
* **1-to-1 structural fidelity:** Preserves `Write`, `Introduce_hybrid`, `Claim`, `Fact`,
  backward `It_suffices_to_show`, `Tightness_sandwich` lower/upper bounds, `Exhibit_simulator`,
  `By_extended_H_technique`, annotated `cc_calc` steps, and `By_CC_routine` compression receipts.
* **CI hygiene lock:** Strictly uses authentic CC literature phrasing (*"attached to the
  $E$-interface"*, *"at the left/right interface"*, *"underlying system $G^{-}$ obtained by
  ignoring the MBO"*) and never emits forbidden Lean-isms.
-/

namespace Informalization.Verbose.Trace

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Routine
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph

/-! ## 1. `MData` Keys & Wrapper Helpers -/

def ccVerboseKindKey   : Name := `ccVerboseKind
def ccVerboseLabelKey  : Name := `ccVerboseLabel
def ccVerboseReasonKey : Name := `ccVerboseReason
def ccVerboseRoleKey   : Name := `ccVerboseRole
def ccVerboseCountKey  : Name := `ccVerboseCount

/-- Build a `KVMap` carrying Verbose-CC authoring metadata. -/
def mkVerboseMData (kind : String)
    (label? : Option String := none)
    (reason? : Option String := none)
    (role? : Option String := none)
    (count? : Option Nat := none) : MData :=
  let kv : KVMap := ({} : KVMap).setString ccVerboseKindKey kind
  let kv := match label? with | some l => kv.setString ccVerboseLabelKey l | none => kv
  let kv := match reason? with | some r => kv.setString ccVerboseReasonKey r | none => kv
  let kv := match role? with | some rl => kv.setString ccVerboseRoleKey rl | none => kv
  let kv := match count? with | some c => kv.setNat ccVerboseCountKey c | none => kv
  kv

/-- Wrap a kernel proof term with zero-cost `Expr.mdata` trace metadata. -/
def wrapVerboseMData (kind : String) (proof : Expr)
    (label? : Option String := none)
    (reason? : Option String := none)
    (role? : Option String := none)
    (count? : Option Nat := none) : Expr :=
  .mdata (mkVerboseMData kind label? reason? role? count?) proof

def mdataGetString? (kv : MData) (k : Name) : Option String :=
  match kv.find k with
  | some (.ofString s) => if s.isEmpty then none else some s
  | _ => none

def mdataGetNat? (kv : MData) (k : Name) : Option Nat :=
  match kv.find k with
  | some (.ofNat n) => some n
  | _ => none

/-- Peel outer non-verbose Lean `mdata` (such as `noImplicitLambda`) to expose the outermost
Verbose-CC `mdata` annotation, if any. -/
partial def unwrapVerboseMData? : Expr → Option (MData × Expr)
  | .mdata kv inner =>
      if (mdataGetString? kv ccVerboseKindKey).isSome then some (kv, inner)
      else unwrapVerboseMData? inner
  | _ => none

/-- Search shallowly inside a step proof term for an annotated `cc_calc_step` reason. -/
partial def findCalcStepReason? (e : Expr) (fuel : Nat := 16) : Option String :=
  if fuel == 0 then none
  else match e with
  | .mdata kv inner =>
      match mdataGetString? kv ccVerboseKindKey, mdataGetString? kv ccVerboseReasonKey with
      | some "cc_calc_step", some r => some r
      | _, _ => findCalcStepReason? inner (fuel - 1)
  | .app f a =>
      findCalcStepReason? a (fuel - 1) <|> findCalcStepReason? f (fuel - 1)
  | .letE _ _ v b _ =>
      findCalcStepReason? v (fuel - 1) <|> findCalcStepReason? b (fuel - 1)
  | _ => none

/-- Check whether an expression contains any `cc_calc_step` annotation in its shallow proof tree. -/
partial def hasAnyCalcStepAnnotation (e : Expr) (fuel : Nat := 24) : Bool :=
  if fuel == 0 then false
  else match e with
  | .mdata kv inner =>
      mdataGetString? kv ccVerboseKindKey == some "cc_calc_step" ||
        hasAnyCalcStepAnnotation inner (fuel - 1)
  | .app f a =>
      hasAnyCalcStepAnnotation f (fuel - 1) || hasAnyCalcStepAnnotation a (fuel - 1)
  | .letE _ _ v b _ =>
      hasAnyCalcStepAnnotation v (fuel - 1) || hasAnyCalcStepAnnotation b (fuel - 1)
  | _ => false

/-- Check whether an expression contains any Verbose-CC `mdata` annotation within `fuel`. -/
partial def hasAnyVerboseAnnotation (e : Expr) (fuel : Nat := 32) : Bool :=
  if fuel == 0 then false
  else match e with
  | .mdata kv inner =>
      (mdataGetString? kv ccVerboseKindKey).isSome ||
        hasAnyVerboseAnnotation inner (fuel - 1)
  | .app f a =>
      hasAnyVerboseAnnotation f (fuel - 1) || hasAnyVerboseAnnotation a (fuel - 1)
  | .letE _ _ v b _ =>
      hasAnyVerboseAnnotation v (fuel - 1) || hasAnyVerboseAnnotation b (fuel - 1)
  | .lam _ _ b _ => hasAnyVerboseAnnotation b (fuel - 1)
  | _ => false

/-- Bounded AST node count (`> limit` stops early) so large combinatorial/arithmetic tactics
(`simp`, `linarith`, `norm_num`) dropped from Verbose-CC are summarized cleanly without `whnf` blowup. -/
partial def exprCountBounded (e : Expr) (limit : Nat := 80) : Nat :=
  let rec go (x : Expr) (rem : Nat) : Nat :=
    if rem == 0 then 0
    else match x with
    | .app f a =>
        let r1 := go f (rem - 1)
        if r1 == 0 then 0 else go a r1
    | .lam _ d b _ =>
        let r1 := go d (rem - 1)
        if r1 == 0 then 0 else go b r1
    | .forallE _ d b _ =>
        let r1 := go d (rem - 1)
        if r1 == 0 then 0 else go b r1
    | .letE _ _ v b _ =>
        let r1 := go v (rem - 1)
        if r1 == 0 then 0 else go b r1
    | .mdata _ i => go i (rem - 1)
    | .proj _ _ s => go s (rem - 1)
    | _ => rem - 1
  limit - go e limit

/-! ## 2. Proof-Term Inspection Helpers -/

private def pickOpener (kind : TransitionKind) : StateRefT DiscourseState MetaM String := do
  let st ← get
  let (op, st') := st.pickOpener kind
  set st'
  return op

private def markStepEmitted : StateRefT DiscourseState MetaM Unit :=
  modify (·.markEmitted)

private def subContextOf (ctx : DecompCtx) : DecompCtx :=
  { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }

private def mkVerboseStep (ctx : DecompCtx) (id : String) (content : Array Inline)
    (children : Array ProofNode) (targetForGoal : Expr) (origin? : Option String := none)
    (defaultExpanded : Bool := false) :
    StateRefT DiscourseState MetaM ProofNode := do
  let goal ← buildGoalState ctx.tbl targetForGoal
  let diagHtml ← (← diagramHookRef.get) targetForGoal
  return .step id content children (some goal) diagHtml origin? false defaultExpanded

private partial def collectConsts (e : Expr) (acc : NameSet := {}) (fuel : Nat := 64) : NameSet :=
  if fuel == 0 then acc
  else match e with
  | .const n _ => acc.insert n
  | .app f a => collectConsts a (collectConsts f acc (fuel - 1)) (fuel - 1)
  | .lam _ d b _ => collectConsts b (collectConsts d acc (fuel - 1)) (fuel - 1)
  | .forallE _ d b _ => collectConsts b (collectConsts d acc (fuel - 1)) (fuel - 1)
  | .letE _ t v b _ =>
      collectConsts b (collectConsts v (collectConsts t acc (fuel - 1)) (fuel - 1)) (fuel - 1)
  | .mdata _ inner => collectConsts inner acc (fuel - 1)
  | .proj _ _ s => collectConsts s acc (fuel - 1)
  | _ => acc

/-- Infer a clean Maurer-voice justification phrase for `It_suffices_to_show` from the checked
reduction body when the author did not provide an explicit string reason. -/
private def inferSufficesReason (env : Environment) (body : Expr) : String :=
  let cs := collectConsts body
  if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le then
    "because converter attachment is non-expanding"
  else if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator then
    "by the simulator characterization of indifferentiability"
  else if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation then
    "by sequential composability of constructions"
  else if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context then
    "by context-insensitivity of constructions"
  else if cs.contains ``ConstructiveCryptography.DistinctionGames.advantage_le_win ||
          cs.contains ``SystemAlgebra.Interface.dist_visible_le ||
          cs.contains ``SystemAlgebra.Interface.game_dist_le then
    "by conditional equivalence"
  else if cs.contains ``SystemAlgebra.RandomSystem.GameEquivalent.abs_decisionProbability_sub_le ||
          cs.contains ``SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent ||
          cs.contains ``SystemAlgebra.RandomSystem.GameEquivalent.transcriptDistance_visible_le then
    "by the fundamental lemma of game playing"
  else if cs.contains ``SystemAlgebra.Interface.distance_le_of_hCoefficient ||
          cs.contains ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le then
    "by the extended H-technique"
  else if cs.contains ``SystemAlgebra.Domain.DistinguisherBehavior.advantage_le_transcriptDistance ||
          cs.contains ``SystemAlgebra.Domain.Distinguisher.advantage_le_transcriptDistance ||
          cs.contains ``ConstructiveCryptography.le_advantageDistance then
    "since distinguishing distance bounds every compatible distinguisher's advantage"
  else if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_singleton_iff ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff then
    "by the constructive security definition"
  else
    -- Look for any project-domain lemma referenced in the reduction body
    let projName? := cs.toList.find? fun n =>
      !isCoreOrMathlibIn env n && !n.toString.startsWith "ConstructiveCryptography.CryptographicAlgebra.Specification"
    match projName? with
    | some pn => s!"by {humanLemmaLabel env pn}"
    | none => "by the checked reduction step"

/-- Extract the converter argument from a substitution-in-context proof term, if present. -/
private def findConverterArgLatex? (tbl : SymbolTable) (proof : Expr) : MetaM (Option String) := do
  for arg in proof.getAppArgs do
    try
      let ty ← inferType arg
      if ty.isAppOf ``Quiver.Hom || ty.isAppOf `SystemAlgebra.TypedConverter then
        return some (← exprToLatex arg tbl)
    catch _ => pure ()
  return none

/-- Extract the intermediate resource `M` from `(distance_triangle _ M _).trans (add_le_add p1 p2)`. -/
private def extractTriangleData? (proof : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  let args := p.getAppArgs
  if fn.isConstOf ``LE.le.trans && args.size ≥ 2 then
    let pTri := args[args.size - 2]!.consumeMData
    let pAdd := args[args.size - 1]!.consumeMData
    if pTri.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.distance_triangle &&
       pAdd.isAppOf ``add_le_add then
      let triArgs := pTri.getAppArgs
      let addArgs := pAdd.getAppArgs
      if triArgs.size ≥ 2 && addArgs.size ≥ 2 then
        let mid := triArgs[triArgs.size - 2]!
        return some (mid, addArgs[addArgs.size - 2]!, addArgs[addArgs.size - 1]!)
  return none

/-! ## 3. Annotated `cc_calc` Chain Flattener -/

private inductive CalcHopKind
  | exactEq
  | computational
  | statistical
  deriving DecidableEq, BEq

private structure CalcHop where
  kind : CalcHopKind
  lhs : Expr
  rhs : Expr
  relLatex : String
  proof : Expr
  prop : Expr

private def splitDistLe? (prop : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let prop ← normalizeForPresentation prop
  if prop.isAppOf ``LE.le then
    let args := prop.getAppArgs
    if args.size ≥ 2 then
      let lhs ← normalizeForPresentation args[args.size - 2]!
      let rhs := args[args.size - 1]!
      if lhs.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.distance then
        let dArgs := lhs.getAppArgs
        if dArgs.size ≥ 2 then
          return some (dArgs[dArgs.size - 2]!, dArgs[dArgs.size - 1]!, rhs)
  return none

private def splitSubstWithin? (prop : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let prop ← normalizeForPresentation prop
  if prop.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin then
    let args := prop.getAppArgs
    if args.size ≥ 3 then
      return some (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)
  return none

private def splitEqTransport? (proof : Expr) : MetaM (Option (Bool × Expr × Expr)) := do
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  let args := p.getAppArgs
  let some head := fn.constName? | return none
  if (head == ``Eq.mp || head == ``Eq.mpr) && args.size ≥ 2 then
    let eqArg := args[args.size - 2]!.consumeMData
    let inner := args[args.size - 1]!
    if eqArg.isAppOf ``congrArg then
      if let some eqProof := eqArg.getAppArgs.back? then
        let eqTy ← inferType eqProof
        if eqTy.isAppOf ``Eq then
          return some (head == ``Eq.mp, eqProof, inner)
  return none

private def splitStatTri? (proof : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some (_, p1, p2) ← extractTriangleData? proof then
    return some (p1, p2)
  return none

private partial def flattenVerboseCalc (tbl : SymbolTable) (proof expected : Expr)
    (fuel : Nat := 32) : MetaM (Array CalcHop) := do
  if fuel == 0 then return #[]
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  if fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.trans then
    let pArgs ← proofValuedArgs p
    if pArgs.size == 2 then
      let (p1, t1) := pArgs[0]!
      let (p2, t2) := pArgs[1]!
      return (← flattenVerboseCalc tbl p1 t1 (fuel - 1)) ++
             (← flattenVerboseCalc tbl p2 t2 (fuel - 1))
  if let some (p1, p2) ← splitStatTri? p then
    let t1 ← inferType p1
    let t2 ← inferType p2
    return (← flattenVerboseCalc tbl p1 t1 (fuel - 1)) ++
           (← flattenVerboseCalc tbl p2 t2 (fuel - 1))
  if let some (isRightJoin, eqProof, inner) ← splitEqTransport? p then
    let eqTy ← inferType eqProof
    let innerTy ← inferType inner
    let innerHops ← flattenVerboseCalc tbl inner innerTy (fuel - 1)
    let mut eqHops : Array CalcHop := #[]
    if let some (_, lhs, rhs) := eqTy.eq? then
      let isRefl := eqProof.consumeMData.isAppOf ``Eq.refl || eqProof.consumeMData.isConstOf ``rfl
      if !isRefl && lhs != rhs then
        eqHops := #[{ kind := .exactEq, lhs, rhs, relLatex := "=", proof := eqProof, prop := eqTy }]
    return if isRightJoin then innerHops ++ eqHops else eqHops ++ innerHops
  if let some (err, lhs, rhs) ← splitSubstWithin? expected then
    let isStat :=
      fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance ||
      fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical
    let errTex ← match err.consumeMData with
      | .lam _ _ body _ =>
          if !body.hasLooseBVar 0 then exprToLatex body tbl else exprToLatex err tbl
      | _ => exprToLatex err tbl
    let rel := if isStat then "\\approx_{" ++ errTex ++ "}" else "\\simeq_{" ++ errTex ++ "}"
    return #[{
      kind := if isStat then .statistical else .computational
      lhs, rhs, relLatex := rel, proof := proof, prop := expected
    }]
  if let some (lhs, rhs, eps) ← splitDistLe? expected then
    let epsTex ← exprToLatex eps tbl
    return #[{
      kind := .statistical
      lhs, rhs, relLatex := "\\approx_{" ++ epsTex ++ "}", proof := proof, prop := expected
    }]
  return #[]

private def describeVerboseHopReason (env : Environment) (tbl : SymbolTable) (hop : CalcHop) :
    MetaM (Array Inline) := do
  if let some custom := findCalcStepReason? hop.proof then
    return #[.text custom]
  let fn := hop.proof.getAppFn.consumeMData
  match hop.kind with
  | .exactEq =>
      match fn with
      | .const cn _ =>
          if cn == ``Eq.trans then pure #[.text "by chaining exact system identities"]
          else if cn == ``Eq.symm then pure #[.text "by symmetry of exact system identity"]
          else pure #[.text "by exact identity (", .emph (humanLemmaLabel env cn), .text ")"]
      | .fvar _ => pure #[.text "by the assumed system identity"]
      | _ => pure #[.text "by exact system identity"]
  | .statistical =>
      match fn with
      | .const cn _ =>
          if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance ||
             cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical then
            pure #[.text "by statistical distance bound"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le then
            pure #[.text "by non-expansion under converter attachment"]
          else
            pure #[.text "by statistical bound (", .emph (humanLemmaLabel env cn), .text ")"]
      | _ => pure #[.text "by statistical distance bound"]
  | .computational =>
      match fn with
      | .const cn _ =>
          if cn == ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_context ||
             cn == ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_attach then
            if let some convTex ← findConverterArgLatex? tbl hop.proof then
              return #[.text "by substituting inside context ", .inlineMath convTex,
                       .text " (absorbing ", .inlineMath convTex, .text " into the distinguisher)"]
            pure #[.text "by substituting inside a converter context"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.symm then
            pure #[.text "by symmetry of substitution"]
          else
            pure #[.text "by substitution (", .emph (humanLemmaLabel env cn), .text ")"]
      | .fvar _ => pure #[.text "by the assumed substitution"]
      | _ => pure #[.text "by substitution"]

private def buildAnnotatedCalcChain (ctx : DecompCtx) (decompileChild : DecompileChild)
    (expected proof : Expr) (idPrefix : String) :
    StateRefT DiscourseState MetaM (Option (Array ProofNode)) := do
  let isSubGoal := (← splitSubstWithin? expected).isSome
  let isDistGoal := (← splitDistLe? expected).isSome
  if !isSubGoal && !isDistGoal then return none
  let hops ← flattenVerboseCalc ctx.tbl proof expected
  if hops.size < 2 then return none
  let op ← pickOpener .elaboration
  let subCtx := subContextOf ctx
  let env ← getEnv
  let mut calcSteps : Array (CalcStep × Array ProofNode) := #[]
  let mut nComp : Nat := 0
  let mut nStat : Nat := 0
  let mut nEq : Nat := 0
  for hop in hops do
    match hop.kind with
    | .computational => nComp := nComp + 1
    | .statistical => nStat := nStat + 1
    | .exactEq => nEq := nEq + 1
    let lhsTex ← exprToLatex hop.lhs ctx.tbl
    let rhsTex ← exprToLatex hop.rhs ctx.tbl
    let reason ← describeVerboseHopReason env ctx.tbl hop
    let subNodes ←
      if hasAnyVerboseAnnotation hop.proof && (unwrapHypothesisFVar? hop.proof).isNone then
        -- Unwrap `cc_calc_step` `mdata` so inner `By_CC_routine` etc. surfaces without raw `calc-80` noise
        let rawStep := match unwrapVerboseMData? hop.proof with
          | some (kv, inner) =>
              if mdataGetString? kv ccVerboseKindKey == some "cc_calc_step" then inner else hop.proof
          | none => hop.proof
        if (unwrapVerboseMData? rawStep).isSome then
          decompileChild subCtx hop.prop rawStep
        else
          pure #[]
      else
        pure #[]
    let diagHtml ← (← diagramHookRef.get) hop.prop
    let cs : CalcStep := {
      lhsLatex := lhsTex
      relationLatex := hop.relLatex
      rhsLatex := rhsTex
      reason
      diagramHtml? := diagHtml
    }
    calcSteps := calcSteps.push (cs, subNodes)
  let goal ← buildGoalState ctx.tbl expected
  let mut summaryParts : List String := []
  if nComp > 0 then
    summaryParts := summaryParts ++ [s!"{countPhrase nComp ⟨"computational substitution", "computational substitutions"⟩}"]
  if nStat > 0 then
    summaryParts := summaryParts ++ [s!"{countPhrase nStat ⟨"statistical bound", "statistical bounds"⟩}"]
  if nEq > 0 then
    summaryParts := summaryParts ++ [s!"{countPhrase nEq ⟨"exact system identity", "exact system identities"⟩}"]
  let ledgerText :=
    if summaryParts.isEmpty then
      s!"{op} chaining the intermediate hybrid systems yields"
    else
      s!"{op} proceeding through the hybrid chain ({joinAnd summaryParts}) and combining the per-step bounds by the triangle inequality gives"
  return some #[.calcChain s!"{idPrefix}-{hops.size}" #[.text ledgerText] calcSteps (some goal)]

/-! ## 4. Extended H-Coefficient Witness Extractor -/

private partial def findHCoeffOfGoodBad? (e : Expr) (fuel : Nat := 16) : Option Expr :=
  if fuel == 0 then none
  else
    let c := e.consumeMData
    if c.getAppFn.consumeMData.isConstOf ``SystemAlgebra.RandomSystem.HCoefficient.ofGoodBad then
      some c
    else match c with
    | .app f a => findHCoeffOfGoodBad? a (fuel - 1) <|> findHCoeffOfGoodBad? f (fuel - 1)
    | .letE _ _ v b _ => findHCoeffOfGoodBad? b (fuel - 1) <|> findHCoeffOfGoodBad? v (fuel - 1)
    | _ => none

private def decompileCombinatorialSubgoal (ctx : DecompCtx) (decompileChild : DecompileChild)
    (idTag : String) (summary : String) (aty ap : Expr) :
    StateRefT DiscourseState MetaM (Array ProofNode) := do
  if let some fvid := unwrapHypothesisFVar? ap then
    let n ← renderHypothesisStep ctx.tbl aty fvid s!"{idTag}-{fvid.name}" (isWrap := true)
    return #[n]
  if hasAnyVerboseAnnotation ap || exprCountBounded ap 45 < 45 then
    decompileChild ctx aty ap
  else
    let g ← buildGoalState ctx.tbl aty
    return #[.routineReceipt idTag summary 1 #[] (some g)]

private def extractHCoefficientChildren (ctx : DecompCtx) (decompileChild : DecompileChild)
    (proof : Expr) : StateRefT DiscourseState MetaM (Array ProofNode) := do
  let subCtx := subContextOf ctx
  let some w := findHCoeffOfGoodBad? proof |
    return ← decompilePremiseArgs subCtx decompileChild proof
  let pArgs ← proofValuedArgs w
  let total := pArgs.size
  let mut out : Array ProofNode := #[]
  -- `ofGoodBad` proof arguments end with: `[..., idealReveal_isProbDist, hε₁, ratio, bad]`
  if total ≥ 4 then
    let (apProb, atyProb) := pArgs[total - 4]!
    let subProb ← decompileCombinatorialSubgoal subCtx decompileChild s!"vcc-hcoeff-prob-rec-{total}"
      "verifying that the auxiliary ideal reveal defines a probability distribution" atyProb apProb
    if !subProb.isEmpty then
      let inlProb ← renderProposition ctx.tbl atyProb
      let gProb ← buildGoalState ctx.tbl atyProb
      out := out.push (.step s!"vcc-hcoeff-prob-{total}"
        (#[.text "First, on the ideal side the auxiliary reveal defines a valid conditional probability law: "] ++
         inlProb ++ #[.text "."]) subProb (some gProb))
  if total ≥ 2 then
    let (apRatio, atyRatio) := pArgs[total - 2]!
    let subRatio ← decompileCombinatorialSubgoal subCtx decompileChild s!"vcc-hcoeff-ratio-rec-{total}"
      "pointwise probability-ratio verification across good extended transcripts" atyRatio apRatio
    let inlRatio ← renderProposition ctx.tbl atyRatio
    let gRatio ← buildGoalState ctx.tbl atyRatio
    out := out.push (.step s!"vcc-hcoeff-ratio-{total}"
      (#[.text "On every attainable good extended transcript, the real-to-ideal probability ratio satisfies "] ++
       inlRatio ++ #[.text "."]) subRatio (some gRatio))
    let (apBad, atyBad) := pArgs[total - 1]!
    let subBad ← decompileCombinatorialSubgoal subCtx decompileChild s!"vcc-hcoeff-bad-rec-{total}"
      "probability-mass bound over bad transcripts across compatible environments" atyBad apBad
    let inlBad ← renderProposition ctx.tbl atyBad
    let gBad ← buildGoalState ctx.tbl atyBad
    out := out.push (.step s!"vcc-hcoeff-bad-{total}"
      (#[.text "For bad extended transcripts on the ideal side, "] ++
       inlBad ++ #[.text "."]) subBad (some gBad))
  return out

/-! ## 5. Primary Verbose-CC `RuleExplainer` (Priority 500) -/

private def originOf (env : Environment) (inner : Expr) : Option String :=
  match inner.getAppFn.consumeMData with
  | .const n _ => if isCoreOrMathlibIn env n then none else some n.toString
  | _ => none

/-- High-priority `RuleExplainer` recognizing Verbose-CC `Expr.mdata` trace tags and rendering
checked proof steps in Ueli Maurer's calm, paper-authentic voice. -/
def verboseCCExplainer : RuleExplainer where
  priority := 500
  explain ctx decompileChild expected proof := do
    -- Case A: Annotated `cc_calc` chain without outer `By_hybrid_chain` wrapper
    if unwrapVerboseMData? proof |>.isNone then
      let fn := proof.getAppFn.consumeMData
      let isChainRoot :=
        fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.trans ||
        (← splitStatTri? proof).isSome ||
        (← splitEqTransport? proof).isSome
      if isChainRoot && hasAnyCalcStepAnnotation proof then
        if let some nodes ← buildAnnotatedCalcChain ctx decompileChild expected proof "vcc-calc" then
          return some nodes
      return none

    let some (kv, inner) := unwrapVerboseMData? proof | return none
    let some kind := mdataGetString? kv ccVerboseKindKey | return none
    let label? := mdataGetString? kv ccVerboseLabelKey
    let reason? := mdataGetString? kv ccVerboseReasonKey
    let role? := mdataGetString? kv ccVerboseRoleKey
    let count? := mdataGetNat? kv ccVerboseCountKey
    let subCtx := subContextOf ctx
    let env ← getEnv

    match kind with
    -- 1. Individual `cc_calc` step wrapper: let outer chain read its reason, or unwrap cleanly
    | "cc_calc_step" =>
        return some (← decompileChild ctx expected inner)

    -- 2. `Write x := e` local shorthand
    | "write" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let step : ProofNode :=
                .step s!"vcc-write-{symTex}-{ctx.factIndex}"
                  #[.text "Write ", .inlineMath s!"{symTex} := {valTex}", .text "."]
                  #[] (some goal)
              let rest ← decompileChild { ctx with isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 3. `Introduce_hybrid H := e`
    | "hybrid" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let step : ProofNode :=
                .step s!"vcc-hybrid-{symTex}-{ctx.factIndex}"
                  #[.text "Introduce the intermediate hybrid ", .inlineMath s!"{symTex} := {valTex}", .text "."]
                  #[] (some goal)
              let rest ← decompileChild { ctx with isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 4. `Claim h : P by ...` and `Fact h : P by ...`
    | "claim" | "fact" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            markStepEmitted
            let valNodes ← decompileChild subCtx ty val
            let tyInl ← renderProposition ctx.tbl ty
            let lead :=
              if kind == "claim" then
                if ctx.factIndex == 0 then "We claim that " else "Next, we claim that "
              else
                if ctx.factIndex == 0 then "First, observe that " else "Moreover, note that "
            let step ← mkVerboseStep ctx s!"vcc-{kind}-{ctx.factIndex}"
              (#[.text lead] ++ tyInl ++ #[.text "."]) valNodes ty
            let rest ← withLetDecl nm ty val fun fv =>
              let nextCtx :=
                { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
              decompileChild nextCtx expected (body.instantiate1 fv)
            return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 5. `It_suffices_to_show P by/because ...`
    | "suffices" =>
        match inner.consumeMData with
        | .letE hNm dom pProof body _ =>
            markStepEmitted
            let (reasonPhrase, reasonNodes) ← withLocalDecl hNm .default dom fun fv => do
              let bodyInst := body.instantiate1 fv
              let rNodes ← decompileChild subCtx expected bodyInst
              let rPhrase := reason?.getD (inferSufficesReason env bodyInst)
              pure (rPhrase, rNodes)
            let pInl ← renderProposition ctx.tbl dom
            let lead := capitalizeFirst reasonPhrase
            let sufficesStep ← mkVerboseStep ctx s!"vcc-suffices-{ctx.factIndex}"
              (#[.text s!"{lead}, it suffices to show that "] ++ pInl ++ #[.text "."])
              reasonNodes dom
            let rest ← decompileChild { ctx with atRootConclusion := false, isProofStart := false } dom pProof
            return some (#[sufficesStep] ++ rest)
        | .app fn pProof =>
            match fn.consumeMData with
            | .lam hNm dom body bi =>
                markStepEmitted
                let (reasonPhrase, reasonNodes) ← withLocalDecl hNm bi dom fun fv => do
                  let bodyInst := body.instantiate1 fv
                  let rNodes ← decompileChild subCtx expected bodyInst
                  let rPhrase := reason?.getD (inferSufficesReason env bodyInst)
                  pure (rPhrase, rNodes)
                let pInl ← renderProposition ctx.tbl dom
                let lead := capitalizeFirst reasonPhrase
                let sufficesStep ← mkVerboseStep ctx s!"vcc-suffices-{ctx.factIndex}"
                  (#[.text s!"{lead}, it suffices to show that "] ++ pInl ++ #[.text "."])
                  reasonNodes dom
                let rest ← decompileChild { ctx with atRootConclusion := false, isProofStart := false } dom pProof
                return some (#[sufficesStep] ++ rest)
            | _ => return some (← decompileChild ctx expected inner)
        | _ => return some (← decompileChild ctx expected inner)

    -- 6. `By_CC_routine { ... }` compression receipt (quiet in Paper mode, expandable in Auditor)
    | "cc_routine" =>
        markStepEmitted
        let routineCtx := { subCtx with lemmaDepth := subCtx.config.maxLemmaDepth }
        let details ← match unwrapHypothesisFVar? inner with
          | some fvid => do
              let n ← renderHypothesisStep ctx.tbl expected fvid s!"vcc-routine-hyp-{fvid.name}" (isWrap := true)
              pure #[n]
          | none => decompileChild routineCtx expected inner
        let goal ← buildGoalState ctx.tbl expected
        let summary := reason?.getD "routine constructive-cryptography normalization and algebraic bookkeeping"
        let cnt := count?.getD (max 1 details.size)
        return some #[.routineReceipt s!"vcc-routine-{ctx.factIndex}" summary cnt details (some goal)]

    -- 7. `By_hybrid_chain { cc_calc ... }`
    | "hybrid_chain" =>
        if let some nodes ← buildAnnotatedCalcChain ctx decompileChild expected inner "vcc-hybrid-chain" then
          return some nodes
        return some (← decompileChild ctx expected inner)

    -- 8. `Construct_using h` / `Construct S from R via π using h`
    | "construct" =>
        let op ← pickOpener .consequence
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} from the checked construction witness, "] ++ conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-construct-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 9. `Replace_converter_in h using hEq`
    | "replace_converter" =>
        let op ← pickOpener .elaboration
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} since the two converters induce identical attachments, replacing the converter preserves the statement and shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-replace-conv-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 10. `By_sequential_composition h1 and h2`
    | "seq_comp" =>
        let op ← pickOpener .consequence
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} composing the inner and outer construction steps sequentially shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-seq-comp-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 11. `By_parallel_composition hL and hR`
    | "par_comp" =>
        let op ← pickOpener .consequence
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} placing the left and right constructions side by side by parallel composability establishes that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-par-comp-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 12. `By_context_insensitivity_right` / `By_context_insensitivity_left`
    | "context_right" =>
        let op ← pickOpener .elaboration
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} by context-insensitivity, making the untouched parallel resource available on the right preserves the construction and shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-ctx-right-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    | "context_left" =>
        let op ← pickOpener .elaboration
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} by context-insensitivity, making the untouched parallel resource available on the left preserves the construction and shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-ctx-left-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 13. `Pull_relaxation_through hOuter using hCompat from hInner`
    | "pull_relax" =>
        let op ← pickOpener .consequence
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} pulling the relaxation to the outside through the outer protocol—accounting for the outer converter via the compatibility property—shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-pull-relax-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 14. `Substitute_in_context ...`
    | "substitute" =>
        let op ← pickOpener .elaboration
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let convTex? ← findConverterArgLatex? ctx.tbl inner
        let ctxPhrase : Array Inline := match convTex? with
          | some c =>
              #[.text "inside the converter context ", .inlineMath c,
                .text " absorbs ", .inlineMath c, .text " into the distinguisher—preserving admissibility by closure of ",
                .inlineMath "\\mathcal{D}", .text "—and shows that "]
          | none =>
              #[.text "inside the surrounding converter context absorbs the context into the distinguisher and shows that "]
        let content : Array Inline :=
          #[.text s!"{op} substituting "] ++ ctxPhrase ++ conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-substitute-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 15. `By_triangle_inequality_via M`
    | "triangle" =>
        let op ← pickOpener .elaboration
        let mut children : Array ProofNode := #[]
        let mut midTex? : Option String := none
        if let some (mid, p1, p2) ← extractTriangleData? inner then
          midTex? := some (← exprToLatex mid ctx.tbl)
          let t1 ← inferType p1
          let t2 ← inferType p2
          let sub1 ← decompileChild subCtx t1 p1
          let sub2 ← decompileChild subCtx t2 p2
          let inl1 ← renderProposition ctx.tbl t1
          let inl2 ← renderProposition ctx.tbl t2
          let g1 ← buildGoalState ctx.tbl t1
          let g2 ← buildGoalState ctx.tbl t2
          children := #[
            .step s!"vcc-tri-left-{ctx.factIndex}"
              (#[.text "For the first leg, "] ++ inl1 ++ #[.text "."]) sub1 (some g1),
            .step s!"vcc-tri-right-{ctx.factIndex}"
              (#[.text "For the second leg, "] ++ inl2 ++ #[.text "."]) sub2 (some g2)
          ]
        else
          children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let viaPhrase : Array Inline := match midTex? with
          | some m => #[.text " via the intermediate system ", .inlineMath m]
          | none => #[]
        let content : Array Inline :=
          #[.text s!"{op} applying the triangle inequality"] ++ viaPhrase ++
          #[.text " shows that "] ++ conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-triangle-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 16. `By_non_expansion`
    | "nonexpand" =>
        let op ← pickOpener .justification
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} non-expansion under converter attachment and parallel composition, "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-nonexpand-{ctx.factIndex}" content #[] expected (originOf env inner)
        return some #[step]

    -- 17. `Exhibit_simulator σ [for_interface E]`
    | "exhibit_simulator" =>
        markStepEmitted
        let args := inner.getAppArgs
        let simTex? ← match label? with
          | some s => pure (some (formatMathIdent s))
          | none => do
              let mut found : Option String := none
              for arg in args.reverse do
                if found.isNone then
                  try
                    let ty ← inferType arg
                    if ty.isAppOf ``Quiver.Hom || ty.isAppOf `SystemAlgebra.TypedConverter then
                      found := some (← exprToLatex arg ctx.tbl)
                  catch _ => pure ()
              pure found
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let simPhrase : Array Inline := match simTex?, role? with
          | some s, some iface =>
              #[.text "We exhibit the explicit simulator ", .inlineMath s,
                .text " attached to the ", .inlineMath (formatMathIdent iface), .text "-interface"]
          | some s, none =>
              #[.text "We exhibit the explicit simulator ", .inlineMath s,
                .text " attached to the adversarial interface"]
          | none, _ =>
              #[.text "We exhibit an admitted simulator attached to the adversarial interface"]
        let content : Array Inline :=
          simPhrase ++
          #[.text " and verify both admissibility and the closeness bound, establishing that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-exhibit-sim-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 18. `Compose_simulators hInner and hOuter [using_commutation hCommutes]`
    | "compose_simulators" =>
        markStepEmitted
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text "By composition-order invariance between the outer protocol and the inner simulator, composing the simulator constructions serially shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-compose-sim-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 19. `Ignore_MBO_of G`
    | "ignore_mbo" =>
        markStepEmitted
        let (realRest, nextExpected) ← do
          let c := inner.consumeMData
          let fn := c.getAppFn.consumeMData
          let cArgs := c.getAppArgs
          if (fn.isConstOf ``Eq.mpr || fn.isConstOf ``Eq.mp) && cArgs.size ≥ 4 then
            let restExpr := cArgs[cArgs.size - 1]!
            let restTy ← inferType restExpr
            pure (restExpr, restTy)
          else
            pure (inner, expected)
        let restNodes ← decompileChild { ctx with isProofStart := false } nextExpected realRest
        let gPhrase : Array Inline := match label? with
          | some g =>
              #[.text "Let ", .inlineMath (formatMathIdent g ++ "^{-}"),
                .text " denote the underlying system resulting from ", .inlineMath (formatMathIdent g),
                .text " by ignoring the MBO; unfolding ", .inlineMath (formatMathIdent g ++ "^{-}"),
                .text " passes to the MBO-free goal."]
          | none =>
              #[.text "Passing to the underlying system obtained by ignoring the MBO reduces to the MBO-free comparison."]
        let step ← mkVerboseStep ctx s!"vcc-ignore-mbo-{ctx.factIndex}"
          gPhrase #[] nextExpected
        return some (#[step] ++ restNodes)

    -- 20. `By_fundamental_lemma_of_game_playing h`
    | "fundamental_game" =>
        markStepEmitted
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text "By the fundamental lemma of game playing, any distinguisher between the underlying systems obtained by ignoring the MBO must provoke the MBO, showing that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-fund-game-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 21. `By_conditional_equivalence h`
    | "cond_equiv" =>
        markStepEmitted
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text "Since the game is conditionally equivalent to the target system while the monotone binary output (MBO) remains unset, we obtain "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-cond-equiv-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 22. `By_extended_H_technique ...`
    | "extended_h_coeff" =>
        let op ← pickOpener .consequence
        let children ← extractHCoefficientChildren ctx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} extending both systems by revealing their auxiliary randomness and applying the extended H-technique—separately bounding the bad-transcript mass on the ideal side and the probability ratio on good transcripts—establishes that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-ext-hcoeff-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 23. `Exhibit_distinguisher D`
    | "exhibit_distinguisher" =>
        markStepEmitted
        let advBody := do
          let mut cur := inner
          for _ in [0:4] do
            if (unwrapVerboseMData? cur).isSome then break
            let c := cur.consumeMData
            let fn := c.getAppFn.consumeMData
            let cArgs := c.getAppArgs
            if (fn.isConstOf ``Eq.mpr || fn.isConstOf ``Eq.mp) && cArgs.size ≥ 4 then
              cur := cArgs[cArgs.size - 1]!
            else if fn.isConstOf ``le_trans && cArgs.size ≥ 6 then
              cur := cArgs[cArgs.size - 2]!
            else
              break
          let advTy ← inferType cur
          decompileChild subCtx advTy cur
        let children ← advBody
        let conclInl ← renderProposition ctx.tbl expected
        let distPhrase : Array Inline := match label? with
          | some d => #[.text "We exhibit the explicit compatible distinguisher ", .inlineMath (formatMathIdent d)]
          | none => #[.text "We exhibit an explicit compatible distinguisher"]
        let content : Array Inline :=
          distPhrase ++
          #[.text "; since the distinguishing distance is the supremum of advantages over all compatible distinguishers, its advantage shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-exhibit-dist-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 24. `Lower_bound_advantage_of D`
    | "lower_bound_adv" =>
        let op ← pickOpener .consequence
        let g ← buildGoalState ctx.tbl expected
        let children : Array ProofNode :=
          #[.routineReceipt s!"vcc-lower-adv-rec-{ctx.factIndex}"
              "computing the decision probabilities on both systems and applying the triangle inequality"
              1 #[] (some g)]
        let conclInl ← renderProposition ctx.tbl expected
        let distPhrase : Array Inline := match label? with
          | some d => #[.inlineMath (formatMathIdent d)]
          | none => #[.text "the distinguisher"]
        let content : Array Inline :=
          #[.text s!"{op} bounding the decision probabilities of "] ++ distPhrase ++
          #[.text " on the real and ideal systems separately shows that "] ++ conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-lower-adv-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 25. `Tightness_sandwich`
    | "tightness_sandwich" =>
        let c := inner.consumeMData
        if c.getAppFn.consumeMData.isConstOf ``And.intro && c.getAppArgs.size ≥ 4 then
          markStepEmitted
          let args := c.getAppArgs
          let p1 := args[args.size - 2]!
          let p2 := args[args.size - 1]!
          let t1 ← inferType p1
          let t2 ← inferType p2
          let sub1 ← decompileChild subCtx t1 p1
          let sub2 ← decompileChild subCtx t2 p2
          let inl1 ← renderProposition ctx.tbl t1
          let inl2 ← renderProposition ctx.tbl t2
          let isUpperFirst := role? == some "upper_lower"
          let lead1 := if isUpperFirst then "For the upper bound, " else "For the lower bound, "
          let lead2 := if isUpperFirst then "For the matching lower bound, " else "For the matching upper bound, "
          let step1 ← mkVerboseStep ctx s!"vcc-sandwich-1-{ctx.factIndex}"
            (#[.text lead1] ++ inl1 ++ #[.text "."]) sub1 t1
          let step2 ← mkVerboseStep ctx s!"vcc-sandwich-2-{ctx.factIndex}"
            (#[.text lead2] ++ inl2 ++ #[.text "."]) sub2 t2
          let conclInl ← renderProposition ctx.tbl expected
          let closeContent : Array Inline :=
            if ctx.atRootConclusion then
              #[.text "Combining the matching lower and upper bounds establishes the tightness sandwich."]
            else
              #[.text "Combining the matching lower and upper bounds establishes "] ++ conclInl ++ #[.text "."]
          let step3 ← mkVerboseStep ctx s!"vcc-sandwich-close-{ctx.factIndex}"
            closeContent #[] expected
          return some #[step1, step2, step3]
        return some (← decompileChild ctx expected inner)

    -- 26. `Combining ...`
    | "combine" =>
        let op ← pickOpener .closing
        let children ←
          if (unwrapVerboseMData? inner).isSome then
            decompileChild subCtx expected inner
          else
            decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          if ctx.atRootConclusion then
            #[.text s!"{op} the claimed security bound, completing the proof."]
          else
            #[.text s!"{op} "] ++ conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-combine-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    | _ =>
        return some (← decompileChild ctx expected inner)

initialize
  registerRuleExplainer verboseCCExplainer

end Informalization.Verbose.Trace
