/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Hygiene
import Informalization.Core.Register
import Informalization.Core.Spine
import Informalization.Verbose.ProseInterp
import Informalization.Verbose.Trace
import Informalization.Verbose.Syntax
import Probability.Distribution
import Probability.StatisticalDistance
import ConstructiveCryptography.Tactics.Basic
import ConstructiveCryptography.Tactics.Categorical
import ConstructiveCryptography.Tactics.Substitution
import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.CryptographicAlgebra.Epsilon
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import ConstructiveCryptography.Notation
import ConstructiveCryptography.Instances.Algebra
import ConstructiveCryptography.Instances.Game
import RandomSystems.Distance.HCoefficient
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Distance.Distinguisher
import RandomSystems.Game.MBO
import RandomSystems.Game.UntilBad

/-!
# Paper-Centric Proof-Move Archetype Combinators & `by_leaf` Opacity Wall

Provides checked proof-move combinators in `namespace PaperProof` (designed to work cleanly
alongside `scoped VerboseCC`):

* **`by_leaf`** (`by_leaf "summary" => tacSeq`, `by_leaf => tacSeq`, `by_leaf "summary" { tacSeq }`,
  `by_leaf { tacSeq }`): elaborates `tacSeq` on a fresh synthetic-opaque metavariable, preserves
  `sorryAx` honestly without masking it (`"sorry_leaf"`), and wraps checked subproofs in
  `wrapByLeafMData` so `ProofGraph` / `Trace` never leak internal tactic steps.
* **`proof_idea "motivation prose"`**: emits a checked `spineNode` with `trust := "authorGloss"`.
* **Archetype 1 — Hybrid transitions & triangle inequality**: `Define_hybrid`, `Hybrid_hop`,
  `Conclude_triangle`, plus lowercase aliases `hybrid_step` and `conclude_triangle`.
* **Archetype 2 — Game hopping / Difference Lemma / MBO conditional equivalence**:
  `Bad_event`, `Identical_until_bad`, `Conclude_difference_lemma`, and `game_hop_step`.
* **Archetype 3 — H-coefficient method**: `Split_transcripts`, `Bound_bad_mass`,
  `Bound_good_ratio`, `Conclude_h_coeff`, and `h_coeff_argument`.
* **Archetype 4 — CC serial/parallel composition & converter substitution**:
  `cc_compose_step` and `cc_substitute_step`.
* **Archetype 5 — Security reduction + `[Reduction]` pseudocode box**:
  `reduction_step` (without duplicating prose parentheticals).
* **Archetype 6 — Distinguisher lower bound & bound contradiction**:
  `distinguisher_lower_bound` and `contradict_bound`.
-/

namespace PaperProof

open Lean Elab Term Tactic Meta
open Lean.Parser.Tactic
open Informalization.Core.Hygiene
open Informalization.Core.Register
open Informalization.Core.Spine
open Informalization.Verbose.ProseInterp
open Informalization.Verbose.Trace

export VerboseCC (difference_lemma_distribution difference_lemma_probDist)

/-! ## Core Checked Leaf & Spine Wrappers -/

private def runTacSeqOn (innerMVar : MVarId)
    (tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [innerMVar]
  try
    Tactic.evalTactic tacSeq.raw
    getGoals
  finally
    setGoals saved

private def runTacOn (innerMVar : MVarId) (tac : TSyntax `tactic) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [innerMVar]
  try
    Tactic.evalTactic tac.raw
    getGoals
  finally
    setGoals saved

/-- Elaborate a closed subproof `tacSeq` for `prop` inside a fresh synthetic-opaque mvar and
wrap it in a strict `by_leaf` opacity wall (`"sorry_leaf"` if `sorryAx` appears anywhere inside). -/
private def elabClosedLeafExpr (summary : String) (prop : Expr)
    (tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM Expr := do
  let leafMVar ← mkFreshExprSyntheticOpaqueMVar prop (Name.mkSimple "by_leaf")
  let rem ← runTacSeqOn leafMVar.mvarId! tacSeq
  unless rem.isEmpty do
    throwError m!"by_leaf left {rem.length} unsolved goal(s)"
  let proof ← instantiateMVars leafMVar
  let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
  return wrapByLeafMData summary proof leafKind

/-- Close the current main goal with `tacSeq` under a `by_leaf` opacity wall. -/
private def wrapMainGoalByLeaf (summary : String)
    (tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM Unit := do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let target ← mvarId.getType
    let wrapped ← elabClosedLeafExpr summary target tacSeq
    mvarId.assign wrapped
    replaceMainGoal []

/-- Wrap the main goal inside `wrapVerboseMData kind ...` while running `runInner`. -/
private def wrapGoalWithPaperMData (kind : String)
    (runInner : MVarId → TacticM (List MVarId))
    (label? : Option String := none)
    (reason? : Option String := none)
    (role? : Option String := none)
    (count? : Option Nat := none) : TacticM Unit := do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let target ← mvarId.getType
    let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
    let remaining ← runInner inner.mvarId!
    let proof ← instantiateMVars inner
    mvarId.assign (wrapVerboseMData kind proof label? reason? role? count?)
    replaceMainGoal remaining

/-- Introduce a checked `let` binding wrapped with `wrapVerboseMData kind`. -/
private def elabPaperLet (kind : String) (id : Ident) (tyOpt? : Option (TSyntax `term))
    (valStx : TSyntax `term) (reason? : Option String := none)
    (role? : Option String := none) : TacticM Unit :=
  withMainContext do
    let expectedTy? ← tyOpt?.mapM fun t => elabType t
    let val ← Tactic.elabTermEnsuringType valStx expectedTy?
    let valTy ← match expectedTy? with
      | some t => pure t
      | none => inferType val
    let mvarId ← getMainGoal
    let target ← mvarId.getType
    let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
    let afterDefine ← inner.mvarId!.define id.getId valTy val
    let (fv, nextGoal) ← afterDefine.intro id.getId
    nextGoal.withContext do
      Term.addLocalVarInfo id (mkFVar fv)
    let proof ← instantiateMVars inner
    mvarId.assign (wrapVerboseMData kind proof (label? := some id.getId.toString)
      (reason? := reason?) (role? := role?))
    replaceMainGoal [nextGoal]

/-- Introduce a checked `have` assertion whose proof is `by_leaf`-isolated under `summary` and
tagged with `kind`. -/
private def elabPaperHaveLeaf (kind : String) (idOpt? : Option Ident) (propStx : TSyntax `term)
    (tacSeq? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (proofTerm? : Option (TSyntax `term)) (summary : String)
    (reason? : Option String := none) (role? : Option String := none) : TacticM Unit :=
  withMainContext do
    let prop ← elabType propStx
    let hName ← match idOpt? with
      | some id => pure id.getId
      | none => mkFreshUserName `paperStep
    let leafVal ← match tacSeq?, proofTerm? with
      | some tacSeq, none => elabClosedLeafExpr summary prop tacSeq
      | none, some pt =>
          let raw ← Tactic.elabTermEnsuringType pt (some prop)
          let leafKind := if exprContainsSorryAx raw then "sorry_leaf" else "leaf"
          pure (wrapByLeafMData summary raw leafKind)
      | _, _ => throwError "expected either tactic proof or proof term"
    let mvarId ← getMainGoal
    let target ← mvarId.getType
    let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
    let afterDefine ← inner.mvarId!.define hName prop leafVal
    let (fv, nextGoal) ← afterDefine.intro hName
    if let some id := idOpt? then
      nextGoal.withContext do
        Term.addLocalVarInfo id (mkFVar fv)
    let lbl? := idOpt?.map (·.getId.toString)
    let proof ← instantiateMVars inner
    mvarId.assign (wrapVerboseMData kind proof (label? := lbl?)
      (reason? := reason?) (role? := role?))
    replaceMainGoal [nextGoal]

/-- Bind a checked proof term `pt` in the local context as an unnamed/anonymous hypothesis
tagged with `kind` (and `by_leaf`-isolated). -/
private def elabPaperWitness (kind : String) (pt : TSyntax `term) (summary : String)
    (reason? : Option String := none) (role? : Option String := none) : TacticM Unit :=
  withMainContext do
    let val ← Tactic.elabTerm pt none
    let prop ← inferType val
    let hName ← mkFreshUserName `paperWitness
    let leafKind := if exprContainsSorryAx val then "sorry_leaf" else "leaf"
    let leafVal := wrapByLeafMData summary val leafKind
    let mvarId ← getMainGoal
    let target ← mvarId.getType
    let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
    let afterDefine ← inner.mvarId!.define hName prop leafVal
    let (_fv, nextGoal) ← afterDefine.intro hName
    let proof ← instantiateMVars inner
    mvarId.assign (wrapVerboseMData kind proof (reason? := reason?) (role? := role?))
    replaceMainGoal [nextGoal]

private def spineTagConst : SpineTag → Expr
  | .overview      => mkConst ``SpineTag.overview
  | .setupEntity   => mkConst ``SpineTag.setupEntity
  | .gameDef       => mkConst ``SpineTag.gameDef
  | .claimBlock    => mkConst ``SpineTag.claimBlock
  | .sinceStep     => mkConst ``SpineTag.sinceStep
  | .calcChain     => mkConst ``SpineTag.calcChain
  | .caseSplit     => mkConst ``SpineTag.caseSplit
  | .inductionStep => mkConst ``SpineTag.inductionStep
  | .obtainStep    => mkConst ``SpineTag.obtainStep
  | .sufficesStep  => mkConst ``SpineTag.sufficesStep
  | .concludeStep  => mkConst ``SpineTag.concludeStep
  | .ccSpineLeaf   => mkConst ``SpineTag.ccSpineLeaf
  | .pseudocodeBox => mkConst ``SpineTag.pseudocodeBox

/-- Wrap the continuation goal in `spineNode .overview ... "authorGloss"`. -/
private def elabProofIdea (prose : String)
    (bodyTac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none) : TacticM Unit := do
  let mvarId ← getMainGoal
  let stx ← getRef
  mvarId.withContext do
    let target ← mvarId.getType
    let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
    let (tmpl, witness) ← parseAndElabProseInterp prose
    let rem ← match bodyTac? with
      | some tacSeq => runTacSeqOn inner.mvarId! tacSeq
      | none => pure [inner.mvarId!]
    let wrapped ← mkAppM ``spineNode #[
      spineTagConst .overview, mkStrLit "proof-idea", mkStrLit tmpl,
      toExpr true, mkStrLit "", mkStrLit "authorGloss", witness, inner
    ]
    mvarId.assign wrapped
    _root_.Lean.Elab.pushInfoLeaf
      (.ofCustomInfo { stx := stx, value := Dynamic.mk (SpineSpanInfo.mk "proof-idea" "proof-idea") })
    replaceMainGoal rem

/-! ### `by_leaf` Opacity Wall & `proof_idea` -/

syntax (name := paperByLeafStrArrow) "by_leaf " str " => " tacticSeq : tactic
syntax (name := paperByLeafArrow) "by_leaf " " => " tacticSeq : tactic
syntax (name := paperByLeafStrBlock) "by_leaf " str " {" tacticSeq "}" : tactic
syntax (name := paperByLeafBlock) "by_leaf " "{" tacticSeq "}" : tactic

elab_rules : tactic
  | `(tactic| by_leaf $s:str => $tacSeq) =>
      wrapMainGoalByLeaf s.getString tacSeq
  | `(tactic| by_leaf => $tacSeq) =>
      wrapMainGoalByLeaf "routine calculation" tacSeq
  | `(tactic| by_leaf $s:str { $tacSeq }) =>
      wrapMainGoalByLeaf s.getString tacSeq
  | `(tactic| by_leaf { $tacSeq }) =>
      wrapMainGoalByLeaf "routine calculation" tacSeq

syntax (name := paperProofIdea) "proof_idea " str : tactic
syntax (name := paperProofIdeaBlock) "proof_idea " str " {" tacticSeq "}" : tactic

elab_rules : tactic
  | `(tactic| proof_idea $s:str) =>
      elabProofIdea s.getString none
  | `(tactic| proof_idea $s:str { $tacSeq }) =>
      elabProofIdea s.getString (some tacSeq)

/-! ### Archetype 1: Hybrid Transition & Triangle Inequality -/

syntax (name := paperDefineHybrid)
  "Define_hybrid " ident (" : " term)? " := " term (" because " str)? : tactic
syntax (name := paperHybridStepDef)
  "hybrid_step " ident (" : " term)? " := " term (" because " str)? : tactic

syntax (name := paperHybridHopByLeaf)
  "Hybrid_hop " str " : " (atomic(ident " : "))? term " by_leaf " (str)? " {" tacticSeq "}" : tactic
syntax (name := paperHybridHopByLeafArrow)
  "Hybrid_hop " str " : " (atomic(ident " : "))? term " by_leaf " (str)? " => " tacticSeq : tactic
syntax (name := paperHybridHopBy)
  "Hybrid_hop " str " : " (atomic(ident " : "))? term " by " tacticSeq : tactic
syntax (name := paperHybridHopArrow)
  "Hybrid_hop " str " : " (atomic(ident " : "))? term " => " tacticSeq : tactic

syntax (name := paperHybridStepByLeaf)
  "hybrid_step " str " : " (atomic(ident " : "))? term " by_leaf " (str)? " {" tacticSeq "}" : tactic
syntax (name := paperHybridStepByLeafArrow)
  "hybrid_step " str " : " (atomic(ident " : "))? term " by_leaf " (str)? " => " tacticSeq : tactic
syntax (name := paperHybridStepBy)
  "hybrid_step " str " : " (atomic(ident " : "))? term " by " tacticSeq : tactic
syntax (name := paperHybridStepArrow)
  "hybrid_step " str " : " (atomic(ident " : "))? term " => " tacticSeq : tactic

syntax (name := paperConcludeTriangle)
  "Conclude_triangle " "using " "[" term,* "]" (" by " tacticSeq)? : tactic
syntax (name := paperConcludeTriangleLower)
  "conclude_triangle " "using " "[" term,* "]" (" by " tacticSeq)? : tactic

/-- Extract the endpoints `(L, R)` of a distance/advantage/absolute-difference inequality or
equality, used to automatically supply intermediate hybrids to triangle inequality lemmas. -/
private def extractDistEndpoints? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e' ← instantiateMVars e
  let lhs := match e'.consumeMData.getAppFnArgs with
    | (``LE.le, args) => if args.size ≥ 4 then args[2]! else e'
    | (``Eq, args) => if args.size ≥ 3 then args[1]! else e'
    | _ => e'
  let (fn, args) := lhs.consumeMData.getAppFnArgs
  if fn == ``EDist.edist || fn == ``Dist.dist then
    if args.size ≥ 2 then return some (args[args.size - 2]!, args[args.size - 1]!)
  if args.size ≥ 2 then
    let nm := fn.toString
    if (nm.splitOn "fibreMetric").length > 1 ||
        (nm.splitOn "advantage").length > 1 ||
        (nm.splitOn "transcriptDistance").length > 1 then
      return some (args[args.size - 2]!, args[args.size - 1]!)
  if fn == ``abs then
    if args.size ≥ 1 then
      let inner := args[args.size - 1]!.consumeMData
      let (sfn, sargs) := inner.getAppFnArgs
      if sfn == ``HSub.hSub && sargs.size ≥ 6 then
        return some (sargs[4]!, sargs[5]!)
  return none

/-- Try closing a single remaining hop bound (exact proof term or trivial arithmetic norm). -/
private def buildSingleHopTac (h : TSyntax `term) : TacticM (TSyntax `tactic) :=
  `(tactic|
    first
      | exact $h
      | simpa only [zero_add, add_zero, add_assoc] using $h
      | refine le_trans $h (by first | rfl | positivity | linarith | omega))

private def extractIneqRhs? (e : Expr) : MetaM (Option Expr) := do
  let e' ← instantiateMVars e
  match e'.consumeMData.getAppFnArgs with
  | (``LE.le, args) =>
      if args.size ≥ 4 then return some args[args.size - 1]! else return none
  | _ => return none

/-- Build a composite triangle-inequality proof tactic from `[h1, h2, ..., hk]` inside `goalMVar`. -/
private def runTriangleChain (hs : Array (TSyntax `term))
    (extraTac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  if hs.isEmpty then
    throwError "Conclude_triangle requires at least one hypothesis inside `using [...]`"
  if hs.size == 1 then
    let single ← buildSingleHopTac hs[0]!
    let rem ← runTacOn (← getMainGoal) single
    unless rem.isEmpty do
      if let some extra := extraTac? then
        let rem2 ← runTacSeqOn (← getMainGoal) extra
        unless rem2.isEmpty do
          throwError m!"Conclude_triangle left {rem2.length} unsolved goal(s)"
      else
        throwError "Conclude_triangle could not close goal from single hypothesis"
    return
  -- Extract intermediate endpoints and RHS bounds from `h_0 .. h_{k-1}` for explicit chaining.
  let mut mids : Array (TSyntax `term) := #[]
  let mut rhsBounds : Array Expr := #[]
  for i in [:hs.size] do
    let hExpr ← Tactic.elabTerm hs[i]! none
    let hTy ← inferType hExpr
    if i < hs.size - 1 then
      if let some (_, midExpr) ← extractDistEndpoints? hTy then
        let midStx ← PrettyPrinter.delab midExpr
        mids := mids.push midStx
    if let some rExpr ← extractIneqRhs? hTy then
      rhsBounds := rhsBounds.push rExpr
  let closed : Bool ←
    if mids.size == hs.size - 1 && rhsBounds.size == hs.size then
      let snap ← saveState
      try
        let g ← getMainGoal
        g.withContext do
          let target ← instantiateMVars (← g.getType)
          let (lhs, rhs) ← match target.consumeMData.getAppFnArgs with
            | (``LE.le, args) =>
                if args.size ≥ 4 then pure (args[args.size - 2]!, args[args.size - 1]!)
                else throwError "goal is not a binary inequality"
            | _ => throwError "goal is not an inequality"
          let mut totalRhs := rhsBounds[rhsBounds.size - 1]!
          for idx in [:rhsBounds.size - 1] do
            let revIdx := rhsBounds.size - 2 - idx
            totalRhs ← mkAppM ``HAdd.hAdd #[rhsBounds[revIdx]!, totalRhs]
          let triTy ← mkAppM ``LE.le #[lhs, totalRhs]
          let normTy ← mkAppM ``LE.le #[totalRhs, rhs]
          let triMVar ← mkFreshExprMVar (some triTy)
          let normMVar ← mkFreshExprMVar (some normTy)
          g.assign (← mkAppM ``le_trans #[triMVar, normMVar])
          setGoals [triMVar.mvarId!]
          for i in [:mids.size] do
            let mid := mids[i]!
            let hCur := hs[i]!
            let curGoal ← getMainGoal
            let triStepTac ← `(tactic|
              first
                | refine (ConstructiveCryptography.CryptographicAlgebra.distance_triangle _ $mid _).trans (add_le_add $hCur ?_)
                | refine (ConstructiveCryptography.Notation.distance_triangle $mid).trans (add_le_add $hCur ?_)
                | refine (edist_triangle _ $mid _).trans (add_le_add $hCur ?_)
                | refine (dist_triangle _ $mid _).trans (add_le_add $hCur ?_)
                | refine (abs_sub_le _ $mid _).trans (add_le_add $hCur ?_)
                | refine (SystemAlgebra.Domain.Distinguisher.advantage_triangle (S := $mid)).trans (add_le_add $hCur ?_))
            let remStep ← runTacOn curGoal triStepTac
            setGoals remStep
          let lastTac ← buildSingleHopTac hs[hs.size - 1]!
          let remLast ← runTacOn (← getMainGoal) lastTac
          unless remLast.isEmpty do
            throwError "remaining tail in Conclude_triangle"
          setGoals [normMVar.mvarId!]
          let hsArr := hs
          let normTac ← `(tactic|
            first
              | rfl
              | norm_num
              | simp only [add_assoc, zero_add, add_zero]
              | linarith [$[$hsArr],*]
              | positivity
              | (ring; rfl))
          let mut remNorm ← runTacOn normMVar.mvarId! normTac
          if !remNorm.isEmpty then
            if let some extra := extraTac? then
              remNorm ← runTacSeqOn normMVar.mvarId! extra
          if remNorm.isEmpty then
            setGoals []
            pure true
          else
            restoreState snap
            pure false
      catch _ =>
        restoreState snap
        pure false
    else
      pure false
  unless closed do
    -- Fallback: let Lean / `linarith` / `extraTac?` combine the bounds directly.
    let hsArr := hs
    let simpLemmas ← hsArr.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:term)
    let fb ← `(tactic|
      first
        | linarith [$[$hsArr],*]
        | nlinarith [$[$hsArr],*]
        | (try simp only [add_assoc, zero_add, add_zero] at *; linarith [$[$hsArr],*])
        | exact (by first | assumption | simp [$[$simpLemmas],*]))
    let rem ← runTacOn (← getMainGoal) fb
    unless rem.isEmpty do
      if let some extra := extraTac? then
        let rem2 ← runTacSeqOn (← getMainGoal) extra
        unless rem2.isEmpty do
          throwError m!"Conclude_triangle left {rem2.length} unsolved goal(s)"
      else
        throwError "Conclude_triangle could not close the goal from the supplied hybrid bounds"

elab_rules : tactic
  | `(tactic| Define_hybrid $id:ident $[: $ty]? := $val $[because $b?:str]?) =>
      elabPaperLet "paper_define_hybrid" id ty val (b?.map (·.getString))
  | `(tactic| hybrid_step $id:ident $[: $ty]? := $val $[because $b?:str]?) =>
      elabPaperLet "paper_define_hybrid" id ty val (b?.map (·.getString))
  | `(tactic| Hybrid_hop $reason:str : $[$id?:ident :]? $prop by_leaf $[$ls?:str]? { $tacSeq }) =>
      elabPaperHaveLeaf "paper_hybrid_hop" id? prop (some tacSeq) none
        (ls?.map (·.getString) |>.getD reason.getString) (reason? := some reason.getString)
  | `(tactic| Hybrid_hop $reason:str : $[$id?:ident :]? $prop by_leaf $[$ls?:str]? => $tacSeq) =>
      elabPaperHaveLeaf "paper_hybrid_hop" id? prop (some tacSeq) none
        (ls?.map (·.getString) |>.getD reason.getString) (reason? := some reason.getString)
  | `(tactic| Hybrid_hop $reason:str : $[$id?:ident :]? $prop by $tacSeq) =>
      elabPaperHaveLeaf "paper_hybrid_hop" id? prop (some tacSeq) none
        reason.getString (reason? := some reason.getString)
  | `(tactic| Hybrid_hop $reason:str : $[$id?:ident :]? $prop => $tacSeq) =>
      elabPaperHaveLeaf "paper_hybrid_hop" id? prop (some tacSeq) none
        reason.getString (reason? := some reason.getString)
  | `(tactic| hybrid_step $reason:str : $[$id?:ident :]? $prop by_leaf $[$ls?:str]? { $tacSeq }) =>
      elabPaperHaveLeaf "paper_hybrid_hop" id? prop (some tacSeq) none
        (ls?.map (·.getString) |>.getD reason.getString) (reason? := some reason.getString)
  | `(tactic| hybrid_step $reason:str : $[$id?:ident :]? $prop by_leaf $[$ls?:str]? => $tacSeq) =>
      elabPaperHaveLeaf "paper_hybrid_hop" id? prop (some tacSeq) none
        (ls?.map (·.getString) |>.getD reason.getString) (reason? := some reason.getString)
  | `(tactic| hybrid_step $reason:str : $[$id?:ident :]? $prop by $tacSeq) =>
      elabPaperHaveLeaf "paper_hybrid_hop" id? prop (some tacSeq) none
        reason.getString (reason? := some reason.getString)
  | `(tactic| hybrid_step $reason:str : $[$id?:ident :]? $prop => $tacSeq) =>
      elabPaperHaveLeaf "paper_hybrid_hop" id? prop (some tacSeq) none
        reason.getString (reason? := some reason.getString)
  | `(tactic| Conclude_triangle using [$[$hs:term],*] $[by $extra?]?) =>
      wrapGoalWithPaperMData "paper_conclude_triangle"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            runTriangleChain hs extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData "By the triangle inequality across the intermediate hybrids," proof leafKind)
            pure []
          finally
            setGoals saved)
        (count? := some hs.size)
  | `(tactic| conclude_triangle using [$[$hs:term],*] $[by $extra?]?) =>
      wrapGoalWithPaperMData "paper_conclude_triangle"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            runTriangleChain hs extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData "By the triangle inequality across the intermediate hybrids," proof leafKind)
            pure []
          finally
            setGoals saved)
        (count? := some hs.size)

/-! ### Archetype 2: Game Hopping / Difference Lemma / MBO Conditional Equivalence -/

syntax (name := paperBadEvent)
  "Bad_event " ident (" : " term)? " := " term (" because " str)? : tactic

syntax (name := paperIdenticalUntilBadTac)
  "Identical_until_bad " (atomic(ident " : "))? term " by " tacticSeq : tactic
syntax (name := paperIdenticalUntilBadLeaf)
  "Identical_until_bad " (atomic(ident " : "))? term " by_leaf " (str)? " {" tacticSeq "}" : tactic
syntax (name := paperIdenticalUntilBadArrow)
  "Identical_until_bad " (atomic(ident " : "))? term " => " tacticSeq : tactic
syntax (name := paperIdenticalUntilBadTerm)
  "Identical_until_bad " term (" because " str)? : tactic

syntax (name := paperConcludeDiffLemma)
  "Conclude_difference_lemma" (" using " "[" term,* "]")? (" by " tacticSeq)? : tactic

syntax (name := paperGameHopStep)
  "game_hop_step " (str)? (" using " "[" term,* "]")? (" by " tacticSeq)? : tactic
syntax (name := paperGameHopNamed)
  "game_hop_step " ident " := " term " using " "[" term,* "]" (" by " tacticSeq)? : tactic

private def mkAppTerm (fn : Name) (args : Array (TSyntax `term)) : TacticM (TSyntax `term) :=
  args.foldlM (fun acc arg => `($acc $arg)) (mkIdent fn)

private def runDifferenceLemmaCloser (hs : Array (TSyntax `term))
    (extraTac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  if let some extra := extraTac? then
    let rem ← runTacSeqOn (← getMainGoal) extra
    if rem.isEmpty then return
  let tGameDist ← mkAppTerm ``SystemAlgebra.Interface.game_dist_le hs
  let tDistVis ← mkAppTerm ``SystemAlgebra.Interface.dist_visible_le hs
  let tSysVis ← mkAppTerm ``SystemAlgebra.RandomSystem.transcriptDistance_visible_le_of_unsetProbability hs
  let tAdvWin ← mkAppTerm ``SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability hs
  let tDiffDist ← mkAppTerm ``VerboseCC.difference_lemma_distribution hs
  let tDiffProb ← mkAppTerm ``VerboseCC.difference_lemma_probDist hs
  let autoTac ← `(tactic|
    first
      | exact $tGameDist
      | exact $tDistVis
      | exact $tSysVis
      | exact $tAdvWin
      | exact $tDiffDist
      | exact $tDiffProb
      | (refine SystemAlgebra.Interface.game_dist_le ?_ ?_ ?_ <;>
          first | assumption | exact_mod_cast (by first | assumption | linarith [$[$hs],*]) | positivity)
      | (refine SystemAlgebra.Interface.dist_visible_le ?_ ?_ <;>
          first | assumption | linarith [$[$hs],*] | positivity)
      | (refine SystemAlgebra.RandomSystem.transcriptDistance_visible_le_of_unsetProbability _ _ _ ?_ ?_ <;>
          first | assumption | linarith [$[$hs],*])
      | (refine VerboseCC.difference_lemma_distribution _ _ _ _ _ ?_ <;> assumption)
      | (refine VerboseCC.difference_lemma_probDist _ _ _ _ ?_ <;> assumption)
      | linarith [$[$hs],*])
  let rem ← runTacOn (← getMainGoal) autoTac
  unless rem.isEmpty do
    throwError m!"Conclude_difference_lemma left {rem.length} unsolved goal(s)"

elab_rules : tactic
  | `(tactic| Bad_event $id:ident $[: $ty]? := $val $[because $b?:str]?) =>
      elabPaperLet "paper_bad_event" id ty val (b?.map (·.getString))
  | `(tactic| Identical_until_bad $[$id?:ident :]? $prop by $tacSeq) =>
      elabPaperHaveLeaf "paper_identical_until_bad" id? prop (some tacSeq) none
        "identical until bad event" (reason? := some "identical until bad event")
  | `(tactic| Identical_until_bad $[$id?:ident :]? $prop by_leaf $[$ls?:str]? { $tacSeq }) =>
      elabPaperHaveLeaf "paper_identical_until_bad" id? prop (some tacSeq) none
        (ls?.map (·.getString) |>.getD "identical until bad event")
        (reason? := some "identical until bad event")
  | `(tactic| Identical_until_bad $[$id?:ident :]? $prop => $tacSeq) =>
      elabPaperHaveLeaf "paper_identical_until_bad" id? prop (some tacSeq) none
        "identical until bad event" (reason? := some "identical until bad event")
  | `(tactic| Identical_until_bad $pt:term $[because $b?:str]?) =>
      elabPaperWitness "paper_identical_until_bad" pt
        "identical until bad event" (reason? := b?.map (·.getString))
  | `(tactic| Conclude_difference_lemma $[using [$hs?:term,*]]? $[by $extra?]?) =>
      let hs := hs?.map (·.getElems) |>.getD #[]
      wrapGoalWithPaperMData "paper_conclude_diff_lemma"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            runDifferenceLemmaCloser hs extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData "By the Difference Lemma," proof leafKind)
            pure []
          finally
            setGoals saved)
  | `(tactic| game_hop_step $[$prose?:str]? $[using [$hs?:term,*]]? $[by $extra?]?) =>
      let hs := hs?.map (·.getElems) |>.getD #[]
      wrapGoalWithPaperMData "paper_conclude_diff_lemma"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            runDifferenceLemmaCloser hs extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            let sum := (prose?.map (·.getString)).getD "By the Difference Lemma,"
            g.assign (wrapByLeafMData sum proof leafKind)
            pure []
          finally
            setGoals saved)
        (reason? := prose?.map (·.getString))
  | `(tactic| game_hop_step $badId:ident := $badVal using [$[$hs:term],*] $[by $extra?]?) => do
      elabPaperLet "paper_bad_event" badId none badVal none
      wrapGoalWithPaperMData "paper_conclude_diff_lemma"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            runDifferenceLemmaCloser hs extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData "By the Difference Lemma," proof leafKind)
            pure []
          finally
            setGoals saved)
        (label? := some badId.getId.toString)

/-! ### Archetype 3: H-Coefficient Method -/

syntax (name := paperSplitTranscripts)
  "Split_transcripts " ident (" : " term)? " := " term (" because " str)? : tactic

syntax (name := paperBoundBadMassTac)
  "Bound_bad_mass " (atomic(ident " : "))? term (" by " tacticSeq) : tactic
syntax (name := paperBoundBadMassLeaf)
  "Bound_bad_mass " (atomic(ident " : "))? term " by_leaf " (str)? " {" tacticSeq "}" : tactic
syntax (name := paperBoundBadMassArrow)
  "Bound_bad_mass " (atomic(ident " : "))? term " => " tacticSeq : tactic
syntax (name := paperBoundBadMassDef)
  "Bound_bad_mass " (ident)? " := " term (" because " str)? : tactic

syntax (name := paperBoundGoodRatioTac)
  "Bound_good_ratio " (atomic(ident " : "))? term (" by " tacticSeq) : tactic
syntax (name := paperBoundGoodRatioLeaf)
  "Bound_good_ratio " (atomic(ident " : "))? term " by_leaf " (str)? " {" tacticSeq "}" : tactic
syntax (name := paperBoundGoodRatioArrow)
  "Bound_good_ratio " (atomic(ident " : "))? term " => " tacticSeq : tactic
syntax (name := paperBoundGoodRatioDef)
  "Bound_good_ratio " (ident)? " := " term (" because " str)? : tactic

syntax (name := paperConcludeHCoeff)
  "Conclude_h_coeff" (" using " "[" term,* "]")? (" by " tacticSeq)? : tactic

syntax (name := paperHCoeffBlock)
  "h_coeff_argument " (str)? " {" tacticSeq "}" : tactic
syntax (name := paperHCoeffUsing)
  "h_coeff_argument " "using " "[" term,* "]" (" by " tacticSeq)? : tactic

private def runHCoeffCloser (hs : Array (TSyntax `term))
    (extraTac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  if let some extra := extraTac? then
    let rem ← runTacSeqOn (← getMainGoal) extra
    if rem.isEmpty then return
  let tRatio ← mkAppTerm ``SystemAlgebra.RandomSystem.transcriptDistance_le_add_of_ratio_on_good hs
  let tNnreal ← mkAppTerm ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le_nnreal hs
  let tHCoeff ← mkAppTerm ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le hs
  let tStat ← mkAppTerm ``Probability.statDist_le_probBad_add_of_ratio_on_good hs
  let autoTac ← `(tactic|
    first
      | exact $tRatio
      | exact $tNnreal
      | exact $tHCoeff
      | exact $tStat
      | (refine SystemAlgebra.RandomSystem.transcriptDistance_le_add_of_ratio_on_good ?_ ?_ ?_ ?_ <;>
          first | assumption | exact (by first | assumption | linarith [$[$hs],*]))
      | linarith [$[$hs],*])
  let rem ← runTacOn (← getMainGoal) autoTac
  unless rem.isEmpty do
    throwError m!"Conclude_h_coeff left {rem.length} unsolved goal(s)"

elab_rules : tactic
  | `(tactic| Split_transcripts $id:ident $[: $ty]? := $val $[because $b?:str]?) =>
      elabPaperLet "paper_split_transcripts" id ty val (b?.map (·.getString))
  | `(tactic| Bound_bad_mass $[$id?:ident :]? $prop by $tacSeq) =>
      elabPaperHaveLeaf "paper_bound_bad_mass" id? prop (some tacSeq) none
        "bad-transcript probability bound" (reason? := some "bounding the bad-transcript mass")
  | `(tactic| Bound_bad_mass $[$id?:ident :]? $prop by_leaf $[$ls?:str]? { $tacSeq }) =>
      elabPaperHaveLeaf "paper_bound_bad_mass" id? prop (some tacSeq) none
        (ls?.map (·.getString) |>.getD "bad-transcript probability bound")
        (reason? := some "bounding the bad-transcript mass")
  | `(tactic| Bound_bad_mass $[$id?:ident :]? $prop => $tacSeq) =>
      elabPaperHaveLeaf "paper_bound_bad_mass" id? prop (some tacSeq) none
        "bad-transcript probability bound" (reason? := some "bounding the bad-transcript mass")
  | `(tactic| Bound_bad_mass $[$id?:ident]? := $pt:term $[because $b?:str]?) =>
      match id? with
      | some id =>
          withMainContext do
            let v ← Tactic.elabTerm pt none
            let t ← inferType v
            let tyStx ← PrettyPrinter.delab t
            elabPaperHaveLeaf "paper_bound_bad_mass" (some id) tyStx none (some pt)
              "bad-transcript probability bound" (reason? := b?.map (·.getString))
      | none =>
          elabPaperWitness "paper_bound_bad_mass" pt
            "bad-transcript probability bound" (reason? := b?.map (·.getString))
  | `(tactic| Bound_good_ratio $[$id?:ident :]? $prop by $tacSeq) =>
      elabPaperHaveLeaf "paper_bound_good_ratio" id? prop (some tacSeq) none
        "good-transcript ratio bound" (reason? := some "bounding the probability ratio on good transcripts")
  | `(tactic| Bound_good_ratio $[$id?:ident :]? $prop by_leaf $[$ls?:str]? { $tacSeq }) =>
      elabPaperHaveLeaf "paper_bound_good_ratio" id? prop (some tacSeq) none
        (ls?.map (·.getString) |>.getD "good-transcript ratio bound")
        (reason? := some "bounding the probability ratio on good transcripts")
  | `(tactic| Bound_good_ratio $[$id?:ident :]? $prop => $tacSeq) =>
      elabPaperHaveLeaf "paper_bound_good_ratio" id? prop (some tacSeq) none
        "good-transcript ratio bound" (reason? := some "bounding the probability ratio on good transcripts")
  | `(tactic| Bound_good_ratio $[$id?:ident]? := $pt:term $[because $b?:str]?) =>
      match id? with
      | some id =>
          withMainContext do
            let v ← Tactic.elabTerm pt none
            let t ← inferType v
            let tyStx ← PrettyPrinter.delab t
            elabPaperHaveLeaf "paper_bound_good_ratio" (some id) tyStx none (some pt)
              "good-transcript ratio bound" (reason? := b?.map (·.getString))
      | none =>
          elabPaperWitness "paper_bound_good_ratio" pt
            "good-transcript ratio bound" (reason? := b?.map (·.getString))
  | `(tactic| Conclude_h_coeff $[using [$hs?:term,*]]? $[by $extra?]?) =>
      let hs := hs?.map (·.getElems) |>.getD #[]
      wrapGoalWithPaperMData "paper_conclude_h_coeff"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            runHCoeffCloser hs extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData "By the H-coefficient theorem," proof leafKind)
            pure []
          finally
            setGoals saved)
  | `(tactic| h_coeff_argument $[$s?:str]? { $tacSeq }) =>
      let sum := (s?.map (·.getString)).getD "By the H-coefficient theorem,"
      wrapGoalWithPaperMData "paper_h_coeff"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let wrapped ← elabClosedLeafExpr sum target tacSeq
            g.assign wrapped
            pure []
          finally
            setGoals saved)
        (reason? := s?.map (·.getString))
  | `(tactic| h_coeff_argument using [$[$hs:term],*] $[by $extra?]?) =>
      wrapGoalWithPaperMData "paper_conclude_h_coeff"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            runHCoeffCloser hs extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData "By the H-coefficient theorem," proof leafKind)
            pure []
          finally
            setGoals saved)

/-! ### Archetype 4: Constructive Cryptography Composition & Substitution -/

syntax (name := paperCCComposePair)
  "cc_compose_step " term " , " term (" because " str)? (" by " tacticSeq)? : tactic
syntax (name := paperCCComposeUsing)
  "cc_compose_step " "using " "[" term,* "]" (" because " str)? (" by " tacticSeq)? : tactic
syntax (name := paperCCComposeBlock)
  "cc_compose_step " (str)? " {" tacticSeq "}" : tactic

syntax (name := paperCCSubstituteUsing)
  "cc_substitute_step " (term)? " using " term (" because " str)? (" by " tacticSeq)? : tactic
syntax (name := paperCCSubstituteAbsorb)
  "cc_substitute_step " "absorbing " term " via " term (" because " str)? : tactic
syntax (name := paperCCSubstituteBlock)
  "cc_substitute_step " (str)? " {" tacticSeq "}" : tactic

elab_rules : tactic
  | `(tactic| cc_compose_step $h1:term , $h2:term $[because $b?:str]? $[by $extra?]?) =>
      let sum := (b?.map (·.getString)).getD "by serial composition,"
      wrapGoalWithPaperMData "paper_cc_compose"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            let rem ← match extra? with
              | some ex =>
                  runTacSeqOn leafMVar.mvarId! ex
              | none =>
                  let compTac ← `(tactic|
                    first
                      | cc_compose $h1, $h2
                      | exact ConstructiveCryptography.Construction.Constructible.serial $h1 $h2
                      | exact ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial $h1 $h2
                      | exact ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial $h1 $h2
                      | simpa only [CategoryTheory.Category.assoc, add_assoc] using
                          ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial $h1 $h2)
                  runTacOn leafMVar.mvarId! compTac
            unless rem.isEmpty do
              throwError m!"cc_compose_step left {rem.length} unsolved goal(s)"
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData sum proof leafKind)
            pure []
          finally
            setGoals saved)
        (reason? := b?.map (·.getString))
  | `(tactic| cc_compose_step using [$[$hs:term],*] $[because $b?:str]? $[by $extra?]?) =>
      let sum := (b?.map (·.getString)).getD "by serial composition,"
      wrapGoalWithPaperMData "paper_cc_compose"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            let rem ← match extra? with
              | some ex => runTacSeqOn leafMVar.mvarId! ex
              | none =>
                  if hs.size == 2 then
                    let h1 := hs[0]!
                    let h2 := hs[1]!
                    let compTac ← `(tactic|
                      first
                        | cc_compose $h1, $h2
                        | exact ConstructiveCryptography.Construction.Constructible.serial $h1 $h2
                        | exact ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial $h1 $h2
                        | exact ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial $h1 $h2)
                    runTacOn leafMVar.mvarId! compTac
                  else
                    let simpLemmas ← hs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:term)
                    let genTac ← `(tactic| first | cc_construct | simp [$[$simpLemmas],*])
                    runTacOn leafMVar.mvarId! genTac
            unless rem.isEmpty do
              throwError m!"cc_compose_step left {rem.length} unsolved goal(s)"
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData sum proof leafKind)
            pure []
          finally
            setGoals saved)
        (reason? := b?.map (·.getString))
  | `(tactic| cc_compose_step $[$s?:str]? { $tacSeq }) =>
      let sum := (s?.map (·.getString)).getD "by serial composition,"
      wrapGoalWithPaperMData "paper_cc_compose"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let wrapped ← elabClosedLeafExpr sum target tacSeq
            g.assign wrapped
            pure []
          finally
            setGoals saved)
        (reason? := s?.map (·.getString))
  | `(tactic| cc_substitute_step $[$c?:term]? using $h:term $[because $b?:str]? $[by $extra?]?) =>
      let sum := (b?.map (·.getString)).getD "by converter absorption,"
      let lbl? := c?.map fun stx => stx.raw.reprint.getD "C" |>.trimAscii.toString
      wrapGoalWithPaperMData "paper_cc_substitute"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            let rem ← match extra? with
              | some ex => runTacSeqOn leafMVar.mvarId! ex
              | none =>
                  let subTac ← `(tactic|
                    first
                      | cc_transport using $h
                      | cc_nonexpand
                      | exact $h
                      | simpa only [CategoryTheory.Category.assoc] using $h)
                  runTacOn leafMVar.mvarId! subTac
            unless rem.isEmpty do
              throwError m!"cc_substitute_step left {rem.length} unsolved goal(s)"
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData sum proof leafKind)
            pure []
          finally
            setGoals saved)
        (label? := lbl?)
        (reason? := b?.map (·.getString))
  | `(tactic| cc_substitute_step absorbing $conv:term via $h:term $[because $b?:str]?) =>
      let lbl := conv.raw.reprint.getD "C" |>.trimAscii.toString
      let sum := (b?.map (·.getString)).getD s!"by absorbing {lbl} into the distinguisher,"
      wrapGoalWithPaperMData "paper_cc_substitute"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            let subTac ← `(tactic|
              first
                | cc_transport using $h
                | cc_nonexpand
                | exact $h)
            let rem ← runTacOn leafMVar.mvarId! subTac
            unless rem.isEmpty do
              throwError m!"cc_substitute_step left {rem.length} unsolved goal(s)"
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData sum proof leafKind)
            pure []
          finally
            setGoals saved)
        (label? := some lbl)
        (reason? := b?.map (·.getString))
  | `(tactic| cc_substitute_step $[$s?:str]? { $tacSeq }) =>
      let sum := (s?.map (·.getString)).getD "by converter absorption,"
      wrapGoalWithPaperMData "paper_cc_substitute"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let wrapped ← elabClosedLeafExpr sum target tacSeq
            g.assign wrapped
            pure []
          finally
            setGoals saved)
        (reason? := s?.map (·.getString))

/-! ### Archetype 5: Security Reduction + `[Reduction]` Pseudocode Box (`B8` Fix) -/

syntax (name := paperReductionBox)
  "reduction_step " ident (" : " term)? " := " term " box " str str : tactic
syntax (name := paperReductionWith)
  "reduction_step " ident (" : " term)? " := " term " with " str : tactic

elab_rules : tactic
  | `(tactic| reduction_step $id:ident $[: $ty]? := $val box $title:str $body:str) =>
      elabPaperLet "paper_reduction" id ty val
        (reason? := some title.getString) (role? := some body.getString)
  | `(tactic| reduction_step $id:ident $[: $ty]? := $val with $body:str) =>
      elabPaperLet "paper_reduction" id ty val
        (reason? := some s!"Reduction adversary {id.getId}") (role? := some body.getString)

/-! ### Archetype 6: Distinguisher Lower Bound & Bound Contradiction -/

syntax (name := paperDistLowerHave)
  "distinguisher_lower_bound " (atomic(ident " : "))? term " by " tacticSeq : tactic
syntax (name := paperDistLowerLeaf)
  "distinguisher_lower_bound " (atomic(ident " : "))? term " by_leaf " (str)? " {" tacticSeq "}" : tactic
syntax (name := paperDistLowerArrow)
  "distinguisher_lower_bound " (atomic(ident " : "))? term " => " tacticSeq : tactic
syntax (name := paperDistLowerBlock)
  "distinguisher_lower_bound " (str)? " {" tacticSeq "}" : tactic

syntax (name := paperContradictUsing)
  "contradict_bound " ("using " "[" term,* "]")? (" because " str)? (" by " tacticSeq)? : tactic
syntax (name := paperContradictOne)
  "contradict_bound " "using " ident (" because " str)? (" by " tacticSeq)? : tactic

private def runContradictCloser (hs : Array (TSyntax `term))
    (extraTac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  if let some extra := extraTac? then
    let rem ← runTacSeqOn (← getMainGoal) extra
    if rem.isEmpty then return
  if hs.isEmpty then
    let bareTac ← `(tactic|
      first
        | (exfalso <;> linarith)
        | (exfalso <;> nlinarith)
        | (exfalso <;> omega)
        | linarith
        | nlinarith
        | omega)
    let rem ← runTacOn (← getMainGoal) bareTac
    unless rem.isEmpty do
      throwError m!"contradict_bound left {rem.length} unsolved goal(s)"
    return
  let tAbsurd ← mkAppTerm ``absurd hs
  let autoTac ← `(tactic|
    first
      | exact $tAbsurd
      | (exfalso <;> linarith [$[$hs],*])
      | (exfalso <;> nlinarith [$[$hs],*])
      | (exfalso <;> omega)
      | linarith [$[$hs],*]
      | nlinarith [$[$hs],*]
      | omega)
  let rem ← runTacOn (← getMainGoal) autoTac
  unless rem.isEmpty do
    throwError m!"contradict_bound left {rem.length} unsolved goal(s)"

elab_rules : tactic
  | `(tactic| distinguisher_lower_bound $[$id?:ident :]? $prop by $tacSeq) =>
      elabPaperHaveLeaf "paper_dist_lower_bound" id? prop (some tacSeq) none
        "by a distinguisher lower bound," (reason? := some "distinguisher lower bound")
  | `(tactic| distinguisher_lower_bound $[$id?:ident :]? $prop by_leaf $[$ls?:str]? { $tacSeq }) =>
      elabPaperHaveLeaf "paper_dist_lower_bound" id? prop (some tacSeq) none
        (ls?.map (·.getString) |>.getD "by a distinguisher lower bound,")
        (reason? := some "distinguisher lower bound")
  | `(tactic| distinguisher_lower_bound $[$id?:ident :]? $prop => $tacSeq) =>
      elabPaperHaveLeaf "paper_dist_lower_bound" id? prop (some tacSeq) none
        "by a distinguisher lower bound," (reason? := some "distinguisher lower bound")
  | `(tactic| distinguisher_lower_bound $[$s?:str]? { $tacSeq }) =>
      let sum := (s?.map (·.getString)).getD "by a distinguisher lower bound,"
      wrapGoalWithPaperMData "paper_dist_lower_bound"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let wrapped ← elabClosedLeafExpr sum target tacSeq
            g.assign wrapped
            pure []
          finally
            setGoals saved)
        (reason? := s?.map (·.getString))
  | `(tactic| contradict_bound $[using [$hs?:term,*]]? $[because $b?:str]? $[by $extra?]?) =>
      let hs := hs?.map (·.getElems) |>.getD #[]
      let sum := (b?.map (·.getString)).getD "the assumed upper bound"
      wrapGoalWithPaperMData "paper_contradict_bound"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            runContradictCloser hs extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData sum proof leafKind)
            pure []
          finally
            setGoals saved)
        (reason? := b?.map (·.getString))
  | `(tactic| contradict_bound using $h:ident $[because $b?:str]? $[by $extra?]?) =>
      let sum := (b?.map (·.getString)).getD "the assumed upper bound"
      wrapGoalWithPaperMData "paper_contradict_bound"
        (fun g => do
          let saved ← getGoals
          setGoals [g]
          try
            let target ← g.getType
            let leafMVar ← mkFreshExprSyntheticOpaqueMVar target (Name.mkSimple "by_leaf")
            setGoals [leafMVar.mvarId!]
            let hTerm : TSyntax `term := h
            runContradictCloser #[hTerm] extra?
            let proof ← instantiateMVars leafMVar
            let leafKind := if exprContainsSorryAx proof then "sorry_leaf" else "leaf"
            g.assign (wrapByLeafMData sum proof leafKind)
            pure []
          finally
            setGoals saved)
        (reason? := b?.map (·.getString))

end PaperProof
