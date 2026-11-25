/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Ontology
import Informalization.Core.ProofGraph
import ConstructiveCryptography.Construction.Basic
import ConstructiveCryptography.Distinguisher
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import RandomSystems.Distance.Decision
import RandomSystems.Distance.Distinguisher

/-!
# Family F: Explicit Distinguisher Lower Bounds, Impossibility & Tightness Sandwiches

Generic Kyle Miller symbolic explainers for lower bounds and negative results in Constructive
Cryptography:
* Explicit distinguisher / environment-probe advantage lower bounds (`advantage_le_transcriptDistance`,
  `statDist_le_transcriptDistance`, `decisionProbability_gap_le`, `decisionProbability_envProbe`,
  `transcriptDistance_eq_iSup`, `transcriptDistance_eq_iSup_behavior`);
* Impossibility and simulator obstructions (`Unconstructible.of_imp`,
  `Unconstructible.mono_constructors`, proofs of `Unconstructible` or negated constructions);
* Tightness sandwiches (`c₁ ≤ Δ(R, S) ∧ Δ(R, S) ≤ c₂`) combining a matching upper bound with
  an explicit distinguisher lower bound.
-/

namespace Informalization.CC.Families.LowerBounds

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph

private def pickMaurerOpener (kind : TransitionKind) :
    StateRefT DiscourseState MetaM String := do
  let st ← get
  let (op, st') := st.pickOpener kind
  set st'
  return op

private def mkStep (ctx : DecompCtx) (id : String) (content : Array Inline)
    (children : Array ProofNode) (expected : Expr) (origin : Name) :
    StateRefT DiscourseState MetaM ProofNode := do
  let goal ← buildGoalState ctx.tbl expected
  let diagHtml ← if ctx.lemmaDepth == 0 then (← diagramHookRef.get) expected else pure none
  return .step id content children (some goal) diagHtml (some origin.toString)

/-- Check if `e` is a `≤` comparison whose left or right side is a CC distinguishing advantage or distance. -/
private def splitOrder? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← normalizeForPresentation e
  if e.isAppOf ``LE.le || e.isAppOf ``LT.lt then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      return some (args[args.size - 2]!, args[args.size - 1]!)
  return none

/-- Check whether an expression represents a CC distinguishing advantage or statistical distance bound. -/
private def isDistanceExpr (e : Expr) : MetaM Bool := do
  let e ← normalizeForPresentation e
  return e.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.distance ||
         e.isAppOf ``SystemAlgebra.RandomSystem.transcriptDistance

/-- Explainer for explicit distinguisher advantage lower bounds and tightness sandwiches. -/
def distinguisherLowerBoundExplainer : RuleExplainer where
  priority := 145
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let args := proof.getAppArgs
    let some head := fn.constName? | return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    -- 1. Tightness sandwich: `And.intro hLower hUpper` where the same quantity is bounded below and above
    if head == ``And.intro && args.size ≥ 4 then
      let p1 := args[args.size - 2]!
      let p2 := args[args.size - 1]!
      let t1 ← inferType p1
      let t2 ← inferType p2
      if let (some (l1, r1), some (l2, r2)) ← (do return (← splitOrder? t1, ← splitOrder? t2)) then
        let isSandwich :=
          ((← isDistanceExpr r1) && (← isDistanceExpr l2) && r1 == l2) ||
          ((← isDistanceExpr l1) && (← isDistanceExpr r2) && l1 == r2)
        if isSandwich then
          let op ← pickMaurerOpener .consequence
          let subCtx : DecompCtx :=
            { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
          let sub1 ← decompileChild subCtx t1 p1
          let sub2 ← decompileChild subCtx t2 p2
          let inl1 ← renderProposition ctx.tbl t1
          let inl2 ← renderProposition ctx.tbl t2
          let g1 ← buildGoalState ctx.tbl t1
          let g2 ← buildGoalState ctx.tbl t2
          let lowerFirst := (← isDistanceExpr r1)
          let node1 : ProofNode := .step "sandwich-part-1"
            (#[.text (if lowerFirst then "For the matching lower bound, " else "For the upper bound, ")] ++
             inl1 ++ #[.text "."]) sub1 (some g1)
          let node2 : ProofNode := .step "sandwich-part-2"
            (#[.text (if lowerFirst then "For the matching upper bound, " else "For the matching lower bound, ")] ++
             inl2 ++ #[.text "."]) sub2 (some g2)
          return ← finish "cc-tightness-sandwich" (fun conclInl =>
            #[.text s!"{op} combining the matching upper and lower bounds establishes the tightness sandwich "] ++
            conclInl ++ #[.text "."]) #[node1, node2]
    -- 2. Explicit distinguisher / environment-probe lower bounds
    if head == ``SystemAlgebra.Domain.Distinguisher.advantage_le_transcriptDistance ||
       head == ``SystemAlgebra.Domain.DistinguisherBehavior.advantage_le_transcriptDistance ||
       head == ``SystemAlgebra.RandomSystem.statDist_le_transcriptDistance ||
       head == ``SystemAlgebra.RandomSystem.decisionProbability_gap_le then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-lower-dist-{head}" (fun conclInl =>
        #[.text s!"{op} because the maximum distinguishing advantage is the supremum of advantages over all compatible distinguishers, this explicit distinguisher yields the lower bound "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.RandomSystem.decisionProbability_envProbe then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-envprobe-{head}" (fun conclInl =>
        #[.text s!"{op} running the query environment and testing the transcript event decides 1 with exactly the event probability: "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.RandomSystem.transcriptDistance_eq_iSup ||
       head == ``SystemAlgebra.RandomSystem.transcriptDistance_eq_iSup_behavior then
      let op ← pickMaurerOpener .elaboration
      return ← finish s!"cc-isup-char-{head}" (fun conclInl =>
        #[.text s!"{op} characterizing the maximum distinguishing advantage as the supremum over all compatible distinguishers gives "] ++
        conclInl ++ #[.text "."]) #[]
    if head == ``SystemAlgebra.RandomSystem.transcriptDistance_le_of_advantage_le then
      let op ← pickMaurerOpener .reduction
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-isup-le-{head}" (fun conclInl =>
        #[.text s!"{op} since the maximum distinguishing advantage is the supremum over all compatible distinguishers, bounding every distinguisher's advantage establishes "] ++
        conclInl ++ #[.text "."]) children
    return none

/-- Explainer for impossibility proofs, non-constructibility, and simulator obstructions. -/
def impossibilityObstructionExplainer : RuleExplainer where
  priority := 145
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | do
      -- Check if proving `Unconstructible ...` directly by contradiction (lambda into `False`)
      let expClean ← normalizeForPresentation expected
      if expClean.isAppOf ``ConstructiveCryptography.Construction.Unconstructible then
        if let .lam nm dom body bi := proof.consumeMData then
          let op ← pickMaurerOpener .setup
          let subCtx : DecompCtx :=
            { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
          let children ← withLocalDecl nm bi dom fun fv =>
            decompileChild subCtx (mkConst ``False) (body.instantiate1 fv)
          let conclInl ← renderProposition ctx.tbl expected
          let content : Array Inline :=
            #[.text s!"{op} suppose toward a contradiction that an admitted construction existed; deriving a contradiction establishes the impossibility "] ++
            conclInl ++ #[.text "."]
          let goal ← buildGoalState ctx.tbl expected
          let diagHtml ← if ctx.lemmaDepth == 0 then (← diagramHookRef.get) expected else pure none
          return some #[.step "cc-unconstructible-contra" content children (some goal) diagHtml]
      return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.Construction.Unconstructible.of_imp then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-unconst-imp-{head}" (fun conclInl =>
        #[.text s!"{op} pulling back the existing impossibility result along the judgment implication establishes "] ++
        conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.Construction.Unconstructible.mono_constructors then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-unconst-mono-{head}" (fun conclInl =>
        #[.text s!"{op} since no constructor in the larger class succeeds, restricting to a smaller class preserves non-constructibility: "] ++
        conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.distance_eq_of_mutual_attach ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_iso then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-dist-iso-{head}" (fun conclInl =>
        #[.text s!"{op} by non-expansion in both directions, mutually invertible converter attachments preserve the maximum distinguishing advantage exactly: "] ++
        conclInl ++ #[.text "."]) children
    return none

initialize
  registerRuleExplainer distinguisherLowerBoundExplainer
  registerRuleExplainer impossibilityObstructionExplainer

end Informalization.CC.Families.LowerBounds
