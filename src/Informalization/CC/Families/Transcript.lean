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
import RandomSystems.Distance.HCoefficient
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Distance.RatioCost
import ConstructiveCryptography.Instances.Algebra

/-!
# Family D: Patarin's H-Coefficient Technique, Revealed Transcripts & Ratio-Cost Bounds

Generic Kyle Miller symbolic explainers for information-theoretic transcript arguments:
* Classical H-coefficient bad-event mass + good-transcript ratio split
  (`RandomSystem.transcriptDistance_le_add_of_ratio_on_good`);
* Extended/revealed-transcript H-coefficient witnesses and expectation method
  (`RandomSystem.HCoefficient`, `HCoefficient.ofGoodBad`, `HCoefficient.transcriptDistance_le`,
  `HCoefficient.transcriptDistance_le_nnreal`, `Interface.distance_le_of_hCoefficient`,
  `RandomSystem.statDist_sLaw_le_of_reveal`);
* Retained good-mass + multiplicative transcript ratio bounds
  (`RandomSystem.transcriptDistance_le_add_of_ratio_and_transcriptCost`).
-/

namespace Informalization.CC.Families.Transcript

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

private def decompileSlotSubproof (ctx : DecompCtx) (decompileChild : DecompileChild)
    (idTag : String) (aty ap : Expr) : StateRefT DiscourseState MetaM (Array ProofNode) := do
  if let some fvid := unwrapHypothesisFVar? ap then
    let node ← renderHypothesisStep ctx.tbl aty fvid s!"{idTag}-{fvid.name}" (isWrap := true)
    return #[node]
  let subCtx : DecompCtx :=
    { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false }
  decompileChild subCtx aty ap

/-- Inspect an `HCoefficient` witness term (unfolding a single project definition if needed)
and extract labeled child nodes for its ratio bound and bad-event/expected-error bound. -/
private partial def explainHCoefficientWitness (ctx : DecompCtx) (decompileChild : DecompileChild)
    (witness : Expr) : StateRefT DiscourseState MetaM (Array ProofNode) := do
  let w ← instantiateMVars witness
  let w := w.consumeMData
  let fn := w.getAppFn.consumeMData
  let args := w.getAppArgs
  if fn.isConstOf ``SystemAlgebra.RandomSystem.HCoefficient.ofGoodBad then
    -- Collect the good-ratio and bad-mass proof obligations cleanly
    let pArgs ← proofValuedArgs w
    let mut children : Array ProofNode := #[]
    let total := pArgs.size
    for idx in [:total] do
      let (ap, aty) := pArgs[idx]!
      -- The last two proof arguments of `ofGoodBad` are `ratio` and `bad`
      if idx + 2 == total then
        let sub ← decompileSlotSubproof ctx decompileChild s!"hcoeff-good-ratio-{idx}" aty ap
        let subInl ← renderProposition ctx.tbl aty
        let goal ← buildGoalState ctx.tbl aty
        children := children.push (.step s!"hcoeff-good-ratio-{idx}"
          (#[.text "On every good extended transcript, the real-to-ideal probability ratio satisfies "] ++
           subInl ++ #[.text "."]) sub (some goal))
      else if idx + 1 == total then
        let sub ← decompileSlotSubproof ctx decompileChild s!"hcoeff-bad-mass-{idx}" aty ap
        let subInl ← renderProposition ctx.tbl aty
        let goal ← buildGoalState ctx.tbl aty
        children := children.push (.step s!"hcoeff-bad-mass-{idx}"
          (#[.text "Under every compatible query-bounded environment, the ideal probability of a bad transcript is bounded by "] ++
           subInl ++ #[.text "."]) sub (some goal))
    return children
  if fn.isConstOf ``SystemAlgebra.RandomSystem.HCoefficient.mk then
    let pArgs ← proofValuedArgs w
    let mut children : Array ProofNode := #[]
    let total := pArgs.size
    for idx in [:total] do
      let (ap, aty) := pArgs[idx]!
      if idx + 2 == total then
        let sub ← decompileSlotSubproof ctx decompileChild s!"hcoeff-class-ratio-{idx}" aty ap
        let subInl ← renderProposition ctx.tbl aty
        let goal ← buildGoalState ctx.tbl aty
        children := children.push (.step s!"hcoeff-class-ratio-{idx}"
          (#[.text "For every extended transcript, the class-wise real-to-ideal ratio satisfies "] ++
           subInl ++ #[.text "."]) sub (some goal))
      else if idx + 1 == total then
        let sub ← decompileSlotSubproof ctx decompileChild s!"hcoeff-class-bound-{idx}" aty ap
        let subInl ← renderProposition ctx.tbl aty
        let goal ← buildGoalState ctx.tbl aty
        children := children.push (.step s!"hcoeff-class-bound-{idx}"
          (#[.text "Taking expectations over the transcript classes under any compatible environment yields "] ++
           subInl ++ #[.text "."]) sub (some goal))
    return children
  -- If `witness` is a named project definition (e.g., `constantReveal`), try one unfold step
  if let .const cn _ := fn then
    if !ctx.seenDecls.contains cn && ctx.lemmaDepth < ctx.config.maxLemmaDepth then
      let env ← getEnv
      if let some (.defnInfo dinfo) := env.find? cn then
        let childCtx : DecompCtx := {
          ctx with
          seenDecls := ctx.seenDecls.insert cn
          lemmaDepth := ctx.lemmaDepth + 1
          isProofStart := false
        }
        let sub ← decompilePremiseArgs childCtx decompileChild w
        let body := (dinfo.value.beta args).consumeMData
        let bodyChildren ←
          if body.getAppFn.isConstOf ``SystemAlgebra.RandomSystem.HCoefficient.ofGoodBad ||
             body.getAppFn.isConstOf ``SystemAlgebra.RandomSystem.HCoefficient.mk then
            explainHCoefficientWitness childCtx decompileChild body
          else
            pure #[]
        return sub ++ bodyChildren
  return #[]

/-- Explainer for Patarin's H-coefficient method, revealed-transcript expectation bounds,
and ratio-plus-transcript-cost bounds. -/
def hCoefficientExplainer : RuleExplainer where
  priority := 150
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let args := proof.getAppArgs
    let some head := fn.constName? | return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    if head == ``SystemAlgebra.Interface.distance_le_of_hCoefficient ||
       head == ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le ||
       head == ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le_nnreal then
      let op ← pickMaurerOpener .consequence
      -- Locate the `HCoefficient` witness argument among `args`
      let mut witnessChildren : Array ProofNode := #[]
      for arg in args do
        try
          let ty ← inferType arg
          if ty.isAppOf ``SystemAlgebra.RandomSystem.HCoefficient then
            witnessChildren := witnessChildren ++ (← explainHCoefficientWitness ctx decompileChild arg)
        catch _ => pure ()
      return ← finish s!"cc-hcoeff-{head}" (fun conclInl =>
        #[.text s!"{op} by the revealed-transcript H-coefficient technique—comparing the extended real and ideal transcript laws and forgetting the auxiliary reveal by data processing—we obtain "] ++
        conclInl ++ #[.text "."]) witnessChildren
    if head == ``SystemAlgebra.RandomSystem.statDist_sLaw_le_of_reveal then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-reveal-expect-{head}" (fun conclInl =>
        #[.text s!"{op} by the expectation method on extended transcripts (applying data processing to marginalize out the revealed record), the statistical distance of the transcript laws is bounded by the ideal expected ratio defect: "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.RandomSystem.transcriptDistance_le_add_of_ratio_on_good then
      let op ← pickMaurerOpener .consequence
      let pArgs ← proofValuedArgs proof
      let mut children : Array ProofNode := #[]
      let total := pArgs.size
      for idx in [:total] do
        let (ap, aty) := pArgs[idx]!
        if idx + 2 == total then
          let sub ← decompileSlotSubproof ctx decompileChild s!"hcoeff-ratio-{idx}" aty ap
          let subInl ← renderProposition ctx.tbl aty
          let goal ← buildGoalState ctx.tbl aty
          children := children.push (.step s!"hcoeff-ratio-{idx}"
            (#[.text "For every good transcript, the real probability satisfies the ratio lower bound "] ++
             subInl ++ #[.text "."]) sub (some goal))
        else if idx + 1 == total then
          let sub ← decompileSlotSubproof ctx decompileChild s!"hcoeff-bad-{idx}" aty ap
          let subInl ← renderProposition ctx.tbl aty
          let goal ← buildGoalState ctx.tbl aty
          children := children.push (.step s!"hcoeff-bad-{idx}"
            (#[.text "The bad-transcript mass under the ideal system is bounded by "] ++
             subInl ++ #[.text "."]) sub (some goal))
      return ← finish s!"cc-hcoeff-goodbad-{head}" (fun conclInl =>
        #[.text s!"{op} by Patarin's H-coefficient technique, splitting transcripts into a bad event and a good set with a uniform real-to-ideal probability ratio yields "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.RandomSystem.transcriptDistance_le_add_of_ratio_and_transcriptCost then
      let op ← pickMaurerOpener .consequence
      let pArgs ← proofValuedArgs proof
      let mut children : Array ProofNode := #[]
      let total := pArgs.size
      for idx in [:total] do
        let (ap, aty) := pArgs[idx]!
        if idx + 3 == total then
          let sub ← decompileSlotSubproof ctx decompileChild s!"rc-ratio-{idx}" aty ap
          let subInl ← renderProposition ctx.tbl aty
          let goal ← buildGoalState ctx.tbl aty
          children := children.push (.step s!"rc-ratio-{idx}"
            (#[.text "On every transcript, the real system dominates the scaled good sub-mass: "] ++
             subInl ++ #[.text "."]) sub (some goal))
        else if idx + 2 == total then
          let sub ← decompileSlotSubproof ctx decompileChild s!"rc-loss-{idx}" aty ap
          let subInl ← renderProposition ctx.tbl aty
          let goal ← buildGoalState ctx.tbl aty
          children := children.push (.step s!"rc-loss-{idx}"
            (#[.text "Each admissible query loses at most the per-step cost from the good sub-mass: "] ++
             subInl ++ #[.text "."]) sub (some goal))
        else if idx + 1 == total then
          let sub ← decompileSlotSubproof ctx decompileChild s!"rc-cost-{idx}" aty ap
          let subInl ← renderProposition ctx.tbl aty
          let goal ← buildGoalState ctx.tbl aty
          children := children.push (.step s!"rc-cost-{idx}"
            (#[.text "Along every possible ideal transcript, the accumulated step cost is bounded by "] ++
             subInl ++ #[.text "."]) sub (some goal))
      return ← finish s!"cc-ratiocost-{head}" (fun conclInl =>
        #[.text s!"{op} combining the retained good-mass potential (which bounds the cumulative bad-event loss) with the multiplicative real-to-good probability ratio yields "] ++
        conclInl ++ #[.text "."]) children
    return none

initialize
  registerRuleExplainer hCoefficientExplainer

end Informalization.CC.Families.Transcript
