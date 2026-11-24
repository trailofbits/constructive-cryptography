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
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction
import ConstructiveCryptography.Substitution.Reduction
import ConstructiveCryptography.Substitution.Implication
import ConstructiveCryptography.Substitution.Quantitative

/-!
# Family B: Substitution Calculus, `cc_calc` Chains & Hybrid Error Ledgers

Generic Kyle Miller symbolic explainers for the Constructive Cryptography substitution calculus
(Jost 2020, Banfi 2023):
* Paper-style `cc_calc` chains (`mixed`, `quantitative`, `statistical`, `counted`), flattening
  `SubstitutesWithin.trans`, exact equality endpoint transports (`Eq.mp`/`Eq.mpr` via `congrArg`),
  and statistical `distance_triangle` chains into a unified `.calcChain` with an automatic
  hybrid error ledger;
* Context transport (`AdmissibleDistinguishers.substitutesWithin_context`,
  `substitutesWithin_attach`, `SubstitutesWithin.attach`, `attach_serial`),
* Distinguisher-class closure (`ClosedUnder.comp`, `ClosedUnder.identity`, `all_closedUnder`),
* Statistical-to-substitution lifting (`SubstitutesWithin.of_distance`, `of_statistical`),
* Counted finite implication witnesses (`Implication.substitutesWithin`,
  `Implication.substitutesWithin_of_mixed`, `derivable_substitutes`).
-/

namespace Informalization.CC.Families.Substitution

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph

/-- Extract all proof-valued arguments `(arg, propType)` from a proof application. -/
private def collectProofArgs (proof : Expr) : MetaM (Array (Expr × Expr)) := do
  let mut out : Array (Expr × Expr) := #[]
  for arg in proof.getAppArgs do
    try
      let ty ← inferType arg
      if ← isProp ty then
        out := out.push (arg, ty)
    catch _ => pure ()
  return out

private def decompileProofArgs (ctx : DecompCtx) (decompileChild : DecompileChild)
    (proof : Expr) : StateRefT DiscourseState MetaM (Array ProofNode) := do
  let pArgs ← collectProofArgs proof
  let mut children : Array ProofNode := #[]
  for (ap, aty) in pArgs do
    let sub ← decompileChild ctx aty ap
    children := children ++ sub
  return children

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
  let diagHtml ← (← diagramHookRef.get) expected
  return .step id content children (some goal) diagHtml (some origin.toString)

/-- Classification of a single hop extracted from a `cc_calc` hybrid chain. -/
private inductive HopKind
  | exactEq
  | computational
  | statistical
  deriving DecidableEq, BEq

private structure ExtractedHop where
  kind : HopKind
  lhs : Expr
  rhs : Expr
  relLatex : String
  proof : Expr
  prop : Expr

/-- Detect if `prop` is `distance lhs rhs ≤ eps` and return `(lhs, rhs, eps)`. -/
private def splitDistanceBound? (prop : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let prop ← normalizeForPresentation prop
  if prop.isAppOf ``LE.le then
    let args := prop.getAppArgs
    if args.size ≥ 2 then
      let lhs := args[args.size - 2]!
      let rhs := args[args.size - 1]!
      let lhs' ← normalizeForPresentation lhs
      if lhs'.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.distance then
        let dArgs := lhs'.getAppArgs
        if dArgs.size ≥ 2 then
          return some (dArgs[dArgs.size - 2]!, dArgs[dArgs.size - 1]!, rhs)
  return none

/-- Detect if `prop` is `SubstitutesWithin model err lhs rhs` and return `(err, lhs, rhs)`. -/
private def splitSubstitutesWithin? (prop : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let prop ← normalizeForPresentation prop
  if prop.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin then
    let args := prop.getAppArgs
    if args.size ≥ 3 then
      return some (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)
  return none

/-- Detect if `proof` is an equality transport `Eq.mp (congrArg f eqProof) inner` or
`Eq.mpr (congrArg f eqProof) inner` produced by `cc_calc` for an exact join `=`. -/
private def splitEqTransport? (proof : Expr) : MetaM (Option (Bool × Expr × Expr)) := do
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  let args := p.getAppArgs
  let some head := fn.constName? | return none
  if (head == ``Eq.mp || head == ``Eq.mpr) && args.size ≥ 2 then
    let eqArg := args[args.size - 2]!.consumeMData
    let inner := args[args.size - 1]!
    if eqArg.isAppOf ``congrArg then
      let cArgs := eqArg.getAppArgs
      if let some eqProof := cArgs.back? then
        let eqTy ← inferType eqProof
        if eqTy.isAppOf ``Eq then
          return some (head == ``Eq.mp, eqProof, inner)
  return none

/-- Detect a statistical triangle step `(distance_triangle _ _ _).trans (add_le_add p1 p2)`. -/
private def splitStatTriangle? (proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  let args := p.getAppArgs
  let some head := fn.constName? | return none
  if head == ``LE.le.trans && args.size ≥ 2 then
    let pTri := args[args.size - 2]!.consumeMData
    let pAdd := args[args.size - 1]!.consumeMData
    if pTri.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.distance_triangle &&
       pAdd.isAppOf ``add_le_add then
      let addArgs := pAdd.getAppArgs
      if addArgs.size ≥ 2 then
        return some (addArgs[addArgs.size - 2]!, addArgs[addArgs.size - 1]!)
  return none

/-- Recursively flatten a `cc_calc` proof term (mixed, quantitative, or statistical) into
ordered `ExtractedHop`s, preserving exact equality joins alongside approximation steps. -/
private partial def flattenCCCalc (tbl : SymbolTable) (proof expected : Expr) (fuel : Nat := 32) :
    MetaM (Array ExtractedHop) := do
  if fuel == 0 then return #[]
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  -- Case 1: `SubstitutesWithin.trans model p1 p2`
  if fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.trans then
    let pArgs ← collectProofArgs p
    if pArgs.size == 2 then
      let (p1, t1) := pArgs[0]!
      let (p2, t2) := pArgs[1]!
      let left ← flattenCCCalc tbl p1 t1 (fuel - 1)
      let right ← flattenCCCalc tbl p2 t2 (fuel - 1)
      return left ++ right
  -- Case 2: Statistical `(distance_triangle ...).trans (add_le_add p1 p2)`
  if let some (p1, p2) ← splitStatTriangle? p then
    let t1 ← inferType p1
    let t2 ← inferType p2
    let left ← flattenCCCalc tbl p1 t1 (fuel - 1)
    let right ← flattenCCCalc tbl p2 t2 (fuel - 1)
    return left ++ right
  -- Case 3: Exact equality join transport `Eq.mp / Eq.mpr (congrArg ...) inner`
  if let some (isRightJoin, eqProof, inner) ← splitEqTransport? p then
    let eqTy ← inferType eqProof
    let innerTy ← inferType inner
    let innerHops ← flattenCCCalc tbl inner innerTy (fuel - 1)
    let mut eqHops : Array ExtractedHop := #[]
    if let some (_, lhs, rhs) := eqTy.eq? then
      -- Skip reflexive no-op joins `X = X`
      let isRefl := eqProof.consumeMData.isAppOf ``Eq.refl || eqProof.consumeMData.isConstOf ``rfl
      if !isRefl && lhs != rhs then
        eqHops := #[{ kind := .exactEq, lhs, rhs, relLatex := "=", proof := eqProof, prop := eqTy }]
    if isRightJoin then
      return innerHops ++ eqHops
    else
      return eqHops ++ innerHops
  -- Leaf case: `SubstitutesWithin` (either statistical via `of_distance`/`of_statistical` or computational)
  if let some (err, lhs, rhs) ← splitSubstitutesWithin? expected then
    let isStat :=
      fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance ||
      fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical
    let errTex ← match err.consumeMData with
      | .lam _ _ body _ =>
          if !body.hasLooseBVar 0 then exprToLatex body tbl
          else exprToLatex err tbl
      | _ => exprToLatex err tbl
    let rel := if isStat then "\\approx_{" ++ errTex ++ "}" else "\\simeq_{" ++ errTex ++ "}"
    return #[{
      kind := if isStat then .statistical else .computational
      lhs, rhs, relLatex := rel, proof := p, prop := expected
    }]
  -- Leaf case: statistical distance `Δ lhs rhs ≤ ε`
  if let some (lhs, rhs, eps) ← splitDistanceBound? expected then
    let epsTex ← exprToLatex eps tbl
    return #[{
      kind := .statistical
      lhs, rhs, relLatex := "\\approx_{" ++ epsTex ++ "}", proof := p, prop := expected
    }]
  return #[]

/-- Produce a concise Maurer-style reason label for one hop in a `cc_calc` chain. -/
private def describeHopReason (env : Environment) (tbl : SymbolTable) (hop : ExtractedHop) :
    MetaM (Array Inline) := do
  let fn := hop.proof.getAppFn.consumeMData
  let args := hop.proof.getAppArgs
  match hop.kind with
  | .exactEq =>
      match fn with
      | .const cn _ =>
          if cn == ``Eq.trans then
            return #[.text "by chaining exact system identities"]
          else if cn == ``Eq.symm then
            return #[.text "by symmetry of exact system identity"]
          else
            return #[.text "by exact identity (", .emph (humanLemmaLabel env cn), .text ")"]
      | .fvar id =>
          let decl ← id.getDecl
          match cleanBinderName? decl.userName with
          | some hn => return #[.text "by identity ", .inlineMath (formatMathIdent hn)]
          | none => return #[.text "by the assumed identity"]
      | _ => return #[.text "by exact system equality"]
  | .statistical =>
      match fn with
      | .const cn _ =>
          if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance ||
             cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical then
            return #[.text "by statistical distance bound"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le then
            return #[.text "by non-expansion under converter attachment"]
          else
            return #[.text "by statistical bound (", .emph (humanLemmaLabel env cn), .text ")"]
      | _ => return #[.text "by statistical distance bound"]
  | .computational =>
      match fn with
      | .const cn _ =>
          if cn == ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_context ||
             cn == ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_attach then
            -- Find the converter argument (first non-Prop explicit argument of arrow/converter type)
            for arg in args do
              try
                let ty ← inferType arg
                if ty.isAppOf `Quiver.Hom || ty.isAppOf `SystemAlgebra.TypedConverter then
                  let convTex ← exprToLatex arg tbl
                  return #[.text "by substituting inside context ", .inlineMath convTex,
                           .text " (absorbing ", .inlineMath convTex, .text " into the distinguisher)"]
              catch _ => pure ()
            return #[.text "by substituting inside a converter context"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.symm then
            return #[.text "by symmetry of substitution"]
          else
            return #[.text "by substitution (", .emph (humanLemmaLabel env cn), .text ")"]
      | .fvar id =>
          let decl ← id.getDecl
          match cleanBinderName? decl.userName with
          | some hn => return #[.text "by assumption ", .inlineMath (formatMathIdent hn)]
          | none => return #[.text "by the assumed substitution"]
      | _ => return #[.text "by substitution"]

/-- Explainer for multi-step `cc_calc` chains (mixed, quantitative, statistical). -/
def ccCalcChainExplainer : RuleExplainer where
  priority := 155
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let isChainRoot :=
      fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.trans ||
      (← splitStatTriangle? proof).isSome ||
      (← splitEqTransport? proof).isSome
    if !isChainRoot then return none
    -- Only trigger when the expected goal is a substitution or statistical distance bound
    let isSubGoal := (← splitSubstitutesWithin? expected).isSome
    let isDistGoal := (← splitDistanceBound? expected).isSome
    if !isSubGoal && !isDistGoal then return none
    let hops ← flattenCCCalc ctx.tbl proof expected
    if hops.size < 2 then return none
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
      let reason ← describeHopReason env ctx.tbl hop
      let subNodes ← decompileChild ctx hop.prop hop.proof
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
    let op ← pickMaurerOpener .elaboration
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
        s!"{op} proceeding through the hybrid chain ({joinAnd summaryParts}) and summing the per-step errors by the triangle inequality gives"
    let chainNode : ProofNode :=
      .calcChain s!"cc-calc-{hops.size}" #[.text ledgerText] calcSteps (some goal)
    return some #[chainNode]

/-- Explainer for individual substitution, context-transport, closure, and counted-implication steps. -/
def substitutionRuleExplainer : RuleExplainer where
  priority := 145
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let args := proof.getAppArgs
    let some head := fn.constName? | return none
    let conclInl ← renderProposition ctx.tbl expected
    if head == ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_context ||
       head == ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_attach ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.attach ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.attach_serial then
      let children ← decompileProofArgs ctx decompileChild proof
      let op ← pickMaurerOpener .elaboration
      -- Try to find the converter term among arguments
      let mut convTex? : Option String := none
      for arg in args do
        if convTex?.isNone then
          try
            let ty ← inferType arg
            if ty.isAppOf `Quiver.Hom || ty.isAppOf `SystemAlgebra.TypedConverter then
              convTex? := some (← exprToLatex arg ctx.tbl)
          catch _ => pure ()
      let convPhrase : Array Inline := match convTex? with
        | some c => #[.text "the converter ", .inlineMath c,
                      .text " (absorbing ", .inlineMath c, .text " into the distinguisher)"]
        | none => #[.text "the surrounding converter context"]
      let content : Array Inline :=
        #[.text s!"{op} transporting the substitution through "] ++ convPhrase ++
        #[.text "—using closure of the distinguisher class—yields "] ++ conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-sub-ctx-{head}" content children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical then
      let children ← decompileProofArgs ctx decompileChild proof
      let op ← pickMaurerOpener .justification
      let content : Array Inline :=
        #[.text s!"{op} every admitted distinguisher's advantage is bounded by the statistical transcript distance, "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-sub-stat-{head}" content children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.symm then
      let children ← decompileProofArgs ctx decompileChild proof
      let op ← pickMaurerOpener .elaboration
      let content : Array Inline :=
        #[.text s!"{op} by symmetry of distinguishing advantage, reversing the substitution preserves the error function and yields "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-sub-symm-{head}" content children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.AdmissibleDistinguishers.ClosedUnder.comp then
      let children ← decompileProofArgs ctx decompileChild proof
      let op ← pickMaurerOpener .consequence
      let content : Array Inline :=
        #[.text s!"{op} absorbing a sequential composition of converters absorbs each converter in turn, so the distinguisher class remains closed: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-closed-comp-{head}" content children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.AdmissibleDistinguishers.ClosedUnder.identity ||
       head == ``ConstructiveCryptography.AdmissibleDistinguishers.all_closedUnder then
      let op ← pickMaurerOpener .elaboration
      let content : Array Inline :=
        #[.text s!"{op} the distinguisher class is trivially closed under this absorption: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-closed-triv-{head}" content #[] expected head
      return some #[node]
    if head == ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.substitutesWithin ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.substitutesWithin_of_mixed ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.derivable_substitutes then
      let children ← decompileProofArgs ctx decompileChild proof
      let op ← pickMaurerOpener .consequence
      let content : Array Inline :=
        #[.text s!"{op} accumulating the per-step error budgets along the finite substitution chain yields "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-implication-{head}" content children expected head
      return some #[node]
    return none

initialize
  registerRuleExplainer ccCalcChainExplainer
  registerRuleExplainer substitutionRuleExplainer

end Informalization.CC.Families.Substitution
