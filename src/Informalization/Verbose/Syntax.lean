/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Spine
import Informalization.Verbose.Trace
import Informalization.Verbose.ProseInterp
import Probability.Distribution
import ConstructiveCryptography.Tactics.Basic
import ConstructiveCryptography.Tactics.Categorical
import ConstructiveCryptography.Tactics.Substitution
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
import Commons.Definitions.Indifferentiability
import ConstructiveCryptography.Instances.Algebra
import ConstructiveCryptography.Instances.Game
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Game.MBO
import RandomSystems.Game.UntilBad

/-!
# Paper-Grounded Verbose-CC Authoring Syntax (`scoped` in `VerboseCC`)

Controlled natural-language tactics grounded strictly in the 70-quote Constructive Cryptography,
Random Systems, and H-Technique paper corpus (`cc_paper_sentence_corpus.md`):

* **F1 (Local shorthands):** `Write x := e`
* **F2 (Constructions, substitutions & composition):** `Construct_using h`, `Construct S from R via π using h`,
  `Replace_converter_in h using hEq`, `By_sequential_composition h1 and h2`,
  `By_parallel_composition hL and hR`, `By_context_insensitivity_right T using h`,
  `By_context_insensitivity_left T using h`, `Pull_relaxation_through hOuter using hCompat from hInner`,
  `Substitute_in_context ...`
* **F3 (Hybrids & `cc_calc`):** `Introduce_hybrid H := e`, `By_triangle_inequality_via M`,
  `By_non_expansion`, `By_hybrid_chain { ... }`, and `because_of "..." => proof`
* **F4 (Simulators & indifferentiability):** `Exhibit_simulator σ`, `Compose_simulators hInner and hOuter`
* **F5 (Games, MBOs & H-coefficients):** `Ignore_MBO_of G`, `By_fundamental_lemma_of_game_playing h`,
  `By_conditional_equivalence h`, `By_extended_H_technique ...`
* **F6 (Distinguishers & sandwiches):** `Exhibit_distinguisher D`, `Lower_bound_advantage_of D ...`,
  `Tightness_sandwich ...`
* **F7 (Discourse transitions & routine compression):** `Claim h : P by ...`, `Fact h : P by ...`,
  `It_suffices_to_show P by/because ...`, `By_CC_routine { ... }`, `Combining ...`

All forms are `scoped` inside `namespace VerboseCC` (`open scoped VerboseCC`), deterministically
lower to checked Constructive Cryptography / Random Systems tactics and lemmas, and emit zero-cost
`Expr.mdata` trace tags without expanding the Lean kernel trust base.
-/

namespace VerboseCC

open Lean Meta Elab Term Tactic
open Lean.Parser.Tactic
open Informalization.Core.Spine
open Informalization.Verbose.Trace
open Informalization.Verbose.ProseInterp

/-! ## Elaboration Helpers -/

/-- Execute `tacs` on a fresh synthetic-opaque metavariable of the current goal type and wrap the
resulting partial or complete proof term in zero-cost Verbose-CC `Expr.mdata`. Any remaining
subgoals created by `tacs` become the new main goals. -/
private def wrapGoalWithMData (kind : String)
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
    mvarId.assign (wrapVerboseMData kind inner label? reason? role? count?)
    replaceMainGoal remaining

/-- Run a `TSyntax \`tactic` on `innerMVar`, returning any leftover subgoals. -/
private def runTacticOnGoal (innerMVar : MVarId) (tac : TSyntax `tactic) :
    TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [innerMVar]
  try
    evalTactic tac
    let rem ← getGoals
    setGoals saved
    return rem
  catch e =>
    setGoals saved
    throw e

/-- Run a `TSyntax \`Lean.Parser.Tactic.tacticSeq` on `innerMVar`, returning any leftover subgoals. -/
private def runTacticSeqOnGoal (innerMVar : MVarId)
    (tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [innerMVar]
  try
    evalTactic tacSeq
    let rem ← getGoals
    setGoals saved
    return rem
  catch e =>
    setGoals saved
    throw e

/-- Extract a concise label string from a syntax term (e.g., simulator/distinguisher identifier). -/
private def syntaxShortLabel? (stx : Syntax) : Option String :=
  match stx.unsetTrailing.reprint with
  | some s =>
      let trimmed := s.trimAscii.toString
      if trimmed.isEmpty || trimmed.length > 32 then none else some trimmed
  | none => none

/-- Event-space Difference Lemma for any nonnegative distribution: if `W₀ ∧ ¬ Z ↔ W₁ ∧ ¬ Z`,
then `|X(W₀) - X(W₁)| ≤ X(Z)`. -/
theorem difference_lemma_distribution {Ω : Type*} (X : Probability.Distribution Ω)
    (hX : X.NonNeg) (W₀ W₁ Z : Ω → Prop)
    (hEquiv : ∀ ω, W₀ ω ∧ ¬ Z ω ↔ W₁ ω ∧ ¬ Z ω) :
    |X.mass W₀ - X.mass W₁| ≤ X.mass Z := by
  classical
  have s0 : X.mass (fun ω => Z ω ∧ W₀ ω) + X.mass (fun ω => ¬ Z ω ∧ W₀ ω) = X.mass W₀ :=
    Probability.Distribution.mass_and_add_mass_not_and X Z W₀
  have s1 : X.mass (fun ω => Z ω ∧ W₁ ω) + X.mass (fun ω => ¬ Z ω ∧ W₁ ω) = X.mass W₁ :=
    Probability.Distribution.mass_and_add_mass_not_and X Z W₁
  have eqNot : X.mass (fun ω => ¬ Z ω ∧ W₀ ω) = X.mass (fun ω => ¬ Z ω ∧ W₁ ω) := by
    refine congrArg (fun f => X.mass f) (funext fun ω => propext ?_)
    exact ⟨fun h => ⟨h.1, ((hEquiv ω).mp ⟨h.2, h.1⟩).1⟩,
      fun h => ⟨h.1, ((hEquiv ω).mpr ⟨h.2, h.1⟩).1⟩⟩
  have b0 : 0 ≤ X.mass (fun ω => Z ω ∧ W₀ ω) := hX.mass_nonneg _
  have b1 : 0 ≤ X.mass (fun ω => Z ω ∧ W₁ ω) := hX.mass_nonneg _
  have u0 : X.mass (fun ω => Z ω ∧ W₀ ω) ≤ X.mass Z :=
    Probability.Distribution.mass_mono hX fun _ h => h.1
  have u1 : X.mass (fun ω => Z ω ∧ W₁ ω) ≤ X.mass Z :=
    Probability.Distribution.mass_mono hX fun _ h => h.1
  rw [abs_le]
  constructor <;> linarith

/-- Event-space Difference Lemma on a probability distribution (`ProbDist`). -/
theorem difference_lemma_probDist {Ω : Type*} (P : Probability.Distribution.ProbDist Ω)
    (W₀ W₁ Z : Ω → Prop)
    (hEquiv : ∀ ω, W₀ ω ∧ ¬ Z ω ↔ W₁ ω ∧ ¬ Z ω) :
    |P.val.mass W₀ - P.val.mass W₁| ≤ P.val.mass Z :=
  difference_lemma_distribution P.val P.property.nonNeg W₀ W₁ Z hEquiv

private def spineTagToExpr : SpineTag → Expr
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

private def wrapSpineIfInterpolated (tag : SpineTag) (idHint : String)
    (startsPara : Bool) (leadHeading trust : String)
    (reason? : Option String) (inner : Expr) (fallback : Expr → Expr) : TacticM Expr := do
  match reason? with
  | some r =>
      if (r.splitOn "${").length > 1 || (r.splitOn "$[").length > 1 then
        let (tmpl, witness) ← parseAndElabProseInterp r
        return ← mkAppM ``spineNode #[
          spineTagToExpr tag, mkStrLit idHint, mkStrLit tmpl,
          toExpr startsPara, mkStrLit leadHeading, mkStrLit trust, witness, inner
        ]
  | none => pure ()
  return fallback inner

/-- Introduce a `let` binding (`Write`, `Let ... denote`, `Define game/hybrid`, `Consider adversary`)
wrapped in zero-cost Verbose-CC `Expr.mdata` (or kernel `spineNode` when interpolated). -/
private def elabVerboseLet (kind : String) (id : Ident) (tyOpt? : Option (TSyntax `term))
    (valStx : TSyntax `term) (reason? : Option String := none) (role? : Option String := none) :
    TacticM Unit := withMainContext do
  let expectedTy? ← tyOpt?.mapM (fun t => elabType t)
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
  let spineTag := if kind == "define_game" then SpineTag.gameDef else SpineTag.setupEntity
  let hd := if kind == "define_game" then role?.getD "" else ""
  let wrapped ← wrapSpineIfInterpolated spineTag kind (kind == "define_game") hd "kernelFormula"
    reason? inner (fun e => wrapVerboseMData kind e (label? := some id.getId.toString)
      (reason? := reason?) (role? := role?))
  mvarId.assign wrapped
  replaceMainGoal [nextGoal]

/-- Introduce a `have` proposition (`We claim`, `We note`, `Claim`, `Fact`) wrapped in Verbose-CC `mdata`. -/
private def elabVerboseHave (kind : String) (idOpt? : Option Ident) (propStx : TSyntax `term)
    (tacSeq? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (proofTerm? : Option (TSyntax `term))
    (reason? : Option String := none) (role? : Option String := none) : TacticM Unit :=
  withMainContext do
    let prop ← elabType propStx
    let hName ← match idOpt? with
      | some id => pure id.getId
      | none => mkFreshUserName `vccClaim
    let valMVar ← mkFreshExprSyntheticOpaqueMVar prop (Name.mkSimple kind)
    match tacSeq?, proofTerm? with
    | some tacSeq, none =>
        let rem ← runTacticSeqOnGoal valMVar.mvarId! tacSeq
        unless rem.isEmpty do
          throwError "{kind}: proof block left {rem.length} unsolved goal(s)"
    | none, some pt =>
        let val ← Tactic.elabTermEnsuringType pt (some prop)
        valMVar.mvarId!.assign val
    | _, _ => throwError "{kind}: expected tactic block or proof term"
    let val ← instantiateMVars valMVar
    if val.hasSorry then
      throwError "{kind} requires a complete proof without `sorry`"
    let mvarId ← getMainGoal
    let target ← mvarId.getType
    let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
    let afterDefine ← inner.mvarId!.define hName prop val
    let (fv, nextGoal) ← afterDefine.intro hName
    nextGoal.withContext do
      if let some id := idOpt? then
        Term.addLocalVarInfo id (mkFVar fv)
    let lbl? := idOpt?.map (·.getId.toString)
    let wrapped ← wrapSpineIfInterpolated .claimBlock kind (kind == "claim") (role?.getD "")
      "kernelProvedClaim" reason? inner
      (fun e => wrapVerboseMData kind e (label? := lbl?) (reason? := reason?) (role? := role?))
    mvarId.assign wrapped
    replaceMainGoal [nextGoal]

/-- Attach a scoped `Expr.mdata` marker (`proof_overview`, `paragraph`) without altering context or goal. -/
private def elabGoalMarker (kind : String) (label? : Option String := none)
    (reason? : Option String := none) (role? : Option String := none) : TacticM Unit :=
  wrapGoalWithMData kind (label? := label?) (reason? := reason?) (role? := role?) fun g =>
    pure [g]

/-- Wrap `mvarId`'s remaining subgoal proof inside a kernel-transparent `spineNode` while
recording a lightweight `SpineSpanInfo` custom node in `InfoTree` for source navigation. -/
private def wrapGoalWithSpineNode (tag : SpineTag) (idHint text : String)
    (startsPara : Bool) (leadHeading trust : String) (witness : Expr)
    (runInner : MVarId → TacticM (List MVarId)) : TacticM Unit := do
  let mvarId ← getMainGoal
  let stx ← getRef
  mvarId.withContext do
    let target ← mvarId.getType
    let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
    let remaining ← runInner inner.mvarId!
    let tagExpr := spineTagToExpr tag
    let wrapped ← mkAppM ``spineNode #[
      tagExpr, mkStrLit idHint, mkStrLit text,
      toExpr startsPara, mkStrLit leadHeading, mkStrLit trust, witness, inner
    ]
    mvarId.assign wrapped
    _root_.Lean.Elab.pushInfoLeaf (.ofCustomInfo { stx := stx, value := Dynamic.mk (SpineSpanInfo.mk idHint idHint) })
    replaceMainGoal remaining

/-- Reject aliasing a `Prop`, predicate (`→ Prop`), or proof term to an arbitrary formula string. -/
private def checkPropFormulaForgery (kind : String) (val valTy : Expr) (sym : String) : MetaM Unit := do
  let valTyW ← whnf valTy
  if valTyW == Expr.sort .zero then
    throwError "Formula-forgery guard: `{kind}` cannot alias 0-ary `Prop` `{← ppExpr val}` to `{sym}`"
  let isPredOrProof : Bool ←
    if ← isProp valTy then pure true
    else forallTelescopeReducing valTy fun _ body =>
      return (← whnf body) == Expr.sort .zero
  if isPredOrProof && isFormulaForgeryLatex sym then
    throwError "Formula-forgery guard: `{kind}` cannot alias `Prop`/predicate `{← ppExpr val}` to a formula string `{sym}`"

/-- Per-declaration tracker of `(declName?, lastBytePos?, recorded (expr, trimmedSym))`
for duplicate-symbol collision warnings inside a single theorem proof. -/
private initialize proofNotationTrackerRef :
    IO.Ref (Option Name × Option Nat × Array (Expr × String)) ←
  IO.mkRef (none, none, #[])

private def checkAndRecordProofNotation (val : Expr) (sym : String) : TacticM Unit := do
  let declName? ← Term.getDeclName?
  let curPos? := (← getRef).getPos?.map (·.byteIdx)
  let symTrim := sym.trimAscii.toString
  let lctx ← getLCtx
  let (prevDecl?, prevPos?, prevEntries) ← proofNotationTrackerRef.get
  let resetNeeded :=
    declName? != prevDecl? ||
    match curPos?, prevPos? with
    | some cp, some pp => cp ≤ pp
    | _, _ => false
  let activeEntries :=
    if resetNeeded then #[]
    else
      prevEntries.filter fun (prevVal, _) =>
        (Lean.collectFVars {} prevVal).fvarIds.all lctx.contains
  for (prevVal, prevSym) in activeEntries do
    if prevSym == symTrim then
      let sameExpr ← try withTransparency .reducible (Meta.isDefEq prevVal val) catch _ => pure false
      if !sameExpr then
        logWarning m!"Notation collision: symbol '{symTrim}' is mapped to two distinct expressions in the same proof; disambiguate with a distinct symbol or subscript."
        break
  proofNotationTrackerRef.set (declName?, curPos?, activeEntries.push (val, symTrim))

/-- Attach a kernel-transparent `with_notation` binding `spineNotation` directly around `inner`
(plus `MData` for legacy metadata), preserving all downstream steps and rejecting `Prop` forgery. -/
private def elabWithNotation (valStx : TSyntax `term) (sym : String)
    (gloss? : Option String := none) : TacticM Unit := withMainContext do
  let val ← Tactic.elabTerm valStx none
  if val.hasSorry then
    throwError "With notation: term contains `sorry`"
  let valTy ← inferType val
  checkPropFormulaForgery "With notation" val valTy sym
  checkAndRecordProofNotation val sym
  let mvarId ← getMainGoal
  let target ← mvarId.getType
  let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
  let spineWrapped ← mkAppM ``spineNotation #[val, mkStrLit sym, mkStrLit (gloss?.getD ""), inner]
  mvarId.assign (wrapVerboseMData "with_notation" spineWrapped (label? := some sym) (reason? := gloss?))
  replaceMainGoal [inner.mvarId!]

/-- Introduce `let id := val` AND bind paper notation `sym` + optional gloss for both `id` and `val`. -/
private def elabLetDenoteAs (id : Ident) (tyOpt? : Option (TSyntax `term))
    (valStx : TSyntax `term) (sym : String) (gloss? : Option String := none) :
    TacticM Unit := withMainContext do
  let expectedTy? ← tyOpt?.mapM (fun t => elabType t)
  let val ← Tactic.elabTermEnsuringType valStx expectedTy?
  let valTy ← match expectedTy? with
    | some t => pure t
    | none => inferType val
  checkPropFormulaForgery "Let ... denote ... as" val valTy sym
  checkAndRecordProofNotation val sym
  let mvarId ← getMainGoal
  let target ← mvarId.getType
  let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
  let afterDefine ← inner.mvarId!.define id.getId valTy val
  let (fv, nextGoal) ← afterDefine.intro id.getId
  nextGoal.withContext do
    Term.addLocalVarInfo id (mkFVar fv)
  let wrapped ← wrapSpineIfInterpolated .setupEntity "let_denote" false "" "kernelFormula"
    gloss? inner (fun e => wrapVerboseMData "with_notation_let" e
      (label? := some sym) (reason? := gloss?) (role? := some id.getId.toString))
  mvarId.assign wrapped
  replaceMainGoal [nextGoal]

/-- Eliminate synthetic premise `let` / lambda wrappers matching `synthNames` directly inside
an elaborated `Expr` so temporary `_since_p*` / `_vcc_p*` names NEVER leak into `GoalState` or
`ProofGraph`. -/
private partial def elimSynthLetNames (synthNames : Array Name) : Expr → Expr
  | .letE nm ty val body nd =>
      let val' := elimSynthLetNames synthNames val
      if synthNames.contains nm && !val'.hasLooseBVars then
        elimSynthLetNames synthNames (body.instantiate1 val')
      else
        .letE nm (elimSynthLetNames synthNames ty) val' (elimSynthLetNames synthNames body) nd
  | .app (.lam nm dom body bi) arg =>
      let arg' := elimSynthLetNames synthNames arg
      if synthNames.contains nm && !arg'.hasLooseBVars then
        elimSynthLetNames synthNames (body.instantiate1 arg')
      else
        .app (.lam nm (elimSynthLetNames synthNames dom) (elimSynthLetNames synthNames body) bi) arg'
  | .app fn a => .app (elimSynthLetNames synthNames fn) (elimSynthLetNames synthNames a)
  | .lam nm dom body bi =>
      .lam nm (elimSynthLetNames synthNames dom) (elimSynthLetNames synthNames body) bi
  | .forallE nm dom body bi =>
      .forallE nm (elimSynthLetNames synthNames dom) (elimSynthLetNames synthNames body) bi
  | .mdata kv inner => .mdata kv (elimSynthLetNames synthNames inner)
  | .proj s idx inner => .proj s idx (elimSynthLetNames synthNames inner)
  | other => other

/-- Elaborate `premises` onto `goal` cleanly using temporary local names, run explicit tactic or
strictly bounded (20k heartbeat, `solve |`, NO `simp_all`) auto-closer, and return `(rem, synthNames, premExprs)`. -/
private def pushPremisesAndAutoCloseEx (g : MVarId) (premises : Array (TSyntax `term))
    (tacSeq? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) :
    TacticM (List MVarId × Array Name × Array Expr) := do
  let mut curG := g
  let mut synthNames : Array Name := #[]
  let mut premExprs : Array Expr := #[]
  for i in [:premises.size] do
    let pStx := premises[i]!
    let (rem, nm, pVal) ← curG.withContext do
      let p ← Tactic.elabTerm pStx none
      if p.hasSorry then
        throwError "Since: premise contains `sorry`"
      let nm ← mkFreshUserName (Name.mkSimple s!"_since_p{i}")
      -- If `pStx` is a bare local/global ident with unresolved implicit metavariables, do NOT force
      -- an incomplete `define` that poisons `val` or crashes `mkAppM`; resolve bare FVar directly if simple.
      let cleanP? : Option Expr ←
        if p.hasExprMVar && pStx.raw.isIdent then
          pure ((← getLCtx).findFromUserName? pStx.raw.getId |>.map (mkFVar ·.fvarId))
        else pure none
      let premTerm := cleanP?.getD p
      let premTy ← instantiateMVars (← inferType premTerm)
      if premTerm.hasExprMVar || premTy.hasExprMVar then
        pure ([curG], nm, premTerm)
      else
        let afterDef ← curG.define nm premTy premTerm
        let (_, nextG) ← afterDef.intro nm
        pure ([nextG], nm, premTerm)
    synthNames := synthNames.push nm
    premExprs := premExprs.push pVal
    match rem with
    | [g'] => curG := g'
    | other => return (other, synthNames, premExprs)
  let rem ← match tacSeq? with
    | some ts =>
        withBoundedHeartbeatsTactic "Since ... we get" do
          runTacticSeqOnGoal curG ts
    | none =>
        runBoundedAutoCloser curG premises[0]? "Since ... we get"
  return (rem, synthNames, premExprs)

/-- Clean goal-closing premise pusher (`Since ... we conclude` / `We conclude ... from`) that
runs the bounded auto-closer and strips `_since_p{i}` let-bindings when the goal closes. -/
private def pushPremisesAndAutoClose (g : MVarId) (premises : Array (TSyntax `term))
    (tacSeq? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM (List MVarId) := do
  let ty ← g.getType
  let tag ← g.getTag
  let valMVar ← mkFreshExprSyntheticOpaqueMVar ty tag
  let (rem, synthNames, _) ← pushPremisesAndAutoCloseEx valMVar.mvarId! premises tacSeq?
  if rem.isEmpty then
    let rawVal ← instantiateMVars valMVar
    let cleanVal := elimSynthLetNames synthNames rawVal
    g.assign cleanVal
    return []
  throwError "Since/We conclude: left {rem.length} unsolved goal(s); append `by ...` to discharge remaining subgoals"

private def runSinceConclude (tag : SpineTag) (label : String)
    (premises : Array (TSyntax `term)) (reason? : Option (TSyntax `str))
    (tacSeq? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  let (tmpl, witness) ← match reason? with
    | some r => parseAndElabProseInterp r.getString
    | none => pure ("", mkConst ``spineNil)
  wrapGoalWithSpineNode tag label tmpl false "" "kernelProvedClaim" witness fun g =>
    pushPremisesAndAutoClose g premises tacSeq?

/-- Forward step `Since hs we get [id :] P [by ...]` wrapped in kernel-transparent `spineNode`
and zero `_vcc_p0`/`_since_p0` binder leakage. -/
private def elabSinceGet (premises : Array (TSyntax `term)) (idOpt? : Option Ident)
    (propStx : TSyntax `term) (tacSeq? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) :
    TacticM Unit := withMainContext do
  let prop ← elabType propStx
  let hName ← match idOpt? with
    | some id => pure id.getId
    | none => mkFreshUserName `vccSince
  let valMVar ← mkFreshExprSyntheticOpaqueMVar prop `since
  let (rem, synthNames, premExprs) ← pushPremisesAndAutoCloseEx valMVar.mvarId! premises tacSeq?
  unless rem.isEmpty do
    throwError "Since ... we get: left {rem.length} unsolved goal(s); append `by ...` to discharge remaining subgoals"
  let rawVal ← instantiateMVars valMVar
  if rawVal.hasSorry then
    throwError "Since ... we get requires a complete proof without `sorry`"
  let val := elimSynthLetNames synthNames rawVal
  let mvarId ← getMainGoal
  let target ← mvarId.getType
  let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
  let afterDefine ← inner.mvarId!.define hName prop val
  let (fv, nextGoal) ← afterDefine.intro hName
  nextGoal.withContext do
    if let some id := idOpt? then
      Term.addLocalVarInfo id (mkFVar fv)
  let witness ← packSpineExprs premExprs
  let wrapped ← mkAppM ``spineNode #[
    mkConst ``SpineTag.sinceStep, mkStrLit (idOpt?.map (·.getId.toString) |>.getD "since"),
    mkStrLit "", toExpr false, mkStrLit "", mkStrLit "kernelProvedClaim", witness, inner
  ]
  mvarId.assign wrapped
  replaceMainGoal [nextGoal]

/-! ## Family 1: Section / Local Shorthands -/

/-- Introduce a theorem-local shorthand definition (`Write U := ...`) recorded in the proof trace. -/
scoped syntax (name := vccWrite) "Write " ident (" : " term)? " := " term : tactic

elab_rules : tactic
  | `(tactic| Write $id:ident $[: $ty]? := $val) =>
      elabVerboseLet "write" id ty val

/-! ## Family 2: Constructions, Substitutions, & Serial/Parallel Composition -/

/-- Close a construction goal using a witness equality, distance bound, or pointwise proof. -/
scoped syntax (name := vccConstructUsing) "Construct_using " term : tactic

/-- Explicit constructive claim form (`Construct S from R via π using h`). -/
scoped syntax (name := vccConstructFull)
  "Construct " term " from " term " via " term " using " term : tactic

elab_rules : tactic
  | `(tactic| Construct_using $h) =>
      wrapGoalWithMData "construct" (label? := syntaxShortLabel? h) fun g => do
        runTacticOnGoal g (← `(tactic| cc_construct using $h))
  | `(tactic| Construct $_tgt from $_src via $_conv using $h) =>
      wrapGoalWithMData "construct" (label? := syntaxShortLabel? h) fun g => do
        runTacticOnGoal g (← `(tactic| cc_construct using $h))

/-- Replace a converter inside a construction using an explicit converter equality. -/
scoped syntax (name := vccReplaceConverterIn)
  "Replace_converter_in " term " using " term : tactic

/-- Prove attachment or construction equivalence directly from a converter equality. -/
scoped syntax (name := vccReplaceConverterUsing)
  "Replace_converter_using " term : tactic

elab_rules : tactic
  | `(tactic| Replace_converter_in $constr using $hEq) =>
      wrapGoalWithMData "replace_converter" fun g => do
        runTacticOnGoal g (← `(tactic| cc_transport $constr using $hEq))
  | `(tactic| Replace_converter_using $hEq) =>
      wrapGoalWithMData "replace_converter" fun g => do
        runTacticOnGoal g (← `(tactic| cc_transport using $hEq))

/-- Compose two construction steps sequentially (`inner` then `outer`). -/
scoped syntax (name := vccSeqComp)
  "By_sequential_composition " ("of ")? term " and " term : tactic

elab_rules : tactic
  | `(tactic| By_sequential_composition $[of]? $h1 and $h2) =>
      wrapGoalWithMData "seq_comp" fun g => do
        runTacticOnGoal g (← `(tactic| cc_compose $h1, $h2))

/-- Compose two construction steps in ordered parallel (`left` beside `right`). -/
scoped syntax (name := vccParComp)
  "By_parallel_composition " ("of ")? term " and " term : tactic

elab_rules : tactic
  | `(tactic| By_parallel_composition $[of]? $hL and $hR) =>
      wrapGoalWithMData "par_comp" fun g => do
        runTacticOnGoal g (← `(tactic| cc_parallel $hL, $hR))

/-- Lift a construction by making a fixed resource `T` available in parallel on the right. -/
scoped syntax (name := vccContextRight)
  "By_context_insensitivity_right " term " using " term : tactic

/-- Lift a construction by making a fixed resource `T` available in parallel on the left. -/
scoped syntax (name := vccContextLeft)
  "By_context_insensitivity_left " term " using " term : tactic

elab_rules : tactic
  | `(tactic| By_context_insensitivity_right $ctxSpec using $hConstr) =>
      wrapGoalWithMData "context_right" (label? := syntaxShortLabel? ctxSpec) fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | cc_context_left $ctxSpec using $hConstr
            | cc_context_left (Singleton.singleton $ctxSpec) using $hConstr
            | (try simp only [← ConstructiveCryptography.CryptographicAlgebra.Specification.parallel_singleton]
               try rw [← CategoryTheory.MonoidalCategory.tensorHom_id]
               first
                 | cc_context_left $ctxSpec using $hConstr
                 | cc_context_left (Singleton.singleton $ctxSpec) using $hConstr)))
  | `(tactic| By_context_insensitivity_left $ctxSpec using $hConstr) =>
      wrapGoalWithMData "context_left" (label? := syntaxShortLabel? ctxSpec) fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | cc_context_right $ctxSpec using $hConstr
            | cc_context_right (Singleton.singleton $ctxSpec) using $hConstr
            | (try simp only [← ConstructiveCryptography.CryptographicAlgebra.Specification.parallel_singleton]
               try rw [← CategoryTheory.MonoidalCategory.id_tensorHom]
               first
                 | cc_context_right $ctxSpec using $hConstr
                 | cc_context_right (Singleton.singleton $ctxSpec) using $hConstr)))

/-- Pull a compatible relaxation to the outside through an outer serial construction. -/
scoped syntax (name := vccPullRelax)
  "Pull_relaxation_through " term " using " term " from " term : tactic

elab_rules : tactic
  | `(tactic| Pull_relaxation_through $hOuter using $hCompat from $hInner) =>
      wrapGoalWithMData "pull_relax" fun g => do
        runTacticOnGoal g (← `(tactic| cc_relax using $hInner, $hOuter with $hCompat))

/-- Substitute inside a converter context, absorbing the context into the distinguisher. -/
scoped syntax (name := vccSubstitutePreserving)
  "Substitute_in_context " term " through " term " preserving_closure " term : tactic

/-- Substitute an abstract `SubstitutionRelation` through a converter context. -/
scoped syntax (name := vccSubstituteRel)
  "Substitute_in_context " term " through " term " using " term : tactic

elab_rules : tactic
  | `(tactic| Substitute_in_context $hStep through $conv preserving_closure $hClosed) =>
      wrapGoalWithMData "substitute" (label? := syntaxShortLabel? conv) fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | exact ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_context
                $conv $hClosed $hStep
            | exact ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_attach
                $conv $hClosed $hStep
            | exact SystemAlgebra.TypedConverter.substitutesWithin_attach
                $conv $hClosed $hStep))
  | `(tactic| Substitute_in_context $rel through $conv using $premise) =>
      wrapGoalWithMData "substitute" (label? := syntaxShortLabel? conv) fun g => do
        runTacticOnGoal g (← `(tactic| cc_substitute $rel through $conv using $premise))

/-! ## Family 3: Hybrid Chains & Triangle Inequality (`cc_calc`) -/

/-- Introduce a named intermediate hybrid system (`Introduce_hybrid H₁ := ...`). -/
scoped syntax (name := vccHybrid) "Introduce_hybrid " ident (" : " term)? " := " term : tactic

elab_rules : tactic
  | `(tactic| Introduce_hybrid $id:ident $[: $ty]? := $val) =>
      elabVerboseLet "hybrid" id ty val

/-- Apply the triangle inequality via an intermediate system `M`, opening both leg subgoals. -/
scoped syntax (name := vccTriangle) "By_triangle_inequality_via " term : tactic

elab_rules : tactic
  | `(tactic| By_triangle_inequality_via $mid) =>
      wrapGoalWithMData "triangle" (label? := syntaxShortLabel? mid) fun g => do
        runTacticOnGoal g (← `(tactic| cc_triangle via $mid))

/-- Close a converter-attachment or parallel-composition non-expansion distance bound. -/
scoped syntax (name := vccNonexpand) "By_non_expansion" : tactic

elab_rules : tactic
  | `(tactic| By_non_expansion) =>
      wrapGoalWithMData "nonexpand" fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | cc_nonexpand
            | (dsimp +zetaDelta only; cc_nonexpand)
            | refine (ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _).trans ?_
            | (dsimp +zetaDelta only
               refine (ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _).trans ?_)
            | refine (ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le _ _ _).trans ?_
            | refine (ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le _ _ _).trans ?_))

/-- Annotate a single `cc_calc` step proof term with a human-readable Maurer justification. -/
scoped elab (name := vccCalcStepTerm) "because_of " reason:str " => " proof:term : term <= expectedType? => do
  let val ← Term.elabTerm proof expectedType?
  return wrapVerboseMData "cc_calc_step" val (reason? := some reason.getString)

/-- Tactic-mode `cc_calc` step wrapper attaching a Maurer justification (`by By_hybrid_step "..." => ...`). -/
scoped syntax (name := vccCalcStepTac) "By_hybrid_step " str " => " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| By_hybrid_step $reason:str => $tacSeq) =>
      wrapGoalWithMData "cc_calc_step" (reason? := some reason.getString) fun g => do
        let rem ← runTacticSeqOnGoal g tacSeq
        unless rem.isEmpty do
          throwError "By_hybrid_step left {rem.length} unsolved goal(s)"
        pure rem

/-- Wrap a `cc_calc` or multi-step hybrid chain block with explicit Verbose-CC trace metadata. -/
scoped syntax (name := vccHybridChainBlock) "By_hybrid_chain " "{" tacticSeq "}" : tactic

elab_rules : tactic
  | `(tactic| By_hybrid_chain { $tacSeq }) =>
      wrapGoalWithMData "hybrid_chain" fun g => do
        runTacticSeqOnGoal g tacSeq

/-! ## Family 4: Simulators & Indifferentiability -/

/-- Exhibit an explicit simulator `σ` attached to the adversarial interface. -/
scoped syntax (name := vccExhibitSim)
  "Exhibit_simulator " term (" for_interface " term)? : tactic

elab_rules : tactic
  | `(tactic| Exhibit_simulator $sim $[for_interface $iface]?) =>
      let simLabel := syntaxShortLabel? sim.raw
      let ifaceLabel := iface.bind (fun t => syntaxShortLabel? t.raw)
      wrapGoalWithMData "exhibit_simulator" (label? := simLabel) (role? := ifaceLabel) fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | refine ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage
                $sim ?_ ?_
            | refine Commons.Indifferentiability.constructs_of_simulator
                $sim ?_ ?_
            | refine ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_star_of_simulator
                $sim ?_ ?_
            | refine ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_star_of_simulator
                $sim ?_ ?_))

/-- Compose two simulator-target constructions serially via composition-order invariance. -/
scoped syntax (name := vccComposeSims)
  "Compose_simulators " term " and " term (" using_commutation " term)? : tactic

elab_rules : tactic
  | `(tactic| Compose_simulators $hInner and $hOuter $[using_commutation $hComm]?) =>
      wrapGoalWithMData "compose_simulators" fun g => do
        match hComm with
        | some hc =>
            runTacticOnGoal g (← `(tactic| cc_compose_simulators $hInner, $hOuter using $hc))
        | none =>
            runTacticOnGoal g (← `(tactic|
              first
                | exact Commons.Indifferentiability.compose $hInner $hOuter
                | exact ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage
                    $hInner $hOuter
                | exact ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage_whiskerRight
                    $hInner $hOuter
                | cc_compose_simulators $hInner, $hOuter using rfl))

/-! ## Family 5: Games, MBOs, & Extended H-Coefficients -/

/-- Pass to the underlying system `G⁻` obtained by ignoring the MBO (via optional `visible` identity). -/
scoped syntax (name := vccIgnoreMBO) "Ignore_MBO_of " term (" via " term)? : tactic

elab_rules : tactic
  | `(tactic| Ignore_MBO_of $game $[via $hVis]?) =>
      wrapGoalWithMData "ignore_mbo" (label? := syntaxShortLabel? game) fun g => do
        match hVis with
        | some hv =>
            runTacticOnGoal g (← `(tactic| rw [← $hv]))
        | none =>
            runTacticOnGoal g (← `(tactic|
              dsimp only [ConstructiveCryptography.DistinctionGames.visible,
                SystemAlgebra.TypedGame.visible, SystemAlgebra.RandomSystem.visible]))

/-- Apply the Fundamental Lemma of Game Playing (`G ≡_g H`) to bound distinguishing advantage or
distance of underlying systems by the game-winning probability. -/
scoped syntax (name := vccFundamentalGame)
  "By_fundamental_lemma_of_game_playing " term : tactic

elab_rules : tactic
  | `(tactic| By_fundamental_lemma_of_game_playing $hGameEq) =>
      wrapGoalWithMData "fundamental_game" fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | exact SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent
                _ _ _ _ $hGameEq
            | refine SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent
                _ ?_ ?_ ?_ $hGameEq
            | exact SystemAlgebra.RandomSystem.GameEquivalent.abs_decisionProbability_sub_le
                _ _ _ $hGameEq _ _ _
            | refine SystemAlgebra.RandomSystem.GameEquivalent.abs_decisionProbability_sub_le
                _ ?_ ?_ ?_ $hGameEq _ _ _
            | refine SystemAlgebra.RandomSystem.GameEquivalent.transcriptDistance_visible_le
                ?_ $hGameEq ?_ ?_ ?_
            | exact SystemAlgebra.RandomSystem.GameEquivalent.winProbability_eq
                _ _ _ _ $hGameEq))

/-- Apply conditional equivalence (`G |≡ T`) to bound distinguishing advantage or distance. -/
scoped syntax (name := vccCondEquiv)
  "By_conditional_equivalence " term (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| By_conditional_equivalence $hCondEq $[using $hSolver]?) =>
      wrapGoalWithMData "cond_equiv" fun g => do
        match hSolver with
        | some hs =>
            runTacticOnGoal g (← `(tactic|
              first
                | exact ConstructiveCryptography.DistinctionGames.advantage_le_win $hCondEq $hs
                | refine (ConstructiveCryptography.DistinctionGames.advantage_le_win $hCondEq $hs).trans ?_
                | exact SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability _ _ _ _ $hCondEq))
        | none =>
            runTacticOnGoal g (← `(tactic|
              first
                | refine (ConstructiveCryptography.DistinctionGames.advantage_le_win $hCondEq (by assumption)).trans ?_
                | exact ConstructiveCryptography.DistinctionGames.advantage_le_win $hCondEq (by assumption)
                | refine SystemAlgebra.Interface.dist_visible_le $hCondEq ?_
                | refine SystemAlgebra.Interface.game_dist_le ?_ $hCondEq ?_
                | exact SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability _ _ _ _ $hCondEq
                | refine SystemAlgebra.RandomSystem.transcriptDistance_visible_le_of_unsetProbability
                    _ _ _ $hCondEq ?_))

/-- Apply the revealed-transcript Extended H-Technique (`HCoefficient.ofGoodBad`), dropping the
ideal reveal probability law, good-transcript ratio bound, and bad-transcript mass bound to
ordinary Lean tactics. -/
scoped syntax (name := vccExtendedHCoeff)
  "By_extended_H_technique "
    "mixing_real " term " over " term " using " term
    " revealing " term " and " term
    " with_bad_transcripts " term " bound_by " term
    " with_good_ratio_loss " term : tactic

/-- Apply a pre-built `HCoefficient` witness to bound distinguishing advantage. -/
scoped syntax (name := vccExtendedHCoeffUsing)
  "By_extended_H_technique_using " term : tactic

elab_rules : tactic
  | `(tactic| By_extended_H_technique
        mixing_real $realF over $sampleP using $hMix
        revealing $realRev and $idealRev
        with_bad_transcripts $badPred bound_by $eps2
        with_good_ratio_loss $eps1) =>
      wrapGoalWithMData "extended_h_coeff" fun g => do
        runTacticOnGoal g (← `(tactic|
          (classical
           try rw [SystemAlgebra.Interface.cc_distance_eq]
           refine (SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le
             (SystemAlgebra.RandomSystem.HCoefficient.ofGoodBad
               $sampleP $realF $hMix ?_ ?_ $realRev $idealRev ?_ $badPred
               (ε₁ := $eps1) (ε₂ := $eps2) ?_ ?_ ?_) ?_).trans ?_
           all_goals
             try first
               | assumption
               | exact Subtype.property _
               | exact fun _ => by assumption
               | exact fun _ => Subtype.property _
               | (positivity; done)
               | (norm_num; done)
               | (simp only [zero_add, add_zero, ENNReal.ofReal_coe_nnreal]; rfl)
               | (simp only [zero_add, add_zero, ENNReal.ofReal_coe_nnreal]; exact le_rfl)
               | (rw [← ENNReal.ofReal_coe_nnreal]
                  simp only [zero_add, add_zero]
                  apply ENNReal.ofReal_le_ofReal
                  norm_num
                  done)
               | exact le_rfl)))
  | `(tactic| By_extended_H_technique_using $w) =>
      wrapGoalWithMData "extended_h_coeff" fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | exact SystemAlgebra.Interface.distance_le_of_hCoefficient $w
            | exact SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le_nnreal $w _
            | exact SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le $w _))

/-! ## Family 6: Distinguisher Constructions, Tightness Sandwiches, & Lower Bounds -/

/-- Exhibit an explicit compatible distinguisher `D` to reduce a distance lower bound `lb ≤ Δ R S`
to lower-bounding `D`'s distinguishing advantage. -/
scoped syntax (name := vccExhibitDist)
  "Exhibit_distinguisher " term (" admissible_by " term)? : tactic

elab_rules : tactic
  | `(tactic| Exhibit_distinguisher $dist $[admissible_by $hAdm]?) =>
      wrapGoalWithMData "exhibit_distinguisher" (label? := syntaxShortLabel? dist) fun g => do
        match hAdm with
        | some ha =>
            runTacticOnGoal g (← `(tactic|
              first
                | refine le_trans ?_ (by
                    rw [ConstructiveCryptography.CompatibleDistinguisherClass.edist_eq]
                    exact ConstructiveCryptography.le_advantageDistance $ha _ _)
                | (rw [SystemAlgebra.Interface.cc_distance_eq]
                   refine le_trans ?_
                     (SystemAlgebra.Domain.DistinguisherBehavior.advantage_le_transcriptDistance $dist _ _))
                | (rw [SystemAlgebra.Interface.cc_distance_eq]
                   refine le_trans ?_
                     (SystemAlgebra.Domain.Distinguisher.advantage_le_transcriptDistance $dist
                       (Subtype.property _) (Subtype.property _)))))
        | none =>
            runTacticOnGoal g (← `(tactic|
              first
                | (rw [SystemAlgebra.Interface.cc_distance_eq]
                   refine le_trans ?_
                     (SystemAlgebra.Domain.DistinguisherBehavior.advantage_le_transcriptDistance $dist _ _))
                | refine le_trans ?_
                    (SystemAlgebra.Domain.DistinguisherBehavior.advantage_le_transcriptDistance $dist _ _)
                | (rw [SystemAlgebra.Interface.cc_distance_eq]
                   refine le_trans ?_
                     (SystemAlgebra.Domain.Distinguisher.advantage_le_transcriptDistance $dist
                       (Subtype.property _) (Subtype.property _)))
                | refine le_trans ?_
                    (SystemAlgebra.Domain.Distinguisher.advantage_le_transcriptDistance $dist
                      (Subtype.property _) (Subtype.property _))))

/-- Bound `ε₀ ≤ D.advantage R S` from explicit decision probability bounds on `R` and `S`. -/
scoped syntax (name := vccLowerBoundAdv)
  "Lower_bound_advantage_of " term " via " term " and " term : tactic

elab_rules : tactic
  | `(tactic| Lower_bound_advantage_of $dist via $hReal and $hIdeal) =>
      wrapGoalWithMData "lower_bound_adv" (label? := syntaxShortLabel? dist) fun g => do
        runTacticOnGoal g (← `(tactic|
          (dsimp only [SystemAlgebra.Domain.DistinguisherBehavior.advantage,
             SystemAlgebra.Domain.Distinguisher.advantage,
             ConstructiveCryptography.Distinguishers.advantage]
           try rw [← ENNReal.ofReal_coe_nnreal]
           try rw [← ENNReal.ofReal_ofNat]
           first
             | (apply ENNReal.ofReal_le_ofReal
                have hr := $hReal
                have hi := $hIdeal
                linarith [le_abs_self (($dist).1 _ - ($dist).1 _),
                          neg_le_abs (($dist).1 _ - ($dist).1 _)])
             | (apply ENNReal.ofReal_le_ofReal
                have hr := $hReal
                have hi := $hIdeal
                linarith [le_abs_self (($dist).probability _ - ($dist).probability _),
                          neg_le_abs (($dist).probability _ - ($dist).probability _)])
             | (apply ENNReal.ofReal_le_ofReal
                have hr := $hReal
                have hi := $hIdeal
                norm_num [hr, hi])
             | skip)))

/-- Prove a tightness sandwich `lb ≤ Δ R S ∧ Δ R S ≤ ub` with explicit lower and upper blocks. -/
scoped syntax (name := vccTightnessBlock)
  "Tightness_sandwich"
    " lower_bound " "{" tacticSeq "}"
    " upper_bound " "{" tacticSeq "}" : tactic

/-- Prove a tightness sandwich from explicit upper- and lower-bound proof terms. -/
scoped syntax (name := vccTightnessTerms)
  "Tightness_sandwich " "upper " term " lower " term : tactic

/-- Split a tightness sandwich conjunction into its two subgoals (`lower` and `upper`). -/
scoped syntax (name := vccTightnessSplit) "Tightness_sandwich" : tactic

elab_rules : tactic
  | `(tactic| Tightness_sandwich lower_bound { $lowTacs } upper_bound { $upTacs }) =>
      wrapGoalWithMData "tightness_sandwich" (role? := some "lower_upper") fun g => do
        let rem ← runTacticOnGoal g (← `(tactic| constructor))
        match rem with
        | [gLow, gUp] =>
            let r1 ← runTacticSeqOnGoal gLow lowTacs
            let r2 ← runTacticSeqOnGoal gUp upTacs
            return r1 ++ r2
        | other => return other
  | `(tactic| Tightness_sandwich upper $hUp lower $hLow) =>
      wrapGoalWithMData "tightness_sandwich" (role? := some "upper_lower") fun g => do
        runTacticOnGoal g (← `(tactic| exact And.intro $hUp $hLow))
  | `(tactic| Tightness_sandwich) =>
      wrapGoalWithMData "tightness_sandwich" (role? := some "lower_upper") fun g => do
        runTacticOnGoal g (← `(tactic| constructor))

/-! ## Family 7: Discourse Transitions, Backward Reductions (`suffices`), & Compression -/

/-- State and prove an intermediate claim (`Claim h : P by ...` or `from ...`). -/
scoped syntax (name := vccClaimBy) "Claim " ident " : " term " by " tacticSeq : tactic
scoped syntax (name := vccClaimFrom) "Claim " ident " : " term " from " term : tactic

/-- State and prove a supporting fact (`Fact h : P by ...` or `from ...`). -/
scoped syntax (name := vccFactBy) "Fact " ident " : " term " by " tacticSeq : tactic
scoped syntax (name := vccFactFrom) "Fact " ident " : " term " from " term : tactic

elab_rules : tactic
  | `(tactic| Claim $id:ident : $prop by $tacSeq) =>
      elabVerboseHave "claim" (some id) prop (some tacSeq) none
  | `(tactic| Claim $id:ident : $prop from $pt) =>
      elabVerboseHave "claim" (some id) prop none (some pt)
  | `(tactic| Fact $id:ident : $prop by $tacSeq) =>
      elabVerboseHave "fact" (some id) prop (some tacSeq) none
  | `(tactic| Fact $id:ident : $prop from $pt) =>
      elabVerboseHave "fact" (some id) prop none (some pt)

/-- Backward reduction (`It_suffices_to_show [h :] P (by | because) tacSeq`), preserving both the
reduction justification (under `⊕`) and the subsequent proof of `P` in Maurer's voice. -/
scoped syntax (name := vccSufficesBy)
  "It_suffices_to_show " (ident " : ")? term " by " tacticSeq : tactic
scoped syntax (name := vccSufficesBecause)
  "It_suffices_to_show " (ident " : ")? term " because " tacticSeq : tactic

/-- Backward reduction with an explicit reader-facing justification string. -/
scoped syntax (name := vccSufficesReason)
  "It_suffices_to_show " (ident " : ")? term " because " str " via " tacticSeq : tactic

private def elabSuffices (idOpt? : Option Ident) (propStx : TSyntax `term)
    (reason? : Option String) (tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM Unit :=
  withMainContext do
    let mvarId ← getMainGoal
    let target ← mvarId.getType
    let prop ← elabType propStx
    let hName := match idOpt? with | some id => id.getId | none => `this
    let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
    let pGoal ← mkFreshExprSyntheticOpaqueMVar prop (Name.mkSimple "sufficesGoal")
    -- `MVarId.define` produces `.letE h prop ?pGoal ?redGoal`, which Lean never beta-reduces
    let afterDef ← inner.mvarId!.define hName prop pGoal
    let (fv, redGoal) ← afterDef.intro hName
    redGoal.withContext do
      if let some id := idOpt? then
        Term.addLocalVarInfo id (mkFVar fv)
    let remRed ← runTacticSeqOnGoal redGoal tacSeq
    let mut leftover : List MVarId := []
    for rg in remRed do
      let saved ← getGoals
      setGoals [rg]
      try
        rg.assign (mkFVar fv)
        setGoals saved
      catch _ =>
        setGoals saved
        leftover := leftover ++ [rg]
    let wrapped ← wrapSpineIfInterpolated .sufficesStep "suffices" false "" "kernelProvedClaim"
      reason? inner (fun e => wrapVerboseMData "suffices" e (reason? := reason?))
    mvarId.assign wrapped
    replaceMainGoal (pGoal.mvarId! :: leftover)

elab_rules : tactic
  | `(tactic| It_suffices_to_show $[$id?:ident :]? $prop by $tacSeq) =>
      elabSuffices id? prop none tacSeq
  | `(tactic| It_suffices_to_show $[$id?:ident :]? $prop because $tacSeq) =>
      elabSuffices id? prop none tacSeq
  | `(tactic| It_suffices_to_show $[$id?:ident :]? $prop because $r:str via $tacSeq) =>
      elabSuffices id? prop (some r.getString) tacSeq

/-- Explicit Paper-mode compression receipt for routine CC algebra & normalization, expandable in
Auditor mode (`By_CC_routine { ... }` or standalone `By_CC_routine`). -/
private def elabCCRoutineBlock (reason? : Option String)
    (tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM Unit :=
  withMainContext do
    if let some r := reason? then
      if (r.splitOn "${").length > 1 || (r.splitOn "$[").length > 1 then
        let (tmpl, witness) ← parseAndElabProseInterp r
        let mvarId ← getMainGoal
        let target ← mvarId.getType
        let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
        let remaining ← runTacticSeqOnGoal inner.mvarId! tacSeq
        let attached := mkApp (mkLambda `_ .default (mkConst ``Unit) inner) witness
        mvarId.assign (wrapVerboseMData "cc_routine" attached (reason? := some tmpl))
        replaceMainGoal remaining
        return
    wrapGoalWithMData "cc_routine" (reason? := reason?) fun g =>
      runTacticSeqOnGoal g tacSeq

scoped syntax (name := vccRoutineBlock)
  "By_CC_routine " (str)? "{" tacticSeq "}" : tactic

scoped syntax (name := vccRoutineAuto) "By_CC_routine" : tactic

elab_rules : tactic
  | `(tactic| By_CC_routine $[$reason?:str]? { $tacSeq }) =>
      elabCCRoutineBlock (reason?.map (·.getString)) tacSeq
  | `(tactic| By_CC_routine) =>
      wrapGoalWithMData "cc_routine" fun g => do
        runTacticOnGoal g (← `(tactic|
          ((try cc_normalize)
           first
             | (solve | rfl)
             | (solve | assumption)
             | (solve | cc_routine)
             | (solve | (simp only [ConstructiveCryptography.cc_normalization]; first | assumption | rfl)))))

/-- Synthesis transition (`Combining { ... }`), closing the goal from checked premises. -/
scoped syntax (name := vccCombiningBlock) "Combining " "{" tacticSeq "}" : tactic
scoped syntax (name := vccCombiningExact) "Combining " term " and " term " yields " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| Combining { $tacSeq }) =>
      wrapGoalWithMData "combine" fun g => do
        runTacticSeqOnGoal g tacSeq
  | `(tactic| Combining $h1 and $h2 yields $tacSeq) =>
      wrapGoalWithMData "combine" fun g => do
        let rem ← runTacticOnGoal g (← `(tactic|
          (have _ := $h1; have _ := $h2)))
        match rem with
        | [g'] => runTacticSeqOnGoal g' tacSeq
        | other => return other

/-! ## Family 8: Massot Spaced-English Paper Surface (`#37`), Scoped Notation & Difference Lemma -/

/-- Optional reader-facing gloss clause (`where "..."` or `explaining "..."`) attached to a
hybrid, game, adversary, claim, notation binding, or Difference Lemma step. -/
declare_syntax_cat vccGlossClause
syntax " where " str : vccGlossClause
syntax " explaining " str : vccGlossClause

private def extractGloss? (g? : Option (TSyntax `vccGlossClause)) : Option String :=
  g?.bind fun stx => stx.raw[1].isStrLit?

/-- Introductory proof roadmap (`Proof overview "prose..."`) opening the first paragraph and breaking
cleanly into the proof body. -/
scoped syntax (name := vccProofOverview) "Proof" &"overview" str : tactic

/-- Insert a clean Boneh–Shoup paragraph break (`New paragraph` or `New paragraph "Game 0."`). -/
scoped syntax (name := vccNewParagraph) "New" &"paragraph" (str)? : tactic

/-- Wrap a sub-block in its own proof paragraph (`Paragraph "Game 0." { ... }` or `Paragraph "..."`). -/
scoped syntax (name := vccParagraphBlock) "Paragraph" (str)? "{" tacticSeq "}" : tactic
scoped syntax (name := vccParagraphStr) "Paragraph" str : tactic

/-- Scoped theorem-and-proof paper notation (`With notation e as "\\mathcal{E}" [explaining "..."]`). -/
scoped syntax (name := vccWithNotation)
  "With" &"notation" term " as " str (vccGlossClause)? : tactic

/-- Local definition optionally carrying scoped paper notation and a reader gloss
(`Let x denote e [as "\\mathcal{E}"] [where/explaining "..."]`). -/
scoped syntax (name := vccLetDenote)
  "Let " ident (" : " term)? &"denote" term (" as " str)? (vccGlossClause)? : tactic

/-- Scoped explicit `With role x as "role"` override (Level 1 in 5-level lattice, embedded in kernel). -/
scoped syntax (name := vccWithRole)
  "With" &"role" ident " as " str : tactic

/-- Depth-1 isolated CC automated leaf inside a Spine proof. -/
scoped syntax (name := vccCCLeaf)
  "With" &"cc_leaf" (str)? "{" tacticSeq "}" : tactic

/-- Structured inline algorithm, hybrid, reduction, attack-game, or distinguisher pseudocode box
with live `${expr}` / `$[prop]` interpolation inside every line. -/
scoped syntax (name := vccPresentPseudocode)
  "Present" &"pseudocode" str str str : tactic

/-- Introduce a Boneh–Shoup security game with automatic `Game k.` paragraph heading and hover card. -/
scoped syntax (name := vccDefineGame)
  "Define" &"game" ident (" : " term)? " := " term (" titled " str)? (vccGlossClause)? : tactic

/-- Introduce an intermediate hybrid system with optional reader gloss. -/
scoped syntax (name := vccDefineHybrid)
  "Define" &"hybrid" ident (" : " term)? " := " term (vccGlossClause)? : tactic

/-- Construct a reduction adversary/distinguisher with reader gloss and hover inspector. -/
scoped syntax (name := vccConsiderAdv)
  "Consider" &"adversary" ident (" : " term)? " := " term (vccGlossClause)? : tactic

elab_rules : tactic
  | `(tactic| Proof overview $txt:str) => do
      let (tmpl, witness) ← parseAndElabProseInterp txt.getString
      if witness.isConstOf ``spineNil then
        elabGoalMarker "proof_overview" (reason? := some txt.getString)
      else
        wrapGoalWithSpineNode .overview "overview" tmpl true "" "intuitionGloss" witness fun g => pure [g]
  | `(tactic| New paragraph $[$head?:str]?) =>
      elabGoalMarker "paragraph" (reason? := head?.map (·.getString))
  | `(tactic| Paragraph $[$head?:str]? { $tacSeq }) =>
      wrapGoalWithMData "paragraph" (reason? := head?.map (·.getString)) fun g =>
        runTacticSeqOnGoal g tacSeq
  | `(tactic| Paragraph $head:str) =>
      elabGoalMarker "paragraph" (reason? := some head.getString)
  | `(tactic| With role $x:ident as $r:str) => withMainContext do
      let val ← Tactic.elabTerm x none
      let mvarId ← getMainGoal
      let inner ← mkFreshExprSyntheticOpaqueMVar (← mvarId.getType) (← mvarId.getTag)
      let sp ← mkAppM ``spineRole #[val, mkStrLit r.getString, inner]
      mvarId.assign (wrapVerboseMData "with_role" sp (label? := some x.getId.toString) (reason? := some r.getString))
      replaceMainGoal [inner.mvarId!]
  | `(tactic| With cc_leaf $[$r?:str]? { $tacSeq }) => do
      let (tmpl, witness) ← match r? with
        | some r => parseAndElabProseInterp r.getString
        | none => pure ("", mkConst ``spineNil)
      wrapGoalWithSpineNode .ccSpineLeaf "cc-leaf" tmpl false "" "kernelProvedClaim" witness fun g =>
        runTacticSeqOnGoal g tacSeq
  | `(tactic| Present pseudocode $kind:str $title:str $body:str) => do
      let k := kind.getString.trimAscii.toString
      let validBoxKinds : List String := ["attackGame", "hybrid", "reduction", "distinguisher", "algorithm"]
      unless validBoxKinds.contains k do
        let allowed := String.intercalate ", " validBoxKinds
        throwError "Unknown pseudocode box kind `{k}`; expected one of: {allowed}"
      let (tmpl, witness) ← parseAndElabProseInterp body.getString
      wrapGoalWithSpineNode .pseudocodeBox title.getString tmpl true k "kernelFormula" witness
        fun g => pure [g]
  | `(tactic| With notation $e as $sym:str $[$g?:vccGlossClause]?) =>
      elabWithNotation e sym.getString (extractGloss? g?)
  | `(tactic| Let $id:ident $[: $ty]? denote $val $[as $sym?]? $[$g?:vccGlossClause]?) =>
      let gloss? := extractGloss? g?
      match sym? with
      | some sym => elabLetDenoteAs id ty val sym.getString gloss?
      | none => elabVerboseLet "write" id ty val gloss?
  | `(tactic| Define game $id:ident $[: $ty]? := $val $[titled $ttl?]? $[$g?:vccGlossClause]?) =>
      elabVerboseLet "define_game" id ty val (extractGloss? g?) (ttl?.map (·.getString))
  | `(tactic| Define hybrid $id:ident $[: $ty]? := $val $[$g?:vccGlossClause]?) =>
      elabVerboseLet "hybrid" id ty val (extractGloss? g?)
  | `(tactic| Consider adversary $id:ident $[: $ty]? := $val $[$g?:vccGlossClause]?) =>
      elabVerboseLet "let_adv" id ty val (extractGloss? g?)

/-- Intermediate claim/fact in Massot spaced English with optional name and reader gloss. -/
scoped syntax (name := vccWeClaimBy)
  "We" &"claim" (atomic(ident " : "))? term (vccGlossClause)? " by " tacticSeq : tactic
scoped syntax (name := vccWeClaimFrom)
  "We" &"claim" (atomic(ident " : "))? term (vccGlossClause)? " from " term : tactic
scoped syntax (name := vccWeNoteBy)
  "We" &"note" (atomic(ident " : "))? term (vccGlossClause)? " by " tacticSeq : tactic
scoped syntax (name := vccWeNoteFrom)
  "We" &"note" (atomic(ident " : "))? term (vccGlossClause)? " from " term : tactic

/-- Forward step `Since h₁ [and h₂] we get [h₃ :] P [by ...]` and `Since h₁ [and h₂] we conclude ...`. -/
scoped syntax (name := vccSinceGet)
  "Since " sepBy1(term, " and ") " we " &"get" (atomic(ident " : "))? term (" by " tacticSeq)? : tactic
scoped syntax (name := vccSinceConclude)
  "Since " sepBy1(term, " and ") " we " &"conclude" (str)? (" by " tacticSeq)? : tactic

/-- Backward reduction (`By "<reason>" it suffices to show [h :] P by/via ...` and `It suffices to show ...`). -/
scoped syntax (name := vccByReasonSufficesBy)
  "By " str &"it" &"suffices" &"to" &"show" (atomic(ident " : "))? term " by " tacticSeq : tactic
scoped syntax (name := vccByReasonSufficesVia)
  "By " str &"it" &"suffices" &"to" &"show" (atomic(ident " : "))? term " via " tacticSeq : tactic
scoped syntax (name := vccItSufficesBy)
  "It" &"suffices" &"to" &"show" (atomic(ident " : "))? term (" because " str)? " by " tacticSeq : tactic
scoped syntax (name := vccItSufficesVia)
  "It" &"suffices" &"to" &"show" (atomic(ident " : "))? term (" because " str)? " via " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| We claim $[$id?:ident :]? $prop $[$g?:vccGlossClause]? by $tacSeq) =>
      elabVerboseHave "claim" id? prop (some tacSeq) none (extractGloss? g?)
  | `(tactic| We claim $[$id?:ident :]? $prop $[$g?:vccGlossClause]? from $pt) =>
      elabVerboseHave "claim" id? prop none (some pt) (extractGloss? g?)
  | `(tactic| We note $[$id?:ident :]? $prop $[$g?:vccGlossClause]? by $tacSeq) =>
      elabVerboseHave "fact" id? prop (some tacSeq) none (extractGloss? g?)
  | `(tactic| We note $[$id?:ident :]? $prop $[$g?:vccGlossClause]? from $pt) =>
      elabVerboseHave "fact" id? prop none (some pt) (extractGloss? g?)
  | `(tactic| Since $[$ps]and* we get $[$id?:ident :]? $prop $[by $tacSeq?]?) =>
      elabSinceGet ps id? prop tacSeq?
  | `(tactic| Since $[$ps]and* we conclude $[$r?:str]? $[by $tacSeq?]?) =>
      runSinceConclude .concludeStep "since_conclude" ps r? tacSeq?
  | `(tactic| By $r:str it suffices to show $[$id?:ident :]? $prop by $tacSeq) =>
      let raw := r.getString.trimAscii.toString
      let low := raw.toLower
      let hasVerb :=
        [" gives", " show", " shows", " yield", " yields", " establish", " establishes",
         " implies", " ensure", " ensures", " bound", " bounds"].any fun v =>
          (low.splitOn v).length > 1
      let msg :=
        if low.startsWith "by " || low.startsWith "since " || low.startsWith "because " ||
           low.startsWith "from " || low.startsWith "under " || low.startsWith "using " ||
           low.startsWith "via " || low.startsWith "applying " ||
           low.startsWith "multiplying " || low.startsWith "combining " ||
           low.startsWith "dividing " || low.startsWith "summing " ||
           low.startsWith "substituting " || low.startsWith "rewriting " ||
           low.startsWith "splitting " then
          Informalization.Core.Grammar.capitalizeFirst raw
        else if hasVerb then
          s!"Since {Informalization.Core.Grammar.lowercaseFirst raw}"
        else
          s!"By {raw}"
      elabSuffices id? prop (some msg) tacSeq
  | `(tactic| By $r:str it suffices to show $[$id?:ident :]? $prop via $tacSeq) =>
      let raw := r.getString.trimAscii.toString
      let low := raw.toLower
      let hasVerb :=
        [" gives", " show", " shows", " yield", " yields", " establish", " establishes",
         " implies", " ensure", " ensures", " bound", " bounds"].any fun v =>
          (low.splitOn v).length > 1
      let msg :=
        if low.startsWith "by " || low.startsWith "since " || low.startsWith "because " ||
           low.startsWith "from " || low.startsWith "under " || low.startsWith "using " ||
           low.startsWith "via " || low.startsWith "applying " ||
           low.startsWith "multiplying " || low.startsWith "combining " ||
           low.startsWith "dividing " || low.startsWith "summing " ||
           low.startsWith "substituting " || low.startsWith "rewriting " ||
           low.startsWith "splitting " then
          Informalization.Core.Grammar.capitalizeFirst raw
        else if hasVerb then
          s!"Since {Informalization.Core.Grammar.lowercaseFirst raw}"
        else
          s!"By {raw}"
      elabSuffices id? prop (some msg) tacSeq
  | `(tactic| It suffices to show $[$id?:ident :]? $prop $[because $r?:str]? by $tacSeq) =>
      elabSuffices id? prop (r?.map (·.getString)) tacSeq
  | `(tactic| It suffices to show $[$id?:ident :]? $prop $[because $r?:str]? via $tacSeq) =>
      elabSuffices id? prop (r?.map (·.getString)) tacSeq

/-- Spaced-English structural CC tactics, hybrid chains, and indifferentiability idioms. -/
scoped syntax (name := vccConstructUsingSpaced)
  "Construct" &"using" term : tactic
scoped syntax (name := vccReplaceConvSpacedIn)
  "Replace" &"converter" " in " term " using " term : tactic
scoped syntax (name := vccReplaceConvSpacedUsing)
  "Replace" &"converter" " using " term : tactic
scoped syntax (name := vccSeqCompSpaced)
  "By" &"sequential" &"composition" (&"of")? term " and " term : tactic
scoped syntax (name := vccParCompSpaced)
  "By" &"parallel" &"composition" (&"of")? term " and " term : tactic
scoped syntax (name := vccContextRightSpaced)
  "By" &"context" &"insensitivity" &"on" &"the" &"right" ("with")? term " using " term : tactic
scoped syntax (name := vccContextLeftSpaced)
  "By" &"context" &"insensitivity" &"on" &"the" &"left" ("with")? term " using " term : tactic
scoped syntax (name := vccPullRelaxSpaced)
  "Pull" &"relaxation" &"through" term " using " term " from " term : tactic
scoped syntax (name := vccSubstitutePreservingSpaced)
  "Substitute" &"in" &"context" term " through " term " preserving" &"closure" term : tactic
scoped syntax (name := vccSubstituteRelSpaced)
  "Substitute" &"in" &"context" term " through " term " using " term : tactic
scoped syntax (name := vccTriangleSpaced)
  "By" &"the" &"triangle" &"inequality" &"via" term : tactic
scoped syntax (name := vccNonexpandFromSpaced)
  "By" "non-expansion" ("from" term)? : tactic
scoped elab (name := vccBecauseSpaced) "because " reason:str " => " proof:term : term <= expectedType? => do
  let val ← Term.elabTerm proof expectedType?
  return wrapVerboseMData "cc_calc_step" val (reason? := some reason.getString)
scoped syntax (name := vccHybridStepSpaced) "By" &"hybrid" &"step" str " => " tacticSeq : tactic
scoped syntax (name := vccHybridChainSpaced) "By" &"hybrid" &"chain" "{" tacticSeq "}" : tactic
scoped syntax (name := vccExhibitSimSpaced)
  "We" &"exhibit" &"simulator" term (" on " "interface " term)? : tactic
scoped syntax (name := vccComposeSimSpaced)
  "By" "composition-order" &"invariance" (&"composing")? term " and " term (" using " term)? : tactic

elab_rules : tactic
  | `(tactic| Construct using $h) =>
      wrapGoalWithMData "construct" (label? := syntaxShortLabel? h) fun g => do
        runTacticOnGoal g (← `(tactic| cc_construct using $h))
  | `(tactic| Replace converter in $constr using $hEq) =>
      wrapGoalWithMData "replace_converter" fun g => do
        runTacticOnGoal g (← `(tactic| cc_transport $constr using $hEq))
  | `(tactic| Replace converter using $hEq) =>
      wrapGoalWithMData "replace_converter" fun g => do
        runTacticOnGoal g (← `(tactic| cc_transport using $hEq))
  | `(tactic| By sequential composition $[of]? $h1 and $h2) =>
      wrapGoalWithMData "seq_comp" fun g => do
        runTacticOnGoal g (← `(tactic| cc_compose $h1, $h2))
  | `(tactic| By parallel composition $[of]? $hL and $hR) =>
      wrapGoalWithMData "par_comp" fun g => do
        runTacticOnGoal g (← `(tactic| cc_parallel $hL, $hR))
  | `(tactic| By context insensitivity on the right $[with]? $ctxSpec using $hConstr) =>
      wrapGoalWithMData "context_right" (label? := syntaxShortLabel? ctxSpec) fun g => do
        runTacticOnGoal g (← `(tactic| By_context_insensitivity_right $ctxSpec using $hConstr))
  | `(tactic| By context insensitivity on the left $[with]? $ctxSpec using $hConstr) =>
      wrapGoalWithMData "context_left" (label? := syntaxShortLabel? ctxSpec) fun g => do
        runTacticOnGoal g (← `(tactic| By_context_insensitivity_left $ctxSpec using $hConstr))
  | `(tactic| Pull relaxation through $hOuter using $hCompat from $hInner) =>
      wrapGoalWithMData "pull_relax" fun g => do
        runTacticOnGoal g (← `(tactic| cc_relax using $hInner, $hOuter with $hCompat))
  | `(tactic| Substitute in context $hStep through $conv preserving closure $hClosed) =>
      wrapGoalWithMData "substitute" (label? := syntaxShortLabel? conv) fun g => do
        runTacticOnGoal g (← `(tactic| Substitute_in_context $hStep through $conv preserving_closure $hClosed))
  | `(tactic| Substitute in context $rel through $conv using $premise) =>
      wrapGoalWithMData "substitute" (label? := syntaxShortLabel? conv) fun g => do
        runTacticOnGoal g (← `(tactic| cc_substitute $rel through $conv using $premise))
  | `(tactic| By the triangle inequality via $mid) =>
      wrapGoalWithMData "triangle" (label? := syntaxShortLabel? mid) fun g => do
        runTacticOnGoal g (← `(tactic| cc_triangle via $mid))
  | `(tactic| By non-expansion $[from $h?]?) =>
      match h? with
      | none =>
          wrapGoalWithMData "nonexpand" fun g => do
            runTacticOnGoal g (← `(tactic| By_non_expansion))
      | some h =>
          wrapGoalWithMData "nonexpand_from" (label? := syntaxShortLabel? h) fun g => do
            runTacticOnGoal g (← `(tactic|
              first
                | exact (ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _).trans $h
                | refine (ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _).trans ?_; exact $h
                | exact (ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le _ _ _).trans $h
                | exact (ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le _ _ _).trans $h
                | (try dsimp +zetaDelta only; cc_nonexpand; try exact $h)
                | (exact (by have hBound := $h; try dsimp +zetaDelta only; first | cc_nonexpand | assumption | exact le_trans (ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _) hBound))))
  | `(tactic| By hybrid step $reason:str => $tacSeq) =>
      wrapGoalWithMData "cc_calc_step" (reason? := some reason.getString) fun g => do
        let rem ← runTacticSeqOnGoal g tacSeq
        unless rem.isEmpty do
          throwError "By hybrid step left {rem.length} unsolved goal(s)"
        pure rem
  | `(tactic| By hybrid chain { $tacSeq }) =>
      wrapGoalWithMData "hybrid_chain" fun g =>
        runTacticSeqOnGoal g tacSeq
  | `(tactic| We exhibit simulator $sim $[on interface $iface?]?) => do
      match iface? with
      | some i => evalTactic (← `(tactic| Exhibit_simulator $sim for_interface $i))
      | none => evalTactic (← `(tactic| Exhibit_simulator $sim))
  | `(tactic| By composition-order invariance $[composing]? $hInner and $hOuter $[using $hComm?]?) =>
      wrapGoalWithMData "compose_simulators" fun g => do
        match hComm? with
        | some hc => runTacticOnGoal g (← `(tactic| Compose_simulators $hInner and $hOuter using_commutation $hc))
        | none => runTacticOnGoal g (← `(tactic| Compose_simulators $hInner and $hOuter))

/-- Spaced-English Games, Difference Lemma, H-Coefficients, Distinguishers, Cases & Closure. -/
scoped syntax (name := vccIgnoreMBOSpaced)
  "Ignoring" &"the" &"MBO" &"of" term (" via " term)? : tactic
scoped syntax (name := vccFundGameSpaced)
  "By" &"the" &"fundamental" &"lemma" &"of" &"game" &"playing" ("from")? term : tactic
scoped syntax (name := vccCondEquivSpaced)
  "By" &"conditional" &"equivalence" ("from")? term (" using " term)? : tactic
scoped syntax (name := vccDiffLemmaUsing)
  "By" &"the" &"Difference" &"Lemma" "with" &"bad" &"event" term (vccGlossClause)? " using " term : tactic
scoped syntax (name := vccDiffLemmaVia)
  "By" &"the" &"Difference" &"Lemma" "with" &"bad" &"event" term (vccGlossClause)? " via " "{" tacticSeq "}" : tactic
scoped syntax (name := vccExtendedHCoeffSpaced)
  "By" &"the" &"extended" "H-technique"
    &"mixing" &"real" term " over " term " using " term
    &"revealing" term " and " term
    " with " &"bad" &"transcripts" term " bound " "by" term
    " with " &"good" &"ratio" &"loss" term : tactic
scoped syntax (name := vccExtendedHCoeffUsingSpaced)
  "By" &"the" &"extended" "H-technique" " using " term : tactic
scoped syntax (name := vccExhibitDistSpaced)
  "We" &"exhibit" &"distinguisher" term (" admissible " "by" term)? : tactic
scoped syntax (name := vccLowerBoundAdvSpaced)
  "By" &"bounding" &"decision" &"probabilities" &"of" term " via " term " and " term : tactic
scoped syntax (name := vccTightnessBlockSpaced)
  "We" &"prove" &"matching" &"lower" " and " &"upper" &"bounds" ":"
    &"lower" &"bound" "{" tacticSeq "}"
    &"upper" &"bound" "{" tacticSeq "}" : tactic
scoped syntax (name := vccTightnessTermsSpaced)
  "We" &"prove" &"matching" &"lower" " and " &"upper" &"bounds" ":" &"upper" term " and " &"lower" term : tactic
scoped syntax (name := vccTightnessSplitSpaced)
  "We" &"prove" &"matching" &"lower" " and " &"upper" &"bounds" : tactic
scoped syntax (name := vccReformulateHyp)
  "We" &"reformulate" ident " as " term (vccGlossClause)? (" by " tacticSeq)? : tactic
scoped syntax (name := vccReformulateGoal)
  "We" &"reformulate" &"the" &"goal" " as " term (vccGlossClause)? (" by " tacticSeq)? : tactic
scoped syntax (name := vccByDefSpaced)
  "By" &"definition" ("{" tacticSeq "}")? : tactic
scoped syntax (name := vccWeComputeSpaced)
  "We" &"compute" ("{" tacticSeq "}")? : tactic
scoped syntax (name := vccRoutineCalcSpaced)
  "By" &"routine" &"calculation" (str)? "{" tacticSeq "}" : tactic
scoped syntax (name := vccRoutineCalcAutoSpaced)
  "By" &"routine" &"calculation" : tactic
scoped syntax (name := vccByCasesSpaced)
  "By" &"cases" &"on" (atomic(ident " : "))? term (vccGlossClause)? : tactic
scoped syntax (name := vccByInductionSpaced)
  "By" &"induction" &"on" ident (vccGlossClause)? : tactic
scoped syntax (name := vccWeObtainTupleSpaced)
  "We" &"obtain" "⟨" sepBy1(ident, ",") "⟩" "from" term (vccGlossClause)? : tactic
scoped syntax (name := vccWeObtainSingleSpaced)
  "We" &"obtain" ident "from" term (vccGlossClause)? : tactic
scoped syntax (name := vccCaseSpaced)
  "Case" str "{" tacticSeq "}" : tactic
scoped syntax (name := vccTelescopingBlock)
  "By" &"telescoping" &"sum" "{" tacticSeq "}" : tactic
scoped syntax (name := vccTelescopingUsing)
  "By" &"telescoping" &"sum" " using " term : tactic
scoped syntax (name := vccUnionBoundBlock)
  "By" &"union" &"bound" "{" tacticSeq "}" : tactic
scoped syntax (name := vccUnionBoundUsing)
  "By" &"union" &"bound" " using " term : tactic
scoped syntax (name := vccWeConcludeBy)
  "We" &"conclude" (str)? " by " tacticSeq : tactic
scoped syntax (name := vccWeConcludeFrom)
  "We" &"conclude" (str)? " from " sepBy1(term, " and ") (" by " tacticSeq)? : tactic
scoped syntax (name := vccWeConcludeAuto)
  "We" &"conclude" (str)? : tactic

elab_rules : tactic
  | `(tactic| Ignoring the MBO of $game $[via $hv?]?) =>
      wrapGoalWithMData "ignore_mbo" (label? := syntaxShortLabel? game) fun g => do
        match hv? with
        | some hv => runTacticOnGoal g (← `(tactic| rw [← $hv]))
        | none => runTacticOnGoal g (← `(tactic| Ignore_MBO_of $game))
  | `(tactic| By the fundamental lemma of game playing $[from]? $hEq) =>
      wrapGoalWithMData "fundamental_game" fun g => do
        runTacticOnGoal g (← `(tactic| By_fundamental_lemma_of_game_playing $hEq))
  | `(tactic| By conditional equivalence $[from]? $hCond $[using $hs?]?) =>
      wrapGoalWithMData "cond_equiv" fun g => do
        match hs? with
        | some hs => runTacticOnGoal g (← `(tactic| By_conditional_equivalence $hCond using $hs))
        | none => runTacticOnGoal g (← `(tactic| By_conditional_equivalence $hCond))
  | `(tactic| By the Difference Lemma with bad event $bad $[$g?:vccGlossClause]? using $hDiff) =>
      let gloss? := extractGloss? g?
      let lbl? := syntaxShortLabel? bad.raw
      withMainContext do
        let mvarId ← getMainGoal
        let target ← mvarId.getType
        let badVal ← Tactic.elabTerm bad none
        let badTy ← inferType badVal
        let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
        let rem ← runTacticOnGoal inner.mvarId! (← `(tactic|
          first
            | exact $hDiff
            | exact difference_lemma_probDist _ _ _ $bad $hDiff
            | refine (difference_lemma_probDist _ _ _ $bad $hDiff).trans ?_
            | exact SystemAlgebra.RandomSystem.GameEquivalent.abs_decisionProbability_sub_le
                _ _ _ $hDiff _ _ _
            | refine (SystemAlgebra.RandomSystem.GameEquivalent.abs_decisionProbability_sub_le
                _ _ _ $hDiff _ _ _).trans ?_
            | exact SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent
                _ _ _ _ $hDiff
            | refine (SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent
                _ _ _ _ $hDiff).trans ?_
            | exact ($hDiff).trans ?_))
        let tagged := mkApp (mkLambda `_ .default badTy inner) badVal
        mvarId.assign (wrapVerboseMData "difference_lemma" tagged (label? := lbl?) (reason? := gloss?))
        replaceMainGoal rem
  | `(tactic| By the Difference Lemma with bad event $bad $[$g?:vccGlossClause]? via { $tacSeq }) =>
      let gloss? := extractGloss? g?
      let lbl? := syntaxShortLabel? bad.raw
      withMainContext do
        let mvarId ← getMainGoal
        let target ← mvarId.getType
        let badVal ← Tactic.elabTerm bad none
        let badTy ← inferType badVal
        let inner ← mkFreshExprSyntheticOpaqueMVar target (← mvarId.getTag)
        let rem ← runTacticSeqOnGoal inner.mvarId! tacSeq
        let tagged := mkApp (mkLambda `_ .default badTy inner) badVal
        mvarId.assign (wrapVerboseMData "difference_lemma" tagged (label? := lbl?) (reason? := gloss?))
        replaceMainGoal rem
  | `(tactic| By the extended H-technique
        mixing real $realF over $sampleP using $hMix
        revealing $realRev and $idealRev
        with bad transcripts $badPred bound by $eps2
        with good ratio loss $eps1) =>
      wrapGoalWithMData "extended_h_coeff" fun g => do
        runTacticOnGoal g (← `(tactic|
          By_extended_H_technique
            mixing_real $realF over $sampleP using $hMix
            revealing $realRev and $idealRev
            with_bad_transcripts $badPred bound_by $eps2
            with_good_ratio_loss $eps1))
  | `(tactic| By the extended H-technique using $w) =>
      wrapGoalWithMData "extended_h_coeff" fun g => do
        runTacticOnGoal g (← `(tactic| By_extended_H_technique_using $w))
  | `(tactic| We exhibit distinguisher $dist $[admissible by $ha?]?) => do
      match ha? with
      | some ha => evalTactic (← `(tactic| Exhibit_distinguisher $dist admissible_by $ha))
      | none => evalTactic (← `(tactic| Exhibit_distinguisher $dist))
  | `(tactic| By bounding decision probabilities of $dist via $hr and $hi) => do
      evalTactic (← `(tactic| Lower_bound_advantage_of $dist via $hr and $hi))
  | `(tactic| We prove matching lower and upper bounds : lower bound { $lowTacs } upper bound { $upTacs }) =>
      wrapGoalWithMData "tightness_sandwich" (role? := some "lower_upper") fun g => do
        runTacticOnGoal g (← `(tactic| Tightness_sandwich lower_bound { $lowTacs } upper_bound { $upTacs }))
  | `(tactic| We prove matching lower and upper bounds : upper $hUp and lower $hLow) =>
      wrapGoalWithMData "tightness_sandwich" (role? := some "upper_lower") fun g => do
        runTacticOnGoal g (← `(tactic| Tightness_sandwich upper $hUp lower $hLow))
  | `(tactic| We prove matching lower and upper bounds) =>
      wrapGoalWithMData "tightness_sandwich" (role? := some "lower_upper") fun g => do
        runTacticOnGoal g (← `(tactic| constructor))
  | `(tactic| We reformulate $h:ident as $newTy $[$g?:vccGlossClause]? $[by $tacSeq?]?) =>
      wrapGoalWithMData "reformulate" (label? := some h.getId.toString) (reason? := extractGloss? g?) fun g => do
        match tacSeq? with
        | some ts => runTacticOnGoal g (← `(tactic| replace $h : $newTy := by $ts))
        | none => runTacticOnGoal g (← `(tactic| replace $h : $newTy := $h))
  | `(tactic| We reformulate the goal as $newTy $[$g?:vccGlossClause]? $[by $tacSeq?]?) =>
      wrapGoalWithMData "reformulate" (label? := some "goal") (reason? := extractGloss? g?) fun g => do
        match tacSeq? with
        | some ts =>
            try
              let hGoalId := mkIdent (← mkFreshUserName `hGoal)
              runTacticOnGoal g (← `(tactic| suffices $hGoalId : $newTy by $ts))
            catch _ =>
              let rem ← runTacticOnGoal g (← `(tactic| change $newTy))
              match rem with
              | [g'] => runTacticSeqOnGoal g' ts
              | other => return other
        | none => runTacticOnGoal g (← `(tactic| change $newTy))
  | `(tactic| By definition $[{ $tacSeq? }]?) =>
      wrapGoalWithMData "cc_routine" (reason? := some "definitional unfolding") fun g => do
        match tacSeq? with
        | some ts => runTacticSeqOnGoal g ts
        | none => runTacticOnGoal g (← `(tactic| (try dsimp only; first | rfl | assumption | simp)))
  | `(tactic| We compute $[{ $tacSeq? }]?) =>
      wrapGoalWithMData "cc_routine" (reason? := some "explicit computation") fun g => do
        match tacSeq? with
        | some ts => runTacticSeqOnGoal g ts
        | none => runTacticOnGoal g (← `(tactic| (first | norm_num | ring | linarith | rfl | simp)))
  | `(tactic| By routine calculation $[$r?:str]? { $tacSeq }) =>
      elabCCRoutineBlock (r?.map (·.getString)) tacSeq
  | `(tactic| By routine calculation) => do
      evalTactic (← `(tactic| By_CC_routine))
  | `(tactic| By cases on $[$id?:ident :]? $prop $[$g?:vccGlossClause]?) => do
      let reason? := extractGloss? g?
      let (tmpl, witness) ← match reason? with
        | some r => parseAndElabProseInterp r
        | none => pure ("", mkConst ``spineNil)
      wrapGoalWithSpineNode .caseSplit "cases" tmpl false "" "kernelProvedClaim" witness fun g => do
        match id? with
        | some id => runTacticOnGoal g (← `(tactic| by_cases $id : $prop))
        | none =>
            let hCase := mkIdent (← mkFreshUserName `hCase)
            runTacticOnGoal g (← `(tactic| by_cases $hCase : $prop))
  | `(tactic| By induction on $x:ident $[$g?:vccGlossClause]?) => do
      let reason? := extractGloss? g?
      let (tmpl, witness) ← match reason? with
        | some r => parseAndElabProseInterp r
        | none => pure ("", mkConst ``spineNil)
      wrapGoalWithSpineNode .inductionStep "induction" tmpl true "" "kernelProvedClaim" witness fun g => do
        let xt : TSyntax ``Lean.Parser.Tactic.elimTarget ← `(Lean.Parser.Tactic.elimTarget| $x:ident)
        runTacticOnGoal g (← `(tactic| induction $xt))
  | `(tactic| We obtain ⟨$[$ids],*⟩ from $pt:term $[$g?:vccGlossClause]?) => do
      let reason? := extractGloss? g?
      let (tmpl, witness) ← match reason? with
        | some r => parseAndElabProseInterp r
        | none => pure ("", mkConst ``spineNil)
      wrapGoalWithSpineNode .obtainStep "obtain" tmpl false "" "kernelProvedClaim" witness fun g => do
        runTacticOnGoal g (← `(tactic| obtain ⟨$[$ids],*⟩ := $pt))
  | `(tactic| We obtain $id:ident from $pt:term $[$g?:vccGlossClause]?) => do
      let reason? := extractGloss? g?
      let (tmpl, witness) ← match reason? with
        | some r => parseAndElabProseInterp r
        | none => pure ("", mkConst ``spineNil)
      wrapGoalWithSpineNode .obtainStep "obtain" tmpl false "" "kernelProvedClaim" witness fun g => do
        runTacticOnGoal g (← `(tactic| obtain $id := $pt))
  | `(tactic| Case $lbl:str { $tacSeq }) =>
      wrapGoalWithMData "case" (label? := some lbl.getString) fun g =>
        runTacticSeqOnGoal g tacSeq
  | `(tactic| By telescoping sum { $tacSeq }) =>
      wrapGoalWithMData "telescoping" fun g =>
        runTacticSeqOnGoal g tacSeq
  | `(tactic| By telescoping sum using $h) =>
      wrapGoalWithMData "telescoping" (label? := syntaxShortLabel? h) fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | exact $h
            | (rw [← $h]; try ring; try linarith)))
  | `(tactic| By union bound { $tacSeq }) =>
      wrapGoalWithMData "union_bound" fun g =>
        runTacticSeqOnGoal g tacSeq
  | `(tactic| By union bound using $h) =>
      wrapGoalWithMData "union_bound" (label? := syntaxShortLabel? h) fun g => do
        runTacticOnGoal g (← `(tactic|
          first
            | exact $h
            | refine le_trans ?_ $h
            | exact le_trans $h ?_))
  | `(tactic| We conclude $[$r?:str]? by $tacSeq) => do
      let (tmpl, witness) ← match r? with
        | some r => parseAndElabProseInterp r.getString
        | none => pure ("", mkConst ``spineNil)
      wrapGoalWithSpineNode .concludeStep "conclude" tmpl false "" "kernelProvedClaim" witness fun g =>
        runTacticSeqOnGoal g tacSeq
  | `(tactic| We conclude $[$r?:str]? from $[$ps]and* $[by $tacSeq?]?) =>
      runSinceConclude .concludeStep "conclude" ps r? tacSeq?
  | `(tactic| We conclude $[$r?:str]?) => do
      let (tmpl, witness) ← match r? with
        | some r => parseAndElabProseInterp r.getString
        | none => pure ("", mkConst ``spineNil)
      wrapGoalWithSpineNode .concludeStep "conclude" tmpl false "" "kernelProvedClaim" witness fun g =>
        runBoundedAutoCloser g none "We conclude"

end VerboseCC
