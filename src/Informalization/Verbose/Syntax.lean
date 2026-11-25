/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Verbose.Trace
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
open Informalization.Verbose.Trace

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

/-- Introduce a `let` binding (`Write` or `Introduce_hybrid`) wrapped in Verbose-CC `mdata`. -/
private def elabVerboseLet (kind : String) (id : Ident) (tyOpt? : Option (TSyntax `term))
    (valStx : TSyntax `term) : TacticM Unit := withMainContext do
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
  mvarId.assign (wrapVerboseMData kind inner (label? := some id.getId.toString))
  replaceMainGoal [nextGoal]

/-- Introduce a `have` proposition (`Claim` or `Fact`) wrapped in Verbose-CC `mdata`. -/
private def elabVerboseHave (kind : String) (id : Ident) (propStx : TSyntax `term)
    (tacSeq? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (proofTerm? : Option (TSyntax `term)) : TacticM Unit := withMainContext do
  let prop ← elabType propStx
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
  let afterDefine ← inner.mvarId!.define id.getId prop val
  let (fv, nextGoal) ← afterDefine.intro id.getId
  nextGoal.withContext do
    Term.addLocalVarInfo id (mkFVar fv)
  mvarId.assign (wrapVerboseMData kind inner (label? := some id.getId.toString))
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

/-- Apply a pre-built `HCoefficient` witness to bound distinguishing distance. -/
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
      elabVerboseHave "claim" id prop (some tacSeq) none
  | `(tactic| Claim $id:ident : $prop from $pt) =>
      elabVerboseHave "claim" id prop none (some pt)
  | `(tactic| Fact $id:ident : $prop by $tacSeq) =>
      elabVerboseHave "fact" id prop (some tacSeq) none
  | `(tactic| Fact $id:ident : $prop from $pt) =>
      elabVerboseHave "fact" id prop none (some pt)

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
    mvarId.assign (wrapVerboseMData "suffices" inner (reason? := reason?))
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
scoped syntax (name := vccRoutineBlock)
  "By_CC_routine " (str)? "{" tacticSeq "}" : tactic

scoped syntax (name := vccRoutineAuto) "By_CC_routine" : tactic

elab_rules : tactic
  | `(tactic| By_CC_routine $[$reason?:str]? { $tacSeq }) =>
      let r? := reason?.map (·.getString)
      wrapGoalWithMData "cc_routine" (reason? := r?) fun g => do
        runTacticSeqOnGoal g tacSeq
  | `(tactic| By_CC_routine) =>
      wrapGoalWithMData "cc_routine" fun g => do
        runTacticOnGoal g (← `(tactic|
          ((try cc_normalize)
           first
             | rfl
             | assumption
             | cc_routine
             | simp_all only [ConstructiveCryptography.cc_normalization])))

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

end VerboseCC
