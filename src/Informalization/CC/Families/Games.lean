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
import ConstructiveCryptography.Problem
import ConstructiveCryptography.Game
import ConstructiveCryptography.CryptographicAlgebra.Game
import ConstructiveCryptography.Instances.Game
import RandomSystems.Game.MBO
import RandomSystems.Game.DiscreteMBO
import RandomSystems.Game.UntilBad
import RandomSystems.Distance.UntilBad

/-!
# Family C: Games, Monotone Binary Outputs (MBOs), Reductions & Identical-Until-Bad

Generic Kyle Miller symbolic explainers for the Constructive Cryptography game-playing layer
(Maurer CR18 §3.7 & §4.4–4.11, Maurer 2002):
* Ordered-performance problem and game reductions (`Problem.performance_le_of_reduction`,
  `Games.win_le_of_reduction`, `Games.absorb_mem`, `Games.absorb_comp`, `DistinctionGames.absorb_mem`);
* Conditional equivalence $G \mathrel{|\!\equiv} T$ linking a game's underlying system $G^-$
  (obtained by ignoring the MBO) to a comparison resource $T$ (`DistinctionGames.advantage_le_win`,
  `Interface.dist_visible_le`, `Interface.game_dist_le`, `transcriptDistance_visible_le_of_unsetProbability`);
* Game equivalence and the fundamental lemma of game playing (`GameEquivalent.transcriptDistance_visible_le`,
  `advantage_le_winProbability_of_gameEquivalent`, `PDG.gameEquivalent_behavior_of_isCoupling`);
* Identical-until-bad potential / transcript-cost union bounds (`transcriptDistance_le_of_transcriptCost_le`,
  `winProbability_le_of_transcriptCost_le`, `one_sub_le_sum_tSupp`).
-/

namespace Informalization.CC.Families.Games

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph

private def mkStep (ctx : DecompCtx) (id : String) (content : Array Inline)
    (children : Array ProofNode) (expected : Expr) (origin : Name) :
    StateRefT DiscourseState MetaM ProofNode := do
  modify (·.markEmitted)
  let goal ← buildGoalState ctx.tbl expected
  return .step id content children (some goal) none (some origin.toString)

/-- Explainer for problem/game reductions and converter absorption into winners/solvers. -/
def problemReductionExplainer : RuleExplainer where
  priority := 145
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.Problem.performance_le_of_reduction ||
       head == ``ConstructiveCryptography.Games.win_le_of_reduction then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-game-red-{head}" (fun conclInl =>
        #[.text "By reduction, "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.Games.absorb_mem ||
       head == ``ConstructiveCryptography.DistinctionGames.absorb_mem then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-game-absorb-{head}" (fun conclInl =>
        #[.text "Absorbing the converter into the solver gives "] ++
        conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.Games.absorb_comp then
      return ← finish s!"cc-game-absorb-comp-{head}" (fun conclInl =>
        #[.text "Absorbing composed converters sequentially gives "] ++
        conclInl ++ #[.text "."]) #[]
    if head == ``SystemAlgebra.Interface.win_le then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-game-winle-{head}" (fun conclInl =>
        #[.text "Bounding every compatible distinguisher's winning probability gives "] ++
        conclInl ++ #[.text "."]) children
    return none

/-- Explainer for MBO games, conditional equivalence `|≡`, game equivalence, and identical-until-bad bounds. -/
def mboGameHopExplainer : RuleExplainer where
  priority := 145
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.DistinctionGames.advantage_le_win ||
       head == ``SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-mbo-adv-{head}" (fun conclInl =>
        #[.text "By conditional equivalence, "] ++ conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.Interface.dist_visible_le ||
       head == ``SystemAlgebra.Interface.game_dist_le ||
       head == ``SystemAlgebra.RandomSystem.transcriptDistance_visible_le_of_unsetProbability then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-mbo-dist-{head}" (fun conclInl =>
        #[.text "By conditional equivalence and the MBO trigger bound, "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.Domain.Distinguisher.winProbability_le_of_unsetProbability ||
       head == ``SystemAlgebra.RandomSystem.winProbability_le_of_unsetProbability ||
       head == ``SystemAlgebra.PDG.one_sub_le_unsetProbability_behavior then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-mbo-unset-{head}" (fun conclInl =>
        #[.text "Bounding the probability of setting the MBO on each query sequence gives "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.RandomSystem.GameEquivalent.transcriptDistance_visible_le ||
       head == ``SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent ||
       head == ``SystemAlgebra.RandomSystem.GameEquivalent.winProbability_eq then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-mbo-fund-{head}" (fun conclInl =>
        #[.text "By the fundamental lemma of game playing, "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.PDG.gameEquivalent_behavior_of_isCoupling then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-mbo-coupling-{head}" (fun conclInl =>
        #[.text "Coupling the two games until their shared bad event establishes "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.RandomSystem.transcriptDistance_le_of_transcriptCost_le ||
       head == ``SystemAlgebra.RandomSystem.winProbability_le_of_transcriptCost_le ||
       head == ``SystemAlgebra.Domain.Distinguisher.winProbability_le_of_transcriptCost_le ||
       head == ``SystemAlgebra.RandomSystem.one_sub_le_sum_tSupp then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-untilbad-{head}" (fun conclInl =>
        #[.text "Summing the per-query bad-event probabilities along each transcript gives "] ++
        conclInl ++ #[.text "."]) children
    return none

initialize
  registerRuleExplainer problemReductionExplainer
  registerRuleExplainer mboGameHopExplainer

end Informalization.CC.Families.Games
