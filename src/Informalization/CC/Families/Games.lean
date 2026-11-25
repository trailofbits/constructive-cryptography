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

/-- Explainer for problem/game reductions and converter absorption into winners/solvers. -/
def problemReductionExplainer : RuleExplainer where
  priority := 145
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let conclInl ← renderProposition ctx.tbl expected
    if head == ``ConstructiveCryptography.Problem.performance_le_of_reduction ||
       head == ``ConstructiveCryptography.Games.win_le_of_reduction then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} by reduction to the target problem—translating the uniform target bound through the monotone loss function—we obtain "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-game-red-{head}" content children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.Games.absorb_mem ||
       head == ``ConstructiveCryptography.DistinctionGames.absorb_mem then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} absorbing the converter into the admitted solver produces an admitted solver for the inner game: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-game-absorb-{head}" content children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.Games.absorb_comp then
      let op ← pickMaurerOpener .elaboration
      let content : Array Inline :=
        #[.text s!"{op} absorbing a serial composition of converters into a winner absorbs each converter in turn, giving "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-game-absorb-comp-{head}" content #[] expected head
      return some #[node]
    if head == ``SystemAlgebra.Interface.win_le then
      let op ← pickMaurerOpener .reduction
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} every admitted winner realizes a compatible probabilistic distinguisher, so bounding every distinguisher's winning probability establishes "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-game-winle-{head}" content children expected head
      return some #[node]
    return none

/-- Explainer for MBO games, conditional equivalence `|≡`, game equivalence, and identical-until-bad bounds. -/
def mboGameHopExplainer : RuleExplainer where
  priority := 145
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let conclInl ← renderProposition ctx.tbl expected
    if head == ``ConstructiveCryptography.DistinctionGames.advantage_le_win ||
       head == ``SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} because the game is conditionally equivalent to the comparison resource while its monotone binary output (MBO) stays unset, the distinguishing advantage between the underlying system ",
          .inlineMath "G^{-}", .text " (obtained by ignoring the MBO) and the comparison resource is bounded by the winning probability: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-mbo-adv-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.Interface.dist_visible_le ||
       head == ``SystemAlgebra.Interface.game_dist_le ||
       head == ``SystemAlgebra.RandomSystem.transcriptDistance_visible_le_of_unsetProbability then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} combining conditional equivalence with the upper bound on setting the MBO over every admissible query sequence bounds the distinguishing distance between the underlying system ",
          .inlineMath "G^{-}", .text " and the target resource: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-mbo-dist-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.Domain.Distinguisher.winProbability_le_of_unsetProbability ||
       head == ``SystemAlgebra.RandomSystem.winProbability_le_of_unsetProbability ||
       head == ``SystemAlgebra.PDG.one_sub_le_unsetProbability_behavior then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} since replies before the MBO is set reveal no information about the hidden bad condition, bounding the probability that the MBO is triggered on every fixed query sequence yields "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-mbo-unset-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.RandomSystem.GameEquivalent.transcriptDistance_visible_le ||
       head == ``SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent ||
       head == ``SystemAlgebra.RandomSystem.GameEquivalent.winProbability_eq then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} by the fundamental lemma of game playing, two games that behave identically until the MBO is set share the same unset-MBO probability mass, so distinguishing their underlying systems requires setting the MBO: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-mbo-fund-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.PDG.gameEquivalent_behavior_of_isCoupling then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} coupling the two discrete games so that their realizations share a common monotone bad condition and agree on all replies until that condition holds establishes game equivalence: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-mbo-coupling-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.RandomSystem.transcriptDistance_le_of_transcriptCost_le ||
       head == ``SystemAlgebra.RandomSystem.winProbability_le_of_transcriptCost_le ||
       head == ``SystemAlgebra.Domain.Distinguisher.winProbability_le_of_transcriptCost_le ||
       head == ``SystemAlgebra.RandomSystem.one_sub_le_sum_tSupp then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} summing the per-query probability of leaving the common good part along every admissible transcript via the potential-function union bound yields "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-untilbad-{head}" content children expected head
      return some #[node]
    return none

initialize
  registerRuleExplainer problemReductionExplainer
  registerRuleExplainer mboGameHopExplainer

end Informalization.CC.Families.Games
