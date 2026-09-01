import RandomSystems.Game.Blind
import RandomSystems.Technique.ConditionalEquivalence
import Probability.Expectation

set_option autoImplicit false

/-!
# Blind absorption

CR18, equation (4.40), adapted to Lanzenberger games. The target answers are
absorbed into the winner, leaving a fixed query history against the source
game.
-/

noncomputable section

namespace RandomSystems

open Classical
open Probability
open scoped ConditionalEquivalence PDG

universe u v

variable {X : Type u} {Y : Type v}

namespace ConditionalEquivalence

/-- CR18, equation (4.40), says that the final step follows by “absorbing
`T̃` into the winner” (printed p. 109). -/
def absorbedWinner (winner : System.Winner X Y)
    (target : System.DDS X Y) : System.Winner X Y :=
  System.fixedQueries
    (((System.tr winner target).getOrElse []).map Prod.fst)

/-- An absorbed winner is blind. -/
lemma isBlind_absorbedWinner (winner : System.Winner X Y)
    (target : System.DDS X Y) :
    System.DDE.IsBlind (absorbedWinner winner target) := by
  intro left right lengthEqual
  unfold absorbedWinner System.fixedQueries
  apply Part.ext'
  · simp only
    exact lengthEqual ▸ Iff.rfl
  · intro leftDefined rightDefined
    simp only
    congr

/-- CR18, equation (4.40): target responses can be absorbed into the winner.
The remaining interaction is against the source game with a blind winner. -/
lemma winProb_enhance_with_MBO_eq (winner : System.Winner X Y)
    (target : PDS X Y) (game : PDG X Y) (domain : Set (List X))
    (targetDomain : PDS.HasDomain target domain)
    (gameDomain : PDG.HasDomain game domain)
    (targetStops : PDS.Stops winner target) :
    PDG.winProb winner (PDG.enhance_with_MBO target game) =
      target.expect fun deterministic =>
        PDG.winProb (absorbedWinner winner deterministic) game := by
  let stoppedTranscript : System.Winner X Y → System.DDS X Y →
      System.Transcript X Y :=
    fun environment system => (System.tr environment system).getOrElse []
  let stoppedQueries : System.Winner X Y → System.DDS X Y → List X :=
    fun environment system =>
      (stoppedTranscript environment system).map Prod.fst
  have wins_iff_condition (environment : System.Winner X Y)
      (deterministicGame : System.DDG X Y)
      (stops : System.Stops environment deterministicGame.system) :
      System.Wins environment deterministicGame ↔
        deterministicGame.condition.1
          (stoppedQueries environment deterministicGame.system) = true := by
    have finalEqual : stoppedTranscript environment deterministicGame.system =
        (System.tr environment deterministicGame.system).get
          (show (System.tr environment deterministicGame.system).Dom from stops) := by
      dsimp only [stoppedTranscript]
      exact Part.getOrElse_of_dom _ stops _
    constructor
    · rintro ⟨transcript, member⟩
      obtain ⟨observed, observedMember, observedEqual⟩ :=
        (Part.mem_map_iff _).mp member
      have observedIsFinal :
          observed = stoppedTranscript environment deterministicGame.system :=
        (Part.mem_unique observedMember (Part.get_mem stops)).trans finalEqual.symm
      rw [observedIsFinal] at observedEqual
      simpa only [stoppedQueries] using congrArg Prod.snd observedEqual
    · intro conditionTrue
      refine ⟨stoppedTranscript environment deterministicGame.system, ?_⟩
      apply (Part.mem_map_iff _).mpr
      refine ⟨_, ?_, Prod.ext rfl conditionTrue⟩
      change stoppedTranscript environment deterministicGame.system ∈
        System.tr environment deterministicGame.system
      rw [finalEqual]
      exact Part.get_mem stops
  have stoppedQueries_eq (environment : System.Winner X Y)
      (system : System.DDS X Y) (stops : System.Stops environment system) :
      stoppedQueries environment system =
        (System.trN environment system (Nat.find stops)).map Prod.fst := by
    dsimp only [stoppedQueries, stoppedTranscript]
    rw [Part.getOrElse_of_dom _ stops,
      System.tr_get_eq_trN stops (Nat.find_spec stops)]
  have enhance_with_MBO_system_eq (deterministicTarget : System.DDS X Y)
      (deterministicGame : System.DDG X Y)
      (sameDomain : System.dom deterministicGame.system =
        System.dom deterministicTarget) :
      (System.enhance_with_MBO deterministicTarget deterministicGame).system =
        deterministicTarget := by
    apply Subtype.ext
    funext history
    apply Part.ext'
    · constructor
      · exact fun admitted => admitted.1
      · intro admitted
        exact ⟨admitted, sameDomain.symm ▸ admitted⟩
    · intro _ _
      rfl
  have fixedQueries_final_queries (system : System.DDS X Y)
      (queries : List X)
      (admitted : queries = [] ∨ queries ∈ System.dom system) :
      stoppedQueries (System.fixedQueries (Y := Y) queries) system = queries := by
    let stops := System.fixedQueries_stops system queries admitted
    have invariant := System.trN_fixedQueries system queries admitted queries.length
    have stable :
        System.trN (System.fixedQueries (Y := Y) queries) system
            (queries.length + 1) =
          System.trN (System.fixedQueries (Y := Y) queries) system
            queries.length := by
      apply System.trN_succ_of_stop
      rw [System.fixedQueries_dom, List.length_map, invariant.1]
      simp
    dsimp only [stoppedQueries, stoppedTranscript]
    rw [Part.getOrElse_of_dom _ stops, System.tr_get_eq_trN stops stable,
      invariant.2, List.take_length]
  have wins_enhance_with_MBO_iff_absorbedWinner
      (environment : System.Winner X Y)
      (deterministicTarget : System.DDS X Y)
      (deterministicGame : System.DDG X Y)
      (sameDomain : System.dom deterministicTarget =
        System.dom deterministicGame.system)
      (stops : System.Stops environment deterministicTarget) :
      System.Wins environment
          (System.enhance_with_MBO deterministicTarget deterministicGame) ↔
        System.Wins (absorbedWinner environment deterministicTarget)
          deterministicGame := by
    let queries := stoppedQueries environment deterministicTarget
    have targetAdmitted :
        queries = [] ∨ queries ∈ System.dom deterministicTarget := by
      change stoppedQueries environment deterministicTarget = [] ∨
        stoppedQueries environment deterministicTarget ∈
          System.dom deterministicTarget
      rcases System.trN_map_fst_mem_dom_or_nil environment deterministicTarget
          (Nat.find stops) with empty | admitted
      · left
        rw [stoppedQueries_eq environment deterministicTarget stops, empty]
        rfl
      · right
        rwa [stoppedQueries_eq environment deterministicTarget stops]
    have gameAdmitted :
        queries = [] ∨ queries ∈ System.dom deterministicGame.system :=
      targetAdmitted.imp id (fun admitted => sameDomain ▸ admitted)
    have combinedSystem :
        (System.enhance_with_MBO deterministicTarget deterministicGame).system =
          deterministicTarget :=
      enhance_with_MBO_system_eq deterministicTarget deterministicGame sameDomain.symm
    have combinedStops :
        System.Stops environment
          (System.enhance_with_MBO deterministicTarget deterministicGame).system := by
      rwa [combinedSystem]
    have left :
        System.Wins environment
            (System.enhance_with_MBO deterministicTarget deterministicGame) ↔
          deterministicGame.condition.1 queries = true := by
      rw [wins_iff_condition environment
        (System.enhance_with_MBO deterministicTarget deterministicGame) combinedStops]
      change deterministicGame.condition.1
        (stoppedQueries environment
          (System.enhance_with_MBO deterministicTarget deterministicGame).system) = true ↔ _
      simp only [combinedSystem]
      rfl
    have right :
        System.Wins (absorbedWinner environment deterministicTarget)
            deterministicGame ↔
          deterministicGame.condition.1 queries = true := by
      have absorbedStops :
          System.Stops (absorbedWinner environment deterministicTarget)
            deterministicGame.system := by
        simpa only [absorbedWinner, stoppedQueries, stoppedTranscript, queries] using
          System.fixedQueries_stops deterministicGame.system queries gameAdmitted
      rw [wins_iff_condition (absorbedWinner environment deterministicTarget)
        deterministicGame absorbedStops]
      change deterministicGame.condition.1
        (stoppedQueries (absorbedWinner environment deterministicTarget)
          deterministicGame.system) = true ↔ _
      have finalQueries :
          stoppedQueries (absorbedWinner environment deterministicTarget)
              deterministicGame.system = queries := by
        simpa only [absorbedWinner, stoppedQueries, stoppedTranscript, queries] using
          fixedQueries_final_queries deterministicGame.system queries gameAdmitted
      rw [finalQueries]
    exact left.trans right.symm
  unfold PDG.winProb PDG.enhance_with_MBO Distribution.expect
  rw [Distribution.mass_fTransform]
  rw [Distribution.mass_congr_of_support
    (Distribution.prod target game)
    (Q := fun pair =>
      System.Wins (absorbedWinner winner pair.1) pair.2) ?_]
  · rw [Distribution.mass_prod_eq_double_sum]
    apply Finsupp.sum_congr
    intro deterministic deterministicSupported
    simp only [Distribution.mass, Finsupp.sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro deterministicGame _
    by_cases wins :
        System.Wins (absorbedWinner winner deterministic) deterministicGame
    · simp [wins]
    · simp [wins]
  · intro pair pairSupported
    obtain ⟨targetSupported, gameSupported⟩ := Finset.mem_product.mp
      (Distribution.support_prod_subset target game pairSupported)
    exact wins_enhance_with_MBO_iff_absorbedWinner winner pair.1 pair.2
      ((targetDomain pair.1 targetSupported).trans
        (gameDomain pair.2 gameSupported).symm)
      (targetStops pair.1 targetSupported)

/-- The absorbed winner is bounded by the supremum winning probability of the
blind game. -/
lemma winProb_enhance_with_MBO_le_supWinProb_blind
    (winner : System.Winner X Y) (target : PDS X Y) (game : PDG X Y)
    (domain : Set (List X)) (targetIsProbability : target.isProbDist)
    (gameNonnegative : game.NonNeg)
    (targetDomain : PDS.HasDomain target domain)
    (gameDomain : PDG.HasDomain game domain)
    (targetStops : PDS.Stops winner target) :
    PDG.winProb winner (PDG.enhance_with_MBO target game) ≤
      Γ(PDG.blind game) := by
  rw [winProb_enhance_with_MBO_eq winner target game domain
    targetDomain gameDomain targetStops]
  calc
    target.expect (fun deterministic =>
        PDG.winProb (absorbedWinner winner deterministic) game) ≤
      Γ(PDG.blind game) * target.weight :=
        Distribution.expect_le_mul_weight targetIsProbability.nonNeg
          (fun deterministic _ =>
            PDG.winProb_le_supWinProb_blind gameNonnegative
              (absorbedWinner winner deterministic)
              (isBlind_absorbedWinner winner deterministic))
    _ = Γ(PDG.blind game) := by rw [targetIsProbability.weight_eq, mul_one]

end ConditionalEquivalence

end RandomSystems
