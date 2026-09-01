import RandomSystems.Technique.ConditionalEquivalence.Absorption
import RandomSystems.Technique.ConditionalEquivalence.Indistinguishability

set_option autoImplicit false

/-!
# Advantage bound from conditional equivalence
-/

noncomputable section

namespace RandomSystems.PDS

open Probability
open scoped ConditionalEquivalence PDG PDS

universe u v

variable {X : Type u} {Y : Type v}

/-- CR18, Theorem 4.17, on Lanzenberger games. Conditional equivalence bounds
ordinary distinguishing advantage by the supremum winning probability of the
blind game. -/
theorem advantage_le_supWinProb_blind_of_conditionallyEquivalent
    (game : PDG X Y) (target : PDS X Y) (domain : Set (List X))
    (gameProbability : game.isProbDist)
    (targetProbability : target.isProbDist)
    (gameDomain : PDG.HasDomain game domain)
    (targetDomain : HasDomain target domain)
    (equivalent : game |≡ target) :
    Adv(game.underlying, target) ≤
      Γ(PDG.blind game) := by
  let enhanced := PDG.enhance_with_MBO target game
  have enhancedProbability : enhanced.isProbDist := by
    unfold enhanced PDG.enhance_with_MBO
    exact Distribution.fTransform_isProbDist _
      (Distribution.prod_isProbDist target game
        targetProbability gameProbability)
  have enhancedInitiallyFalse : enhanced.InitiallyFalse := by
    simpa only [enhanced] using
      PDG.initiallyFalse_enhance_with_MBO target game
        equivalent.initiallyFalse
  have gameEquivalence : game ≡ᵍ enhanced := by
    simpa only [enhanced] using
      ConditionalEquivalence.equivalentAsGames_enhance_with_MBO_of_conditionallyEquivalent
        game target domain gameProbability targetProbability
        gameDomain targetDomain equivalent
  have enhancedUnderlying : enhanced.underlying = target := by
    simpa only [enhanced] using
      PDG.underlying_enhance_with_MBO_eq target game domain
        gameProbability.weight_eq targetDomain gameDomain
  have blindNonnegative : (PDG.blind game).NonNeg :=
    gameProbability.nonNeg.fTransform _
  have gammaNonnegative : 0 ≤ Γ(PDG.blind game) := by
    apply Real.sSup_nonneg
    rintro value ⟨winner, rfl⟩
    exact blindNonnegative.mass_nonneg _
  unfold advantage
  refine Real.sSup_le ?_ gammaNonnegative
  rintro value ⟨environment, _, rfl⟩
  have enhancedCompatible : Compatible environment.1 enhanced.underlying := by
    rw [enhancedUnderlying]
    exact environment.2.2.1
  have enhancedStops : Stops environment.1 enhanced.underlying := by
    rw [enhancedUnderlying]
    exact environment.2.2.2
  calc
    statDist (trLaw environment.1 game.underlying)
        (trLaw environment.1 target) =
      statDist (trLaw environment.1 game.underlying)
        (trLaw environment.1 enhanced.underlying) := by
          rw [enhancedUnderlying]
    _ ≤ PDG.winProb environment.1 enhanced :=
      statDist_trLaw_le_winProb_of_equivalentAsGames
        environment.1 game enhanced equivalent.initiallyFalse
        enhancedInitiallyFalse gameProbability enhancedProbability
        environment.2.1.1 enhancedCompatible environment.2.1.2 enhancedStops
        gameEquivalence
    _ ≤ Γ(PDG.blind game) := by
      simpa only [enhanced] using
        ConditionalEquivalence.winProb_enhance_with_MBO_le_supWinProb_blind
          environment.1 target game domain targetProbability
          gameProbability.nonNeg targetDomain gameDomain environment.2.2.2

/-- A real-valued blind-winning bound yields an ordinary Random Systems
advantage bound with a nonnegative error budget. -/
theorem advantage_le_of_conditionallyEquivalent_of_supWinProb_blind_le
    (game : PDG X Y) (target : PDS X Y) (domain : Set (List X))
    (gameProbability : game.isProbDist)
    (targetProbability : target.isProbDist)
    (gameDomain : PDG.HasDomain game domain)
    (targetDomain : HasDomain target domain)
    (equivalent : game |≡ target)
    (epsilon : ℝ)
    (supWinProb_blind_le : Γ(PDG.blind game) ≤ epsilon) :
    Adv(game.underlying, target) ≤ epsilon :=
  (advantage_le_supWinProb_blind_of_conditionallyEquivalent
    game target domain gameProbability targetProbability
    gameDomain targetDomain equivalent).trans supWinProb_blind_le

end RandomSystems.PDS
