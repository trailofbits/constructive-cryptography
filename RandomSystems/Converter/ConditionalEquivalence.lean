import RandomSystems.Converter.RandomSystem
import RandomSystems.Technique.ConditionalEquivalence.Advantage

set_option autoImplicit false

/-!
# Conditional equivalence for cumulative random systems
-/

namespace RandomSystems.Ambient.RandomSystem

noncomputable section

open Probability

universe u v

variable {X : Type u} {Y : Type v}

/-- Conditional equivalence bounds a cumulative random-system comparison once
that comparison is bounded by the underlying fixed-interface comparison. -/
theorem advantage_le_supWinProb_blind_of_conditionallyEquivalent
    {left right : RandomSystem (Interface.single X Y)}
    (game : Distribution.ProbDist (System.DDG X Y))
    (target : Distribution.ProbDist (System.DDS X Y))
    (domain : Set (List X))
    (gameDomain : RandomSystems.PDG.HasDomain game.1 domain)
    (targetDomain : RandomSystems.PDS.HasDomain target.1 domain)
    (equivalent :
      RandomSystems.ConditionalEquivalence.ConditionallyEquivalent game.1 target.1)
    (refinement :
      advantage left right ≤
        RandomSystems.PDS.advantage
          (RandomSystems.PDG.underlying game.1) target.1) :
    advantage left right ≤
      RandomSystems.PDG.supWinProb (RandomSystems.PDG.blind game.1) :=
  refinement.trans
    (RandomSystems.PDS.advantage_le_supWinProb_blind_of_conditionallyEquivalent
      game.1 target.1 domain game.2 target.2
      gameDomain targetDomain equivalent)

end

end RandomSystems.Ambient.RandomSystem
