import RandomSystems.Game

set_option autoImplicit false

/-!
# Winning probability
-/

noncomputable section

namespace RandomSystems.PDG

open Probability

universe u v

variable {X : Type u} {Y : Type v}

/-- Lanzenberger, Definition 2.25: the winning probability of one
deterministic environment against a probabilistic game. -/
def winProb (winner : System.Winner X Y) (game : PDG X Y) : ℝ :=
  game.mass (System.Wins winner)

/-- Lanzenberger, Definition 2.25: the supremum winning probability over
deterministic environments. -/
def supWinProb (game : PDG X Y) : ℝ :=
  sSup (Set.range fun winner : System.Winner X Y => winProb winner game)

/-- Lanzenberger's notation for the supremum winning probability. -/
scoped notation:max "ν(" game ")" => supWinProb game

/-- A deterministic environment's winning probability is bounded by the
supremum winning probability. -/
lemma winProb_le_supWinProb {game : PDG X Y} (nonnegative : game.NonNeg)
    (winner : System.Winner X Y) :
    winProb winner game ≤ ν(game) := by
  apply le_csSup
  · refine ⟨game.weight, ?_⟩
    rintro value ⟨candidate, rfl⟩
    exact Distribution.mass_le_weight nonnegative _
  · exact ⟨winner, rfl⟩

/-- A common upper bound for every deterministic winner bounds the maximal
winning probability. -/
lemma supWinProb_le {game : PDG X Y} {bound : ℝ}
    (boundNonnegative : 0 ≤ bound)
    (winProb_le : ∀ winner : System.Winner X Y,
      winProb winner game ≤ bound) :
    supWinProb game ≤ bound := by
  unfold supWinProb
  refine Real.sSup_le ?_ boundNonnegative
  rintro value ⟨winner, rfl⟩
  exact winProb_le winner

end RandomSystems.PDG
