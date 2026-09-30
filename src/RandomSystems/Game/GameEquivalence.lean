import RandomSystems.Game.Game
import RandomSystems.Cumulative.CumulativeObservation
import Probability.StatisticalDistance

/-!
# The game-equivalence bound

Maurer, *Conditional Equivalence of Random Systems and Indistinguishability Proofs*,
Definition 13 and Theorem 3 (printed pp. 3153–3154): the joint probability of the replies
with the condition unset factors as the ideal reply probability times the probability that
the condition is unset. The distinguishing advantage between the game's system and the
ideal system is then at most the blind winning probability of the game.

## Main definitions

* `GameEquivalent G S`: the factorization of the game `G` through the random system `S`

## Main results

* `RandomSystem.statDist_sLaw_le_of_ratio`: a uniform lower bound on probability ratios
  bounds every compatible transcript law
* `GameEquivalent.statDist_le_blind`: game equivalence bounds distinguishing by blind
  winning
-/

namespace SystemAlgebra

open Classical Probability

namespace RandomSystem

/-- A uniform lower bound on cumulative probability ratios bounds every
compatible finite transcript observation. -/
theorem statDist_sLaw_le_of_ratio {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y}
    (R S : RandomSystem X Y D) (e : List Y →. X) (n : ℕ) (hR : R.Compatible e)
    (hS : S.Compatible e) {ε : ℝ} (hε : 0 ≤ ε) (ratio : ∀ h, (1 - ε) * S h ≤ R h) :
    statDist (R.sLaw e n) (S.sLaw e n) ≤ ε := by
  have pr := R.sLaw_isProbDist hR n
  have ps := S.sLaw_isProbDist hS n
  have bound := statDist_le_probBad_add_of_ratio_on_good
    (R.sLaw e n) (S.sLaw e n) (fun _ => False) ⟨ε, hε⟩
    pr.1 ps.1 (pr.2.trans ps.2.symm) ps.2.le (by
      intro h _
      simp only [sLaw_apply]
      split_ifs
      · exact ratio h
      · simp)
  rw [probBad, Distribution.mass_eq_zero_of_forall_not _ (fun _ h => h), zero_add] at bound
  exact bound

end RandomSystem

/-- The conditional-probability witness of the one-sided game-equivalence technique: on
each transcript, the replies with the condition unset factor through `S`. -/
def GameEquivalent {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y}
    (G : PDG X Y D) (S : RandomSystem X Y D) : Prop :=
  ∀ h, G.goodProbability h = (1 - G.badProbability (h.map Prod.fst)) * S h

namespace GameEquivalent

variable {X Y : Type} [Fintype X] [Fintype Y] {E : List X → Prop} {bound : ℕ}
  {hE : ∀ h, E h → h.length ≤ bound} (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
  {G : PDG X Y (Domain.ofInputs E bound hE)} {S : RandomSystem X Y (Domain.ofInputs E bound hE)}

theorem ratio_le (equiv : GameEquivalent G S) (hG : G.isProbDist) (h : List (X × Y)) :
    (1 - (G.blind hE').supWinProbability) * S h ≤
      PDS.behavior G.underlying (PDG.underlying_probability hG) h := by
  by_cases hz : S h = 0
  · simp only [hz, mul_zero]
    exact RandomSystem.mass_nonneg _ _
  have admitted : h.map Prod.fst = [] ∨ E (h.map Prod.fst) := by
    rcases List.eq_nil_or_concat h with rfl | ⟨p, z, rfl⟩
    · exact Or.inl rfl
    · right
      by_contra hd
      exact hz (by simpa only [List.concat_eq_append] using
        S.mass_eq_zero_of_not_admitted (by simpa using hd) z.2)
  calc
    (1 - (G.blind hE').supWinProbability) * S h
        ≤ (1 - G.badProbability (h.map Prod.fst)) * S h :=
      mul_le_mul_of_nonneg_right
        (sub_le_sub_left (PDG.badProbability_le_blind hE' hG.1 _ admitted) 1)
        (S.mass_nonneg h)
    _ = G.goodProbability h := (equiv h).symm
    _ ≤ _ := PDG.goodProbability_le hG.1 h

/-- **Game equivalence bounds distinguishing by blind winning.** -/
theorem statDist_le_blind (equiv : GameEquivalent G S) (hG : G.isProbDist)
    (e : List Y →. X) (n : ℕ)
    (hr : (PDS.behavior G.underlying (PDG.underlying_probability hG)).Compatible e)
    (hs : S.Compatible e) :
    statDist ((PDS.behavior G.underlying (PDG.underlying_probability hG)).sLaw e n)
      (S.sLaw e n) ≤ (G.blind hE').supWinProbability := by
  apply RandomSystem.statDist_sLaw_le_of_ratio _ _ e n hr hs
  · exact (hG.1.mass_nonneg _).trans
      (PDG.badProbability_le_blind hE' hG.1 [] (Or.inl rfl))
  · exact equiv.ratio_le hE' hG

end GameEquivalent

end SystemAlgebra
