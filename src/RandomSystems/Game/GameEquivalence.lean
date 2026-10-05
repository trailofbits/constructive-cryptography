import RandomSystems.Game.DiscreteMBO

/-!
# The game-equivalence bound

A probabilistic discrete game `G` is game-equivalent to a random system `S` when, on each
transcript, the joint probability of the replies with the condition unset is the probability
that the condition does not hold on the queries times the probability of the transcript under
`S`. The game of `G`, with the condition as its MBO, is then conditionally equivalent to `S`
(CR18, Definition 4.19; Maurer, *Conditional Equivalence of Random Systems and
Indistinguishability Proofs*, Definition 13). By CR18, Lemma 4.16 and Theorem 4.17, each
distinguisher's advantage between the visible system of `G` and `S` is at most its winning
probability, which the blind bound on the condition bounds. The transcript distance, the
largest advantage, is therefore at most the blind winning probability of `G`.

## Main definitions

* `GameEquivalent G S`: the factorization of the game `G` through the random system `S`

## Main results

* `GameEquivalent.conditionallyEquivalent`: game equivalence is conditional equivalence
* `GameEquivalent.winProbability_behavior_le`: a bound on the condition at every admitted
  query sequence bounds the winning probability
* `GameEquivalent.transcriptDistance_le_blind`: game equivalence bounds the transcript distance
  by blind winning
-/

namespace SystemAlgebra

open Classical Probability

/-- **Game equivalence**: on each transcript, the replies with the condition unset factor
through `S`. -/
def GameEquivalent {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y}
    (G : PDG X Y D) (S : RandomSystem X Y D) : Prop :=
  ∀ h, G.goodProbability h = (1 - G.badProbability (h.map Prod.fst)) * S h

namespace GameEquivalent

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {G : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)} (hG : G.isProbDist)
  (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
  {S : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}

include hE' in
/-- **Game equivalence is conditional equivalence**: the game of a probabilistic discrete game
equivalent to a random system is conditionally equivalent to it. -/
theorem conditionallyEquivalent (equiv : GameEquivalent G S) :
    (G.behavior hG).ConditionallyEquivalent S := by
  intro h
  rcases List.eq_nil_or_concat h with rfl | ⟨p, z, rfl⟩
  · simp only [unsetMBOs, List.map_nil, RandomSystem.mass_nil, RandomSystem.unsetProbability_nil,
      mul_one]
  · simp only [List.concat_eq_append]
    have hfst : (unsetMBOs (p ++ [z])).map Prod.fst = (p ++ [z]).map Prod.fst := by
      simp [unsetMBOs, Function.comp_def]
    by_cases hadm : E ((p ++ [z]).map Prod.fst)
    · rw [PDG.unsetProbability_behavior hG hE' hadm, ← equiv, PDG.behavior_apply,
        PDG.goodProbability]
      apply Distribution.mass_congr
      intro g
      have hsnd : (unsetMBOs (p ++ [z])).map Prod.snd =
          ((p ++ [z]).map Prod.snd).map (tagMBO false) := by
        simp [unsetMBOs, Function.comp_def]
      rw [hfst, hsnd]
      exact DDG.replies_withMBO_unset_iff g.1 (by simp) _
    · have hS : S (p ++ [z]) = 0 :=
        S.mass_eq_zero_of_not_admitted (by simpa using hadm) z.2
      have hG0 : G.behavior hG (unsetMBOs (p ++ [z])) = 0 := by
        rw [unsetMBOs, List.map_append, List.map_singleton]
        exact (G.behavior hG).mass_eq_zero_of_not_admitted
          (by simpa [Function.comp_def] using hadm) _
      rw [hS, hG0, mul_zero]

include hE' in
/-- **A bound on the condition bounds winning**: for a probabilistic discrete game equivalent to
a random system, a bound on the condition at every admitted query sequence bounds the winning
probability of every distinguisher for its game. -/
theorem winProbability_behavior_le (equiv : GameEquivalent G S)
    (hU : (PDS.behavior G.underlying (PDG.underlying_probability hG)).RepliesAtQueriedInterface)
    (hS : S.RepliesAtQueriedInterface) {ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ xs, E xs → G.badProbability xs ≤ ε)
    (P : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).Distinguisher) :
    P.winProbability (G.behavior hG) ≤ ε := by
  refine P.winProbability_le_of_unsetProbability (PDG.repliesAtQueriedInterface_behavior hG hU)
    hS (PDG.monotoneMBO_behavior hG) (equiv.conditionallyEquivalent hG hE') fun h hh => ?_
  rcases List.eq_nil_or_concat h with rfl | ⟨p, z, rfl⟩
  · rw [List.map_nil, RandomSystem.unsetProbability_nil]
    linarith
  · simp only [List.concat_eq_append] at hh ⊢
    have hadm : E ((p ++ [z]).map Prod.fst) := by
      by_contra hd
      exact hh (S.mass_eq_zero_of_not_admitted (by simpa using hd) z.2)
    rw [PDG.unsetProbability_behavior hG hE' hadm]
    linarith [hbad _ hadm]

/-- **Game equivalence bounds the transcript distance by blind winning** (CR18, Theorem 4.17,
printed p. 109: "If for an (X, Y)-system S one can define an MBO such that Ŝ |≡ T, then [...]
∆(S, T) ≤ Γ(bŜ)"): the transcript distance between the visible system of a probabilistic
discrete game and a random system equivalent to it, both replying at the queried interface, is
at most the blind winning probability of the game. -/
theorem transcriptDistance_le_blind (equiv : GameEquivalent G S)
    (hU : (PDS.behavior G.underlying (PDG.underlying_probability hG)).RepliesAtQueriedInterface)
    (hS : S.RepliesAtQueriedInterface) :
    (PDS.behavior G.underlying (PDG.underlying_probability hG)).transcriptDistance S ≤
      ENNReal.ofReal (G.blind hE').supWinProbability := by
  -- The transcript distance is the largest advantage of a probabilistic distinguisher.
  rw [RandomSystem.transcriptDistance_eq_iSup hU hS]
  refine iSup_le fun P => ENNReal.ofReal_le_ofReal ?_
  -- The visible systems of `G` present the visible system of its game.
  rw [← PDG.visible_behavior hG]
  calc |P.probability (G.behavior hG).visible - P.probability S|
      -- CR18, Lemma 4.16: under conditional equivalence the advantage is at most winning.
      ≤ P.winProbability (G.behavior hG) :=
        P.advantage_le_winProbability (PDG.repliesAtQueriedInterface_behavior hG hU) hS
          (PDG.monotoneMBO_behavior hG) (equiv.conditionallyEquivalent hG hE')
    -- Blind winning bounds the condition at every admitted query sequence, hence winning.
    _ ≤ (G.blind hE').supWinProbability :=
        equiv.winProbability_behavior_le hG hE' hU hS
          ((hG.1.mass_nonneg _).trans (PDG.badProbability_le_blind hE' hG.1 [] (Or.inl rfl)))
          (fun xs hxs => PDG.badProbability_le_blind hE' hG.1 xs (Or.inr hxs)) P

end GameEquivalent

end SystemAlgebra
