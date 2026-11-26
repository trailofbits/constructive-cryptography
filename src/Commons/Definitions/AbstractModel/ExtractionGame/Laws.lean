module

public import Commons.Definitions.AbstractModel.ExtractionGame
public import RandomSystems.Game.Transcript

/-!
# Terminal extraction scores

`extractionGame_winProbability_submit` identifies a fixed terminal guess with its mass in
the retained secret law. It applies the one-query game-score law, then reads the existing
extraction condition; no observation or computation is required.
-/

@[expose] public section

namespace Commons.AbstractModel

open Probability Probability.Distribution SystemAlgebra

/-- Submitting `guess` immediately wins exactly on the draws whose original secret is `guess`.
The caller's final decision leaves the game's hidden winning condition unchanged. -/
lemma extractionGame_winProbability_submit
    -- `M` computes with values in `S` and parameters in `P`; `ι` names registers.
    {S P ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]
    [Fintype S] [Fintype ι] [Fintype M.Operation] [Fintype M.Query]
    [∀ ρ, Fintype (M.Reply ρ)]
    -- `input` initially holds the secret; `k` permits ordinary calls before submission.
    (input : ι) (k : ℕ)
    -- `D` retains a parameter and secret together; `guess` is the submitted secret value.
    (D : ProbDist (P × S)) (guess : S)
    -- `accept` determines the caller's decision after the submission acknowledgment.
    (accept : List (M.Command ι) × List (Σ i, M.Output i) → Prop) :
    (M.extractionGame input k D).1.1.winProbability
      (envProbe (DDE.ofQueries [⟨.submit, guess⟩]) accept)
      (envProbe_isDDD (DDE.ofQueries_queryBounded
        (X := M.Command ι) (Y := Σ i, M.Output i) [⟨.submit, guess⟩])) =
        D.1.mass (fun z => z.2 = guess) := by
  have admitted : M.Admitted input k [⟨.submit, guess⟩] := by
    apply (admitted_snoc_iff input k [] ⟨.submit, guess⟩).mpr
    simp [ordinary, reads]
  have score := PDG.winProbability_behavior_ofQueries_singleton
    (M.extractionPDG input k D).1 (M.extractionPDG input k D).2
    ⟨.submit, guess⟩ admitted accept
  refine score.trans ?_
  -- The same sampled secret appears in the visible system and the extraction condition.
  rw [PDG.badProbability, extractionPDG, ProbDist.map_val, mass_fTransform]
  apply mass_congr
  intro z
  change some guess = some z.2 ↔ z.2 = guess
  simp only [Option.some.injEq, eq_comm]

end Commons.AbstractModel
