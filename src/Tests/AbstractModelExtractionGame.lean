module

public import Commons.Definitions.AbstractModel.ExtractionGame
public import RandomSystems.Game.Transcript
public import Tests.AbstractModelExtraction

/-!
# Extraction-game scores with no ordinary queries

The existing Boolean model receives one final guess, `false`. Its retained secret is fair,
so this caller wins with probability `1/2`; point secrets give scores one and zero. The
calculation applies the generic one-query score law to the admitted final submission.
-/

@[expose] public noncomputable section

namespace Tests.AbstractModelExtractionGame

open Commons.AbstractModel SystemAlgebra Probability Probability.Distribution
open Tests.AbstractModelConverter (model)

/-- Zero ordinary calls, with the separate final guess still admitted. -/
abbrev submissionInterface : Interface := model.interface false 0

/-- Submit `false` as the guess for the retained original secret. -/
def guess : Σ i, submissionInterface.X i := ⟨.submit, false⟩

/-- Ask only the terminal submission and stop after its acknowledgment. -/
def submit : DDE (Σ i, submissionInterface.X i) (Σ i, submissionInterface.Y i) :=
  DDE.ofQueries [guess]

lemma submit_bounded : QueryBounded 1 submit := DDE.ofQueries_queryBounded [guess]

/-- The final decision is irrelevant to the game's hidden winning bit. -/
def winner : DDD submissionInterface.I submissionInterface.X submissionInterface.Y :=
  envProbe submit (fun _ => False)

lemma winner_isDDD : IsDDD winner := envProbe_isDDD submit_bounded

/-- In this zero-ordinary-query test, the supplied joint law scores exactly its false secrets. -/
lemma winning_probability (D : ProbDist (Unit × Bool)) :
    (model.extractionGame false 0 D).1.1.winProbability winner winner_isDDD =
      D.1.mass (fun z => z.2 = false) := by
  have score := PDG.winProbability_behavior_ofQueries_singleton
    (model.extractionPDG false 0 D).1 (model.extractionPDG false 0 D).2 guess
    Tests.AbstractModelExtraction.zero_query_extraction.1 (fun _ => False)
  refine score.trans ?_
  rw [PDG.badProbability, extractionPDG, ProbDist.map_val, mass_fTransform]
  apply mass_congr
  intro z
  change some false = some z.2 ↔ z.2 = false
  simp only [Option.some.injEq, eq_comm]

/-- One fair retained secret gives an immediate fixed guess success probability `1/2`. -/
example :
    (model.extractionGame false 0 (𝒰[Bool].map fun x => ((), x))).1.1.winProbability
      winner winner_isDDD = 1 / 2 := by
  rw [winning_probability, ProbDist.map_val, mass_fTransform]
  simp only [ProbDist.uniform, mass_singleton, uniform_apply, Fintype.card_bool, Nat.cast_ofNat]

example : (model.extractionGame false 0 (ProbDist.single ((), false))).1.1.winProbability
    winner winner_isDDD = 1 := by
  rw [winning_probability]
  simp only [ProbDist.single, mass_single, ite_true]

example : (model.extractionGame false 0 (ProbDist.single ((), true))).1.1.winProbability
    winner winner_isDDD = 0 := by
  rw [winning_probability]
  simp only [ProbDist.single, mass_single, Bool.true_eq_false, ite_false]

#print axioms Commons.AbstractModel.extractionSystem_presents
#print axioms Commons.AbstractModel.extractionGame_visible
#print axioms SystemAlgebra.PDG.winProbability_behavior_ofQueries_singleton
#print axioms winning_probability

end Tests.AbstractModelExtractionGame
