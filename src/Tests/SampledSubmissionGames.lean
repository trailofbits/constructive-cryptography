module

public import RandomSystems.Typed.SubmissionSampling

/-!
# Selected laws of sampled submissions

One shared bit submitted twice scores equality with probability one; independent bits score
one half. A nonuniform law on ℕ is presented on its finite support, or decoded into a Boolean
submission, without changing the selected probabilities.
-/

@[expose] public section

namespace Tests.SampledSubmissionGames

open Probability Probability.Distribution SystemAlgebra

/-- Draw one uniform bit and submit the same bit in both fields. -/
noncomputable def diagonalLaw : ProbDist (Bool × Bool) := 𝒰[Bool].map (fun b => (b, b))

/-- Retaining one draw makes the two submitted fields equal surely. -/
lemma diagonal_score :
    (TypedSolver.submission diagonalLaw).winProbability
      (TypedGame.submission {pair | pair.1 = pair.2}) = 1 := by
  rw [TypedSolver.submission_winProbability]
  change diagonalLaw.1.mass (fun pair => pair.1 = pair.2) = 1
  simp only [diagonalLaw, ProbDist.map_val, mass_fTransform, eq_self, mass_true]
  exact 𝒰[Bool].2.2

/-- Two independent uniform bits agree with probability one half. -/
lemma independent_score :
    (TypedSolver.submission (prodProbDist 𝒰[Bool] 𝒰[Bool])).winProbability
      (TypedGame.submission {pair | pair.1 = pair.2}) = 1 / 2 := by
  rw [TypedSolver.submission_winProbability, prodProbDist_uniform]
  change (Distribution.uniform (Bool × Bool)).mass (fun pair => pair.1 = pair.2) = _
  rw [mass_eq_sum]
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Distribution.uniform_apply]

/-- The selected law assigns mass `2/3` to 7 and `1/3` to 9. -/
noncomputable def biasedNat : ProbDist ℕ :=
  ⟨Finsupp.single 7 (2 / 3) + Finsupp.single 9 (1 / 3), by
    constructor
    · intro n
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> norm_num
    · rw [weight_add, weight_single, weight_single]
      norm_num⟩

/-- Finite-support presentation retains the nonuniform mass on the infinite carrier ℕ. -/
lemma finite_support_score :
    (TypedSolver.submission
      (biasedNat.onFinset biasedNat.1.support (Finset.Subset.refl _))).winProbability
      (TypedGame.submission {n | n.1 = 7}) = 2 / 3 := by
  refine (TypedSolver.submission_onFinset_winProbability biasedNat biasedNat.1.support
    (Finset.Subset.refl _) {n | n = 7}).trans ?_
  change (Finsupp.single 7 (2 / 3) + Finsupp.single 9 (1 / 3) : Distribution ℕ).mass
    (fun n => n = 7) = 2 / 3
  rw [mass_add, mass_single, mass_single]
  norm_num

/-- Decode a natural-number sample into the bit `n = 9`; acceptance has mass `1/3`. -/
example :
    (TypedSolver.submission (biasedNat.map (fun n => n == 9))).winProbability
      (TypedGame.submission {b | b = true}) = 1 / 3 := by
  rw [TypedSolver.submission_winProbability, ProbDist.map_val]
  change (fTransform (fun n => n == 9) biasedNat.1).mass (fun b => b = true) = 1 / 3
  rw [mass_fTransform]
  change (Finsupp.single 7 (2 / 3) + Finsupp.single 9 (1 / 3) : Distribution ℕ).mass _ = _
  rw [mass_add, mass_single, mass_single]
  norm_num

/-- No sampled value satisfies the empty successful set. -/
example : (TypedSolver.submission diagonalLaw).winProbability
    (TypedGame.submission (∅ : Set (Bool × Bool))) = 0 := by
  rw [TypedSolver.submission_winProbability]
  exact mass_eq_zero_of_forall_not _ (fun _ => id)

/-- Replacing a shared bit by two independent draws changes the game score. -/
example :
    (TypedSolver.submission diagonalLaw).winProbability
        (TypedGame.submission {pair | pair.1 = pair.2}) ≠
      (TypedSolver.submission (prodProbDist 𝒰[Bool] 𝒰[Bool])).winProbability
        (TypedGame.submission {pair | pair.1 = pair.2}) := by
  rw [diagonal_score, independent_score]
  norm_num

#print axioms TypedSolver.submission_winProbability
#print axioms TypedSolver.submission_onFinset_winProbability
#print axioms diagonal_score
#print axioms independent_score
#print axioms finite_support_score

end Tests.SampledSubmissionGames
