import RandomSystems.System.RandomObjects
import Probability.Counting

noncomputable section

open scoped NNReal

namespace Informalization.Examples

/-- Arithmetic used by a PRP/PRF switching proof: the permutation consistency
mass dominates the function consistency mass up to the birthday defect.

This is not itself a statement about random systems or distinguishing
advantage. -/
theorem switching_ratio_arithmetic {N q : ℕ} (hq : q ≤ N) (hN : 0 < N)
    (hε : ((q * (q - 1) : ℕ) : NNReal) / ((2 * N : ℕ) : NNReal) ≤ 1) :
    (1 - ((q * (q - 1) : ℕ) : NNReal) / ((2 * N : ℕ) : NNReal)) *
        (((N - q).factorial : NNReal) / (N.factorial : NNReal)) ≤
      1 / (N : NNReal) ^ q := by
  exact Probability.Counting.switching_ratio_le hq hN hε

/-- The scalar birthday inequality consumed by a switching proof.

This theorem deliberately does not carry the name `urf_urp_switching`: it
contains no PDS, query filter, or distinguishing advantage. -/
theorem birthday_bound_arithmetic {N q : ℕ} (hq : q ≤ N) (hN : 0 < N) :
    1 - (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
  exact Probability.Counting.birthday_bound hq hN

#print axioms birthday_bound_arithmetic

end Informalization.Examples
