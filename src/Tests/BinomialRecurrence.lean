module

public import Probability.Counting.BinomialRecurrence
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# Binomial recurrence bounds on signed and natural arrays

The real array has negative entries. A natural array obeys the recurrence only through `Q`,
then jumps, checking that the theorem needs no infinite extension of its hypotheses.
-/

@[expose] public section

namespace Probability.Tests.BinomialRecurrence

open Counting

/-- The negative array `u(n,k)=−2^n` meets the recurrence with `δ=1`. -/
example (Q n k : ℕ) (within : n ≤ Q) :
    -(2 : ℝ) ^ n ≤ (n.choose (k + 1) : ℝ) := by
  simpa only [one_pow, mul_one] using
    le_choose_mul_pow_of_succ_le (fun n _ => -(2 : ℝ) ^ n) (δ := 1)
      (by norm_num) (by intro k; norm_num)
      (by
        intro i _
        exact (neg_nonpos.mpr (pow_nonneg (by norm_num) i)).trans (Nat.cast_nonneg i))
      (by intro i _ j; rw [pow_succ]; linarith) within k

/-- Through time `Q`, the first column is `n` and all others are zero; later every entry jumps. -/
def finiteColumn (Q n k : ℕ) : ℕ :=
  if n ≤ Q then if k = 0 then n else 0 else n + 1

lemma finiteColumn_bound (Q n k : ℕ) (within : n ≤ Q) :
    finiteColumn Q n k ≤ n.choose (k + 1) * 0 ^ k := by
  refine le_choose_mul_pow_of_succ_le (finiteColumn Q) (δ := (0 : ℕ))
    ?_ ?_ ?_ ?_ within k
  · exact Nat.zero_le _
  · intro j
    simp only [finiteColumn, Nat.zero_le, ↓reduceIte, ite_self]
  · intro i hi
    simp only [finiteColumn, hi, ↓reduceIte, Nat.cast_id, le_refl]
  · intro i hi j
    simp only [finiteColumn, Nat.le_of_lt hi, Nat.succ_le_of_lt hi,
      Nat.add_one_ne_zero, ↓reduceIte, zero_mul, add_zero, le_refl]

/-- Zero draws force every column to zero. -/
example (k : ℕ) : finiteColumn 0 0 k = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [Nat.choose_zero_succ, zero_mul] using finiteColumn_bound 0 0 k le_rfl

/-- At `δ=0`, the first column still permits `Q`: its exponent is zero. -/
example (Q : ℕ) : finiteColumn Q Q 0 ≤ Q := by
  simpa only [Nat.zero_add, Nat.choose_one_right, pow_zero, mul_one] using
    finiteColumn_bound Q Q 0 le_rfl

/-- A column indexed by at least `Q` has order greater than the number of draws. -/
example (Q k : ℕ) (beyond : Q ≤ k) : finiteColumn Q Q k = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le beyond), zero_mul] using
    finiteColumn_bound Q Q k le_rfl

#print axioms le_choose_mul_pow_of_succ_le
#print axioms finiteColumn_bound

end Probability.Tests.BinomialRecurrence
