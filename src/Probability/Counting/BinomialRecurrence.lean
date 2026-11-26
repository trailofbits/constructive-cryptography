module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Ring

/-!
# A finite Pascal recurrence bound

`le_choose_mul_pow_of_succ_le` bounds an array by `choose(n,k+1) δ^k` when its first
column is at most `n` and each other entry grows by at most `δ` times its previous neighbor.
The comparison uses only rows through a selected horizon `Q`; array entries may be negative.

For adaptive occupancy, the entries are expected counts of monochromatic subsets. The
probability argument supplies the recurrence; this module supplies its binomial solution.
-/

@[expose] public section

namespace Probability.Counting

/-- A Pascal-type upper recurrence gives `u(n,k) ≤ choose(n,k+1) δ^k`. -/
theorem le_choose_mul_pow_of_succ_le
    -- `R` carries the ordered arithmetic; no positivity of the array entries is assumed.
    {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    -- `u n k` is the entry at time `n` and column `k`; only times up to `Q` are constrained.
    (u : ℕ → ℕ → R) {Q : ℕ} {δ : R} (nonnegative : 0 ≤ δ)
    (initial : ∀ k, u 0 k ≤ 0) (first : ∀ n ≤ Q, u n 0 ≤ (n : R))
    -- Each next entry is bounded by its old value plus `δ` times the column to its left.
    (growth : ∀ n < Q, ∀ k, u (n + 1) (k + 1) ≤ u n (k + 1) + δ * u n k)
    {n : ℕ} (within : n ≤ Q) (k : ℕ) :
    u n k ≤ (n.choose (k + 1) : R) * δ ^ k := by
  induction n generalizing k with
  | zero => simpa only [Nat.choose_zero_succ, Nat.cast_zero, zero_mul] using initial k
  | succ n ih =>
    cases k with
    | zero =>
      simpa only [Nat.zero_add, Nat.choose_one_right, pow_zero, mul_one] using
        first (n + 1) within
    | succ k =>
      have earlier : n ≤ Q := Nat.le_of_succ_le within
      calc
        u (n + 1) (k + 1) ≤ u n (k + 1) + δ * u n k :=
          growth n (Nat.lt_of_succ_le within) k
        _ ≤ (n.choose (k + 2) : R) * δ ^ (k + 1) +
            δ * ((n.choose (k + 1) : R) * δ ^ k) :=
          add_le_add (ih earlier (k + 1)) (mul_le_mul_of_nonneg_left (ih earlier k) nonnegative)
        -- Pascal's identity combines the two adjacent binomial coefficients.
        _ = ((n + 1).choose (k + 2) : R) * δ ^ (k + 1) := by
          rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]
          ring

end Probability.Counting
