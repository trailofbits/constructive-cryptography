module

public import Probability.Counting.BinomialSum

/-!
# Finite occupancy count laws

An arbitrary bin carrier tests fresh and already occupied bins. The first-order law counts
every new entry once; a symbolic heavy bin supplies a witness without enumerating bins.
-/

@[expose] public section

namespace Probability.Tests.BinomialSum

-- `B` may be infinite; the count map `c` has finite support.
variable {B : Type*} (c : B →₀ ℕ) (b : B)

/-- A fresh bin creates no subset of size at least two. -/
example (fresh : c b = 0) (k : ℕ) :
    (c + Finsupp.single b 1).chooseSum (k + 2) = c.chooseSum (k + 2) := by
  rw [Finsupp.chooseSum_add_single, fresh, Nat.choose_zero_succ, add_zero]

/-- An occupied bin contributes the binomial count of its previous entries. -/
example (n k : ℕ) (count : c b = n + 1) :
    (c + Finsupp.single b 1).chooseSum (k + 1) =
      c.chooseSum (k + 1) + (n + 1).choose k := by
  rw [Finsupp.chooseSum_add_single, count]

/-- First-order binomial count is increased by one, including at an empty bin. -/
example : (c + Finsupp.single b 1).chooseSum 1 = c.chooseSum 1 + 1 := by
  simpa only [Nat.choose_zero_right] using c.chooseSum_add_single b 0

/-- A heavy-bin witness gives a nonzero binomial count over an arbitrary carrier. -/
example (m : ℕ) (positive : 0 < m) (heavy : ∃ b, m ≤ c b) : 1 ≤ c.chooseSum m := by
  obtain ⟨witness, occupied⟩ := heavy
  exact c.one_le_chooseSum_of_le positive occupied

/-- Zero draws have no within-bin subsets. -/
example (m : ℕ) : (0 : ℕ →₀ ℕ).chooseSum m = 0 := Finsupp.chooseSum_zero m

#print axioms Finsupp.chooseSum_add_single
#print axioms Finsupp.one_le_chooseSum_of_le

end Probability.Tests.BinomialSum
