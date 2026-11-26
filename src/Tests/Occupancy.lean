module

public import Probability.Occupancy

/-!
# Optional occupancy increments

The tests distinguish an absent draw, a fresh bin and a repeated bin. Bin types remain
arbitrary, and a signed optional law checks the exact increment's stated generality.
-/

@[expose] public section

noncomputable section

namespace Probability.Tests.Occupancy

open Distribution

/-- An absent draw preserves every positive-order count. -/
example {B : Type*} (c : B →₀ ℕ) (k : ℕ) :
    expect (Finsupp.single none 1 : Distribution (Option B))
      (fun o => ((c.addDraw o).chooseSum (k + 1) : ℝ)) = c.chooseSum (k + 1) := by
  simp only [expect, Finsupp.sum_single_index, zero_mul, one_mul, Finsupp.addDraw, Option.elim]

/-- A signed draw law `−δ_none + 2δ_b` adds twice the binomial increment at `b`. -/
example {B : Type*} (c : B →₀ ℕ) (b : B) (k : ℕ) :
    (Finsupp.single none (-1) + Finsupp.single (some b) 2 : Distribution (Option B)).expect
      (fun o => ((c.addDraw o).chooseSum (k + 1) : ℝ)) =
      (c.chooseSum (k + 1) : ℝ) + 2 * ((c b).choose k : ℝ) := by
  rw [expect_chooseSum_addDraw, weight_add, weight_single, weight_single, expect_add_left]
  simp only [expect, Finsupp.sum_single_index, zero_mul, Option.elim]
  ring

/-- A new bin creates no pair. -/
example {B : Type*} (c : B →₀ ℕ) (b : B) (fresh : c b = 0) :
    expect (Finsupp.single (some b) 1 : Distribution (Option B))
      (fun o => ((c.addDraw o).chooseSum 2 : ℝ)) = c.chooseSum 2 := by
  rw [expect_chooseSum_addDraw, weight_single]
  simp only [expect, Finsupp.sum_single_index, Option.elim, fresh,
    Nat.choose_zero_succ, Nat.cast_zero, mul_zero, mul_one, add_zero]

/-- A bin with two entries contributes two new pairs when it is drawn again. -/
example (b : ℕ) :
    expect (Finsupp.single (some b) 1 : Distribution (Option ℕ))
      (fun o => (((Finsupp.single b 2).addDraw o).chooseSum 2 : ℝ)) = 3 := by
  rw [expect_chooseSum_addDraw, weight_single]
  simp only [expect, Finsupp.sum_single_index, zero_mul, Option.elim,
    Finsupp.single_eq_same, Finsupp.chooseSum]
  norm_num

/-- With probability `2/3`, bin `7` receives its third entry; otherwise there is no draw. -/
def optionalBin : Distribution (Option ℕ) :=
  Finsupp.single none (1 / 3) + Finsupp.single (some 7) (2 / 3)

/-- The expected pair count is at most `1 + (2/3) · 2 = 7/3`. -/
example : optionalBin.expect
    (fun o => (((Finsupp.single 7 2).addDraw o).chooseSum 2 : ℝ)) ≤ 7 / 3 := by
  have atom : ∀ b ∈ (Finsupp.single 7 2 : ℕ →₀ ℕ).support,
      optionalBin (some b) ≤ (2 / 3 : ℝ) := by
    intro b member
    have hb : b = 7 := (Finsupp.mem_support_single b 7 2).mp member |>.1
    subst b
    simp only [optionalBin, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (Option.some_ne_none 7), zero_add, le_refl]
  have bound := expect_chooseSum_addDraw_le optionalBin (Finsupp.single 7 2) 0 atom
  norm_num [optionalBin, weight_add, weight_single, Finsupp.chooseSum,
    Finsupp.sum_single_index] at bound ⊢
  exact bound

#print axioms Distribution.expect_chooseSum_addDraw
#print axioms Distribution.expect_chooseSum_addDraw_one
#print axioms Distribution.expect_chooseSum_addDraw_le

end Probability.Tests.Occupancy
