module

public import Probability.Counting.BinomialSum
public import Probability.Counting.BinomialRecurrence
public import Probability.Expectation

/-!
# Adaptive occupancy counts

`Finsupp.addDraw c o` adds one entry to the optional bin `o`. A missing draw leaves `c`
unchanged. The binomial count `c.chooseSum m` records subsets of size `m` in one bin.

`expect_chooseSum_addDraw` averages the exact binomial increment. Its first-order form
counts the probability of making a draw; `expect_chooseSum_addDraw_le` bounds higher-order
increments by a per-bin atom bound times the previous-order binomial count.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

/-- `addDraw c none = c`; `addDraw c (some b) = c + δ_b` adds one entry to bin `b`. -/
def Finsupp.addDraw
    -- `c` is a finite count map on bins `B`; `draw` selects a bin or makes no increment.
    {B : Type*} (c : B →₀ ℕ) (draw : Option B) : B →₀ ℕ :=
  draw.elim c (fun b => c + Finsupp.single b 1)

namespace Probability.Distribution

/-- An optional draw increases the order-`k+1` binomial count by `choose(c b,k)` at its bin. -/
lemma expect_chooseSum_addDraw
    -- `P` is a finite signed law of optional bins; `c` records the counts before the draw.
    {B : Type*} (P : Distribution (Option B)) (c : B →₀ ℕ) (k : ℕ) :
    P.expect (fun o => ((c.addDraw o).chooseSum (k + 1) : ℝ)) =
      (c.chooseSum (k + 1) : ℝ) * P.weight +
        P.expect (fun o => o.elim 0 (fun b => ((c b).choose k : ℝ))) := by
  have increment (o : Option B) : ((c.addDraw o).chooseSum (k + 1) : ℝ) =
      (c.chooseSum (k + 1) : ℝ) + o.elim 0 (fun b => ((c b).choose k : ℝ)) := by
    cases o with
    | none => exact (add_zero _).symm
    | some b =>
      change ((c + Finsupp.single b 1).chooseSum (k + 1) : ℝ) =
        (c.chooseSum (k + 1) : ℝ) + ((c b).choose k : ℝ)
      rw [Finsupp.chooseSum_add_single, Nat.cast_add]
  -- Average the unchanged count and the increment separately.
  calc
    _ = P.expect (fun o => (c.chooseSum (k + 1) : ℝ) +
        o.elim 0 (fun b => ((c b).choose k : ℝ))) :=
      congrArg P.expect (funext increment)
    _ = _ := by rw [expect_add_right', expect_const]

/-- The first-order count increases by the mass of making a draw. -/
lemma expect_chooseSum_addDraw_one
    {B : Type*} (P : Distribution (Option B)) (c : B →₀ ℕ) :
    P.expect (fun o => ((c.addDraw o).chooseSum 1 : ℝ)) =
      (c.chooseSum 1 : ℝ) * P.weight + P.mass (fun o => o.isSome) := by
  rw [expect_chooseSum_addDraw]
  congr 1
  calc
    _ = P.expect (fun o => if o.isSome then (1 : ℝ) else 0) :=
      congrArg P.expect (funext fun o => by cases o <;> simp only [Option.elim,
        Nat.choose_zero_right, Nat.cast_one, Option.isSome, Bool.false_eq_true, ↓reduceIte])
    _ = _ := expect_indicator P _

/-- A per-bin atom bound controls the next higher binomial count. -/
theorem expect_chooseSum_addDraw_le
    -- `P` may have signed weights; the unchanged count retains its total weight explicitly.
    {B : Type*} (P : Distribution (Option B)) (c : B →₀ ℕ) (k : ℕ) {δ : ℝ}
    -- Only occupied bins can create a subset of size `k+2` by one new entry.
    (atom : ∀ b ∈ c.support, P (some b) ≤ δ) :
    P.expect (fun o => ((c.addDraw o).chooseSum (k + 2) : ℝ)) ≤
      (c.chooseSum (k + 2) : ℝ) * P.weight + δ * (c.chooseSum (k + 1) : ℝ) := by
  classical
  rw [expect_chooseSum_addDraw]
  apply add_le_add le_rfl
  -- Group the increment by its finitely many occupied bins.
  have grouped := expect_comp_eq_sum_mass_of_eq_zero P id
    (fun o => o.elim 0 (fun b => ((c b).choose (k + 1) : ℝ)))
    (c.support.image some) (by
      intro o outside
      cases o with
      | none => rfl
      | some b =>
        have absent : b ∉ c.support := fun h => outside (Finset.mem_image.mpr ⟨b, h, rfl⟩)
        simp only [Option.elim, Finsupp.notMem_support_iff.mp absent,
          Nat.choose_zero_succ, Nat.cast_zero])
  simp only [id_eq] at grouped
  calc
    _ = ∑ b ∈ c.support, ((c b).choose (k + 1) : ℝ) * P (some b) := by
      rw [grouped, Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)]
      simp only [Option.elim, mass_singleton]
    _ ≤ ∑ b ∈ c.support, ((c b).choose (k + 1) : ℝ) * δ :=
      Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (atom b hb) (Nat.cast_nonneg _)
    _ = δ * (c.chooseSum (k + 1) : ℝ) := by
      rw [Finsupp.chooseSum, Finsupp.sum, Nat.cast_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end Probability.Distribution
