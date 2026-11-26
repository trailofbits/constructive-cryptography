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

For evolving state laws, `expect_chooseSum_le` iterates these increments through the finite
Pascal recurrence. `mass_occupancy_ge_le` then bounds a heavy-bin event by its binomial
count. State types may vary with time; the bin carrier needs no finiteness assumption.
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

/-! ## Adaptive kernels -/

section Adaptive

variable
    -- `A i` carries the state at time `i`; `B` is the arbitrary bin carrier.
    {A : ℕ → Type*} {B : Type*}
    -- `μ i` is the state law, and `K i s` chooses its next state conditionally on `s`.
    (μ : (i : ℕ) → ProbDist (A i)) (K : (i : ℕ) → A i → ProbDist (A (i + 1)))
    -- `counts i s` records bin occupancies; `draw i s t` names the optional new bin.
    (counts : (i : ℕ) → A i → B →₀ ℕ)
    (draw : (i : ℕ) → A i → A (i + 1) → Option B) {Q : ℕ}
    -- The evolution and count updates need hold only through the selected horizon `Q`.
    (evolution : ∀ i < Q, (μ (i + 1)).1 = bindK (μ i).1 (fun s => (K i s).1))
    (initial : ∀ s ∈ (μ 0).1.support, counts 0 s = 0)
    (increment : ∀ i < Q, ∀ s ∈ (μ i).1.support, ∀ t ∈ (K i s).1.support,
      counts (i + 1) t = (counts i s).addDraw (draw i s t))

include evolution initial increment in
/-- At most one entry per transition gives expected total occupancy at most the horizon. -/
lemma expect_chooseSum_one_le {n : ℕ} (within : n ≤ Q) :
    (μ n).1.expect (fun s => ((counts n s).chooseSum 1 : ℝ)) ≤ n := by
  induction n with
  | zero =>
    calc
      _ = (μ 0).1.expect 0 := expect_congr_of_support fun s hs => by
        simp only [initial s hs, Finsupp.chooseSum_zero, Nat.cast_zero, Pi.zero_apply]
      _ ≤ (0 : ℕ) := by rw [expect_zero_right, Nat.cast_zero]
  | succ n ih =>
    have hn : n < Q := Nat.lt_of_succ_le within
    -- Each conditional draw contributes its probability of being present, at most one.
    have growth (s : A n) (hs : s ∈ (μ n).1.support) :
        (K n s).1.expect (fun t => ((counts (n + 1) t).chooseSum 1 : ℝ)) ≤
          ((counts n s).chooseSum 1 : ℝ) + 1 := by
      calc
        _ = (K n s).1.expect
            (fun t => (((counts n s).addDraw (draw n s t)).chooseSum 1 : ℝ)) :=
          expect_congr_of_support fun t ht => by rw [increment n hn s hs t ht]
        _ = (fTransform (draw n s) (K n s).1).expect
            (fun o => (((counts n s).addDraw o).chooseSum 1 : ℝ)) :=
          (expect_fTransform (K n s).1 (draw n s)
            (fun o => (((counts n s).addDraw o).chooseSum 1 : ℝ))).symm
        _ ≤ _ := by
          rw [expect_chooseSum_addDraw_one, weight_fTransform, (K n s).2.2, mul_one]
          exact add_le_add le_rfl
            ((mass_le_weight ((K n s).2.1.fTransform _) _).trans_eq
              ((weight_fTransform _ _).trans (K n s).2.2))
    calc
      _ = (μ n).1.expect (fun s =>
          (K n s).1.expect (fun t => ((counts (n + 1) t).chooseSum 1 : ℝ))) := by
        rw [evolution n hn, expect_bindK]
      _ ≤ (μ n).1.expect (fun s => ((counts n s).chooseSum 1 : ℝ) + 1) :=
        expect_mono_of_support (μ n).2.1 growth
      _ ≤ (n + 1 : ℕ) := by
        rw [expect_add_right', expect_const, (μ n).2.2, mul_one, Nat.cast_add, Nat.cast_one]
        exact add_le_add (ih (Nat.le_of_succ_le within)) le_rfl

include evolution initial increment in
/-- Adaptive draws with occupied-bin atoms at most `δ` have binomial moment
`𝔼[∑_b choose(count_b,k+1)] ≤ choose(n,k+1) δ^k`. -/
theorem expect_chooseSum_le
    -- `δ` bounds only bins already occupied in the current state.
    {δ : ℝ} (nonnegative : 0 ≤ δ)
    (atom : ∀ i < Q, ∀ s ∈ (μ i).1.support, ∀ b ∈ (counts i s).support,
      (K i s).1.mass (fun t => draw i s t = some b) ≤ δ)
    {n : ℕ} (within : n ≤ Q) (k : ℕ) :
    (μ n).1.expect (fun s => ((counts n s).chooseSum (k + 1) : ℝ)) ≤
      (n.choose (k + 1) : ℝ) * δ ^ k := by
  apply Counting.le_choose_mul_pow_of_succ_le
    (fun i j => (μ i).1.expect (fun s => ((counts i s).chooseSum (j + 1) : ℝ)))
    nonnegative ?_ ?_ ?_ within k
  · intro j
    calc
      _ = (μ 0).1.expect 0 := expect_congr_of_support fun s hs => by
        simp only [initial s hs, Finsupp.chooseSum_zero, Nat.cast_zero, Pi.zero_apply]
      _ ≤ 0 := by rw [expect_zero_right]
  · exact fun i hi => expect_chooseSum_one_le μ K counts draw evolution initial increment hi
  · intro i hi j
    -- Average the conditional Pascal increment, using only supported transitions.
    calc
      _ = (μ i).1.expect (fun s =>
          (K i s).1.expect (fun t => ((counts (i + 1) t).chooseSum (j + 2) : ℝ))) := by
        rw [evolution i hi, expect_bindK]
      _ ≤ (μ i).1.expect (fun s => ((counts i s).chooseSum (j + 2) : ℝ) +
          δ * ((counts i s).chooseSum (j + 1) : ℝ)) := by
        apply expect_mono_of_support (μ i).2.1
        intro s hs
        calc
          _ = (K i s).1.expect
              (fun t => (((counts i s).addDraw (draw i s t)).chooseSum (j + 2) : ℝ)) :=
            expect_congr_of_support fun t ht => by rw [increment i hi s hs t ht]
          _ = (fTransform (draw i s) (K i s).1).expect
              (fun o => (((counts i s).addDraw o).chooseSum (j + 2) : ℝ)) :=
            (expect_fTransform (K i s).1 (draw i s)
              (fun o => (((counts i s).addDraw o).chooseSum (j + 2) : ℝ))).symm
          _ ≤ _ := by
            simpa only [weight_fTransform, (K i s).2.2, mul_one] using
              expect_chooseSum_addDraw_le (fTransform (draw i s) (K i s).1) (counts i s) j
                (fun b hb => (fTransform_apply_eq_mass _ _ _).trans_le (atom i hi s hs b hb))
      _ = _ := by rw [expect_add_right', expect_const_mul]

include evolution initial increment in
/-- Among `Q` adaptive optional draws, a bin reaches `m > 0` entries with probability
at most `choose(Q,m) δ^(m−1)`. -/
theorem mass_occupancy_ge_le
    -- The atom bound is needed only for previously occupied bins, on supported states.
    {δ : ℝ} (nonnegative : 0 ≤ δ)
    (atom : ∀ i < Q, ∀ s ∈ (μ i).1.support, ∀ b ∈ (counts i s).support,
      (K i s).1.mass (fun t => draw i s t = some b) ≤ δ)
    -- `m` is the positive occupancy threshold; `Q` is the number of opportunities to draw.
    {m : ℕ} (positive : 0 < m) :
    (μ Q).1.mass (fun s => ∃ b, m ≤ counts Q s b) ≤
      (Q.choose m : ℝ) * δ ^ (m - 1) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  calc
    _ = (μ Q).1.expect (fun s => if ∃ b, k + 1 ≤ counts Q s b then 1 else 0) :=
      (expect_indicator _ _).symm
    -- A heavy bin contributes at least one subset of the required size.
    _ ≤ (μ Q).1.expect (fun s => ((counts Q s).chooseSum (k + 1) : ℝ)) := by
      apply expect_mono (μ Q).2.1
      intro s
      split_ifs with heavy
      · obtain ⟨b, hb⟩ := heavy
        exact_mod_cast Finsupp.one_le_chooseSum_of_le (counts Q s) (Nat.succ_pos k) hb
      · exact Nat.cast_nonneg _
    _ ≤ _ := by
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        expect_chooseSum_le μ K counts draw evolution initial increment nonnegative atom le_rfl k

end Adaptive

end Probability.Distribution
