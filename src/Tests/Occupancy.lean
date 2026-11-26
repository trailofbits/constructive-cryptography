module

public import Probability.Occupancy

/-!
# Optional and adaptive occupancy counts

The tests distinguish an absent draw, a fresh bin and a repeated bin. Bin types remain
arbitrary, and a signed optional law checks the exact increment's stated generality.
A state-dependent two-draw process checks the heavy-bin bound with all contracts supplied;
a varying state carrier checks the finite-horizon interface.
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

/-! ## An adaptive two-draw process -/

/-- A false state tosses a fresh coin; a true state returns false deterministically. -/
def adaptiveKernel (s : Bool) : ProbDist Bool :=
  if s then ProbDist.single false else 𝒰[Bool]

/-- Start at false and iterate the state-dependent kernel. -/
def adaptiveLaw : ℕ → ProbDist Bool
  | 0 => ProbDist.single false
  | n + 1 => (adaptiveLaw n).bind adaptiveKernel

/-- First enter bin 7; then enter bin 7 or 8 according to the new state. -/
def adaptiveDraw : ℕ → Bool → Bool → Option ℕ
  | 0, _, _ => some 7
  | _ + 1, _, t => some (if t then 7 else 8)

/-- Counts through the two opportunities: empty, one in bin 7, then the selected second bin. -/
def adaptiveCounts : ℕ → Bool → ℕ →₀ ℕ
  | 0, _ => 0
  | 1, _ => Finsupp.single 7 1
  | _ + 2, t => Finsupp.single 7 1 + Finsupp.single (if t then 7 else 8) 1

/-- The finite-horizon update follows the same bin selected by `adaptiveDraw`. -/
lemma adaptive_increment (i : ℕ) (hi : i < 2) (s t : Bool) :
    adaptiveCounts (i + 1) t = (adaptiveCounts i s).addDraw (adaptiveDraw i s t) := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl <;>
    simp only [adaptiveCounts, adaptiveDraw, Finsupp.addDraw, Option.elim, zero_add]

/-- The repeat probability is one half after false and zero after true. -/
lemma adaptive_atom (i : ℕ) (hi : i < 2) (s : Bool) (b : ℕ)
    (occupied : b ∈ (adaptiveCounts i s).support) :
    (adaptiveKernel s).1.mass (fun t => adaptiveDraw i s t = some b) ≤ (1 / 2 : ℝ) := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · simp only [adaptiveCounts, Finsupp.support_zero, Finset.notMem_empty] at occupied
  · have hb : b = 7 := (Finsupp.mem_support_single b 7 1).mp occupied |>.1
    subst b
    cases s <;> norm_num [adaptiveKernel, adaptiveDraw, mass_eq_sum, ProbDist.uniform,
      ProbDist.single, uniform_apply, Fintype.sum_bool, Finsupp.single_apply]

/-- The adaptive second draw collides with the first with probability at most `1/2`. -/
example : (adaptiveLaw 2).1.mass (fun s => ∃ b, 2 ≤ adaptiveCounts 2 s b) ≤ 1 / 2 := by
  have bound := mass_occupancy_ge_le adaptiveLaw (fun _ => adaptiveKernel)
    adaptiveCounts adaptiveDraw
    (Q := 2) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun i hi s _ t _ => adaptive_increment i hi s t)
    (δ := 1 / 2) (by norm_num) (fun i hi s _ b hb => adaptive_atom i hi s b hb)
    (m := 2) (by norm_num)
  norm_num at bound ⊢
  exact bound

/-- Three entries cannot occur in two optional draws, including this adaptive process. -/
example : (adaptiveLaw 2).1.mass (fun s => ∃ b, 3 ≤ adaptiveCounts 2 s b) ≤ 0 := by
  have bound := mass_occupancy_ge_le adaptiveLaw (fun _ => adaptiveKernel)
    adaptiveCounts adaptiveDraw
    (Q := 2) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun i hi s _ t _ => adaptive_increment i hi s t)
    (δ := 1 / 2) (by norm_num) (fun i hi s _ b hb => adaptive_atom i hi s b hb)
    (m := 3) (by norm_num)
  norm_num at bound ⊢
  exact bound

/-- At horizon zero there is no occupied bin, even when `δ=0` and `m=1`. -/
example : (adaptiveLaw 0).1.mass (fun s => ∃ b, 1 ≤ adaptiveCounts 0 s b) ≤ 0 := by
  have bound := mass_occupancy_ge_le adaptiveLaw (fun _ => adaptiveKernel)
    adaptiveCounts adaptiveDraw
    (Q := 0) (fun i hi => (Nat.not_lt_zero i hi).elim) (fun _ _ => rfl)
    (fun i hi => (Nat.not_lt_zero i hi).elim)
    (δ := 0) le_rfl (fun i hi => (Nat.not_lt_zero i hi).elim) (m := 1) (by norm_num)
  norm_num at bound ⊢
  exact bound

/-- The state carrier may grow with time; absent draws keep every count zero. -/
example (Q : ℕ) :
    (ProbDist.single (0 : Fin (Q + 1))).1.mass
      (fun _ => ∃ b : ℕ, Q + 1 ≤ (0 : ℕ →₀ ℕ) b) ≤ 0 := by
  have evolution (i : ℕ) (_ : i < Q) :
      (ProbDist.single (0 : Fin (i + 2))).1 =
        bindK (ProbDist.single (0 : Fin (i + 1))).1
          (fun s => (ProbDist.single s.castSucc).1) := by
    simp only [ProbDist.single, bindK_single, one_smul]
    rfl
  have bound := mass_occupancy_ge_le
    (fun i => ProbDist.single (0 : Fin (i + 1)))
    (fun _ s => ProbDist.single s.castSucc)
    (fun _ _ => (0 : ℕ →₀ ℕ)) (fun _ _ _ => none)
    evolution (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
    (δ := 0) le_rfl
    (fun _ _ _ _ _ hb => (Finset.notMem_empty _ hb).elim) (m := Q + 1) (Nat.succ_pos Q)
  simpa only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self Q), Nat.cast_zero, zero_mul] using bound

#print axioms Distribution.expect_chooseSum_one_le
#print axioms Distribution.expect_chooseSum_le
#print axioms Distribution.mass_occupancy_ge_le

#print axioms Distribution.expect_chooseSum_addDraw
#print axioms Distribution.expect_chooseSum_addDraw_one
#print axioms Distribution.expect_chooseSum_addDraw_le

end Probability.Tests.Occupancy
