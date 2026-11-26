module

public import Probability.Expectation

/-!
# Supported kernel potentials

The law `μᵢ = δ₀ + 2⁻ⁱδ₁` follows a state-dependent kernel. Its potential `V(s)=2s−1`
decreases on the support, while the same inequality fails at the unreachable state `2`.
-/

@[expose] public section

noncomputable section

namespace Probability.Tests.KernelPotential

open Distribution

/-- `law i = δ₀ + 2⁻ⁱδ₁`: mass at `0` persists, while mass at `1` halves. -/
def law (i : ℕ) : Distribution ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 ((1 / 2 : ℝ) ^ i)

/-- At `0`, stay; at `1`, retain half the mass; elsewhere, move from `s` to `s+1`. -/
def next (s : ℕ) : Distribution ℕ :=
  if s = 0 then Finsupp.single 0 1
  else if s = 1 then Finsupp.single 1 (1 / 2) else Finsupp.single (s + 1) 1

/-- `potential s = 2s−1`, including its negative value at `s=0`. -/
def potential (s : ℕ) : ℝ := 2 * s - 1

/-- Both surviving atoms have nonnegative mass. -/
lemma law_nonneg (i : ℕ) : (law i).NonNeg := by
  intro s
  simp only [law, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> positivity

/-- One kernel application preserves the mass at `0` and halves the mass at `1`. -/
lemma law_succ (i : ℕ) : law (i + 1) = bindK (law i) next := by
  simp only [law, bindK_add, bindK_single, next, Nat.one_ne_zero, ↓reduceIte, one_smul,
    Finsupp.smul_single, smul_eq_mul, pow_succ]

/-- Only `0` and `1` are reachable under `law i`. -/
lemma eq_zero_or_one_of_mem_support (i s : ℕ) (supported : s ∈ (law i).support) :
    s = 0 ∨ s = 1 := by
  by_cases zero : s = 0
  · exact Or.inl zero
  apply Or.inr
  by_contra one
  apply Finsupp.mem_support_iff.mp supported
  simp [law, zero, one]

/-- The conditional expected potential decreases at each reachable state. -/
lemma next_decrease (i s : ℕ) (supported : s ∈ (law i).support) :
    (next s).expect potential ≤ potential s := by
  rcases eq_zero_or_one_of_mem_support i s supported with rfl | rfl <;>
    norm_num [next, potential, expect, Finsupp.sum_single_index]

/-- Drift fails at `2`, so the global conditional hypothesis would reject this example. -/
example : ¬ (next 2).expect potential ≤ potential 2 := by
  norm_num [next, potential, expect, Finsupp.sum_single_index]

/-- Support-local drift gives the comparison between any two times. -/
example {m n : ℕ} (times : m ≤ n) :
    (law n).expect potential ≤ (law m).expect potential :=
  expect_antitone_of_bindK law law_nonneg (fun _ => next) law_succ
    (fun _ => potential) next_decrease times

/-- The same kernel decreases `W(s)=s`, which dominates the event indicator on the support. -/
example (n : ℕ) : (law n).mass (fun s => s = 1) ≤ 1 := by
  have decrease (i s : ℕ) (supported : s ∈ (law i).support) :
      (next s).expect (fun t => (t : ℝ)) ≤ s := by
    rcases eq_zero_or_one_of_mem_support i s supported with rfl | rfl <;>
      norm_num [next, expect, Finsupp.sum_single_index]
  calc
    _ = (law n).expect (fun s => if s = 1 then 1 else 0) :=
      (expect_indicator _ _).symm
    _ ≤ (law n).expect (fun s => (s : ℝ)) := by
      apply expect_mono_of_support (law_nonneg n)
      intro s supported
      rcases eq_zero_or_one_of_mem_support n s supported with rfl | rfl <;> norm_num
    _ ≤ (law 0).expect (fun s => (s : ℝ)) :=
      expect_antitone_of_bindK law law_nonneg (fun _ => next) law_succ
        (fun _ s => (s : ℝ)) decrease (Nat.zero_le n)
    _ = 1 := by
      rw [law, expect_add_left]
      norm_num [expect, Finsupp.sum_single_index]

/-- The state carrier can grow with time: `Fin (i+1)` embeds into `Fin (i+2)`. -/
example : Antitone (fun i : ℕ =>
    Distribution.expect (Finsupp.single (0 : Fin (i + 1)) 1)
      (fun s => (s.val : ℝ))) := by
  apply expect_antitone_of_bindK
    (K := fun _ s => Finsupp.single s.castSucc 1)
  case nonnegative =>
    intro i s
    simp only [Finsupp.single_apply]
    split <;> norm_num
  case evolution =>
    intro i
    rw [bindK_single, one_smul]
    rfl
  case decrease =>
    intro i s _
    simp only [expect, Finsupp.sum_single_index, zero_mul, one_mul, Fin.val_castSucc]
    exact le_rfl

#print axioms Distribution.expect_mono_of_support
#print axioms Distribution.expect_mono
#print axioms Distribution.expect_antitone_of_bindK
#print axioms law_succ
#print axioms next_decrease

end Probability.Tests.KernelPotential
