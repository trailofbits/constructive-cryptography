module

public import Probability.Kernel

/-!
# Branching kernels

Signed laws on `ℕ` exercise branch restriction and retained draws with a non-point fallback.
The carrier is infinite; only the laws have finite support.
-/

public section

open Probability Probability.Distribution

namespace Tests.KernelBranch

/-- Signed input weights: `μ(0) = 2`, `μ(1) = -1`. -/
noncomputable def input : Distribution ℕ :=
  Finsupp.single 0 2 + Finsupp.single 1 (-1)

/-- A signed fallback on two outcomes: `ν(42) = -3`, `ν(43) = 4`. -/
noncomputable def fallback : Distribution ℕ :=
  Finsupp.single 42 (-3) + Finsupp.single 43 4

example : bindK input (fun _ => fallback) = fallback := by
  rw [bindK_const]
  have hweight : input.weight = 1 := by
    norm_num only [input, weight_add, weight_single]
  rw [hweight, one_smul]

example : bindK input (fun a => if a = 0 then Finsupp.single (a + 10) 3
    else Finsupp.single (a + 20) (-2)) =
    Finsupp.single 10 6 + Finsupp.single 21 2 := by
  rw [bindK_ite_eq_add_restrict]
  norm_num only [input, restrict, Finsupp.filter_add, Finsupp.filter_single_of_pos,
    Finsupp.filter_single_of_neg,
    bindK_single, bindK_zero, bindK_add, Finsupp.smul_single, smul_eq_mul, add_zero, zero_add]

example : bindK input (fun a => if a = 0 then Finsupp.single a 1 else fallback) =
    Finsupp.single 0 2 + (-1 : ℝ) • fallback := by
  rw [bindK_ite_single]
  norm_num only [input, restrict, mass_add, mass_single, Finsupp.filter_add,
    Finsupp.filter_single_of_pos,
    Finsupp.filter_single_of_neg,
    weight_add, weight_single, ↓reduceIte, add_zero, zero_add]

#print axioms bindK_const
#print axioms bindK_ite_eq_add_restrict
#print axioms bindK_ite_single
#print axioms ProbDist.bind_const

end Tests.KernelBranch
