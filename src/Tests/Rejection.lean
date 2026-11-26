module

public import Probability.Rejection
public import Tests.Conditioning

/-!
# Finite-trial rejection sampling

The trial law assigns masses `1/2, 1/3, 1/6` to `0, 1, 2`. Accept `0` or `1`;
the non-point fallback instead returns `7` or `9`, so exhaustion remains observable.
-/

@[expose] public section

open Probability Probability.Distribution Probability.Distribution.ConditioningTests

namespace Tests.Rejection

/-- The fallback assigns mass `1/4` to `7` and mass `3/4` to `9`, both outside acceptance. -/
noncomputable def fallback : ProbDist ℕ :=
  ⟨Finsupp.single 7 (1 / 4) + Finsupp.single 9 (3 / 4), by
    constructor
    · intro n
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split <;> split <;> norm_num
    · norm_num only [weight_add, weight_single]⟩

example : biased.rejection (fun n => n / 2 = 0) fallback 0 = fallback :=
  ProbDist.rejection_zero _ _ _

/-- Two trials fail with probability `1/36`, leaving conditional weight `35/36`. -/
example : (biased.rejection (fun n => n / 2 = 0) fallback 2).1 =
    (35 / 36 : ℝ) • (biased.conditionOn (fun n => n / 2 = 0) fallback).1 +
      (1 / 36 : ℝ) • fallback.1 := by
  rw [ProbDist.rejection_eq, first_fiber_mass]
  norm_num

/-- Exhaustion really can return an outcome outside the acceptance event. -/
example : biased.rejection (fun n => n / 2 = 0) fallback 2 7 = 1 / 144 := by
  rw [ProbDist.rejection_eq, first_fiber_mass]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have rejected : biased.conditionOn (fun n => n / 2 = 0) fallback 7 = 0 := by
    rw [ProbDist.conditionOn_apply_of_mass_ne_zero _ _ _
      (by rw [first_fiber_mass]; norm_num), first_fiber_mass]
    norm_num
  rw [rejected]
  norm_num [fallback, Finsupp.single_apply]

example (T : ℕ) : biased.rejection (fun n => n / 2 = 2) fallback T = fallback := by
  apply ProbDist.rejection_of_mass_zero
  norm_num [biased, mass_add, mass_single]

/-- If every trial is accepted, every positive trial count returns the original trial law. -/
example (T : ℕ) : biased.rejection (fun _ => True) fallback (T + 1) = biased := by
  have full : biased.1.mass (fun _ => True) = 1 := (mass_true _).trans biased.2.2
  rw [ProbDist.rejection_of_mass_one _ _ _ _ full]
  apply Subtype.ext
  have conditional := ProbDist.mass_smul_conditionOn biased (fun _ => True) fallback
  rw [full, one_smul] at conditional
  refine conditional.trans ?_
  ext n
  simp only [restrict_apply, ite_true]

/-- A fallback supported on acceptance preserves acceptance after any number of trials. -/
example (T : ℕ) (n : ℕ)
    (possible : n ∈ (biased.rejection (fun n => n / 2 = 0) (ProbDist.single 0) T).1.support) :
    n / 2 = 0 := by
  apply ProbDist.rejection_support biased _ (ProbDist.single 0) T ?_ n possible
  intro a ha
  have same : a = 0 := by
    simpa only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
      Finset.mem_singleton] using ha
  subst a
  rfl

#print axioms ProbDist.rejection
#print axioms ProbDist.mem_support_rejection
#print axioms ProbDist.rejection_support
#print axioms ProbDist.rejection_eq
#print axioms ProbDist.rejection_of_mass_zero
#print axioms ProbDist.rejection_of_mass_one

end Tests.Rejection
