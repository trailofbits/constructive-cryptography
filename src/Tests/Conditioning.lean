module

public import Probability.Conditioning
public import Mathlib.Tactic.NormNum

/-!
# Normalized conditioning checks

A nonuniform law on `ℕ` is observed through `n ↦ n / 2`. Its first fiber has two
outcomes; an unreachable fiber returns an explicitly different fallback.
-/

@[expose] public section

namespace Probability.Distribution.ConditioningTests

/-- `biased` assigns masses `1/2, 1/3, 1/6` to `0, 1, 2`. -/
noncomputable def biased : ProbDist ℕ :=
  ⟨Finsupp.single 0 (1 / 2) + Finsupp.single 1 (1 / 3) + Finsupp.single 2 (1 / 6), by
    constructor
    · intro n
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split <;> split <;> split <;> norm_num
    · norm_num only [weight_add, weight_single]⟩

lemma first_fiber_mass : biased.1.mass (fun n => n / 2 = 0) = 5 / 6 := by
  norm_num [biased, mass_add, mass_single]

/-- The two retained atoms have conditional masses `3/5` and `2/5`. -/
example : biased.conditionOn (fun n => n / 2 = 0) (ProbDist.single 9) 0 = 3 / 5 ∧
    biased.conditionOn (fun n => n / 2 = 0) (ProbDist.single 9) 1 = 2 / 5 := by
  have nonzero : biased.1.mass (fun n => n / 2 = 0) ≠ 0 := by
    rw [first_fiber_mass]
    norm_num
  constructor <;>
    rw [ProbDist.conditionOn_apply_of_mass_ne_zero _ _ _ nonzero, first_fiber_mass] <;>
    norm_num [biased]

/-- Support is computed by the public conditional-support law. -/
example : 1 ∈ (biased.conditionOn (fun n => n / 2 = 0) (ProbDist.single 9)).1.support := by
  apply (ProbDist.mem_support_conditionOn_iff _ _ _ (by rw [first_fiber_mass]; norm_num) _).mpr
  norm_num [biased, Finsupp.mem_support_iff]

/-- The nonempty event `{n | n / 2 = 2}` is unreachable under `biased`. -/
example : biased.conditionOn (fun n => n / 2 = 2) (ProbDist.single 9) = ProbDist.single 9 := by
  apply ProbDist.conditionOn_of_mass_eq_zero
  norm_num [biased, mass_add, mass_single]

/-- Resampling the fiber retains the exact joint law of observation and latent outcome. -/
example :
    ProbDist.jointLaw (biased.map (fun n => n / 2))
        (fun b => biased.conditionOn (fun n => n / 2 = b) (ProbDist.single 9)) =
      biased.map (fun n => (n / 2, n)) :=
  ProbDist.jointLaw_conditionOn_eq_map _ _ _

/-- Disintegrate the conditioned law with a different fallback at each observation. -/
example :
    biased.conditionOn (fun n => n / 2 = 0) (ProbDist.single 9) =
      ((biased.conditionOn (fun n => n / 2 = 0) (ProbDist.single 9)).map (fun n => n % 2)).bind
        (fun b => biased.conditionOn (fun n => n / 2 = 0 ∧ n % 2 = b)
          (ProbDist.single (9 + b))) :=
  ProbDist.conditionOn_eq_bind _ _ _ (by rw [first_fiber_mass]; norm_num) _ _

/-- The uniform conditional atom uses the caller's decidable event. -/
example : ProbDist.uniformOn (fun b : Bool => b = true) (ProbDist.single false) true = 1 := by
  rw [ProbDist.uniformOn_apply_of_nonempty (fun b : Bool => b = true) ⟨true, rfl⟩]
  norm_num [Finset.filter_eq']

/-- Rescaling a positive-mass conditional law recovers its unnormalized restriction. -/
example : (5 / 6 : ℝ) • (biased.conditionOn (fun n => n / 2 = 0) (ProbDist.single 9)).1 =
    biased.1.restrict (fun n => n / 2 = 0) := by
  rw [← first_fiber_mass]
  exact ProbDist.mass_smul_conditionOn _ _ _

/-- The same equation applies at an unreachable fiber, independently of its fallback. -/
example : (0 : ℝ) • (biased.conditionOn (fun n => n / 2 = 2) (ProbDist.single 9)).1 =
    biased.1.restrict (fun n => n / 2 = 2) := by
  have null : biased.1.mass (fun n => n / 2 = 2) = 0 := by
    norm_num [biased, mass_add, mass_single]
  rw [← null]
  exact ProbDist.mass_smul_conditionOn _ _ _

#print axioms ProbDist.mass_smul_conditionOn

#print axioms ProbDist.conditionOn_eq_bind
#print axioms ProbDist.uniformOn_apply_of_nonempty

#print axioms ProbDist.conditionOn
#print axioms ProbDist.conditionOn_val_of_mass_ne_zero
#print axioms ProbDist.conditionOn_apply_of_mass_ne_zero
#print axioms ProbDist.conditionOn_of_mass_eq_zero
#print axioms ProbDist.mem_support_conditionOn_iff
#print axioms ProbDist.jointLaw_conditionOn_eq_map

end Probability.Distribution.ConditioningTests
