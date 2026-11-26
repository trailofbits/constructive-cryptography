module

public import Probability.PolynomialEvaluation
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Polynomial root probabilities

A nonuniform law on `ℤ` checks that neither a field nor a finite carrier is required.
Uniform prime-field sampling gives the usual degree-over-cardinality bound.
-/

@[expose] public section

namespace Probability.Distribution.Tests

open Polynomial

/-- Draw `0`, `1`, `2` with respective masses `2/5`, `2/5`, `1/5`. -/
noncomputable def biasedInteger : Distribution ℤ :=
  Finsupp.single 0 (2 / 5) + Finsupp.single 1 (2 / 5) + Finsupp.single 2 (1 / 5)

lemma biasedInteger_nonNeg : biasedInteger.NonNeg := by
  intro x
  simp only [biasedInteger, Finsupp.add_apply, Finsupp.single_apply]
  split <;> split <;> split <;> norm_num

lemma biasedInteger_apply_le (x : ℤ) : biasedInteger x ≤ 2 / 5 := by
  by_cases h0 : x = 0
  · subst x
    norm_num [biasedInteger]
  · by_cases h1 : x = 1
    · subst x
      norm_num [biasedInteger]
    · by_cases h2 : x = 2
      · subst x
        norm_num [biasedInteger]
      · simp only [biasedInteger, Finsupp.add_apply, Finsupp.single_apply,
          Ne.symm h0, Ne.symm h1, Ne.symm h2]
        norm_num

/-- A quadratic over the integers inherits the probability bound from its root count. -/
example (p : Polynomial ℤ) (hp : p ≠ 0) (hdegree : p.natDegree = 2) :
    biasedInteger.mass (fun x => p.eval x = 0) ≤ 4 / 5 := by
  have bound := mass_polynomial_eval_eq_zero_le biasedInteger biasedInteger_nonNeg p hp
    (show (0 : ℝ) ≤ 2 / 5 by norm_num) biasedInteger_apply_le
  calc
    _ ≤ (p.natDegree : ℝ) * (2 / 5) := bound
    _ = 4 / 5 := by rw [hdegree]; norm_num

/-- Comparing `X` with the constant `1` gives the sharp bound for the heavier atom. -/
example : biasedInteger.mass (fun x => x = 1) ≤ 2 / 5 := by
  have bound := mass_polynomial_eval_eq_le biasedInteger biasedInteger_nonNeg
    X (C 1) (X_ne_C 1) (show (0 : ℝ) ≤ 2 / 5 by norm_num) biasedInteger_apply_le
  simpa only [eval_X, eval_C, natDegree_X_sub_C, Nat.cast_one, one_mul] using bound

/-- Uniform sampling specializes the atom bound to the reciprocal field cardinality. -/
example (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    (uniform (ZMod p)).mass (fun x => f.eval x = 0) ≤ (f.natDegree : ℝ) / p := by
  have bound := mass_polynomial_eval_eq_zero_le (uniform (ZMod p)) uniform_nonNeg f hf
    (show (0 : ℝ) ≤ 1 / Fintype.card (ZMod p) by positivity)
    (fun x => (uniform_apply x).le)
  simpa only [ZMod.card, mul_one_div] using bound

#print axioms mass_polynomial_eval_eq_zero_le
#print axioms mass_polynomial_eval_eq_le

end Probability.Distribution.Tests
