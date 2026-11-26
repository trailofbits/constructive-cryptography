module

public import Probability.Permutation.Walk

/-!
# Permutation avoidance checks

Repeated requests, mixed forward/inverse requests, and an empty family at a full table
use the same joint bound. Numerical bounds use the table likelihood, without enumerating
permutations.
-/

@[expose] public section

namespace Tests.PermutationAvoidance

open Probability Probability.Counting
open scoped BigOperators

/-- Two request indices may read the same fresh edge; the union bound charges both. -/
example : (1 / 2 : ℝ) ≤
    (Distribution.uniform (Equiv.Perm (Fin 4))).mass (fun π => π 0 ≠ 1) := by
  have bound := permutation_avoid_mass_ge (Equiv.refl (Fin 4)) ∅
    (Finset.univ : Finset Bool) (fun _ => false) (fun _ => 0) (fun _ => {1})
    (by intro i _; exact Finset.notMem_empty _)
  norm_num [Finset.sum_const, Distribution.mass_true, Distribution.weight_uniform] at bound
  exact bound

/-- Given `π(0)=0`, the fresh forward and inverse replies at `1` each avoid at most `m` values. -/
example (bad : Bool → Finset (Fin 4)) (m : ℕ)
    (size : ∀ b, (bad b).card ≤ m) :
    (1 - 2 * (m : ℝ) / 3) *
        (Distribution.uniform (Equiv.Perm (Fin 4))).mass (fun π => π 0 = 0) ≤
      (Distribution.uniform (Equiv.Perm (Fin 4))).mass
        (fun π => π 0 = 0 ∧ π 1 ∉ bad false ∧ π.symm 1 ∉ bad true) := by
  have bound := permutation_avoid_mass_ge_of_card_le (Equiv.refl (Fin 4)) {0}
    (Finset.univ : Finset Bool) id (fun _ => 1) bad
    (by intro b _; cases b <;> norm_num) m (by intro b _; exact size b)
  norm_num at bound
  exact bound

/-- Forward and inverse requests share the same partial table and the same loss accounting. -/
example :
    (1 / 3 : ℝ) * (Distribution.uniform (Equiv.Perm (Fin 4))).mass (fun π => π 0 = 0) ≤
      (Distribution.uniform (Equiv.Perm (Fin 4))).mass
        (fun π => π 0 = 0 ∧ π 1 ≠ 2 ∧ π.symm 1 ≠ 2) := by
  have bound := permutation_avoid_mass_ge (Equiv.refl (Fin 4)) {0}
    (Finset.univ : Finset Bool) id (fun _ => 1) (fun _ => {2})
    (by intro b _; cases b <;> norm_num)
  norm_num [Finset.sum_const] at bound
  exact bound

/-- An empty request family is allowed even when the recorded table is full. -/
example (reference : Equiv.Perm (Fin 3)) :
    (Distribution.uniform (Equiv.Perm (Fin 3))).mass (fun π => ∀ x, π x = reference x) ≤
      (Distribution.uniform (Equiv.Perm (Fin 3))).mass (fun π => ∀ x, π x = reference x) := by
  have bound := permutation_avoid_mass_ge reference Finset.univ (∅ : Finset ℕ)
    (fun _ => false) (fun _ => 0) (fun _ => ∅)
    (by intro i hi; exact (Finset.notMem_empty i hi).elim)
  simpa only [Finset.sum_empty, sub_zero, one_mul, Finset.mem_univ, forall_const,
    Finset.notMem_empty, false_implies, and_true] using bound

/-- One recorded edge and one fresh forbidden output leave joint probability at least `1/6`. -/
example : (1 / 6 : ℝ) ≤
    (Distribution.uniform (Equiv.Perm (Fin 4))).mass (fun π => π 0 = 0 ∧ π 1 ≠ 2) := by
  have table := permutation_agreement_mass (Equiv.refl (Fin 4)) [0]
  norm_num [Nat.descFactorial] at table
  have bound := permutation_avoid_mass_ge (Equiv.refl (Fin 4)) {0} ({0} : Finset ℕ)
    (fun _ => false) (fun _ => 1) (fun _ => {2})
    (by intro i _; norm_num)
  norm_num [table] at bound
  exact bound

#print axioms permutation_avoid_mass_ge
#print axioms permutation_avoid_mass_ge_of_card_le

end Tests.PermutationAvoidance
