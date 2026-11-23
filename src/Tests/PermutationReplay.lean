module

public import Probability.Permutation.Replay

/-! # A forward reply followed by an inverse query -/

@[expose] public section

namespace Tests.PermutationReplay

open Probability Probability.Counting

/-- After learning that false is fixed, the only fresh inverse reply to true is true. -/
example :
    (Distribution.uniform (Equiv.Perm Bool)).mass
      (fun π => (∀ z ∈ ({false} : Finset Bool), π z = z) ∧ π.symm true = true) =
    (Distribution.uniform (Equiv.Perm Bool)).mass
      (fun π => ∀ z ∈ ({false} : Finset Bool), π z = z) := by
  have replay := permutation_inverse_fresh_edge_factor (Equiv.refl Bool)
    {false} true true (by simp) (by simp)
  norm_num at replay ⊢
  exact replay

/-- After fixing `0 ↦ 0` on three points, a fresh forward query divides the mass by two. -/
example :
    (Distribution.uniform (Equiv.Perm (Fin 3))).mass
      (fun π => π 0 = 0 ∧ π 1 = 2) =
    (1 / 2 : ℝ) * (Distribution.uniform (Equiv.Perm (Fin 3))).mass (fun π => π 0 = 0) := by
  have replay := permutation_fresh_edge_factor (Equiv.refl (Fin 3)) {0} 1 2
    (by simp) (by simp)
  norm_num at replay ⊢
  exact replay

/-- Repeating an observed edge gives exactly the same event. -/
example (π : Equiv.Perm Bool) : π false = false ∧ π.symm false = false ↔ π false = false := by
  rw [π.symm_apply_eq]
  exact ⟨And.left, fun h => ⟨h, h.symm⟩⟩

/-- A conflicting reply to the recorded output has zero joint mass. -/
example : (Distribution.uniform (Equiv.Perm Bool)).mass
    (fun π => π false = false ∧ π.symm false = true) = 0 := by
  apply Distribution.mass_eq_zero_of_forall_not
  rintro π ⟨forward, inverse⟩
  have h := π.injective (forward.trans (π.symm_apply_eq.mp inverse))
  exact Bool.false_ne_true h

end Tests.PermutationReplay
