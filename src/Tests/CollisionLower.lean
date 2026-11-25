module

public import Probability.CollisionLower

/-!
# Tests for Cauchy–Schwarz pair and cross-collision lower bounds

* Any map into `Bool` collides on two independent uniform inputs with probability at least `1 / 2`.
* Distinct-input collisions of a map `Fin 4 → Bool` occur with probability at least `1 / 2 - 1 / 4`.
* Four independent uniform values in `Fin 4` form two equal pairs with probability `1 / 4²`.
* Cross collisions and distinct-input cross collisions between two batches of size `2` satisfy the
  second-moment lower bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.CollisionLower

open Probability Probability.Counting

/-- Any map into `Bool` collides on two independent uniform inputs with probability `≥ 1/2`. -/
example {M : Type} [Fintype M] [Nonempty M] (f : M → Bool) :
    1 / 2 ≤ ((Distribution.fTransform f (Distribution.uniform M)).prod
      (Distribution.fTransform f (Distribution.uniform M))).mass
        (fun pair => pair.1 = pair.2) := by
  simpa only [Fintype.card_bool, Nat.cast_ofNat] using pair_collision_mass_ge _
    ((Distribution.weight_fTransform f _).trans Distribution.weight_uniform)

/-- Distinct-input collisions of a map `Fin 4 → Bool` occur with probability `≥ 1/2 - 1/4`. -/
example (f : Fin 4 → Bool) :
    1 / 2 - 1 / 4 ≤ (Distribution.uniform (Fin 4 × Fin 4)).mass
      (fun pair => pair.1 ≠ pair.2 ∧ f pair.1 = f pair.2) := by
  simpa only [Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat] using
    distinct_pair_collision_mass_ge f

/-- Cross collisions between two batches of two inputs from `Fin 8` into `Bool`. -/
example (f : Fin 8 → Bool) :
    (2 : ℝ) ^ 2 / (2 * ((2 : ℝ) ^ 2 + 2)) ≤
      (Distribution.uniform ((Fin 2 → Fin 8) × (Fin 2 → Fin 8))).mass
        (fun seed => crossCount f seed ≠ 0) := by
  simpa only [Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat] using
    crossCount_nonzero_mass_ge (I := Fin 2) f

/-- Distinct-input cross collisions between two batches of two inputs from `Fin 16` into `Bool`. -/
example (f : Fin 16 → Bool) :
    (2 : ℝ) ^ 2 / (2 * ((2 : ℝ) ^ 2 + 2)) - (2 : ℝ) ^ 2 / 16 ≤
      (Distribution.uniform ((Fin 2 → Fin 16) × (Fin 2 → Fin 16))).mass
        (fun seed => ∃ i j, seed.1 i ≠ seed.2 j ∧ f (seed.1 i) = f (seed.2 j)) := by
  simpa only [Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat] using
    distinct_cross_collision_mass_ge (I := Fin 2) f

/-- Four independent uniform values in `Fin 4` form two equal pairs with probability `1 / 4²`. -/
example :
    (Distribution.uniform (Bool ⊕ Bool → Fin 4)).mass
      (fun f => f (.inl false) = f (.inl true) ∧ f (.inr false) = f (.inr true)) =
        1 / (4 : ℝ) ^ 2 := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using uniform_two_pairs_mass (T := Fin 4)

#print axioms pair_collision_mass_ge
#print axioms distinct_pair_collision_mass_ge
#print axioms Distribution.expect_sq_le_mass_ne_zero_mul_second
#print axioms crossCount_nonzero_mass_ge
#print axioms distinct_cross_collision_mass_ge

end Tests.CollisionLower
