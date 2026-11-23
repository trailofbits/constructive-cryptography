module

public import Probability.Permutation

/-! # Empty and complete observations of a uniform permutation -/

@[expose] public section

namespace Tests.PermutationRestriction

open Probability Probability.Counting

/-- With no prescribed inputs every permutation is accepted. -/
example (x y : Empty ↪ Bool) :
    (Distribution.uniform (Equiv.Perm Bool)).mass (fun π => ∀ i, π (x i) = y i) = 1 := by
  rw [permutation_constraints_mass]
  norm_num [Nat.descFactorial]

/-- Fixing both bits prescribes one of the two Boolean permutations. -/
example (x y : Bool ↪ Bool) :
    (Distribution.uniform (Equiv.Perm Bool)).mass (fun π => ∀ i, π (x i) = y i) = 1 / 2 := by
  rw [permutation_constraints_mass]
  norm_num [Fintype.card_bool, Nat.descFactorial]

/-- Recording the same Boolean input twice still costs one factor of two. -/
example (reference : Equiv.Perm Bool) :
    (Distribution.uniform (Equiv.Perm Bool)).mass
      (fun π => ∀ x ∈ [false, false], π x = reference x) = 1 / 2 := by
  rw [permutation_agreement_mass]
  norm_num [Fintype.card_bool, Nat.descFactorial]

end Tests.PermutationRestriction
