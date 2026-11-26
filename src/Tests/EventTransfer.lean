module

public import Probability.Distribution
public import Mathlib.Tactic.NormNum

/-!
# Event transfer checks

Two laws agree outside `{0, 1}` but assign different masses inside it. The comparison
law has a negative atom, while the transfer bound for the nonnegative law is sharp.
A second pair shows why agreement alone does not replace equality of total weights.
-/

@[expose] public section

namespace Probability.Distribution.EventTransferTests

/-- `concentrated` places masses `3/4, 1/4` at `0, 2`. -/
noncomputable def concentrated : Distribution ℕ :=
  Finsupp.single 0 (3 / 4) + Finsupp.single 2 (1 / 4)

/-- `redistributed` places masses `-1/4, 1, 1/4` at `0, 1, 2`, retaining total weight one. -/
noncomputable def redistributed : Distribution ℕ :=
  Finsupp.single 0 (-1 / 4) + Finsupp.single 1 1 + Finsupp.single 2 (1 / 4)

lemma concentrated_nonNeg : concentrated.NonNeg := by
  intro n
  simp only [concentrated, Finsupp.add_apply, Finsupp.single_apply]
  split <;> split <;> norm_num

lemma equal_weight : concentrated.weight = redistributed.weight := by
  norm_num only [concentrated, redistributed, weight_add, weight_single]

lemma equal_outside (n : ℕ) (outside : ¬ (n = 0 ∨ n = 1)) :
    concentrated n = redistributed n := by
  have h0 : 0 ≠ n := Ne.symm (fun h => outside (Or.inl h))
  have h1 : 1 ≠ n := Ne.symm (fun h => outside (Or.inr h))
  simp only [concentrated, redistributed, Finsupp.add_apply, Finsupp.single_apply,
    h0, h1, ite_false, zero_add]

/-- The comparison law's negative atom is permitted by the transfer contract. -/
example : redistributed 0 < 0 := by
  norm_num [redistributed]

/-- The enlarged event has equal mass despite distinct signed atoms inside it. -/
example : concentrated.mass (fun n => n = 0 ∨ n = 1) =
    redistributed.mass (fun n => n = 0 ∨ n = 1) :=
  mass_eq_of_eq_on_compl _ _ _ equal_weight equal_outside

/-- Transfer bounds the event `{0}` by `3/4`; that is its exact mass. -/
example : concentrated.mass (fun n => n = 0) ≤ 3 / 4 := by
  have transfer := mass_le_of_eq_on_compl concentrated redistributed concentrated_nonNeg
    (P := fun n => n = 0) (Q := fun n => n = 0 ∨ n = 1)
    (fun _ h => Or.inl h) equal_weight equal_outside
  norm_num only [redistributed, mass_add, mass_single, true_or, false_or,
    ite_true, ite_false] at transfer
  exact transfer

example : concentrated.mass (fun n => n = 0) = 3 / 4 := by
  norm_num only [concentrated, mass_add, mass_single, ite_true, ite_false]

/-- Agreement outside `{0}` alone permits different event masses and total weights. -/
example :
    (∀ n : ℕ, n ≠ 0 → (Finsupp.single 0 (2 : ℝ) : Distribution ℕ) n =
      (Finsupp.single 0 (1 : ℝ) : Distribution ℕ) n) ∧
    mass (Finsupp.single 0 (2 : ℝ) : Distribution ℕ) (fun n => n = 0) >
      mass (Finsupp.single 0 (1 : ℝ) : Distribution ℕ) (fun n => n = 0) := by
  constructor
  · intro n hn
    simp only [Finsupp.single_apply, Ne.symm hn, ite_false]
  · norm_num only [mass_single, ite_true]

#print axioms mass_eq_of_eq_on
#print axioms mass_eq_of_eq_on_compl
#print axioms mass_le_of_eq_on_compl

end Probability.Distribution.EventTransferTests
