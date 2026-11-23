module

public import Probability.Permutation

/-!
# Extending a partial permutation

After `m` distinct input/output pairs have been fixed, each unused image has conditional
mass `1 / (|S| - m)` at a fresh input. The reference permutation witnesses consistency
of the recorded pairs. An inverse reply specifies the same edge in reverse.
-/

@[expose] public section

namespace Probability.Counting

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Adding one fresh input `x ∉ points` with one fresh image `y` imposes exactly one further
constraint: the joint likelihood is `1 / (|S|)_{|points| + 1}`. -/
lemma permutation_fresh_edge_mass (reference : Equiv.Perm S) (points : Finset S)
    (x y : S) (hx : x ∉ points) (hy : y ∉ points.image reference) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => (∀ z ∈ points, π z = reference z) ∧ π x = y) =
        1 / ((Fintype.card S).descFactorial (points.card + 1) : ℝ) := by
  classical
  -- Post-composition by a swap moves the fresh image while fixing every recorded reply.
  let completed := reference.trans (Equiv.swap (reference x) y)
  have hfix (z : S) (hz : z ∈ points) : completed z = reference z := by
    change Equiv.swap (reference x) y (reference z) = reference z
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he
      exact hx (reference.injective he ▸ hz)
    · intro he
      exact hy (Finset.mem_image.mpr ⟨z, hz, he⟩)
  have hnew : completed x = y := Equiv.swap_apply_left (reference x) y
  have hm := permutation_agreement_mass completed (insert x points).toList
  rw [Finset.toList_toFinset, Finset.card_insert_of_notMem hx] at hm
  refine (Distribution.mass_congr _ (fun π => ?_)).trans hm
  simp only [Finset.mem_toList, Finset.mem_insert]
  constructor
  · rintro ⟨hp, he⟩ z (rfl | hz)
    · exact he.trans hnew.symm
    · exact (hp z hz).trans (hfix z hz).symm
  · intro hp
    exact ⟨fun z hz => (hp z (Or.inr hz)).trans (hfix z hz),
      (hp x (Or.inl rfl)).trans hnew⟩

/-- **Conditional replay**: the fresh-edge likelihood is the recorded-table likelihood divided
by the unused space `|S| - |points|`. -/
lemma permutation_fresh_edge_factor (reference : Equiv.Perm S) (points : Finset S)
    (x y : S) (hx : x ∉ points) (hy : y ∉ points.image reference) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => (∀ z ∈ points, π z = reference z) ∧ π x = y) =
        (1 / (Fintype.card S - points.card : ℝ)) *
          (Distribution.uniform (Equiv.Perm S)).mass
            (fun π => ∀ z ∈ points, π z = reference z) := by
  have hm := permutation_agreement_mass reference points.toList
  simp only [Finset.mem_toList, Finset.toList_toFinset] at hm
  rw [permutation_fresh_edge_mass reference points x y hx hy, hm,
    Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub points.card_le_univ]
  rw [one_div, one_div, one_div, mul_inv]

/-- For an unused output `x` and unused input `y`, the inverse reply `π⁻¹ x = y`
fixes the same edge as the forward reply `π y = x`, at the same cost. -/
lemma permutation_inverse_fresh_edge_factor (reference : Equiv.Perm S) (points : Finset S)
    (x y : S) (hx : x ∉ points.image reference) (hy : y ∉ points) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => (∀ z ∈ points, π z = reference z) ∧ π.symm x = y) =
      (1 / (Fintype.card S - points.card : ℝ)) *
        (Distribution.uniform (Equiv.Perm S)).mass (fun π => ∀ z ∈ points, π z = reference z) := by
  convert permutation_fresh_edge_factor reference points y x hy hx using 1
  apply Distribution.mass_congr
  intro π
  rw [π.symm_apply_eq, eq_comm (a := x)]

end Probability.Counting
