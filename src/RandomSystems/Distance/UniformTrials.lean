module

public import RandomSystems.Distance.SignedObservation

/-!
# A uniform choice among observer trials

A trial occupies a slot even if another slot contains the same observer. With `N > 0`
slots, pick one uniformly and run its observer for the entire interaction. Vacant slots run
a supplied padding observer. If it has zero signed gap, multiplying the mixed gap by `N`
gives the sum of occupied trial gaps. At `N = 0` the observer is the padding itself.
-/

@[expose] public section

namespace SystemAlgebra.Domain.Distinguisher

open Probability Distribution

variable {I : Type} [Fintype I] {X Y : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

/-- Select one slot uniformly. `occupied` identifies the trials to run; the remaining
slots and the empty family run `padding`. -/
noncomputable def uniformTrials (padding : 𝒟.Distinguisher) {N : ℕ}
    (occupied : Finset (Fin N)) (trials : Fin N → 𝒟.Distinguisher) : 𝒟.Distinguisher :=
  match N, occupied, trials with
  | 0, _, _ => padding
  | n + 1, slots, family => 𝒰[Fin (n + 1)].bind (fun i => if i ∈ slots then family i else padding)

/-- Multiplying the signed gap by the number of slots counts each occupied slot once. -/
theorem signedGap_uniformTrials (padding : 𝒟.Distinguisher) {N : ℕ}
    (occupied : Finset (Fin N)) (trials : Fin N → 𝒟.Distinguisher)
    -- The padding observer decides with the same probability on the two systems.
    (R S : RandomSystem _ _ 𝒟) (zeroGap : padding.signedGap R S = 0) :
    (N : ℝ) * (uniformTrials padding occupied trials).signedGap R S =
      ∑ i ∈ occupied, (trials i).signedGap R S := by
  cases N with
  | zero =>
    rw [Subsingleton.elim occupied ∅]
    simp only [Nat.cast_zero, zero_mul, Finset.sum_empty]
  | succ n =>
    -- Average the signed gaps before taking any absolute value.
    rw [uniformTrials, signedGap_bind, Distribution.expect_eq_sum, Finset.mul_sum]
    calc
      _ = ∑ i : Fin (n + 1), if i ∈ occupied then (trials i).signedGap R S else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [ProbDist.uniform, uniform_apply, Fintype.card_fin, ← mul_assoc]
        rw [mul_one_div_cancel (by positivity : (↑(n + 1) : ℝ) ≠ 0), one_mul]
        by_cases hi : i ∈ occupied
        · simp only [hi, ite_true]
        · simp only [hi, ite_false, zeroGap]
      _ = _ := Finset.sum_ite_mem_eq _ _

/-- Every support property common to the padding and occupied trials survives the mixture.
For a query budget, take `P d` to bound the queries of the deterministic observer `d`. -/
lemma uniformTrials_support (padding : 𝒟.Distinguisher) {N : ℕ}
    (occupied : Finset (Fin N)) (trials : Fin N → 𝒟.Distinguisher)
    -- `d` is one complete deterministic observer compatible with the domain.
    (P : {d : DDD I X Y // IsDDD d ∧ 𝒟.DecisionCompatible d} → Prop)
    (paddingBound : ∀ d ∈ padding.1.support, P d)
    (trialsBound : ∀ i ∈ occupied, ∀ d ∈ (trials i).1.support, P d) :
    ∀ d ∈ (uniformTrials padding occupied trials).1.support, P d := by
  cases N with
  | zero => exact paddingBound
  | succ n =>
    intro d hd
    -- A supported observer comes from the one selected slot.
    obtain ⟨i, _, hi⟩ := Distribution.mem_support_bindK (μ := 𝒰[Fin (n + 1)].1)
      (f := fun i => (if i ∈ occupied then trials i else padding).1) hd
    by_cases selected : i ∈ occupied
    · exact trialsBound i selected d (by simpa only [selected, ite_true] using hi)
    · exact paddingBound d (by simpa only [selected, ite_false] using hi)

end SystemAlgebra.Domain.Distinguisher
