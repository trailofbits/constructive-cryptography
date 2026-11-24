module

public import Probability.Counting

/-!
# Uniform list-guessing and single-coordinate resampling

Two finite-probability laws for uniform samples:

* `uniform_mass_mem_list_le`: a uniform draw `k ←$ K` hits a candidate list `guesses` with
  probability at most `guesses.length / |K|`, counting repeated guesses at most once.
* `fTransform_update_uniform`: replacing one coordinate `i` of a uniform vector `I → Y` by an
  independent uniform draw preserves the uniform law on `I → Y`.
-/

@[expose] public section

set_option autoImplicit false

namespace Probability.Counting

/-- Repeated guesses cannot increase the fraction of uniform keys hit by a list:
`Pr_{k ← K}[k ∈ guesses] ≤ guesses.length / |K|`. -/
lemma uniform_mass_mem_list_le {K : Type*} [Fintype K] [Nonempty K] (guesses : List K) :
    (Distribution.uniform K).mass (fun k => k ∈ guesses) ≤
      guesses.length / (Fintype.card K : ℝ) := by
  classical
  rw [Distribution.uniform_mass_eq_card_filter]
  have he : Finset.univ.filter (fun k => k ∈ guesses) = guesses.toFinset := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  rw [he]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (List.toFinset_card_le _)) (by positivity)

/-- Replacing one coordinate `i` of a uniform function `I → Y` by an independent uniform value
preserves `Distribution.uniform (I → Y)`. -/
lemma fTransform_update_uniform {I Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype Y] [Nonempty Y] (i : I) :
    Distribution.fTransform (fun p : (I → Y) × Y => Function.update p.1 i p.2)
      (Distribution.uniform ((I → Y) × Y)) = Distribution.uniform (I → Y) := by
  classical
  let points (j : I) : I ⊕ Unit := if j = i then .inr () else .inl j
  have hinj : Function.Injective points := by
    intro j k he
    by_cases hj : j = i <;> by_cases hk : k = i
    · exact hj.trans hk.symm
    · simp only [points, ite_eq_left hj, ite_eq_right hk, Sum.inr_ne_inl] at he
    · simp only [points, ite_eq_right hj, ite_eq_left hk, Sum.inl_ne_inr] at he
    · simpa only [points, ite_eq_right hj, ite_eq_right hk, Sum.inl.injEq] using he
  let split := (Equiv.sumArrowEquivProdArrow I Unit Y).trans
    (Equiv.prodCongr (Equiv.refl (I → Y)) (Equiv.funUnique Unit Y))
  rw [← Distribution.fTransform_equiv_uniform split, Distribution.fTransform_fTransform]
  convert Counting.fTransform_eval_uniform_eq_uniform (Y := Y) points hinj using 1
  congr 1
  funext values j
  by_cases hj : j = i
  · subst j
    simp only [Function.comp_apply, Function.update_self, points, ite_eq_left rfl]
    rfl
  · simp only [Function.comp_apply, Function.update_of_ne hj, points, ite_eq_right hj]
    rfl

end Probability.Counting
