module

public import Probability.PolynomialEvaluation
public import Probability.Expectation

/-!
# Affine collisions and guessing

A coefficient pair `c : R × R` represents `c.1 * x + c.2`. Distinct pairs agree at
at most one argument in an integral domain, so their collision mass is at most an atom bound
`δ`. A finite set `s` has collision mass at most `C(|s|, 2) * δ`; including one fixed guess
adds `δ`.

`mass_affine_eq_le` is the degree-one instance of the polynomial root bound.
`mass_affine_not_injOn_le_choose` uses the existing unordered-pair union bound.
The uniform corollaries replace `δ` by `1 / |R|`, and
`mass_prod_uniform_eq_or_affine_not_injOn_le` averages over an independent seed.
`expect_mass_le_of_affine_injOn_eq` transfers that bound to laws agreeing with the seed law
wherever affine evaluation is injective, using equal-total-mass event transfer.

The source counts “at most k(k + 1)/2 values x” [1, Appendix F.1, p. 27].
Here `s` counts distinct coefficient pairs, including constants.

## References

1. U. Maurer, C. Portmann, and J. Zhu. *Unifying Generic Group Models*. Cryptology ePrint
   Archive, Paper 2020/996, 2020. https://eprint.iacr.org/2020/996
-/

@[expose] public section

namespace Probability.Distribution

open Polynomial

-- `R` contains coefficients and arguments; absence of zero divisors gives the root bound.
variable {R : Type*} [CommRing R] [IsDomain R]

/-- Distinct affine expressions agree with mass at most the largest allowed atom mass. -/
lemma mass_affine_eq_le
    -- `μ` is the argument law, with nonnegative masses bounded by `δ`.
    (μ : Distribution R) (hμ : μ.NonNeg) {δ : ℝ} (hδ : 0 ≤ δ)
    (hatom : ∀ x, μ x ≤ δ)
    -- `c`, `d` are distinct slope/intercept pairs.
    {c d : R × R} (hne : c ≠ d) :
    μ.mass (fun x => c.1 * x + c.2 = d.1 * x + d.2) ≤ δ := by
  let difference : Polynomial R := C (c.1 - d.1) * X + C (c.2 - d.2)
  -- Zero coefficients would identify both slopes and both intercepts.
  have nonzero : difference ≠ 0 := by
    intro equal
    have slope := congrArg (fun p : Polynomial R => p.coeff 1) equal
    have intercept := congrArg (fun p : Polynomial R => p.coeff 0) equal
    simp only [difference, coeff_add, coeff_C_mul_X, coeff_C, coeff_zero,
      ite_true, one_ne_zero, ite_false, add_zero] at slope
    simp only [difference, coeff_add, coeff_C_mul_X, coeff_C, coeff_zero,
      zero_ne_one, ite_false, ite_true, zero_add] at intercept
    exact hne (Prod.ext (sub_eq_zero.mp slope) (sub_eq_zero.mp intercept))
  have degree : difference.natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simpa only [pow_one] using natDegree_C_mul_X_pow_le (c.1 - d.1) 1
    · rw [natDegree_C]
      exact Nat.zero_le _
  -- Apply the polynomial root bound, then the degree-one bound.
  have roots := mass_polynomial_eval_eq_zero_le μ hμ difference nonzero hδ hatom
  have event : μ.mass (fun x => c.1 * x + c.2 = d.1 * x + d.2) =
      μ.mass (fun x => difference.eval x = 0) := by
    apply mass_congr
    intro x
    simp only [difference, eval_add, eval_mul, eval_C, eval_X, sub_mul,
      sub_add_sub_comm, sub_eq_zero]
  calc
    _ = μ.mass (fun x => difference.eval x = 0) := event
    _ ≤ (difference.natDegree : ℝ) * δ := roots
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right
      (by simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr degree) hδ
    _ = δ := one_mul _

/-- A finite set of distinct coefficient pairs has collision mass at most
`C(|s|, 2) * δ` under the atom bound `δ`. -/
lemma mass_affine_not_injOn_le_choose
    -- `μ` samples the argument, and each atom has mass at most `δ`.
    (μ : Distribution R) (hμ : μ.NonNeg) {δ : ℝ} (hδ : 0 ≤ δ)
    (hatom : ∀ x, μ x ≤ δ)
    -- `s` contains the coefficient pairs; repeated expressions occur only once.
    (s : Finset (R × R)) :
    μ.mass (fun x => ¬ Set.InjOn (fun c : R × R => c.1 * x + c.2)
      (s : Set (R × R))) ≤ (s.card.choose 2 : ℝ) * δ := by
  classical
  have pairs := mass_exists_pair_le_choose μ hμ s
    (fun c d x => c.1 * x + c.2 = d.1 * x + d.2)
    (fun _ _ _ equal => equal.symm) δ
    (fun _ _ _ _ hne => mass_affine_eq_le μ hμ hδ hatom hne)
  -- Noninjectivity supplies the unordered pair charged by the union bound.
  refine (mass_mono hμ ?_).trans pairs
  intro x collision
  unfold Set.InjOn at collision
  push Not at collision
  obtain ⟨c, hc, d, hd, equal, hne⟩ := collision
  exact ⟨c, hc, d, hd, hne, equal⟩

/-- A fixed guess adds at most one atom to the affine collision bound. -/
lemma mass_eq_or_affine_not_injOn_le
    -- `μ` samples the argument, with every atom bounded by `δ`.
    (μ : Distribution R) (hμ : μ.NonNeg) {δ : ℝ} (hδ : 0 ≤ δ)
    (hatom : ∀ x, μ x ≤ δ)
    -- `s` and `guess` are fixed before this argument is sampled.
    (s : Finset (R × R)) (guess : R) :
    μ.mass (fun x => x = guess ∨
      ¬ Set.InjOn (fun c : R × R => c.1 * x + c.2) (s : Set (R × R))) ≤
        (1 + (s.card.choose 2 : ℝ)) * δ := by
  calc
    _ ≤ μ.mass (fun x => x = guess) + μ.mass (fun x =>
        ¬ Set.InjOn (fun c : R × R => c.1 * x + c.2) (s : Set (R × R))) :=
      mass_or_le hμ _ _
    _ ≤ δ + (s.card.choose 2 : ℝ) * δ :=
      add_le_add ((mass_singleton μ guess).trans_le (hatom guess))
        (mass_affine_not_injOn_le_choose μ hμ hδ hatom s)
    _ = _ := by rw [add_mul, one_mul]

-- Finiteness is needed only to sample uniformly from all of `R`.
variable [Fintype R]

/-- Two distinct affine expressions collide at a uniform argument with probability at
most `1 / |R|`. -/
lemma uniform_mass_affine_eq_le {c d : R × R} (hne : c ≠ d) :
    (uniform R).mass (fun x => c.1 * x + c.2 = d.1 * x + d.2) ≤
      1 / (Fintype.card R : ℝ) :=
  mass_affine_eq_le _ uniform_nonNeg (by positivity) (fun x => (uniform_apply x).le) hne

/-- Uniform affine evaluation fails to be injective on `s` with probability at most
`C(|s|, 2) / |R|`. -/
lemma uniform_mass_affine_not_injOn_le_choose (s : Finset (R × R)) :
    (uniform R).mass (fun x =>
      ¬ Set.InjOn (fun c : R × R => c.1 * x + c.2) (s : Set (R × R))) ≤
        (s.card.choose 2 : ℝ) / Fintype.card R := by
  simpa only [mul_one_div] using mass_affine_not_injOn_le_choose
    (uniform R) uniform_nonNeg (by positivity) (fun x => (uniform_apply x).le) s

/-- A uniform argument equals a fixed guess or collides on `s` with probability at most
`(1 + C(|s|, 2)) / |R|`. -/
lemma uniform_mass_eq_or_affine_not_injOn_le (s : Finset (R × R)) (guess : R) :
    (uniform R).mass (fun x => x = guess ∨
      ¬ Set.InjOn (fun c : R × R => c.1 * x + c.2) (s : Set (R × R))) ≤
        (1 + (s.card.choose 2 : ℝ)) / Fintype.card R := by
  simpa only [mul_one_div] using mass_eq_or_affine_not_injOn_le
    (uniform R) uniform_nonNeg (by positivity) (fun x => (uniform_apply x).le) s guess

/-- An independent seed selecting at most `M` affine expressions and one guess preserves
the uniform guessing-or-collision bound `(1 + C(M, 2)) / |R|`. -/
theorem mass_prod_uniform_eq_or_affine_not_injOn_le
    -- `Ω` carries seeds and `μ` is their normalized finite-support law.
    {Ω : Type*} (μ : ProbDist Ω)
    -- `forms ω` and `guess ω` depend on the seed, independently of the uniform argument.
    (forms : Ω → Finset (R × R)) (guess : Ω → R)
    -- `M` bounds the distinct expressions at every seed with positive mass.
    {M : ℕ} (hcard : ∀ ω ∈ μ.1.support, (forms ω).card ≤ M) :
    (prodProbDist μ 𝒰[R]).1.mass (fun ωx => ωx.2 = guess ωx.1 ∨
      ¬ Set.InjOn (fun c : R × R => c.1 * ωx.2 + c.2) (forms ωx.1 : Set (R × R))) ≤
        (1 + (M.choose 2 : ℝ)) / Fintype.card R := by
  classical
  -- The product law averages fixed-seed probabilities without conditioning the argument.
  change (prod μ.1 (uniform R)).mass (fun ωx => ωx.2 = guess ωx.1 ∨
    ¬ Set.InjOn (fun c : R × R => c.1 * ωx.2 + c.2) (forms ωx.1 : Set (R × R))) ≤ _
  rw [← expect_indicator, expect_prod_eq]
  simp only [expect_indicator]
  refine (expect_le_mul_weight μ.2.1 (c :=
    (1 + (M.choose 2 : ℝ)) / Fintype.card R) ?_).trans_eq ?_
  · intro ω hω
    exact (uniform_mass_eq_or_affine_not_injOn_le (forms ω) (guess ω)).trans
      (div_le_div_of_nonneg_right (add_le_add le_rfl
        (Nat.cast_le.mpr (Nat.choose_le_choose 2 (hcard ω hω)))) (Nat.cast_nonneg _))
  · rw [μ.2.2, mul_one]

/-- Laws agreeing with an independent seed law on injective affine evaluations inherit
the guessing bound `(1 + C(M, 2)) / |R|`. -/
theorem expect_mass_le_of_affine_injOn_eq
    -- `Ω` carries outcomes; `μ` is the reference law and `T x` is the law at secret `x`.
    {Ω : Type*} (μ : ProbDist Ω) (T : R → ProbDist Ω)
    -- Each outcome chooses coefficient pairs `forms ω` and a candidate secret `guess ω`.
    (forms : Ω → Finset (R × R)) (guess : Ω → R)
    -- Success `W x ω` requires the candidate secret to equal `x`.
    (W : R → Ω → Prop) (guessed : ∀ x ω, W x ω → x = guess ω)
    -- `same` fixes the outcome masses whenever its affine expressions remain distinct.
    (same : ∀ x ω, Set.InjOn (fun c : R × R => c.1 * x + c.2)
      (forms ω : Set (R × R)) → (T x).1 ω = μ.1 ω)
    -- `M` bounds the number of distinct expressions on the support of `μ`.
    {M : ℕ} (hcard : ∀ ω ∈ μ.1.support, (forms ω).card ≤ M) :
    (uniform R).expect (fun x => (T x).1.mass (W x)) ≤
      (1 + (M.choose 2 : ℝ)) / Fintype.card R := by
  classical
  let covered (x : R) (ω : Ω) := x = guess ω ∨
    ¬ Set.InjOn (fun c : R × R => c.1 * x + c.2) (forms ω : Set (R × R))
  have fixed (x : R) : (T x).1.mass (W x) ≤ μ.1.mass (covered x) :=
    mass_le_of_eq_on_compl (T x).1 μ.1 (T x).2.1
      (fun ω h => Or.inl (guessed x ω h)) ((T x).2.2.trans μ.2.2.symm)
      (fun ω outside => same x ω (of_not_not (fun h => outside (Or.inr h))))
  calc
    -- Transfer first at each secret, then average over the unchanged uniform law.
    _ ≤ (uniform R).expect (fun x => μ.1.mass (covered x)) :=
      expect_mono uniform_nonNeg fixed
    _ = (prod (uniform R) μ.1).mass (fun xω => covered xω.1 xω.2) := by
      symm
      rw [← expect_indicator, expect_prod_eq]
      apply congrArg (uniform R).expect
      funext x
      exact expect_indicator μ.1 (covered x)
    -- Swap the independent draws to use the seed-first guessing-or-collision bound.
    _ = (prodProbDist μ 𝒰[R]).1.mass (fun ωx => covered ωx.2 ωx.1) := by
      rw [← fTransform_swap_prod μ.1 (uniform R), mass_fTransform]
      rfl
    _ ≤ _ := mass_prod_uniform_eq_or_affine_not_injOn_le μ forms guess hcard

end Probability.Distribution
