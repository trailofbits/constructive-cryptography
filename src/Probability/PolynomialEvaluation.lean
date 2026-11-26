module

public import Probability.Distribution
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial evaluation under an atom bound

If every atom of a nonnegative finite-support law has mass at most `δ`, a nonzero
polynomial vanishes with mass at most `degree · δ`. The carrier may be any integral domain.

`mass_polynomial_eval_eq_zero_le` combines the polynomial root bound with the finite union
bound. `mass_polynomial_eval_eq_le` applies it to the difference of two polynomials;
affine collisions are the degree-one case.
-/

@[expose] public section

namespace Probability.Distribution

/-- A nonzero polynomial of degree `d` vanishes with mass at most `d * δ` when each atom
has mass at most `δ`. -/
theorem mass_polynomial_eval_eq_zero_le
    -- `R` carries polynomial coefficients and sampled arguments; it has no zero divisors.
    {R : Type*} [CommRing R] [IsDomain R]
    -- `μ` is a finite-support law; normalization is not required.
    (μ : Distribution R) (hμ : μ.NonNeg)
    -- `p` is the tested polynomial; `hp` excludes the polynomial that vanishes everywhere.
    (p : Polynomial R) (hp : p ≠ 0)
    -- `δ` bounds the mass of every possible argument, including roots of `p`.
    {δ : ℝ} (hδ : 0 ≤ δ) (hatom : ∀ x, μ x ≤ δ) :
    μ.mass (fun x => p.eval x = 0) ≤ (p.natDegree : ℝ) * δ := by
  classical
  calc
    -- Every zero is among the finitely many distinct roots.
    _ ≤ μ.mass (fun x => ∃ r ∈ p.roots.toFinset, x = r) :=
      mass_mono hμ (fun x hx =>
        ⟨x, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hx), rfl⟩)
    -- Charge at most one atom for each distinct root.
    _ ≤ ∑ r ∈ p.roots.toFinset, μ.mass (fun x => x = r) :=
      mass_exists_le hμ _ _
    _ ≤ ∑ _ ∈ p.roots.toFinset, δ :=
      Finset.sum_le_sum (fun r _ => (mass_singleton μ r).trans_le (hatom r))
    _ = (p.roots.toFinset.card : ℝ) * δ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    -- Distinct roots are no more numerous than roots counted with multiplicity.
    _ ≤ (p.natDegree : ℝ) * δ :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
        ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))) hδ

/-- Distinct polynomials agree only at roots of their difference, with mass at most
`natDegree (p - q) * δ` under the atom bound `δ`. -/
lemma mass_polynomial_eval_eq_le
    -- `R` carries coefficients and arguments; `μ` is their nonnegative finite-support law.
    {R : Type*} [CommRing R] [IsDomain R] (μ : Distribution R) (hμ : μ.NonNeg)
    -- `p`, `q` are distinct polynomials evaluated at the same sampled argument.
    (p q : Polynomial R) (hne : p ≠ q)
    -- `δ` bounds every atom of `μ`.
    {δ : ℝ} (hδ : 0 ≤ δ) (hatom : ∀ x, μ x ≤ δ) :
    μ.mass (fun x => p.eval x = q.eval x) ≤ ((p - q).natDegree : ℝ) * δ := by
  -- Equality of evaluations is the zero event of the difference polynomial.
  simpa only [Polynomial.eval_sub, sub_eq_zero] using
    mass_polynomial_eval_eq_zero_le μ hμ (p - q) (sub_ne_zero.mpr hne) hδ hatom

end Probability.Distribution
