module

public import ConstructiveCryptography.Substitution.Reduction
public import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction
public import ConstructiveCryptography.Instances.Algebra
public import ConstructiveCryptography.Notation.Basic
public import RandomSystems.Typed.StructuredDistinguisher
public import Probability.Expectation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Signed-gap hybrid telescoping and structured distinguishers

This module extends the substitution calculus with three tools needed by multi-step hybrid
arguments without altering `TypedDistinguisher` or its global instances:

1. **0-inclusive finite hybrid chains** (`SubstitutesWithin.chain`) on any
   `DistinguisherAdvantage`.
2. **Signed-gap averaging and uniform-index telescoping hybrids** on any `Distinguishers` /
   `AdmissibleDistinguishers` model: averaging a family of step distinguishers over a finite law
   averages their signed gaps; for a uniform index `i ←$ Fin L` matching adjacent hybrid steps
   `H i` and `H (i + 1)`, the endpoint gap telescopes to `L * (Pr[B(X₀)] - Pr[B(X₁)])`, giving
   `advantage d (H 0) (H L) ≤ L * advantage B X₀ X₁` and lifting `X₀ ≃[ε] X₁` to
   `H 0 ≃[fun d => L * ε (ρ d)] H L`.
3. **Structured (non-erasing) distinguishers on `Interface`**:
   `Interface.structuredDistinguisherAdvantage` packages concrete `StructuredDistinguisher`
   (`Domain.Distinguisher`) as a `DistinguisherAdvantage` with `DominatedByDistance`, concrete
   converter absorption compatible with `TypedDistinguisher`, bidirectional bridges to
   `TypedDistinguisher` substitutions, and uniform-index `SubstitutesWithin` lifting via
   `StructuredDistinguisher.uniformChoice`.

## Main definitions

* `Distinguishers.signedGap`: signed decision gap `Pr[d(R) = 1] - Pr[d(S) = 1]`
* `SystemAlgebra.Interface.structuredDistinguisherAdvantage`: `DistinguisherAdvantage` on concrete
  `StructuredDistinguisher`
* `SystemAlgebra.Interface.structuredDistinguisherAdvantageDominated`: `DominatedByDistance` for
  concrete distinguishers

## Main results

* `CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.chain`
* `Distinguishers.signedGap_telescoping`, `signedGap_average_expect`,
  `signedGap_uniform_telescoping`, `advantage_uniform_telescoping`,
  `advantage_uniform_telescoping_le`
* `AdmissibleDistinguishers.substitutesWithin_uniform_telescoping`
* `SystemAlgebra.Interface.structuredSubstitutesWithin_attach`,
  `structuredSubstitutesWithin_of_typed`, `typedSubstitutesWithin_of_structured`,
  `structuredSubstitutesWithin_uniform_telescoping`

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. M. Bellare, R. Canetti, and H. Krawczyk. Pseudorandom Functions Revisited: The Cascade
   Construction and Its Concrete Security. FOCS 1996.
-/

@[expose] public section

set_option autoImplicit false

namespace ConstructiveCryptography

open CategoryTheory Probability
open scoped BigOperators NNReal SystemAlgebra

universe u v w x

/-! ### 0-inclusive finite hybrid chains on `DistinguisherAdvantage` -/

namespace CryptographicAlgebra.DistinguisherAdvantage

-- `C` contains interfaces; `Systems A` resources and `Distinguisher A` candidate tests on `A`.
variable {C : Type u} {Systems : C → Type w} {Distinguisher : C → Type x}

/-- 0-inclusive finite hybrid chain: adjacent bounds `stepError i` sum to `∑ i, stepError i d`
between `H 0` and `H (Fin.last n)`. -/
lemma SubstitutesWithin.chain
    -- `model` fixes admitted distinguishers and per-test advantages.
    (model : DistinguisherAdvantage C Systems Distinguisher)
    -- `H` is a sequence of `n + 1` resources on `A`; `stepError i` bounds the `i`-th step.
    {A : C} {n : ℕ} (H : Fin (n + 1) → Systems A)
    (stepError : Fin n → Distinguisher A → ENNReal)
    (hstep : ∀ i : Fin n, model.SubstitutesWithin (stepError i) (H i.castSucc) (H i.succ)) :
    model.SubstitutesWithin (fun d => ∑ i : Fin n, stepError i d) (H 0) (H (Fin.last n)) := by
  induction n with
  | zero =>
    intro d _
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    change model.advantage A d (H 0) (H 0) ≤ 0
    rw [model.advantage_self]
  | succ n ih =>
    have hprefix := ih (fun i => H i.castSucc) (fun i => stepError i.castSucc)
      (fun i => hstep i.castSucc)
    have hlast := hstep (Fin.last n)
    have htrans := SubstitutesWithin.trans model hprefix hlast
    intro d hd
    have hsum : (∑ i : Fin n, stepError i.castSucc d) + stepError (Fin.last n) d =
        ∑ i : Fin (n + 1), stepError i d :=
      (Fin.sum_univ_castSucc (fun i => stepError i d)).symm
    exact (htrans d hd).trans_eq hsum

end CryptographicAlgebra.DistinguisherAdvantage

/-! ### Signed-gap averaging and uniform-index telescoping on `Distinguishers` -/

namespace Distinguishers

-- `I` contains interfaces, `Phi A` resources, and `D A` distinguishers with real evaluations.
variable {I : Type u} {Phi : I → Type v} {D : I → Type w} [Distinguishers I Phi D]

/-- Signed distinguishing gap `Pr[d(R) = 1] - Pr[d(S) = 1]` [1, Definition 4.7, p. 91]. -/
def signedGap {A : I} (d : D A) (R S : Phi A) : ℝ :=
  probability d R - probability d S

/-- Absolute advantage is the extended nonnegative magnitude of `signedGap`. -/
lemma advantage_eq_ofReal_abs_signedGap {A : I} (d : D A) (R S : Phi A) :
    advantage d R S = ENNReal.ofReal |signedGap d R S| :=
  rfl

/-- Signed gaps telescope along any finite hybrid sequence `H : Fin (L + 1) → Phi A`. -/
lemma signedGap_telescoping {A : I} {L : ℕ} (d : D A) (H : Fin (L + 1) → Phi A) :
    signedGap d (H 0) (H (Fin.last L)) =
      ∑ i : Fin L, signedGap d (H i.castSucc) (H i.succ) := by
  let acc : ℕ → ℝ := fun k =>
    if hk : k < L + 1 then probability d (H ⟨k, hk⟩) else 0
  have hterm (i : Fin L) :
      signedGap d (H i.castSucc) (H i.succ) = acc i.val - acc (i.val + 1) := by
    have hi1 : i.val < L + 1 := Nat.lt_succ_of_lt i.isLt
    have hi2 : i.val + 1 < L + 1 := Nat.succ_lt_succ i.isLt
    simp only [signedGap, acc, hi1, hi2, ↓reduceDIte]
    rfl
  have hsum : ∑ i : Fin L, (acc i.val - acc (i.val + 1)) = acc 0 - acc L :=
    (Fin.sum_univ_eq_sum_range (fun k => acc k - acc (k + 1)) L).trans
      (Finset.sum_range_sub' acc L)
  rw [Finset.sum_congr rfl (fun i _ => hterm i), hsum]
  have h0 : 0 < L + 1 := Nat.zero_lt_succ L
  have hL : L < L + 1 := Nat.lt_succ_self L
  simp only [signedGap, acc, h0, hL, ↓reduceDIte]
  rfl

/-- `Nat`-indexed signed-gap telescoping for `H : ℕ → Phi A`. -/
lemma signedGap_telescoping_nat {A : I} (L : ℕ) (d : D A) (H : ℕ → Phi A) :
    signedGap d (H 0) (H L) =
      ∑ i : Fin L, signedGap d (H i.val) (H (i.val + 1)) :=
  signedGap_telescoping d (fun i : Fin (L + 1) => H i.val)

/-- Averaging a distinguisher family under a finite law `μ` averages its signed gaps. -/
theorem signedGap_average_expect {A : I} {K : Type*}
    -- `μ` is a finite probability law over reduction choices `K`.
    (μ : Distribution.ProbDist K)
    -- `stepDistinguisher k` runs on index `k`; `reduction` averages the family under `μ`.
    (stepDistinguisher : K → D A) (reduction : D A) (X₀ X₁ : Phi A)
    (hX₀ : probability reduction X₀ = μ.1.expect (fun k => probability (stepDistinguisher k) X₀))
    (hX₁ : probability reduction X₁ = μ.1.expect (fun k => probability (stepDistinguisher k) X₁)) :
    signedGap reduction X₀ X₁ = μ.1.expect (fun k => signedGap (stepDistinguisher k) X₀ X₁) := by
  rw [signedGap, hX₀, hX₁, ← Distribution.expect_sub_right]
  rfl

/-- Scaled uniform-index telescoping signed-gap theorem [2, Theorem 3.1]:
`Pr[d(H 0)] - Pr[d(H L)] = L * scale * (Pr[reduction(X₀)] - Pr[reduction(X₁)])`. -/
theorem signedGap_uniform_telescoping_scaled {A B : I} {L : ℕ} (hL : 0 < L)
    -- `d` distinguishes the hybrid sequence `H` on interface `A`.
    (d : D A) (H : Fin (L + 1) → Phi A)
    -- `stepDistinguisher i` handles the `i`-th hybrid step on `B`; `reduction` averages them.
    (stepDistinguisher : Fin L → D B) (reduction : D B) (X₀ X₁ : Phi B)
    -- `scale` is an optional per-step factor (set `1` for an unscaled hybrid).
    (scale : ℝ)
    (hX₀ : probability reduction X₀ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₀)
    (hX₁ : probability reduction X₁ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₁)
    (hstep : ∀ i : Fin L,
      signedGap d (H i.castSucc) (H i.succ) = scale * signedGap (stepDistinguisher i) X₀ X₁) :
    signedGap d (H 0) (H (Fin.last L)) = (L : ℝ) * scale * signedGap reduction X₀ X₁ := by
  rw [signedGap_telescoping d H, signedGap, hX₀, hX₁, ← mul_sub, ← Finset.sum_sub_distrib]
  have hne : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hcancel : (L : ℝ) * scale * (1 / (L : ℝ)) = scale := by field_simp
  rw [← mul_assoc, hcancel, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hstep i)

/-- **Uniform-index telescoping signed-gap theorem**: sampling `i ←$ Fin L` uniformly once yields
`Pr[d(H 0)] - Pr[d(H L)] = L * (Pr[reduction(X₀)] - Pr[reduction(X₁)])`. -/
theorem signedGap_uniform_telescoping {A B : I} {L : ℕ} (hL : 0 < L)
    (d : D A) (H : Fin (L + 1) → Phi A)
    (stepDistinguisher : Fin L → D B) (reduction : D B) (X₀ X₁ : Phi B)
    (hX₀ : probability reduction X₀ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₀)
    (hX₁ : probability reduction X₁ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₁)
    (hstep : ∀ i : Fin L,
      signedGap d (H i.castSucc) (H i.succ) = signedGap (stepDistinguisher i) X₀ X₁) :
    signedGap d (H 0) (H (Fin.last L)) = (L : ℝ) * signedGap reduction X₀ X₁ := by
  have h := signedGap_uniform_telescoping_scaled hL d H stepDistinguisher reduction X₀ X₁ 1
    hX₀ hX₁ (fun i => by simpa only [one_mul] using hstep i)
  simpa only [mul_one] using h

/-- **Scaled uniform-index telescoping advantage equality**: for nonnegative `scale`,
`advantage d (H 0) (H L) = L * ofReal scale * advantage reduction X₀ X₁`. -/
theorem advantage_uniform_telescoping_scaled {A B : I} {L : ℕ} (hL : 0 < L)
    (d : D A) (H : Fin (L + 1) → Phi A)
    (stepDistinguisher : Fin L → D B) (reduction : D B) (X₀ X₁ : Phi B)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hX₀ : probability reduction X₀ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₀)
    (hX₁ : probability reduction X₁ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₁)
    (hstep : ∀ i : Fin L,
      signedGap d (H i.castSucc) (H i.succ) = scale * signedGap (stepDistinguisher i) X₀ X₁) :
    advantage d (H 0) (H (Fin.last L)) =
      (L : ENNReal) * ENNReal.ofReal scale * advantage reduction X₀ X₁ := by
  rw [advantage_eq_ofReal_abs_signedGap, advantage_eq_ofReal_abs_signedGap,
    signedGap_uniform_telescoping_scaled hL d H stepDistinguisher reduction X₀ X₁ scale
      hX₀ hX₁ hstep,
    abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg L), abs_of_nonneg hscale,
    ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg L) hscale),
    ENNReal.ofReal_mul (Nat.cast_nonneg L), ENNReal.ofReal_natCast]

/-- **Uniform-index telescoping advantage equality**:
`advantage d (H 0) (H L) = L * advantage reduction X₀ X₁`. -/
theorem advantage_uniform_telescoping {A B : I} {L : ℕ} (hL : 0 < L)
    (d : D A) (H : Fin (L + 1) → Phi A)
    (stepDistinguisher : Fin L → D B) (reduction : D B) (X₀ X₁ : Phi B)
    (hX₀ : probability reduction X₀ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₀)
    (hX₁ : probability reduction X₁ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₁)
    (hstep : ∀ i : Fin L,
      signedGap d (H i.castSucc) (H i.succ) = signedGap (stepDistinguisher i) X₀ X₁) :
    advantage d (H 0) (H (Fin.last L)) = (L : ENNReal) * advantage reduction X₀ X₁ := by
  have h := advantage_uniform_telescoping_scaled hL d H stepDistinguisher reduction X₀ X₁
    zero_le_one hX₀ hX₁ (fun i => by simpa only [one_mul] using hstep i)
  simpa only [ENNReal.ofReal_one, mul_one] using h

/-- **Uniform-index telescoping advantage bound**:
`advantage d (H 0) (H L) ≤ L * advantage reduction X₀ X₁`. -/
theorem advantage_uniform_telescoping_le {A B : I} {L : ℕ} (hL : 0 < L)
    (d : D A) (H : Fin (L + 1) → Phi A)
    (stepDistinguisher : Fin L → D B) (reduction : D B) (X₀ X₁ : Phi B)
    (hX₀ : probability reduction X₀ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₀)
    (hX₁ : probability reduction X₁ =
      (1 / (L : ℝ)) * ∑ i : Fin L, probability (stepDistinguisher i) X₁)
    (hstep : ∀ i : Fin L,
      signedGap d (H i.castSucc) (H i.succ) = signedGap (stepDistinguisher i) X₀ X₁) :
    advantage d (H 0) (H (Fin.last L)) ≤ (L : ENNReal) * advantage reduction X₀ X₁ :=
  (advantage_uniform_telescoping hL d H stepDistinguisher reduction X₀ X₁ hX₀ hX₁ hstep).le

end Distinguishers

/-! ### Uniform-index telescoping on `AdmissibleDistinguishers` -/

namespace AdmissibleDistinguishers

-- `I` contains interfaces, `Phi A` resources, `D A` distinguishers, and `admissible A` the
-- selected tests quantified over by `≃[ε]`.
variable {I : Type u} {Phi : I → Type v} {D : I → Type w}
  [Distinguishers I Phi D] [AdmissibleDistinguishers I D]

/-- Uniform-index telescoping hybrid reduction: an admitted uniform average `ρ d` over `Fin L`
lifts `X₀ ≃[ε] X₁` to `H 0 ≃[fun d => L * ε (ρ d)] H (Fin.last L)`. -/
theorem substitutesWithin_uniform_telescoping
    {A B : I} {L : ℕ} (hL : 0 < L)
    (H : Fin (L + 1) → Phi A) (X₀ X₁ : Phi B)
    (stepDistinguisher : D A → Fin L → D B) (ρ : D A → D B)
    (hρ : ∀ d ∈ admissible A, ρ d ∈ admissible B)
    (hX₀ : ∀ d ∈ admissible A,
      Distinguishers.probability (ρ d) X₀ =
        (1 / (L : ℝ)) * ∑ i : Fin L, Distinguishers.probability (stepDistinguisher d i) X₀)
    (hX₁ : ∀ d ∈ admissible A,
      Distinguishers.probability (ρ d) X₁ =
        (1 / (L : ℝ)) * ∑ i : Fin L, Distinguishers.probability (stepDistinguisher d i) X₁)
    (hstep : ∀ d ∈ admissible A, ∀ i : Fin L,
      Distinguishers.signedGap d (H i.castSucc) (H i.succ) =
        Distinguishers.signedGap (stepDistinguisher d i) X₀ X₁)
    {ε : D B → ENNReal}
    (h : X₀ ≃[ε] X₁) :
    H 0 ≃[fun d => (L : ENNReal) * ε (ρ d)] H (Fin.last L) := by
  intro d hd
  have htel := Distinguishers.advantage_uniform_telescoping_le hL d H (stepDistinguisher d)
    (ρ d) X₀ X₁ (hX₀ d hd) (hX₁ d hd) (hstep d hd)
  exact htel.trans (mul_le_mul' le_rfl (h (ρ d) (hρ d hd)))

end AdmissibleDistinguishers

end ConstructiveCryptography

/-! ### Concrete `StructuredDistinguisher` advantage model on `Interface` -/

namespace SystemAlgebra.Interface

open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra

/-- `DistinguisherAdvantage` model on `StructuredDistinguisher`, preserving `transcriptLaw`,
`ProbDist.bind`, and `IsNonAdaptive` alongside `TypedDistinguisher`. -/
noncomputable def structuredDistinguisherAdvantage
    -- `admitted A` selects the structured distinguishers quantified over on interface `A`.
    (admitted : ∀ A : Interface, Set (StructuredDistinguisher A)) :
    DistinguisherAdvantage Interface TypedSystem StructuredDistinguisher where
  admissible := admitted
  advantage _ D R S := D.advantage R S
  advantage_self _ D R := D.advantage_self R
  advantage_symm _ D R S := D.advantage_symm R S
  advantage_triangle _ D R S T := D.advantage_triangle R S T

/-- Every `StructuredDistinguisher` has advantage bounded by `Δ R S`. -/
lemma structuredAdvantage_le_distance {A : Interface} (D : StructuredDistinguisher A)
    (R S : TypedSystem A) :
    D.advantage R S ≤ Δ R S := by
  rw [cc_distance_eq]
  exact D.advantage_le_transcriptDistance R S

/-- `DominatedByDistance` for `structuredDistinguisherAdvantage` over any admitted set. -/
noncomputable instance structuredDistinguisherAdvantageDominated
    (admitted : ∀ A : Interface, Set (StructuredDistinguisher A)) :
    DistinguisherAdvantage.DominatedByDistance (structuredDistinguisherAdvantage admitted) where
  advantage_le_distance D _ R S := structuredAdvantage_le_distance D R S

/-- Transport a `StructuredDistinguisher` substitution through converter attachment `α • _`. -/
lemma structuredSubstitutesWithin_attach
    (admitted : ∀ A : Interface, Set (StructuredDistinguisher A))
    {A B : Interface} (α : A ⟶ B)
    (hclosed : ∀ D ∈ admitted A, D.absorb α ∈ admitted B)
    {error : StructuredDistinguisher B → ENNReal} {R S : TypedSystem B}
    (h : (structuredDistinguisherAdvantage admitted).SubstitutesWithin error R S) :
    (structuredDistinguisherAdvantage admitted).SubstitutesWithin
      (fun D => error (D.absorb α)) (α • R) (α • S) :=
  DistinguisherAdvantage.SubstitutesWithin.attach (structuredDistinguisherAdvantage admitted)
    α (fun D => D.absorb α) hclosed (fun D R S => (D.advantage_absorb α R S).symm) h

/-- Lift a `TypedDistinguisher` substitution to `StructuredDistinguisher` along `toTyped`. -/
lemma structuredSubstitutesWithin_of_typed
    (admittedTyped : ∀ A : Interface, Set (TypedDistinguisher A))
    (admittedStructured : ∀ A : Interface, Set (StructuredDistinguisher A))
    {A : Interface} (hsub : ∀ D ∈ admittedStructured A, D.toTyped ∈ admittedTyped A)
    {ε : TypedDistinguisher A → ENNReal} {R S : TypedSystem A}
    (h : (Distinguishers.distinguisherAdvantage (Phi := TypedSystem)
      admittedTyped).SubstitutesWithin ε R S) :
    (structuredDistinguisherAdvantage admittedStructured).SubstitutesWithin
      (fun D => ε D.toTyped) R S := by
  intro D hD
  exact h D.toTyped (hsub D hD)

/-- Lift a `StructuredDistinguisher` substitution back to `TypedDistinguisher` via realizations. -/
lemma typedSubstitutesWithin_of_structured
    (admittedTyped : ∀ A : Interface, Set (TypedDistinguisher A))
    (admittedStructured : ∀ A : Interface, Set (StructuredDistinguisher A))
    {A : Interface} {εStructured : StructuredDistinguisher A → ENNReal}
    {εTyped : TypedDistinguisher A → ENNReal} {R S : TypedSystem A}
    (hrealize : ∀ d ∈ admittedTyped A,
      ∃ D ∈ admittedStructured A, D.toTyped = d ∧ εStructured D ≤ εTyped d)
    (h : (structuredDistinguisherAdvantage admittedStructured).SubstitutesWithin
      εStructured R S) :
    (Distinguishers.distinguisherAdvantage (Phi := TypedSystem)
      admittedTyped).SubstitutesWithin εTyped R S := by
  intro d hd
  obtain ⟨D, hD, rfl, hle⟩ := hrealize d hd
  exact (h D hD).trans hle

/-- Uniform-index telescoping hybrid substitution on `StructuredDistinguisher` via
`StructuredDistinguisher.uniformChoice`. -/
theorem structuredSubstitutesWithin_uniform_telescoping
    (admitted : ∀ A : Interface, Set (StructuredDistinguisher A))
    {A B : Interface} {L : ℕ} (hL : 0 < L)
    (H : Fin (L + 1) → TypedSystem A) (X₀ X₁ : TypedSystem B)
    (stepDistinguisher : StructuredDistinguisher A → Fin L → StructuredDistinguisher B)
    (hclosed : ∀ D ∈ admitted A,
      StructuredDistinguisher.uniformChoice hL (stepDistinguisher D) ∈ admitted B)
    (hstep : ∀ D ∈ admitted A, ∀ i : Fin L,
      D.signedGap (H i.castSucc) (H i.succ) = (stepDistinguisher D i).signedGap X₀ X₁)
    {ε : StructuredDistinguisher B → ENNReal}
    (h : (structuredDistinguisherAdvantage admitted).SubstitutesWithin ε X₀ X₁) :
    (structuredDistinguisherAdvantage admitted).SubstitutesWithin
      (fun D => (L : ENNReal) * ε (StructuredDistinguisher.uniformChoice hL (stepDistinguisher D)))
      (H 0) (H (Fin.last L)) := by
  intro D hD
  have htel := StructuredDistinguisher.advantage_telescoping_uniformChoice_le
    hL D H (stepDistinguisher D) X₀ X₁ (hstep D hD)
  exact htel.trans (mul_le_mul' le_rfl (h _ (hclosed D hD)))

end SystemAlgebra.Interface
