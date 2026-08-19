/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Distribution
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Convex.Jensen

/-!
# Expectation over finite signed distributions (tower level L1, `DESIGN.md` §12)

`Distribution.expect X f = ∑_a X(a)·f(a)` — the pen-and-paper `𝔼_X[f]` of
`FOUNDATIONS.md` — together with the moment calculus that lives at this level:
bilinearity in the pair `(X, f)`, monotonicity, Markov, Cauchy–Schwarz, Jensen,
the indicator/mass identity, and `Distribution.variance`.

This module is deliberately free of measure theory.  The one-way transport into
mathlib's `PMF`/`Measure`/`SignedMeasure` stack — and every fact imported
through it, e.g. Chebyshev — lives in `RandomSystems.DistMeasure`, so callers
of the bare expectation calculus do not pay mathlib's measure-theory build
cost.

Like `Distribution.mass` and `Distribution.weight` (and unlike the old inline spelling
`∑ a, X a * f a`), `expect` sums over the finite support carried by
`Distribution A = A →₀ ℝ`, so no `Fintype` hypothesis is needed; `expect_eq_sum` is
the `Finset.univ` unfolding for finite carriers.

## Hypothesis discipline (`DESIGN.md` §12)

Each statement carries the *weakest* of the three distribution layers at which
it is true — signed (no hypothesis), `Distribution.NonNeg`, or `Distribution.isProbDist` — as
measured, with a proved counterexample one layer down for each, in
`scratch/TransportProbe.lean`:

* **signed**: bilinearity (`expect_add_left`/`expect_smul_left`,
  `expect_add_right`/`expect_const_mul`, …), the indicator/mass identity
  `expect_indicator_const`, and the square expansion `expect_sub_sq`.
  Linearity in the *distribution* is unstatable after transport — `PMF` has no
  `+`, `Measure` only an `ℝ≥0∞`-conical `smul` — which is why the signed
  unnormalized carrier is the home of the bilinear pairing;
* **`NonNeg`**: monotonicity, Markov, Cauchy–Schwarz, and nonnegativity of the
  `𝔼[(f-c)²]` form of variance;
* **`isProbDist`** (resp. bare `weight = 1` where nonnegativity plays no
  role): Jensen, and the `𝔼[f²] - 𝔼[f]²` form of variance.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Probability

namespace Distribution

variable {A : Type*}

/-- Expectation of `f : A → ℝ` under a finite signed distribution:
`𝔼_X[f] = ∑_a X(a)·f(a)`, summed over the finite support of `X`.

For arbitrary signed `X` this is the bilinear pairing of `X` and `f`; it is an
honest expectation when `X.isProbDist`.  Weakest-layer facts about it are
collected in this file; the transport identifying it with the Bochner integral
against `Distribution.toPMF` is `integral_toPMF_eq_expect` in
`RandomSystems.DistMeasure`. -/
def expect (X : Distribution A) (f : A → ℝ) : ℝ :=
  X.sum fun a w => w * f a

/-- On a finite carrier, `expect` is the ordinary sum over all points — the
`Finset.univ` unfolding used by proofs that reason over the whole carrier
(cf. `weight_eq_sum`, `mass_eq_sum`). -/
theorem expect_eq_sum [Fintype A] (X : Distribution A) (f : A → ℝ) :
    X.expect f = ∑ a : A, X a * f a :=
  Finsupp.sum_fintype X (fun a w => w * f a) fun a => zero_mul (f a)

/-- `expect` may be computed over any `Finset` containing the support: the
off-support summands vanish. -/
theorem expect_eq_sum_of_support_subset (X : Distribution A) (f : A → ℝ) {s : Finset A}
    (hs : X.support ⊆ s) :
    X.expect f = ∑ a ∈ s, X a * f a :=
  Finset.sum_subset hs fun a _ ha => by
    simp [Finsupp.notMem_support_iff.mp ha]

/-! ### Linearity in the distribution — signed layer

These are the statements that *cannot even be written* on the mathlib side of
the transport (`PMF` has no addition, `Measure` only a conical `smul`); the
signed unnormalized carrier is exactly what makes `expect` a bilinear
pairing. -/

/-- Additivity of expectation in the distribution.  Signed layer: no
hypothesis. -/
theorem expect_add_left (X Y : Distribution A) (f : A → ℝ) :
    (X + Y).expect f = X.expect f + Y.expect f :=
  Finsupp.sum_add_index' (fun a => zero_mul (f a)) fun a w₁ w₂ => add_mul w₁ w₂ (f a)

/-- Scalar homogeneity of expectation in the distribution.  Signed layer: no
hypothesis. -/
theorem expect_smul_left (r : ℝ) (X : Distribution A) (f : A → ℝ) :
    (r • X).expect f = r * X.expect f := by
  unfold expect
  rw [Finsupp.sum_smul_index fun a => zero_mul (f a)]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_assoc r (X a) (f a)

/-- Expectation under a difference of distributions is the difference of
expectations.  Signed layer: no hypothesis — this is the form consumed by
`statDist`-style arguments on the signed carrier. -/
theorem expect_sub_left (X Y : Distribution A) (f : A → ℝ) :
    (X - Y).expect f = X.expect f - Y.expect f :=
  Finsupp.sum_sub_index fun a w₁ w₂ => sub_mul w₁ w₂ (f a)

/-- Expectation under the zero distribution vanishes. -/
@[simp]
theorem expect_zero_left (f : A → ℝ) : (0 : Distribution A).expect f = 0 :=
  Finsupp.sum_zero_index

/-! ### Linearity in the function — signed layer -/

/-- Additivity of expectation in the function.  Signed layer: no
hypothesis. -/
theorem expect_add_right (X : Distribution A) (f g : A → ℝ) :
    X.expect (f + g) = X.expect f + X.expect g := by
  unfold expect
  simp only [Pi.add_apply, mul_add]
  exact Finsupp.sum_add

/-- Expectation pulls out a constant factor of the function.  Signed layer: no
hypothesis.  (`expect_smul_right` is the `•` spelling.) -/
theorem expect_const_mul (X : Distribution A) (r : ℝ) (f : A → ℝ) :
    X.expect (fun a => r * f a) = r * X.expect f := by
  unfold expect Finsupp.sum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_left_comm (X a) r (f a)

/-- Scalar homogeneity of expectation in the function.  Signed layer: no
hypothesis. -/
theorem expect_smul_right (X : Distribution A) (r : ℝ) (f : A → ℝ) :
    X.expect (r • f) = r * X.expect f :=
  expect_const_mul X r f

/-- Expectation of a difference of functions is the difference of expectations
(the function-side mirror of `expect_sub_left`).  Signed layer: no
hypothesis. -/
theorem expect_sub_right (X : Distribution A) (f g : A → ℝ) :
    X.expect (fun a => f a - g a) = X.expect f - X.expect g := by
  unfold expect Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Expectation of the zero function vanishes. -/
@[simp]
theorem expect_zero_right (X : Distribution A) : X.expect 0 = 0 := by
  unfold expect Finsupp.sum
  simp

/-- Expectation of a constant is the constant times the total weight; at
`weight = 1` this is `𝔼[c] = c`.  Signed layer: no hypothesis. -/
theorem expect_const (X : Distribution A) (c : ℝ) :
    X.expect (fun _ => c) = c * X.weight := by
  unfold expect weight Finsupp.sum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => mul_comm (X a) c

/-- Expectation of a finite sum of functions is the sum of expectations
(the finite-sum form of `expect_add_right`, mirroring mathlib's
`MeasureTheory.integral_finset_sum`).  Signed layer: no hypothesis. -/
theorem expect_finset_sum {ι : Type*} (X : Distribution A) (s : Finset ι)
    (f : ι → A → ℝ) :
    X.expect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, X.expect (f i) := by
  unfold expect Finsupp.sum
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-! ### The indicator/mass identity — signed layer -/

/-- Expectation of a scaled indicator is the scalar times the event mass:
`𝔼_X[c·𝟙[P]] = c·X(P)`.  Signed layer: no hypothesis.  Statement-level
`[DecidablePred P]` per the decidability policy of `Probability.Distribution`. -/
theorem expect_indicator_const (X : Distribution A) (P : A → Prop) [DecidablePred P]
    (c : ℝ) :
    X.expect (fun a => if P a then c else 0) = c * X.mass P := by
  classical
  unfold expect mass Finsupp.sum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    by_cases h : P a <;> simp [h, mul_comm]

/-- Expectation of an indicator is the event mass: `𝔼_X[𝟙[P]] = X(P)`.  This
is the relation of `expect` to `Distribution.mass`.  Signed layer: no hypothesis. -/
theorem expect_indicator (X : Distribution A) (P : A → Prop) [DecidablePred P] :
    X.expect (fun a => if P a then (1 : ℝ) else 0) = X.mass P := by
  rw [expect_indicator_const, one_mul]

/-! ### Order facts — `NonNeg` layer

Each fails on the signed layer; the counterexamples are
`expect_mono_fails_signed`, `dist_markov_fails_signed` and
`dist_cauchy_schwarz_fails_signed` in `scratch/TransportProbe.lean`. -/

/-- Expectation of a nonnegative function under a nonnegative distribution is
nonnegative.  `NonNeg` layer. -/
theorem expect_nonneg {X : Distribution A} (hX : X.NonNeg) {f : A → ℝ}
    (hf : ∀ a, 0 ≤ f a) :
    0 ≤ X.expect f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hX a) (hf a)

/-- Monotonicity of expectation.  `NonNeg` layer: fails signed (one point of
mass `-1`). -/
theorem expect_mono {X : Distribution A} (hX : X.NonNeg) {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) :
    X.expect f ≤ X.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hX a)

/-- A uniform bound on `f` over the support bounds the expectation by
`c · |X|`.  `NonNeg` layer; the bound is only required where `X` has mass. -/
theorem expect_le_mul_weight {X : Distribution A} (hX : X.NonNeg) {f : A → ℝ} {c : ℝ}
    (h : ∀ a ∈ X.support, f a ≤ c) :
    X.expect f ≤ c * X.weight := by
  unfold expect weight Finsupp.sum
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun a ha =>
    (mul_le_mul_of_nonneg_left (h a ha) (hX a)).trans_eq (mul_comm _ _)

/-- **Markov's inequality**: `X{a | c ≤ f a} ≤ 𝔼_X[f]/c` for nonnegative `f`
and `c > 0`.  `NonNeg` layer — total weight plays no role, so this holds for
arbitrary nonnegative (sub- or super-normalized) distributions; fails signed
(off-event negative mass pulls the expectation below the event mass).

UPSTREAM-CANDIDATE: the finitely-supported weighted-sum form of Markov,
independent of everything in this library except the `Distribution` carrier. -/
theorem mass_ge_le_expect_div {X : Distribution A} (hX : X.NonNeg) {f : A → ℝ}
    (hf : ∀ a, 0 ≤ f a) {c : ℝ} (hc : 0 < c) :
    X.mass (fun a => c ≤ f a) ≤ X.expect f / c := by
  classical
  rw [le_div_iff₀ hc]
  unfold mass expect Finsupp.sum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : c ≤ f a
  · simpa [ha] using mul_le_mul_of_nonneg_left ha (hX a)
  · simpa [ha] using mul_nonneg (hX a) (hf a)

/-- **Discrete Cauchy–Schwarz**: `𝔼_X[uv]² ≤ 𝔼_X[u²]·𝔼_X[v²]`.  `NonNeg`
layer — this is positive semidefiniteness of the pairing, not normalization,
so any nonnegative weight works; fails signed (the pairing becomes
indefinite).  Name mirrors mathlib's `Finset.sum_mul_sq_le_sq_mul_sq`.

UPSTREAM-CANDIDATE: the weighted Cauchy–Schwarz for finitely supported
nonnegative weights. -/
theorem expect_mul_sq_le_sq_mul_sq {X : Distribution A} (hX : X.NonNeg) (u v : A → ℝ) :
    (X.expect fun a => u a * v a) ^ 2
      ≤ (X.expect fun a => u a ^ 2) * X.expect fun a => v a ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq X.support
    (fun a => Real.sqrt (X a) * u a) fun a => Real.sqrt (X a) * v a
  have h1 : ∀ a, Real.sqrt (X a) * u a * (Real.sqrt (X a) * v a)
      = X a * (u a * v a) := fun a => by
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (hX a)]
  have h2 : ∀ (w : A → ℝ) (a : A), (Real.sqrt (X a) * w a) ^ 2
      = X a * w a ^ 2 := fun w a => by
    rw [mul_pow, Real.sq_sqrt (hX a)]
  simpa only [expect, Finsupp.sum, h1, h2 u, h2 v] using h

/-! ### Variance -/

/-- Variance of `f` under `X`, in the `𝔼[(f - 𝔼f)²]` form.  This form is the
definition because its nonnegativity already holds at the `NonNeg` layer
(`variance_nonneg`); the subtracted form `𝔼[f²] - 𝔼[f]²` agrees with it only
at `weight = 1` (`variance_eq_expect_sq_sub_sq_expect`), and goes negative at
weight 2 (`variance_sub_form_fails_at_weight_two` in
`scratch/TransportProbe.lean`). -/
def variance (X : Distribution A) (f : A → ℝ) : ℝ :=
  X.expect fun a => (f a - X.expect f) ^ 2

/-- Nonnegativity of the `𝔼[(f-c)²]` form for any center `c`.  `NonNeg`
layer. -/
theorem expect_sub_sq_nonneg {X : Distribution A} (hX : X.NonNeg) (f : A → ℝ) (c : ℝ) :
    0 ≤ X.expect fun a => (f a - c) ^ 2 :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hX a) (sq_nonneg _)

/-- Variance is nonnegative.  `NonNeg` layer (the `𝔼[(f-c)²]` form at
`c = 𝔼f`; no normalization needed). -/
theorem variance_nonneg {X : Distribution A} (hX : X.NonNeg) (f : A → ℝ) :
    0 ≤ X.variance f :=
  expect_sub_sq_nonneg hX f _

/-- Expansion of the square about an arbitrary center:
`𝔼[(f-c)²] = 𝔼[f²] - 2c·𝔼[f] + c²·|X|`.  Signed layer: pure bilinearity. -/
theorem expect_sub_sq (X : Distribution A) (f : A → ℝ) (c : ℝ) :
    (X.expect fun a => (f a - c) ^ 2)
      = (X.expect fun a => f a ^ 2) - 2 * c * X.expect f + c ^ 2 * X.weight := by
  unfold expect weight Finsupp.sum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- At total weight one, variance takes the subtracted form
`Var_X f = 𝔼[f²] - 𝔼[f]²` (mathlib: `ProbabilityTheory.variance_def'`).
Weakest layer: `weight = 1` alone — nonnegativity of `X` plays no role in the
*identity*, only in the sign of either side. -/
theorem variance_eq_expect_sq_sub_sq_expect {X : Distribution A} (hw : X.weight = 1)
    (f : A → ℝ) :
    X.variance f = (X.expect fun a => f a ^ 2) - X.expect f ^ 2 := by
  rw [variance, expect_sub_sq, hw]
  ring

/-- Nonnegativity of the subtracted form: `𝔼[f]² ≤ 𝔼[f²]`.  `isProbDist`
layer — this genuinely needs both conjuncts: `NonNeg` for the sign of the
`𝔼[(f-c)²]` form and `weight = 1` to equate the two forms
(`variance_sub_form_fails_at_weight_two` in `scratch/TransportProbe.lean`
shows failure at `NonNeg` weight 2). -/
theorem expect_sq_sub_sq_expect_nonneg {X : Distribution A} (hX : X.isProbDist)
    (f : A → ℝ) :
    0 ≤ (X.expect fun a => f a ^ 2) - X.expect f ^ 2 := by
  rw [← variance_eq_expect_sq_sub_sq_expect hX.2]
  exact variance_nonneg hX.1 f

/-! ### Jensen — `isProbDist` layer

Fails at `NonNeg` even for subprobability weight (`dist_jensen_fails_subprob`
in `scratch/TransportProbe.lean`): total weight one is load-bearing. -/

/-- **Jensen's inequality**, concave case: `𝔼_X[φ∘f] ≤ φ(𝔼_X[f])` for a
probability distribution `X`.  `isProbDist` layer.  Name mirrors mathlib's
`ConcaveOn.le_map_sum`.

UPSTREAM-CANDIDATE: finitely-supported-weights Jensen. -/
theorem _root_.ConcaveOn.le_map_expect {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ Set.univ φ) {X : Distribution A} (hX : X.isProbDist)
    (f : A → ℝ) :
    (X.expect fun a => φ (f a)) ≤ φ (X.expect f) := by
  have h := hφ.le_map_sum (t := X.support) (w := fun a => X a) (p := f)
    (fun a _ => hX.1 a) hX.2 (fun a _ => trivial)
  simpa only [expect, Finsupp.sum, smul_eq_mul] using h

/-- **Jensen's inequality**, convex case: `φ(𝔼_X[f]) ≤ 𝔼_X[φ∘f]` for a
probability distribution `X`.  `isProbDist` layer.  Name mirrors mathlib's
`ConvexOn.map_sum_le`.

UPSTREAM-CANDIDATE: finitely-supported-weights Jensen. -/
theorem _root_.ConvexOn.map_expect_le {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {X : Distribution A} (hX : X.isProbDist)
    (f : A → ℝ) :
    φ (X.expect f) ≤ X.expect fun a => φ (f a) := by
  have h := hφ.map_sum_le (t := X.support) (w := fun a => X a) (p := f)
    (fun a _ => hX.1 a) hX.2 (fun a _ => trivial)
  simpa only [expect, Finsupp.sum, smul_eq_mul] using h

end Distribution

end Probability
