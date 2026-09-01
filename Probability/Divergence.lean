/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.StatisticalDistance
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Deriv
import Probability.DistributionMeasure
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Relative entropy and Pinsker's inequality (tower level L2)

mathlib carries `InformationTheory.klDiv` on **measures** but no Pinsker
inequality in any form.  This module supplies the missing half, and does so
**natively on `Distribution`** rather than by transporting into mathlib and
pulling back.

## Why native, and why that is checkable rather than asserted

Pinsker's left-hand side is `statDist`, a first-class object of this library;
mathlib's `klDiv` lives on `Measure`, and the transport of a finitely supported
law into a `PMF` requires `[Fintype]` on the carrier.  The carriers this
inequality is wanted on (transcript spaces, system laws) must not be `Fintype`,
so stating it after transport would restrict it to exactly the carriers that do
not need it.  So `Distribution.klDiv` is defined here directly.

To keep that from becoming an ad hoc convention, §4 proves `klDiv_toPMF`: on a
`Fintype` carrier the divergence **is** mathlib's `InformationTheory.klDiv` of
the transported measures.  Nothing above §4 depends on that lemma — it exists so
the native/transport choice is a checked fact rather than a claim.

The agreement is **scoped**, and both qualifications are load-bearing:

1. **Only on the `isProbDist` slice.**  mathlib's `klDiv` carries a correction
   term `ν(univ) − μ(univ)` that the native sum does not, so off total weight one
   the two are genuinely different functions, not two renderings of one.  This is
   exactly why the weight-general Pinsker below — the form used *before* a law
   has been renormalized — has no mathlib counterpart to agree with.
2. **Modulo `ENNReal.ofReal`.**  mathlib's is `ℝ≥0∞`-valued; the equality is
   `klDiv μ ν = ENNReal.ofReal (klDiv X Y)`, not a real equality.

## Base: nats, not bits

`klDiv` is in **nats** (`Real.log`), which is what pins Pinsker's constant to
`½`.  `Probability.Entropy` and `Probability.ShannonEntropy` are in **bits**
(`Real.logb 2`, CR18's convention).  The two conventions coexist deliberately:
each is the one its own textbook statement is stated in, and mixing them would
put a stray `log 2` in either Pinsker or the entropy ladder.  Convert with
`Real.logb` = `Real.log · / Real.log 2`.

## Hypothesis discipline

The carrier is signed; the nonnegative slice is `NonNeg` plus a weight
hypothesis. Each statement carries the weakest layer at which it is true:

* `klDiv_self`, `klDiv_zero_left` — signed.
* `klDiv_nonneg` (Gibbs), and the squared form
  `sq_statDist_le_weight_mul_klDiv_div_two` — `NonNeg` on both laws, with the
  weights merely *compared* (`X.weight = Y.weight`) rather than normalized.
  The unnormalized form is the load-bearing one: it is what lets the bound be
  used before a law has been renormalized.
* `statDist_le_sqrt_klDiv_div_two` — the textbook Pinsker, `isProbDist`, an
  immediate corollary of the squared form at `weight = 1`.

Absolute continuity (`hac : X.support ⊆ Y.support`) is required throughout and
is not a technicality: `Real.log` junk makes the divergence finite where it
should be infinite, so without it the inequality is false.
-/

noncomputable section

open scoped BigOperators

namespace Probability

/-! ## 1. The pointwise bound -/

def klf (x : ℝ) : ℝ := x * Real.log x - x + 1 - 3 * (x - 1) ^ 2 / (2 * (x + 2))

def klf' (x : ℝ) : ℝ := Real.log x - 3 * (x - 1) * (x + 5) / (2 * (x + 2) ^ 2)

def klf'' (x : ℝ) : ℝ := 1 / x - 27 / (x + 2) ^ 3

theorem hasDerivAt_klf {x : ℝ} (hx : 0 < x) : HasDerivAt klf (klf' x) x := by
  have hne : (2 : ℝ) * (x + 2) ≠ 0 := by positivity
  have hu : HasDerivAt (fun y : ℝ => 3 * (y - 1) ^ 2) (6 * (x - 1)) x := by
    have h : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
      change @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
        (NormedAlgebra.toNormedSpace ℝ).toModule _ _
        (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x
      convert ((hasDerivAt_id x).sub_const 1).pow 2 using 1
      · funext y
        rfl
      · norm_num [id_eq]
    change @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℝ).toModule _ _
      (fun y : ℝ => 3 * (y - 1) ^ 2) (6 * (x - 1)) x
    convert h.const_mul (3 : ℝ) using 1; ring
  have hv : HasDerivAt (fun y : ℝ => 2 * (y + 2)) 2 x := by
    change @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℝ).toModule _ _
      (fun y : ℝ => 2 * (y + 2)) 2 x
    convert ((hasDerivAt_id x).add_const 2).const_mul (2 : ℝ) using 1
    · funext y
      rfl
    · ring
  have hml : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log x + 1) x :=
    Real.hasDerivAt_mul_log hx.ne'
  have hmain : HasDerivAt (fun y : ℝ => y * Real.log y - y + 1) (Real.log x + 1 - 1) x := by
    simpa using (hml.sub (hasDerivAt_id x)).add_const 1
  have hall := hmain.sub (hu.div hv hne)
  show HasDerivAt (fun y : ℝ => y * Real.log y - y + 1 - 3 * (y - 1) ^ 2 / (2 * (y + 2)))
    (klf' x) x
  change @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ ℝ).toModule _ _
    (fun y : ℝ => y * Real.log y - y + 1 - 3 * (y - 1) ^ 2 / (2 * (y + 2)))
    (klf' x) x
  convert hall using 1
  · funext y
    rfl
  · unfold klf'
    have hx2 : x + 2 ≠ 0 := by positivity
    field_simp
    ring

theorem hasDerivAt_klf' {x : ℝ} (hx : 0 < x) : HasDerivAt klf' (klf'' x) x := by
  have hx2 : (0 : ℝ) < x + 2 := by linarith
  have hne : (2 : ℝ) * (x + 2) ^ 2 ≠ 0 := by positivity
  have hu : HasDerivAt (fun y : ℝ => 3 * (y - 1) * (y + 5)) (6 * (x + 2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => 3 * (y - 1)) 3 x := by
      change @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
        (NormedAlgebra.toNormedSpace ℝ).toModule _ _
        (fun y : ℝ => 3 * (y - 1)) 3 x
      convert ((hasDerivAt_id x).sub_const 1).const_mul (3 : ℝ) using 1
      · funext y
        rfl
      · ring
    change @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℝ).toModule _ _
      (fun y : ℝ => 3 * (y - 1) * (y + 5)) (6 * (x + 2)) x
    convert h1.mul ((hasDerivAt_id x).add_const 5) using 1
    · funext y
      rfl
    · norm_num [id_eq]
      ring
  have hv : HasDerivAt (fun y : ℝ => 2 * (y + 2) ^ 2) (4 * (x + 2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => (y + 2) ^ 2) (2 * (x + 2)) x := by
      change @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
        (NormedAlgebra.toNormedSpace ℝ).toModule _ _
        (fun y : ℝ => (y + 2) ^ 2) (2 * (x + 2)) x
      convert ((hasDerivAt_id x).add_const 2).pow 2 using 1
      · funext y
        rfl
      · norm_num [id_eq]
    change @HasDerivAt ℝ _ ℝ Real.normedCommRing.toCommRing.toAddCommGroup
      (NormedAlgebra.toNormedSpace ℝ).toModule _ _
      (fun y : ℝ => 2 * (y + 2) ^ 2) (4 * (x + 2)) x
    convert h1.const_mul (2 : ℝ) using 1; ring
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hall := hlog.sub (hu.div hv hne)
  show HasDerivAt (fun y : ℝ => Real.log y - 3 * (y - 1) * (y + 5) / (2 * (y + 2) ^ 2))
    (klf'' x) x
  change @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ ℝ).toModule _ _
    (fun y : ℝ => Real.log y - 3 * (y - 1) * (y + 5) / (2 * (y + 2) ^ 2))
    (klf'' x) x
  convert hall using 1
  · funext y
    rfl
  · unfold klf''
    field_simp
    ring

theorem convexOn_klf : ConvexOn ℝ (Set.Ici 0) klf := by
  have hI : interior (Set.Ici (0 : ℝ)) = Set.Ioi 0 := interior_Ici
  have hderiv : Set.EqOn (deriv klf) klf' (Set.Ioi 0) := fun y hy => (hasDerivAt_klf hy).deriv
  have hev : ∀ y ∈ Set.Ioi (0 : ℝ), deriv klf =ᶠ[nhds y] klf' := fun y hy =>
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) hderiv
  refine convexOn_of_deriv2_nonneg (convex_Ici 0) ?_ ?_ ?_ ?_
  · have hc : Continuous fun y : ℝ => y * Real.log y - y + 1 :=
      (Real.continuous_mul_log.sub continuous_id).add continuous_const
    refine hc.continuousOn.sub (ContinuousOn.div ?_ ?_ ?_)
    · exact (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).continuousOn
    · exact (continuous_const.mul (continuous_id.add continuous_const)).continuousOn
    · intro y hy
      have : (0 : ℝ) ≤ y := hy
      exact ne_of_gt (by linarith)
  · rw [hI]
    exact fun y hy => (hasDerivAt_klf hy).differentiableAt.differentiableWithinAt
  · rw [hI]
    exact fun y hy =>
      ((hasDerivAt_klf' hy).differentiableAt.congr_of_eventuallyEq
        (hev y hy)).differentiableWithinAt
  · rw [hI]
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have h2 : deriv^[2] klf y = klf'' y := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      rw [(hev y hy).deriv_eq, (hasDerivAt_klf' hy).deriv]
    rw [h2, klf'', sub_nonneg, div_le_div_iff₀ (by positivity) hy0]
    nlinarith [mul_nonneg (sq_nonneg (y - 1)) (by linarith : (0 : ℝ) ≤ y + 8)]

/-- **The pointwise Pinsker bound**, normalized form: for `x ≥ 0`,
`3(x−1)²/(2(x+2)) ≤ x·log x − x + 1`.

`x log x - x + 1` is mathlib's `klFun`, the pointwise integrand of the
Kullback–Leibler divergence; the rational lower bound is the sharp one that
turns Cauchy–Schwarz into Pinsker's inequality with the constant `½` (a weaker
denominator such as `x + 1` makes the statement false at `x = ½`).

Proof: `f x = klFun x − 3(x−1)²/(2(x+2))` has `f''(x) = 1/x − 27/(x+2)³`, and
`(x+2)³ − 27x = (x−1)²(x+8) ≥ 0`, so `f` is convex on `[0, ∞)`; `f'(1) = 0`
puts its minimum at `x = 1`, where `f 1 = 0`.

Mathlib has `klFun` and its convexity but no quantitative lower bound. -/
theorem sq_sub_one_div_le_mul_log_sub_add_one {x : ℝ} (hx : 0 ≤ x) :
    3 * (x - 1) ^ 2 / (2 * (x + 2)) ≤ x * Real.log x - x + 1 := by
  have hmem : (1 : ℝ) ∈ interior (Set.Ici (0 : ℝ)) := by
    rw [interior_Ici]; exact Set.mem_Ioi.mpr one_pos
  have hrd : derivWithin klf (Set.Ioi 1) 1 = 0 := by
    rw [(hasDerivAt_klf one_pos).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 1)]
    norm_num [klf']
  have hmin := convexOn_klf.isMinOn_of_rightDeriv_eq_zero hmem hrd
  have h := isMinOn_iff.mp hmin x hx
  have h1 : klf 1 = 0 := by norm_num [klf]
  rw [h1] at h
  rw [klf] at h
  linarith

/-- **The pointwise Pinsker bound**, homogeneous form: for `a ≥ 0` and `b > 0`,
`3(a−b)²/(2(a+2b)) ≤ a·log(a/b) − a + b`.

Both sides are `1`-homogeneous in `(a, b)`, so this is
`sq_sub_one_div_le_mul_log_sub_add_one` at `x = a/b`, multiplied by `b`. -/
theorem sq_sub_div_le_mul_log_div_sub_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    3 * (a - b) ^ 2 / (2 * (a + 2 * b)) ≤ a * Real.log (a / b) - a + b := by
  have hb' : b ≠ 0 := hb.ne'
  have hab : a + 2 * b ≠ 0 := by positivity
  have hab2 : a / b + 2 ≠ 0 := by positivity
  have h := sq_sub_one_div_le_mul_log_sub_add_one (div_nonneg ha hb.le)
  have hmul := mul_le_mul_of_nonneg_left h hb.le
  have key1 : b * (3 * (a / b - 1) ^ 2 / (2 * (a / b + 2)))
      = 3 * (a - b) ^ 2 / (2 * (a + 2 * b)) := by
    field_simp
  have key2 : b * (a / b * Real.log (a / b) - a / b + 1)
      = a * Real.log (a / b) - a + b := by
    field_simp
  rw [key1, key2] at hmul
  exact hmul

/-! ## 2. Kullback–Leibler divergence on `Distribution` -/

namespace Distribution

variable {A : Type*}

/-- **Kullback–Leibler divergence** (relative entropy)
`D(X ‖ Y) = ∑_a X(a)·log(X(a)/Y(a))`, in nats. -/
def klDiv (X Y : Distribution A) : ℝ := X.sum fun a x => x * Real.log (x / Y a)

/-- `klDiv` is the `Distribution` expectation of the log-likelihood ratio — the L1
vocabulary, so the whole `Distribution.expect` calculus applies to it.  `rfl`:
`Finsupp.sum` evaluates its body at `X a`. -/
theorem klDiv_eq_expect (X Y : Distribution A) :
    klDiv X Y = X.expect fun a => Real.log (X a / Y a) := rfl

/-- `klDiv` as a sum over any finite set carrying the support of the first
argument; the summand vanishes off `X.support`. -/
theorem klDiv_eq_sum_of_support_subset {X Y : Distribution A} {s : Finset A} (hs : X.support ⊆ s) :
    klDiv X Y = ∑ a ∈ s, X a * Real.log (X a / Y a) :=
  (klDiv_eq_expect X Y).trans (expect_eq_sum_of_support_subset X _ hs)

/-- `D(X ‖ X) = 0`.  Signed layer: on `X.support` the ratio is literally `1`. -/
@[simp]
theorem klDiv_self (X : Distribution A) : klDiv X X = 0 := by
  show ∑ a ∈ X.support, X a * Real.log (X a / X a) = 0
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [div_self (Finsupp.mem_support_iff.mp ha), Real.log_one, mul_zero]

/-- The zero distribution has no divergence from anything. -/
@[simp]
theorem klDiv_zero_left (Y : Distribution A) : klDiv 0 Y = 0 := by
  simp [klDiv]

/-- Every summand of `∑ (X log(X/Y) − X + Y)` is nonnegative on `Y.support`
under absolute continuity — the homogeneous pointwise bound
`sq_sub_div_le_mul_log_div_sub_add` read at `(X a, Y a)`. -/
theorem klTerm_nonneg {X Y : Distribution A} (hX : X.NonNeg) (hY : Y.NonNeg)
    {a : A} (ha : a ∈ Y.support) :
    0 ≤ X a * Real.log (X a / Y a) - X a + Y a := by
  have hb : 0 < Y a := (hY a).lt_of_ne (Ne.symm (Finsupp.mem_support_iff.mp ha))
  have h := sq_sub_div_le_mul_log_div_sub_add (hX a) hb
  have h0 : 0 ≤ 3 * (X a - Y a) ^ 2 / (2 * (X a + 2 * Y a)) := by
    have : 0 < 2 * (X a + 2 * Y a) := by nlinarith [hX a]
    positivity
  linarith

/-- The `klFun`-shaped sum over `Y.support` in terms of `klDiv` and the two
weights.  Signed layer apart from the absolute-continuity hypothesis. -/
theorem sum_klTerm_eq {X Y : Distribution A} (hac : X.support ⊆ Y.support) :
    ∑ a ∈ Y.support, (X a * Real.log (X a / Y a) - X a + Y a)
      = klDiv X Y - X.weight + Y.weight := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← klDiv_eq_sum_of_support_subset hac, ← weight_eq_sum_of_support_subset X hac,
    ← weight_eq_sum_of_support_subset Y (subset_refl Y.support)]

/-- **Gibbs' inequality**: relative entropy is nonnegative.

`NonNeg` layer plus equal weight (`isProbDist` is *not* needed: the statement is
scale-invariant, `D(cX ‖ cY) = c·D(X ‖ Y)`), plus absolute continuity
`X.support ⊆ Y.support` — without which the junk value `Real.log (x / 0) = 0`
makes the statement false (`X = δ₀`, `Y = δ₁` gives `klDiv = 0` but should be
`+∞`). -/
theorem klDiv_nonneg {X Y : Distribution A} (hX : X.NonNeg) (hY : Y.NonNeg)
    (hw : X.weight = Y.weight) (hac : X.support ⊆ Y.support) :
    0 ≤ klDiv X Y := by
  have h : 0 ≤ ∑ a ∈ Y.support, (X a * Real.log (X a / Y a) - X a + Y a) :=
    Finset.sum_nonneg fun a ha => klTerm_nonneg hX hY ha
  rw [sum_klTerm_eq hac, hw] at h
  linarith

end Distribution

/-! ## 3. Pinsker's inequality -/

/-- **Pinsker's inequality, weight-general form**:
`δ(X, Y)² ≤ |X|·D(X ‖ Y)/2`.

`NonNeg` layer plus equal weight — *not* `isProbDist`.  Both sides scale the
same way (`δ(cX, cY) = c·δ(X, Y)`, `D(cX ‖ cY) = c·D(X ‖ Y)`), so the
normalization enters only through the explicit factor `|X|`; equal weight is
what the statistical-distance side needs, and it is exactly the hypothesis of
`statDist_eq_half_sum_abs_of_weight_eq`.  Absolute continuity
`X.support ⊆ Y.support` is unavoidable with a real-valued divergence: without
it `Real.log (x / 0) = 0` reports a finite divergence where the true value is
`+∞`.

Proof (Csiszár's Cauchy–Schwarz argument, in Engel form): apply
`Finset.sq_sum_div_le_sum_sq_div` to `f a = |X(a) − Y(a)|` and
`g a = X(a) + 2Y(a)` over `Y.support`, then bound each `f²/g` by
`⅔·(X log(X/Y) − X + Y)` with `sq_sub_div_le_mul_log_div_sub_add`.  With
`∑ g = 3|X|` and `∑ f = 2δ` this is `4δ²/(3|X|) ≤ ⅔·D`. -/
theorem sq_statDist_le_weight_mul_klDiv_div_two {A : Type*} {X Y : Distribution A}
    (hX : X.NonNeg) (hY : Y.NonNeg) (hw : X.weight = Y.weight)
    (hac : X.support ⊆ Y.support) :
    statDist X Y ^ 2 ≤ X.weight * Distribution.klDiv X Y / 2 := by
  have hYpos : ∀ a ∈ Y.support, 0 < Y a := fun a ha =>
    (hY a).lt_of_ne (Ne.symm (Finsupp.mem_support_iff.mp ha))
  have hsub : (X - Y).support ⊆ Y.support := by
    intro a ha
    rw [Finsupp.mem_support_iff] at ha ⊢
    intro hY0
    refine ha ?_
    have hX0 : X a = 0 := by
      by_contra h
      exact Finsupp.mem_support_iff.mp (hac (Finsupp.mem_support_iff.mpr h)) hY0
    rw [Finsupp.sub_apply, hX0, hY0, sub_zero]
  have hstat : statDist X Y = ∑ a ∈ Y.support, max (X a - Y a) 0 := by
    show ∑ a ∈ (X - Y).support, max (X a - Y a) 0 = _
    refine Finset.sum_subset hsub fun a _ ha => ?_
    rw [Finsupp.notMem_support_iff, Finsupp.sub_apply, sub_eq_zero] at ha
    rw [ha, sub_self, max_self]
  have hsumX : X.weight = ∑ a ∈ Y.support, X a := Distribution.weight_eq_sum_of_support_subset X hac
  have hsumY : Y.weight = ∑ a ∈ Y.support, Y a :=
    Distribution.weight_eq_sum_of_support_subset Y (subset_refl _)
  have habs : ∑ a ∈ Y.support, |X a - Y a| = 2 * statDist X Y := by
    have hpt : ∀ a ∈ Y.support, |X a - Y a| = 2 * max (X a - Y a) 0 - (X a - Y a) := by
      intro a _
      rcases le_total (X a) (Y a) with h | h
      · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]; ring
      · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hstat,
      Finset.sum_sub_distrib, ← hsumX, ← hsumY, hw, sub_self, sub_zero]
  have hgpos : ∀ a ∈ Y.support, 0 < X a + 2 * Y a := fun a ha => by
    have h1 := hX a
    have h2 := hYpos a ha
    linarith
  have hgsum : ∑ a ∈ Y.support, (X a + 2 * Y a) = 3 * X.weight := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hsumX, ← hsumY, hw]
    ring
  have hEngel := Finset.sq_sum_div_le_sum_sq_div (g := fun a => X a + 2 * Y a)
    Y.support (fun a => |X a - Y a|) hgpos
  rw [habs, hgsum] at hEngel
  have hbound : ∑ a ∈ Y.support, |X a - Y a| ^ 2 / (X a + 2 * Y a)
      ≤ 2 / 3 * Distribution.klDiv X Y := by
    have hpt : ∀ a ∈ Y.support, |X a - Y a| ^ 2 / (X a + 2 * Y a)
        ≤ 2 / 3 * (X a * Real.log (X a / Y a) - X a + Y a) := by
      intro a ha
      have h := sq_sub_div_le_mul_log_div_sub_add (hX a) (hYpos a ha)
      have hg := hgpos a ha
      have hrw : 3 * (X a - Y a) ^ 2 / (2 * (X a + 2 * Y a))
          = 3 / 2 * (|X a - Y a| ^ 2 / (X a + 2 * Y a)) := by
        rw [sq_abs]
        field_simp
      rw [hrw] at h
      linarith
    calc ∑ a ∈ Y.support, |X a - Y a| ^ 2 / (X a + 2 * Y a)
        ≤ ∑ a ∈ Y.support, 2 / 3 * (X a * Real.log (X a / Y a) - X a + Y a) :=
          Finset.sum_le_sum hpt
      _ = 2 / 3 * (Distribution.klDiv X Y - X.weight + Y.weight) := by
          rw [← Finset.mul_sum, Distribution.sum_klTerm_eq hac]
      _ = 2 / 3 * Distribution.klDiv X Y := by rw [hw]; ring
  rcases eq_or_lt_of_le hX.weight_nonneg with h0 | hpos
  · have hYw : Y.weight = 0 := by rw [← hw, ← h0]
    have hempty : Y.support = ∅ := by
      by_contra hne
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hp : 0 < ∑ b ∈ Y.support, Y b :=
        Finset.sum_pos' (fun b _ => hY b) ⟨a, ha, hYpos a ha⟩
      rw [← hsumY, hYw] at hp
      exact lt_irrefl 0 hp
    have h1 : statDist X Y = 0 := by rw [hstat, hempty, Finset.sum_empty]
    have h2 : Distribution.klDiv X Y = 0 := by
      rw [Distribution.klDiv_eq_sum_of_support_subset hac, hempty, Finset.sum_empty]
    rw [h1, h2, ← h0]
    norm_num
  · have h3w : 0 < 3 * X.weight := by linarith
    rw [div_le_iff₀ h3w] at hEngel
    nlinarith [mul_le_mul_of_nonneg_right hbound h3w.le]

/-- **Pinsker's inequality**: `δ(X, Y) ≤ √(D(X ‖ Y)/2)`, with `D` in nats.

`isProbDist` layer, which is where the constant `½` is pinned: the general
statement is `sq_statDist_le_weight_mul_klDiv_div_two`, and weight one is what
turns its `|X|·D/2` into `D/2`.  The remaining hypothesis
`X.support ⊆ Y.support` is absolute continuity `X ≪ Y`
(`∀ a, Y a = 0 → X a = 0`, via `Finsupp.support_subset_iff`); it cannot be
dropped, since `Real.log (x / 0) = 0` would otherwise report `D = 0` for
`X = δ₀`, `Y = δ₁`, where `δ(X, Y) = 1`.

Mathlib has `InformationTheory.klDiv` but no Pinsker
inequality in any form (checked against the pinned revision). -/
theorem statDist_le_sqrt_klDiv_div_two {A : Type*} {X Y : Distribution A}
    (hX : X.isProbDist) (hY : Y.isProbDist) (hac : X.support ⊆ Y.support) :
    statDist X Y ≤ Real.sqrt (Distribution.klDiv X Y / 2) := by
  have h := sq_statDist_le_weight_mul_klDiv_div_two hX.1 hY.1 (hX.2.trans hY.2.symm) hac
  rw [hX.2, one_mul] at h
  have hd : 0 ≤ statDist X Y := Finset.sum_nonneg fun _ _ => le_max_right _ _
  calc statDist X Y = Real.sqrt (statDist X Y ^ 2) := (Real.sqrt_sq hd).symm
    _ ≤ Real.sqrt (Distribution.klDiv X Y / 2) := Real.sqrt_le_sqrt h

/-! ## 4. Agreement with mathlib's `klDiv` under the transport

On a `Fintype` carrier, `Distribution.klDiv` is exactly mathlib's
`InformationTheory.klDiv` of the transported
measures.  This is the one statement in the file whose conclusion is a
measure-theory object, so — per the instance discipline of
`Probability/DistributionMeasure.lean` — it is also the only one carrying
`[MeasurableSpace A]`.  Nothing above depends on it; it is what makes the
native/transport choice checkable rather than asserted. -/

namespace Distribution

open MeasureTheory ProbabilityTheory

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- Singleton mass of the transported measure. -/
theorem toPMF_toMeasure_singleton (X : Distribution A) (hX : X.isProbDist) (a : A) :
    (toPMF X hX).toMeasure {a} = ENNReal.ofReal (X a) := by
  classical
  rw [show ({a} : Set A) = {x | x = a} by ext x; simp, toPMF_toMeasure_apply, mass_eq_sum]
  simp

/-- Under absolute continuity the transported `X` is a density against the
transported `Y`, the density being the pointwise ratio. -/
theorem toPMF_toMeasure_eq_withDensity (X Y : Distribution A) (hX : X.isProbDist)
    (hY : Y.isProbDist) (hac : X.support ⊆ Y.support) :
    (toPMF X hX).toMeasure
      = (toPMF Y hY).toMeasure.withDensity fun a => ENNReal.ofReal (X a / Y a) := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton,
    toPMF_toMeasure_singleton, toPMF_toMeasure_singleton]
  by_cases h0 : Y a = 0
  · have hX0 : X a = 0 := by
      by_contra h
      exact Finsupp.mem_support_iff.mp (hac (Finsupp.mem_support_iff.mpr h)) h0
    simp [h0, hX0]
  · rw [← ENNReal.ofReal_mul (div_nonneg (hX.1 a) (hY.1 a)), div_mul_cancel₀ _ h0]

/-- **`Distribution.klDiv` is mathlib's `klDiv`**: the Kullback–Leibler divergence of
the transported measures is `ENNReal.ofReal` of the discrete formula, under
absolute continuity. -/
theorem klDiv_toPMF (X Y : Distribution A) (hX : X.isProbDist) (hY : Y.isProbDist)
    (hac : X.support ⊆ Y.support) :
    InformationTheory.klDiv (toPMF X hX).toMeasure (toPMF Y hY).toMeasure
      = ENNReal.ofReal (klDiv X Y) := by
  classical
  set μ := (toPMF X hX).toMeasure with hμ
  set ν := (toPMF Y hY).toMeasure with hν
  have hdens : μ = ν.withDensity fun a => ENNReal.ofReal (X a / Y a) :=
    toPMF_toMeasure_eq_withDensity X Y hX hY hac
  have hAC : μ ≪ ν := hdens ▸ withDensity_absolutelyContinuous ν _
  have hint : Integrable (llr μ ν) μ := .of_finite
  have hrn : μ.rnDeriv ν =ᵐ[μ] fun a => ENNReal.ofReal (X a / Y a) := by
    have h1 : μ.rnDeriv ν =ᵐ[ν] fun a => ENNReal.ofReal (X a / Y a) := by
      conv_lhs => rw [hdens]
      exact Measure.rnDeriv_withDensity ν Measurable.of_discrete
    exact h1.filter_mono hAC.ae_le
  have hllr : llr μ ν =ᵐ[μ] fun a => Real.log (X a / Y a) := by
    filter_upwards [hrn] with a ha
    show Real.log (μ.rnDeriv ν a).toReal = _
    rw [ha, ENNReal.toReal_ofReal (div_nonneg (hX.1 a) (hY.1 a))]
  have hν1 : ν.real Set.univ = 1 := by
    have : IsProbabilityMeasure ν := by rw [hν]; infer_instance
    simp
  have hμ1 : μ.real Set.univ = 1 := by
    have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
    simp
  rw [InformationTheory.klDiv_of_ac_of_integrable hAC hint, integral_congr_ae hllr,
    integral_toPMF_eq_expect X hX, klDiv_eq_expect, hν1, hμ1]
  congr 1
  ring

end Distribution

end Probability
