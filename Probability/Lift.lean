/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.StatisticalDistance
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Group.PosPart

/-!
# Lifting between the three distribution layers

Each probabilistic statement carries the weakest layer at which it is true:
signed `Distribution`, `Distribution.NonNeg`, or
`Distribution.isProbDist`. This module relates those layers through the Jordan
split and normalization.

## The two lifts

* **signed → `NonNeg`, by the Jordan split.**  On `Distribution A = A →₀ ℝ` mathlib's
  lattice-ordered-group positive/negative parts `X⁺`/`X⁻` (`posPart`/`negPart`,
  `Mathlib.Algebra.Order.Group.PosPart`, via `Finsupp`'s lattice on an
  `ℝ`-valued `Finsupp`) *already are* the operator, with `X⁺ - X⁻ = X`
  (`posPart_sub_negPart`) and `X⁺ ⊓ X⁻ = 0`
  (`posPart_inf_negPart_eq_zero`) supplied upstream.  No `Distribution.posPart` is
  introduced. What is added is the `Distribution`-vocabulary face: the pointwise
  formula, nonnegativity of both parts, support disjointness, and transport of
  `Distribution.expect`, `Distribution.weight`, and `Distribution.mass` across
  the split.
* **`NonNeg` → `isProbDist`, by normalization.**  `Distribution.normalize X = |X|⁻¹ • X`
  is a probability distribution as soon as `X` is nonnegative of nonzero
  weight, and `expect`/`mass` transport across it with an explicit factor of
  `X.weight`.

## What lifting does and does not buy

Lifting transports **proofs, not truth**.  The facts that fail one layer down
still fail: monotonicity of expectation, Markov and Cauchy–Schwarz are false on
signed distributions. Jensen fails on a one-point law of mass `1/2` with the
constant concave function `-1`, and the unnormalized variance identity fails
on a one-point law of mass `2` with `f = 1`. A lifted corollary is therefore
always a *different proposition*: it is about the
parts (`mass_ge_le_expect_posPart_div` bounds a signed event mass by the
expectation under `X⁺`, never under `X`), or it carries the weight factor the
normalization introduces (`ConcaveOn.le_map_expect_of_nonNeg`,
`weight_sq_mul_variance_normalize`).  None of them may be read as the original
inequality holding one layer down.

## Demonstrated lifts

* `ConcaveOn.le_map_expect_of_nonNeg` / `ConvexOn.map_expect_le_of_nonNeg` —
  Jensen at the `NonNeg` layer with an explicit weight factor.
* `variance_normalize_eq_expect_sq_sub_sq_expect` and
  `weight_sq_mul_variance_normalize` — the `𝔼[f²] - 𝔼[f]²` variance form below
  `weight = 1`, an identity no weakening of the hypotheses can reach.
* `mass_ge_le_expect_posPart_div` — Markov's inequality for a *signed*
  distribution, stated through its positive part.
-/

noncomputable section

open scoped BigOperators

namespace Probability

/-! ## Generic lattice-ordered-group facts

Two facts about `posPart`/`negPart` that mathlib does not carry and that are
used at both of the levels this file works with (the scalars `ℝ`, and `Distribution A`
itself).  Both are stated in the generality in which they are proved. -/

/-- `a⁺ * a⁻ = 0`: at most one of the two parts of a real number is nonzero.
This is the multiplicative face of `posPart_inf_negPart_eq_zero`. -/
theorem posPart_mul_negPart (a : ℝ) : a⁺ * a⁻ = 0 := by
  rcases le_total a 0 with h | h
  · rw [posPart_eq_zero.mpr h, zero_mul]
  · rw [negPart_eq_zero.mpr h, mul_zero]

/-- `a - a ⊓ b = (a - b)⁺` in a lattice-ordered additive group: the amount by
which `a` exceeds `b` is exactly what the meet discards. -/
theorem sub_inf_eq_posPart_sub {α : Type*} [Lattice α] [AddCommGroup α]
    [AddLeftMono α] (a b : α) : a - a ⊓ b = (a - b)⁺ := by
  rw [posPart_def, sub_eq_add_neg, neg_inf, add_sup, add_neg_cancel,
    ← sub_eq_add_neg, sup_comm]

/-- `a ⊓ b + (a - b)⁺ = a`: the meet plus the one-sided excess rebuilds `a`.
This is the identity behind the diagonal of an optimal coupling, where the
meet is the shared mass and the excess is what must be transported. -/
theorem inf_add_posPart_sub {α : Type*} [Lattice α] [AddCommGroup α]
    [AddLeftMono α] (a b : α) : a ⊓ b + (a - b)⁺ = a := by
  rw [← sub_inf_eq_posPart_sub, add_sub_cancel]

namespace Distribution

variable {A : Type*}

/-! ## The `NonNeg` predicate is the `Finsupp` order

The bridge that makes the lattice-ordered-group vocabulary usable on `Distribution`:
the library's pointwise predicate `Distribution.NonNeg` is mathlib's `0 ≤ X` for the
pointwise order on `A →₀ ℝ`. -/

/-- `Distribution.NonNeg` is the `Finsupp` order relation `0 ≤ X`.  Every mathlib fact
about the ordered group `A →₀ ℝ` reaches a `NonNeg` hypothesis through this. -/
theorem nonNeg_iff_zero_le {X : Distribution A} : X.NonNeg ↔ 0 ≤ X := by
  simp [NonNeg, Finsupp.le_def]

/-! ## Lift 1 — the Jordan split: signed `Distribution` → two `NonNeg` distributions

`X⁺` and `X⁻` are mathlib's `posPart`/`negPart` for the lattice-ordered group
`A →₀ ℝ`.  Reconstruction (`X⁺ - X⁻ = X`, `posPart_sub_negPart`), disjointness
(`X⁺ ⊓ X⁻ = 0`, `posPart_inf_negPart_eq_zero`) and `0 ≤ X⁺`
(`posPart_nonneg`) come from there; the `Distribution` face is below. -/

/-- Pointwise formula for the positive part: `X⁺(a) = max(X(a), 0)`. -/
@[simp]
theorem posPart_apply (X : Distribution A) (a : A) : X⁺ a = max (X a) 0 := by
  simp [posPart_def, Finsupp.sup_apply]

/-- Pointwise formula for the negative part: `X⁻(a) = max(-X(a), 0)`. -/
@[simp]
theorem negPart_apply (X : Distribution A) (a : A) : X⁻ a = max (-X a) 0 := by
  simp [negPart_def, Finsupp.sup_apply]

/-- The positive part is an honest (nonnegative) distribution: this is the
lift itself — a signed `Distribution` produces a `NonNeg` one. -/
theorem nonNeg_posPart (X : Distribution A) : (X⁺).NonNeg := fun a => by
  rw [posPart_apply]; exact le_max_right _ _

/-- The negative part is an honest (nonnegative) distribution. -/
theorem nonNeg_negPart (X : Distribution A) : (X⁻).NonNeg := fun a => by
  rw [negPart_apply]; exact le_max_right _ _

/-- The two parts never charge the same point: `X⁺(a)·X⁻(a) = 0`. -/
theorem posPart_mul_negPart_apply (X : Distribution A) (a : A) : X⁺ a * X⁻ a = 0 := by
  simpa using posPart_mul_negPart (X a)

/-- The two parts have disjoint supports — the `Finsupp` face of
`posPart_inf_negPart_eq_zero`. -/
theorem disjoint_support_posPart_negPart (X : Distribution A) :
    Disjoint (X⁺).support (X⁻).support := by
  refine Finset.disjoint_left.mpr fun a ha ha' => ?_
  have h := posPart_mul_negPart_apply X a
  rcases mul_eq_zero.mp h with h0 | h0
  · exact Finsupp.mem_support_iff.mp ha h0
  · exact Finsupp.mem_support_iff.mp ha' h0

/-- On a nonnegative distribution the split is trivial: `X⁺ = X`. -/
theorem posPart_eq_self_of_nonNeg {X : Distribution A} (hX : X.NonNeg) : X⁺ = X :=
  posPart_eq_self.mpr (nonNeg_iff_zero_le.mp hX)

/-- On a nonnegative distribution the split is trivial: `X⁻ = 0`. -/
theorem negPart_eq_zero_of_nonNeg {X : Distribution A} (hX : X.NonNeg) : X⁻ = 0 :=
  negPart_eq_zero.mpr (nonNeg_iff_zero_le.mp hX)

/-! ### Transport across the split

`expect`, `weight` and `mass` are all linear in a signed distribution, so each
decomposes across `X = X⁺ - X⁻`. These laws turn a claim about signed `X` into
the difference of two claims about nonnegative distributions. -/

/-- Expectation decomposes across the Jordan split:
`𝔼_{X⁺}[f] - 𝔼_{X⁻}[f] = 𝔼_X[f]`.  Signed layer: no hypothesis. -/
theorem expect_posPart_sub_expect_negPart (X : Distribution A) (f : A → ℝ) :
    (X⁺).expect f - (X⁻).expect f = X.expect f := by
  rw [← expect_sub_left, posPart_sub_negPart]

/-- Total weight decomposes across the Jordan split:
`|X⁺| - |X⁻| = |X|`.  Signed layer: no hypothesis. -/
theorem weight_posPart_sub_weight_negPart (X : Distribution A) :
    (X⁺).weight - (X⁻).weight = X.weight := by
  conv_rhs => rw [← posPart_sub_negPart X]
  unfold weight
  exact (Finsupp.sum_sub_index fun _ _ _ => rfl).symm

/-- Event mass decomposes across the Jordan split:
`X⁺(P) - X⁻(P) = X(P)`.  Signed layer: no hypothesis. -/
theorem mass_posPart_sub_mass_negPart (X : Distribution A) (P : A → Prop) :
    (X⁺).mass P - (X⁻).mass P = X.mass P := by
  classical
  conv_rhs => rw [← posPart_sub_negPart X]
  unfold mass
  refine (Finsupp.sum_sub_index fun a b₁ b₂ => ?_).symm
  by_cases h : P a <;> simp [h]

/-- A signed distribution never charges an event more than its positive part
does.  This is the inequality that carries `NonNeg`-layer facts to signed
statements — see `mass_ge_le_expect_posPart_div`. -/
theorem mass_le_mass_posPart (X : Distribution A) (P : A → Prop) :
    X.mass P ≤ (X⁺).mass P := by
  rw [← mass_posPart_sub_mass_negPart X P]
  simpa using (nonNeg_negPart X).mass_nonneg P

/-! ### The split and `statDist`

`statDist` is the one-sided excess `∑_a max(X(a) - Y(a), 0)`, i.e. exactly the
total weight of the positive part of `X - Y`. -/

/-- **`statDist` is the weight of a positive part**: `δ(X, Y) = |(X - Y)⁺|`.
No layer hypothesis and no `Fintype` assumption are required. -/
theorem statDist_eq_weight_posPart (X Y : Distribution A) :
    statDist X Y = ((X - Y)⁺).weight := by
  classical
  have hfun : ∀ a : A, ((X - Y)⁺) a = max (X a - Y a) 0 := fun a => by
    rw [posPart_apply, Finsupp.sub_apply]
  unfold statDist weight Finsupp.sum
  rw [Finset.sum_congr rfl fun a _ => hfun a]
  refine (Finset.sum_subset (fun a ha => ?_) (fun a _ ha => ?_)).symm
  · rw [Finsupp.mem_support_iff] at ha ⊢
    intro h
    rw [Finsupp.sub_apply] at h
    rw [hfun a, h, max_self] at ha
    exact ha rfl
  · rw [Finsupp.notMem_support_iff, hfun a] at ha
    exact ha

/-- A nonnegative distribution of zero total weight is the zero distribution. -/
theorem eq_zero_of_nonNeg_of_weight_eq_zero {X : Distribution A} (hX : X.NonNeg)
    (hw : X.weight = 0) : X = 0 := by
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_contra ha
  have hle : X a ≤ X.weight := by
    unfold weight Finsupp.sum
    exact Finset.single_le_sum (fun a' _ => hX a')
      (Finsupp.mem_support_iff.mpr ha)
  rw [hw] at hle
  exact ha (le_antisymm hle (hX a))

/-- A vanishing statistical distance kills the whole positive part:
`δ(X, Y) = 0 → (X - Y)⁺ = 0`.  The `Distribution`-level form of "each one-sided excess
summand vanishes". -/
theorem posPart_eq_zero_of_statDist_eq_zero {X Y : Distribution A}
    (h : statDist X Y = 0) : (X - Y)⁺ = 0 :=
  eq_zero_of_nonNeg_of_weight_eq_zero (nonNeg_posPart _)
    (by rw [← statDist_eq_weight_posPart, h])

/-- Pointwise face of `posPart_eq_zero_of_statDist_eq_zero`, in the `max`
spelling `statDist` is written in: `δ(X, Y) = 0` kills every one-sided excess
summand `max(X(a) - Y(a), 0)`.  Consumed by the optimal-coupling construction
in `Probability.Coupling`. -/
theorem max_sub_eq_zero_of_statDist_eq_zero {X Y : Distribution A}
    (h : statDist X Y = 0) (a : A) : max (X a - Y a) 0 = 0 := by
  simpa using
    congrArg (fun Z : Distribution A => Z a) (posPart_eq_zero_of_statDist_eq_zero h)

/-! ## Lift 2 — normalization: `NonNeg` → `isProbDist` -/

/-- Weight is homogeneous: `|c · X| = c · |X|`.  Signed layer. -/
theorem weight_smul (c : ℝ) (X : Distribution A) : (c • X).weight = c * X.weight := by
  unfold weight
  rw [Finsupp.sum_smul_index fun _ => rfl]
  unfold Finsupp.sum
  rw [Finset.mul_sum]

/-- Event mass is homogeneous: `(c · X)(P) = c · X(P)`.  Signed layer. -/
theorem mass_smul (c : ℝ) (X : Distribution A) (P : A → Prop) :
    (c • X).mass P = c * X.mass P := by
  classical
  unfold mass
  rw [Finsupp.sum_smul_index fun _ => by simp]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    by_cases h : P a <;> simp [h]

/-- Normalization of a distribution: `X̂ = |X|⁻¹ · X`.  A probability
distribution as soon as `X` is nonnegative of nonzero weight
(`isProbDist_normalize`); the second of the two lifts. -/
def normalize (X : Distribution A) : Distribution A := X.weight⁻¹ • X

/-- Pointwise value of the normalization. -/
@[simp]
theorem normalize_apply (X : Distribution A) (a : A) :
    X.normalize a = X.weight⁻¹ * X a := by
  simp [normalize]

/-- The normalization has total weight one.  Needs only `|X| ≠ 0`:
nonnegativity plays no role in the *weight* computation. -/
theorem weight_normalize {X : Distribution A} (hw : X.weight ≠ 0) :
    X.normalize.weight = 1 := by
  rw [normalize, weight_smul, inv_mul_cancel₀ hw]

/-- Normalization preserves nonnegativity. -/
theorem nonNeg_normalize {X : Distribution A} (hX : X.NonNeg) : X.normalize.NonNeg :=
  fun a => by
    rw [normalize_apply]
    exact mul_nonneg (inv_nonneg.mpr hX.weight_nonneg) (hX a)

/-- **The lift**: a nonnegative distribution of nonzero weight normalizes to a
probability distribution, so every `isProbDist`-layer fact becomes applicable
to `X.normalize`. -/
theorem isProbDist_normalize {X : Distribution A} (hX : X.NonNeg) (hw : X.weight ≠ 0) :
    X.normalize.isProbDist :=
  ⟨nonNeg_normalize hX, weight_normalize hw⟩

/-! ### Transport across the normalization -/

/-- Expectation under the normalization, in terms of expectation under `X`.
Signed layer: no hypothesis (at `|X| = 0` both sides are `0`). -/
theorem expect_normalize (X : Distribution A) (f : A → ℝ) :
    X.normalize.expect f = X.weight⁻¹ * X.expect f := by
  rw [normalize, expect_smul_left]

/-- **Transport law for `expect`**: `𝔼_X[f] = |X| · 𝔼_{X̂}[f]`. -/
theorem expect_eq_weight_mul_expect_normalize {X : Distribution A} (hw : X.weight ≠ 0)
    (f : A → ℝ) : X.expect f = X.weight * X.normalize.expect f := by
  rw [expect_normalize, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]

/-- Event mass under the normalization, in terms of mass under `X`.
Signed layer: no hypothesis. -/
theorem mass_normalize (X : Distribution A) (P : A → Prop) :
    X.normalize.mass P = X.weight⁻¹ * X.mass P := by
  rw [normalize, mass_smul]

/-- **Transport law for `mass`**: `X(P) = |X| · X̂(P)`. -/
theorem mass_eq_weight_mul_mass_normalize {X : Distribution A} (hw : X.weight ≠ 0)
    (P : A → Prop) : X.mass P = X.weight * X.normalize.mass P := by
  rw [mass_normalize, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]

/-! ## Lifted corollaries

Each statement is obtained by running an
`isProbDist`- or `NonNeg`-layer fact through one of the two lifts.  None of
them says the original inequality survives one layer down. -/

/-- **Jensen at the `NonNeg` layer**, concave case:
`𝔼_X[φ∘f] ≤ |X| · φ(𝔼_X[f]/|X|)`.

Jensen itself remains an `isProbDist`-layer fact: on a one-point law of weight
`1/2`, the constant concave function `-1` gives `-1/2 > -1`. The normalization
lift gives the corrected statement with the required weight factor; at
`|X| = 1` it collapses back to
`ConcaveOn.le_map_expect`. -/
theorem _root_.ConcaveOn.le_map_expect_of_nonNeg {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ Set.univ φ) {X : Distribution A} (hX : X.NonNeg)
    (hw : X.weight ≠ 0) (f : A → ℝ) :
    (X.expect fun a => φ (f a))
      ≤ X.weight * φ (X.weight⁻¹ * X.expect f) := by
  rw [expect_eq_weight_mul_expect_normalize hw fun a => φ (f a),
    ← expect_normalize]
  exact mul_le_mul_of_nonneg_left
    (hφ.le_map_expect (isProbDist_normalize hX hw) f) hX.weight_nonneg

/-- **Jensen at the `NonNeg` layer**, convex case:
`|X| · φ(𝔼_X[f]/|X|) ≤ 𝔼_X[φ∘f]`.  See `ConcaveOn.le_map_expect_of_nonNeg` for
why the weight factor is not removable. -/
theorem _root_.ConvexOn.map_expect_le_of_nonNeg {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {X : Distribution A} (hX : X.NonNeg)
    (hw : X.weight ≠ 0) (f : A → ℝ) :
    X.weight * φ (X.weight⁻¹ * X.expect f)
      ≤ X.expect fun a => φ (f a) := by
  rw [expect_eq_weight_mul_expect_normalize hw fun a => φ (f a),
    ← expect_normalize]
  exact mul_le_mul_of_nonneg_left
    (hφ.map_expect_le (isProbDist_normalize hX hw) f) hX.weight_nonneg

/-- **The `𝔼[f²] - 𝔼[f]²` variance form below `weight = 1`**:
`Var_{X̂} f = 𝔼_X[f²]/|X| - (𝔼_X[f]/|X|)²`.

`variance_eq_expect_sq_sub_sq_expect` needs `weight = 1` and the need is real —
on a one-point law of mass `2` with `f = 1`, the subtracted form is
`2 - 2² = -2`. The normalization lift makes the identity available for `X̂`
rather than `X`. Signed layer in `X`: only `|X| ≠ 0` is used. -/
theorem variance_normalize_eq_expect_sq_sub_sq_expect {X : Distribution A}
    (hw : X.weight ≠ 0) (f : A → ℝ) :
    X.normalize.variance f
      = X.weight⁻¹ * (X.expect fun a => f a ^ 2)
          - (X.weight⁻¹ * X.expect f) ^ 2 := by
  rw [variance_eq_expect_sq_sub_sq_expect (weight_normalize hw),
    expect_normalize, expect_normalize]

/-- The same identity cleared of inverses: `|X|² · Var_{X̂} f =
|X| · 𝔼_X[f²] - 𝔼_X[f]²`.  This is the `𝔼[f²] - 𝔼[f]²` variance form carrying
its explicit weight factor, in pure `Distribution` vocabulary. -/
theorem weight_sq_mul_variance_normalize {X : Distribution A} (hw : X.weight ≠ 0)
    (f : A → ℝ) :
    X.weight ^ 2 * X.normalize.variance f
      = X.weight * (X.expect fun a => f a ^ 2) - X.expect f ^ 2 := by
  rw [variance_normalize_eq_expect_sq_sub_sq_expect hw]
  field_simp

/-- `𝔼_X[f]² ≤ |X| · 𝔼_X[f²]` at the `NonNeg` layer: the sign of the
subtracted variance form, with its weight factor.  At `|X| = 1` this is
`expect_sq_sub_sq_expect_nonneg`.

(The same inequality also follows from `expect_mul_sq_le_sq_mul_sq` at `u = 1`;
it is stated here because it is what the variance lift delivers, and because it
is the honest `NonNeg`-layer replacement for a bound that is *false* without
the factor — at weight 2 with `f ≡ 1`, `𝔼[f]² = 4 > 2 = 𝔼[f²]`.) -/
theorem sq_expect_le_weight_mul_expect_sq {X : Distribution A} (hX : X.NonNeg)
    (f : A → ℝ) :
    X.expect f ^ 2 ≤ X.weight * X.expect fun a => f a ^ 2 := by
  by_cases hw : X.weight = 0
  · rw [eq_zero_of_nonNeg_of_weight_eq_zero hX hw]
    simp
  · have h : 0 ≤ X.weight ^ 2 * X.normalize.variance f :=
      mul_nonneg (sq_nonneg _)
        (variance_nonneg (nonNeg_normalize hX) f)
    rw [weight_sq_mul_variance_normalize hw] at h
    linarith

/-- **Markov's inequality for a signed distribution**, through the positive
part: `X{a | c ≤ f a} ≤ 𝔼_{X⁺}[f]/c`.

This is not Markov for `X`: with masses `1,-1`, values `1,2`, and threshold
`1`, the event has mass `0` while the expectation is `-1`. The expectation on
the right is therefore taken under `X⁺`. The statement collapses to
`mass_ge_le_expect_div` when `X` is already nonnegative
(`posPart_eq_self_of_nonNeg`). -/
theorem mass_ge_le_expect_posPart_div (X : Distribution A) {f : A → ℝ}
    (hf : ∀ a, 0 ≤ f a) {c : ℝ} (hc : 0 < c) :
    X.mass (fun a => c ≤ f a) ≤ (X⁺).expect f / c :=
  (mass_le_mass_posPart X _).trans (mass_ge_le_expect_div (nonNeg_posPart X) hf hc)

/-! ## The overlap calculus (Lanzenberger Lemma 2.3)

Lemma 2.3 splits a law against another into the part they **share** and the
part by which the first **exceeds** the second.  Both are already here: the
shared part is the lattice meet `X ⊓ Y` and the excess is the positive part
`(X - Y)⁺`, and `inf_add_posPart_sub` is Lemma 2.3's split.  What follows is
the `weight`/`statDist` face of that split. The shared and excess parts are the
existing lattice operations; only their weight arithmetic is added. -/

/-- Pointwise formula for the meet: `(X ⊓ Y)(a) = min(X(a), Y(a))`. -/
@[simp]
theorem inf_apply (X Y : Distribution A) (a : A) : (X ⊓ Y) a = min (X a) (Y a) := by
  rw [Finsupp.inf_apply]

theorem inf_le_left_apply (X Y : Distribution A) (a : A) : (X ⊓ Y) a ≤ X a := by
  rw [inf_apply]; exact min_le_left _ _

theorem inf_le_right_apply (X Y : Distribution A) (a : A) : (X ⊓ Y) a ≤ Y a := by
  rw [inf_apply]; exact min_le_right _ _

/-- The shared part of two honest laws is honest. -/
theorem nonNeg_inf {X Y : Distribution A} (hX : X.NonNeg) (hY : Y.NonNeg) :
    (X ⊓ Y).NonNeg := fun a => by
  rw [inf_apply]; exact le_min (hX a) (hY a)

/-- A point mass with nonnegative weight is honest. -/
theorem single_nonNeg {c : ℝ} (hc : 0 ≤ c) (a : A) :
    NonNeg (Finsupp.single a c : Distribution A) := by
  classical
  intro a'
  rw [Finsupp.single_apply]
  split
  · exact hc
  · exact le_rfl

/-- The gap between two ordered laws is honest. -/
theorem nonNeg_sub_of_le {X Y : Distribution A} (h : X ≤ Y) : (Y - X).NonNeg :=
  fun a => by
    rw [Finsupp.sub_apply]
    exact sub_nonneg.mpr (Finsupp.le_def.mp h a)

/-- Restoring a law from a part of it and the gap. -/
theorem add_sub_cancel' (X Y : Distribution A) : X + (Y - X) = Y :=
  Finsupp.ext fun a => by simp

/-- Weight is additive. -/
theorem weight_add (X Y : Distribution A) :
    (X + Y).weight = X.weight + Y.weight :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- Weight is subtractive. -/
theorem weight_sub (X Y : Distribution A) :
    (X - Y).weight = X.weight - Y.weight := by
  have h := weight_add (X - Y) Y
  rw [sub_add_cancel] at h
  linarith

/-- The weight of a point mass is its mass. -/
@[simp]
theorem weight_single (a : A) (c : ℝ) :
    weight (Finsupp.single a c : Distribution A) = c := by
  unfold weight
  exact Finsupp.sum_single_index rfl

/-- Weight is monotone. -/
theorem weight_le_weight_of_le {X Y : Distribution A} (h : X ≤ Y) :
    X.weight ≤ Y.weight := by
  have := (nonNeg_sub_of_le h).weight_nonneg
  rw [weight_sub] at this
  linarith

/-- The weight of the shared part, as a sum of pointwise minima over any finite
set covering both supports. -/
theorem weight_inf [DecidableEq A] (X Y : Distribution A) :
    (X ⊓ Y).weight = ∑ a ∈ X.support ∪ Y.support, min (X a) (Y a) := by
  have hsub : (X ⊓ Y).support ⊆ X.support ∪ Y.support := by
    intro a ha
    rw [Finsupp.mem_support_iff, inf_apply] at ha
    by_contra hc
    rw [Finset.mem_union] at hc
    push Not at hc
    rw [Finsupp.notMem_support_iff.mp hc.1, Finsupp.notMem_support_iff.mp hc.2] at ha
    exact ha (min_self 0)
  rw [weight_eq_sum_of_support_subset (X ⊓ Y) hsub]
  exact Finset.sum_congr rfl fun a _ => inf_apply X Y a

/-- **Lemma 2.3's overlap formula**: the one-sided distance is the first
weight minus the weight of the shared part.  This is the identity the
attainment construction maximizes against — making `δ` large is making the
overlap small. -/
theorem statDist_eq_weight_sub_weight_inf (X Y : Distribution A) :
    statDist X Y = X.weight - (X ⊓ Y).weight := by
  have hsplit : (X ⊓ Y) + (X - Y)⁺ = X := inf_add_posPart_sub X Y
  have hw := congrArg weight hsplit
  rw [weight_add, ← statDist_eq_weight_posPart] at hw
  linarith

/-- Shifting both laws by a common summand leaves the distance alone. -/
theorem statDist_add_add_left (X Y Z : Distribution A) :
    statDist (X + Y) (X + Z) = statDist Y Z := by
  rw [statDist_eq_weight_posPart, statDist_eq_weight_posPart,
    add_sub_add_left_eq_sub]

/-- Removing a common part from both laws leaves the distance unchanged. No
nonnegativity hypothesis is needed because the difference is unchanged. -/
theorem statDist_sub_sub (X Y E : Distribution A) :
    statDist (X - E) (Y - E) = statDist X Y := by
  rw [statDist_eq_weight_posPart, statDist_eq_weight_posPart,
    sub_sub_sub_cancel_right]

/-- The weight gap is a lower bound on the one-sided distance. -/
theorem weight_sub_weight_le_statDist (X Y : Distribution A) :
    X.weight - Y.weight ≤ statDist X Y := by
  classical
  rw [statDist_eq_weight_sub_weight_inf]
  have : (X ⊓ Y).weight ≤ Y.weight :=
    weight_le_weight_of_le (Finsupp.le_def.mpr (inf_le_right_apply X Y))
  linarith

/-- Scaling both laws by a nonnegative factor scales the distance. -/
theorem statDist_smul {c : ℝ} (hc : 0 ≤ c) (X Y : Distribution A) :
    statDist (c • X) (c • Y) = c * statDist X Y := by
  classical
  have hsub : ((c • X : Distribution A) - c • Y).support ⊆ (X - Y).support := by
    intro a ha
    rw [Finsupp.mem_support_iff] at ha ⊢
    intro h
    refine ha ?_
    have h' : X a - Y a = 0 := by simpa [Finsupp.sub_apply] using h
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [← mul_sub, h', mul_zero]
  rw [statDist_eq_sum_of_support_subset (c • X) (c • Y) hsub, statDist,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [← mul_sub, mul_max_of_nonneg _ _ hc, mul_zero]

/-- A filter that keeps nothing on the support is the zero law. -/
theorem filter_of_forall_not (X : Distribution A) (P : A → Prop)
    [DecidablePred P] (h : ∀ a ∈ X.support, ¬ P a) : X.filter P = 0 :=
  Finsupp.ext fun a => by
    rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
    by_cases ha : a ∈ X.support
    · exact if_neg (h a ha)
    · rw [Finsupp.notMem_support_iff.mp ha, ite_self]

/-- A filter that keeps everything on the support is the identity. -/
theorem filter_of_forall (X : Distribution A) (P : A → Prop)
    [DecidablePred P] (h : ∀ a ∈ X.support, P a) : X.filter P = X :=
  Finsupp.ext fun a => by
    rw [Finsupp.filter_apply]
    by_cases ha : a ∈ X.support
    · exact if_pos (h a ha)
    · rw [Finsupp.notMem_support_iff.mp ha, ite_self]

/-- Filtering after a pushforward is pushing forward the pulled-back filter. -/
theorem filter_fTransform {B : Type*} (g : A → B) (X : Distribution A)
    (P : B → Prop) [DecidablePred P] [DecidablePred fun a => P (g a)] :
    (fTransform g X).filter P = fTransform g (X.filter fun a => P (g a)) :=
  Finsupp.ext fun b => by
    rw [Finsupp.filter_apply, fTransform_apply_eq_mass, fTransform_apply_eq_mass,
      show mass (Finsupp.filter (fun a => P (g a)) X) (fun a => g a = b)
          = X.mass (fun a => g a = b ∧ P (g a)) from mass_filter X _ _]
    by_cases hb : P b
    · rw [if_pos hb]
      exact mass_congr X fun a => ⟨fun h => ⟨h, h.symm ▸ hb⟩, And.left⟩
    · rw [if_neg hb]
      exact (mass_eq_zero_of_forall_not X
        fun a (hc : g a = b ∧ P (g a)) => hb (hc.1 ▸ hc.2)).symm

end Distribution

end Probability
