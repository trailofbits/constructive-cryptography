import Probability.StatisticalDistance
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Group.PosPart

/-!
# Positive parts, normalization and overlaps

Relates signed, nonnegative and probability distributions.

## Main definitions

* `X⁺`, `X⁻`: the positive and negative parts of a distribution (the lattice
  parts of `A →₀ ℝ`)
* `normalize X`: `X` scaled to weight `1`
* `X ⊓ Y`: the pointwise minimum of two distributions

## Main results

* `nonNeg_iff_zero_le`, `posPart_apply`, `negPart_apply`, `nonNeg_posPart`
* `statDist_eq_weight_posPart`: `δ(X, Y) = |(X − Y)⁺|`
* `statDist_eq_weight_sub_weight_inf`: `δ(X, Y) = |X| − |X ⊓ Y|`
-/

noncomputable section

open scoped BigOperators

namespace Probability

/-! ## Generic lattice-ordered-group facts -/

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

/-! ## The `NonNeg` predicate is the `Finsupp` order -/

/-- `Distribution.NonNeg` is the `Finsupp` order relation `0 ≤ X`.  Every mathlib fact
about the ordered group `A →₀ ℝ` reaches a `NonNeg` hypothesis through this. -/
theorem nonNeg_iff_zero_le {X : Distribution A} : X.NonNeg ↔ 0 ≤ X := by
  simp [NonNeg, Finsupp.le_def]

/-! ## Positive and negative parts -/

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

/-- The two parts never charge the same point: `X⁺(a)·X⁻(a) = 0`. -/
theorem posPart_mul_negPart_apply (X : Distribution A) (a : A) : X⁺ a * X⁻ a = 0 := by
  simpa using posPart_mul_negPart (X a)

/-! ### The split and `statDist` -/

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

/-! ## Normalization -/

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

/-! ## Overlaps -/

/-- Pointwise formula for the meet: `(X ⊓ Y)(a) = min(X(a), Y(a))`. -/
@[simp]
theorem inf_apply (X Y : Distribution A) (a : A) : (X ⊓ Y) a = min (X a) (Y a) := by
  rw [Finsupp.inf_apply]

/-- A point mass with nonnegative weight is honest. -/
theorem single_nonNeg {c : ℝ} (hc : 0 ≤ c) (a : A) :
    NonNeg (Finsupp.single a c : Distribution A) := by
  classical
  intro a'
  rw [Finsupp.single_apply]
  split
  · exact hc
  · exact le_rfl

/-- Weight is subtractive. -/
theorem weight_sub (X Y : Distribution A) :
    (X - Y).weight = X.weight - Y.weight := by
  have h := weight_add (X - Y) Y
  rw [sub_add_cancel] at h
  linarith

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

end Distribution

end Probability
