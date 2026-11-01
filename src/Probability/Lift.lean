import Probability.StatisticalDistance
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Group.PosPart

/-!
# Positive parts, normalization and overlaps

Relates signed, nonnegative and probability distributions.

## Main definitions

* `X⁺`, `X⁻`: the positive and negative parts of a distribution (the lattice
  parts of `A →₀ ℝ`)
* `normalize X`: `|X|⁻¹ • X`, of weight `1` when `|X| ≠ 0`
* `normalizeOr X hX fallback`: for `X ≥ 0`, `normalize X` at nonzero weight and the explicit
  probability law `fallback` at weight zero
* `X ⊓ Y`: the pointwise minimum of two distributions

## Main results

* `nonNeg_iff_zero_le`, `posPart_apply`, `negPart_apply`, `nonNeg_posPart`
* `statDist_eq_weight_posPart`: `δ(X, Y) = |(X − Y)⁺|`
* `statDist_eq_weight_sub_weight_inf`: `δ(X, Y) = |X| − |X ⊓ Y|`, the overlap formula of
  [1, Definition 3, p. 10]
* `isProbDist_normalize`: `normalize X` is a probability law for `X ≥ 0` with `|X| ≠ 0`
* `weight_smul_normalizeOr`: `|X| • normalizeOr X hX fallback = X`, including at weight zero,
  where nonnegativity forces `X = 0`
* `mass_finset_sum`: `(∑ i ∈ s, Xᵢ)(E) = ∑ i ∈ s, Xᵢ(E)` for signed laws; with `mass_smul`,
  this computes event probabilities in mixtures from their component masses.

## References

1. D. Lanzenberger and U. Maurer. Coupling of Random Systems. In *Theory of Cryptography
   (TCC 2020)*, Springer, 2020. Cryptology ePrint Archive, Paper 2020/1187.
-/

noncomputable section

open scoped BigOperators

namespace Probability

/-! ## Generic lattice-ordered-group facts -/

/-- `a⁺ * a⁻ = 0`: at most one of the two parts of a real number is nonzero.
This is the multiplicative face of `posPart_inf_negPart_eq_zero`. -/
lemma posPart_mul_negPart (a : ℝ) : a⁺ * a⁻ = 0 := by
  rcases le_total a 0 with h | h
  · rw [posPart_eq_zero.mpr h, zero_mul]
  · rw [negPart_eq_zero.mpr h, mul_zero]

/-- `a - a ⊓ b = (a - b)⁺` in a lattice-ordered additive group: the amount by
which `a` exceeds `b` is exactly what the meet discards. -/
lemma sub_inf_eq_posPart_sub {α : Type*} [Lattice α] [AddCommGroup α]
    [AddLeftMono α] (a b : α) : a - a ⊓ b = (a - b)⁺ := by
  rw [posPart_def, sub_eq_add_neg, neg_inf, add_sup, add_neg_cancel,
    ← sub_eq_add_neg, sup_comm]

/-- `a ⊓ b + (a - b)⁺ = a`: the meet plus the one-sided excess rebuilds `a`.
This is the identity behind the diagonal of an optimal coupling, where the
meet is the shared mass and the excess is what must be transported. -/
lemma inf_add_posPart_sub {α : Type*} [Lattice α] [AddCommGroup α]
    [AddLeftMono α] (a b : α) : a ⊓ b + (a - b)⁺ = a := by
  rw [← sub_inf_eq_posPart_sub, add_sub_cancel]

namespace Distribution

variable {A : Type*}

/-! ## The `NonNeg` predicate is the `Finsupp` order -/

/-- `Distribution.NonNeg` is the `Finsupp` order relation `0 ≤ X`.  Every mathlib fact
about the ordered group `A →₀ ℝ` reaches a `NonNeg` hypothesis through this. -/
lemma nonNeg_iff_zero_le {X : Distribution A} : X.NonNeg ↔ 0 ≤ X := by
  simp [NonNeg, Finsupp.le_def]

/-! ## Positive and negative parts -/

/-- Pointwise formula for the positive part: `X⁺(a) = max(X(a), 0)`. -/
@[simp]
lemma posPart_apply (X : Distribution A) (a : A) : X⁺ a = max (X a) 0 := by
  simp [posPart_def, Finsupp.sup_apply]

/-- Pointwise formula for the negative part: `X⁻(a) = max(-X(a), 0)`. -/
@[simp]
lemma negPart_apply (X : Distribution A) (a : A) : X⁻ a = max (-X a) 0 := by
  simp [negPart_def, Finsupp.sup_apply]

/-- The positive part is an honest (nonnegative) distribution: this is the
lift itself — a signed `Distribution` produces a `NonNeg` one. -/
lemma nonNeg_posPart (X : Distribution A) : (X⁺).NonNeg := fun a => by
  rw [posPart_apply]; exact le_max_right _ _

/-- The two parts never charge the same point: `X⁺(a)·X⁻(a) = 0`. -/
lemma posPart_mul_negPart_apply (X : Distribution A) (a : A) : X⁺ a * X⁻ a = 0 := by
  simpa using posPart_mul_negPart (X a)

/-! ### The split and `statDist` -/

/-- **`statDist` is the weight of a positive part**: `δ(X, Y) = |(X - Y)⁺|`.
No layer hypothesis and no `Fintype` assumption are required. -/
lemma statDist_eq_weight_posPart (X Y : Distribution A) :
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
lemma eq_zero_of_nonNeg_of_weight_eq_zero {X : Distribution A} (hX : X.NonNeg)
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
lemma mass_smul (c : ℝ) (X : Distribution A) (P : A → Prop) :
    (c • X).mass P = c * X.mass P := by
  classical
  unfold mass
  rw [Finsupp.sum_smul_index fun _ => by simp]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by
    by_cases h : P a <;> simp [h]

/-- **Event mass of a finite sum**: for signed laws `Xᵢ` and an event `E`,
`(∑ i ∈ s, Xᵢ)(E) = ∑ i ∈ s, Xᵢ(E)`. Neither nonnegativity nor normalization is needed.
With `mass_smul`, it gives mixture event masses `(∑ₖ P(k) • Xₖ)(E) = ∑ₖ P(k) · Xₖ(E)`. -/
lemma mass_finset_sum {I X : Type*} (s : Finset I) (laws : I → Distribution X)
    (event : X → Prop) :
    (∑ i ∈ s, laws i).mass event = ∑ i ∈ s, (laws i).mass event := by
  classical
  induction s using Finset.induction with
  -- The empty family assigns zero mass to the event.
  | empty => simp only [Finset.sum_empty, mass, Finsupp.sum_zero_index]
  -- Adding one law adds its event mass; the remaining family satisfies the identity by induction.
  | insert i s hi ih => rw [Finset.sum_insert hi, mass_add, ih, Finset.sum_insert hi]

/-- Normalization of a distribution: `X̂ = |X|⁻¹ · X`.  A probability
distribution as soon as `X` is nonnegative of nonzero weight
(`isProbDist_normalize`); the second of the two lifts. -/
def normalize (X : Distribution A) : Distribution A := X.weight⁻¹ • X

/-- Pointwise value of the normalization. -/
@[simp]
lemma normalize_apply (X : Distribution A) (a : A) :
    X.normalize a = X.weight⁻¹ * X a := by
  simp [normalize]

/-- Dividing a nonnegative law of nonzero weight by its weight gives a probability law:
`|X|⁻¹ · X(a) ≥ 0` and `|X|⁻¹ • X` has weight `|X|⁻¹ · |X| = 1`. -/
lemma isProbDist_normalize
    -- `hX`: `X ≥ 0` pointwise; `hw`: `|X| ≠ 0`, so `|X|⁻¹ · |X| = 1`.
    {X : Distribution A} (hX : X.NonNeg) (hw : X.weight ≠ 0) :
    X.normalize.isProbDist := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [normalize_apply]
    exact mul_nonneg (inv_nonneg.mpr hX.weight_nonneg) (hX a)
  · rw [normalize, weight_smul, inv_mul_cancel₀ hw]

open Classical in
/-- `normalizeOr X hX fallback = normalize X` when `|X| ≠ 0`, and exactly `fallback` when
`|X| = 0`. It is a probability law for every nonnegative `X`. `weight_smul_normalizeOr`
rescales by `|X|`, so at weight zero `fallback` is multiplied by `0`. -/
def normalizeOr
    -- `X` is a finitely supported mass function on `A`; `hX` makes its masses nonnegative.
    (X : Distribution A) (hX : X.NonNeg)
    -- `fallback`: the caller's probability law, returned when `|X| = 0`.
    (fallback : ProbDist A) : ProbDist A :=
  if hw : X.weight = 0 then fallback else ⟨X.normalize, isProbDist_normalize hX hw⟩

/-- Scaling the normalized law by the original weight recovers every mass:
`|X| • normalizeOr X hX fallback = X`, for every `fallback`. At `|X| = 0` both sides vanish:
the left is `0 • fallback`, and a nonnegative `X` of weight zero is `0`. -/
lemma weight_smul_normalizeOr
    -- `X ≥ 0` by `hX`; `fallback` is any probability law on `A`.
    (X : Distribution A) (hX : X.NonNeg) (fallback : ProbDist A) :
    X.weight • (X.normalizeOr hX fallback).1 = X := by
  classical
  unfold normalizeOr
  split_ifs with hw
  · -- A nonnegative law of weight zero vanishes at every point.
    rw [hw, zero_smul, eq_zero_of_nonNeg_of_weight_eq_zero hX hw]
  · -- At positive weight, `|X| · |X|⁻¹ · X = X`.
    change X.weight • (X.weight⁻¹ • X) = X
    rw [smul_smul, mul_inv_cancel₀ hw, one_smul]

/-! ## Overlaps -/

/-- Pointwise formula for the meet: `(X ⊓ Y)(a) = min(X(a), Y(a))`. -/
@[simp]
lemma inf_apply (X Y : Distribution A) (a : A) : (X ⊓ Y) a = min (X a) (Y a) := by
  rw [Finsupp.inf_apply]

/-- A point mass with nonnegative weight is honest. -/
lemma single_nonNeg {c : ℝ} (hc : 0 ≤ c) (a : A) :
    NonNeg (Finsupp.single a c : Distribution A) := by
  classical
  intro a'
  rw [Finsupp.single_apply]
  split
  · exact hc
  · exact le_rfl

/-- Weight is subtractive. -/
lemma weight_sub (X Y : Distribution A) :
    (X - Y).weight = X.weight - Y.weight := by
  have h := weight_add (X - Y) Y
  rw [sub_add_cancel] at h
  linarith

/-- The overlap formula [1, Definition 3, p. 10]: “δ(X, Y) = |X| − ∑ₐ min(X(a), Y(a))”.
Here `X ⊓ Y` is the pointwise shared mass. The identity also holds for signed laws. -/
theorem statDist_eq_weight_sub_weight_inf (X Y : Distribution A) :
    statDist X Y = X.weight - (X ⊓ Y).weight := by
  have hsplit : (X ⊓ Y) + (X - Y)⁺ = X := inf_add_posPart_sub X Y
  have hw := congrArg weight hsplit
  rw [weight_add, ← statDist_eq_weight_posPart] at hw
  linarith

end Distribution

end Probability
