module

public import Probability.Counting
public import Probability.Expectation
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Prod

/-!
# Collision lower bounds for arbitrary maps

Upper bounds on collision probabilities (`Probability.Counting.uniform_mass_not_injOn_le_choose`)
have matching lower bounds that need no uniformity of the map. For any `f : M → T`:

* **Cauchy–Schwarz**: two independent samples of any distribution on `T` points coincide with
  probability at least `1 / |T|` (`pair_collision_mass_ge`); hence two distinct uniform inputs
  collide under `f` with probability at least `1 / |T| - 1 / |M|`
  (`distinct_pair_collision_mass_ge`).
* **Second moment (Paley–Zygmund)**: the number `crossCount f` of equal-label pairs between two
  independent uniform batches of size `m = |I|` is positive with probability at least
  `m² / (2 (m² + |T|))` (`crossCount_nonzero_mass_ge`), so two batches contain a cross
  collision of distinct inputs with probability at least
  `m² / (2 (m² + |T|)) - m² / |M|` (`distinct_cross_collision_mass_ge`).

```text
E[X]² ≤ Pr[X ≠ 0] · E[X²]       (Distribution.expect_sq_le_mass_ne_zero_mul_second)
E[X]  = m² · Σ_t p_t²,   E[X²] ≤ 2 m² p₂ (m² p₂ + 1)       (crossCount_mean, crossCount_second_le)
p₂ = Σ_t p_t² ≥ 1 / |T|                                  (pair_collision_mass_ge)
```

The cubic moment `Σ_t p_t³` in `E[X²]` is absorbed algebraically (`cubic_moment_le`), so the
bound holds for biased label distributions.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Probability.Counting

open scoped BigOperators

noncomputable section

universe u v w

/-! ### Two samples -/

/-- Collision probability of two independent samples of `P`: `Σ_x P(x)²`, with no uniformity
assumption. -/
lemma pair_collision_mass {X : Type u} [Fintype X] (P : Distribution X) :
    (P.prod P).mass (fun pair => pair.1 = pair.2) = ∑ x, P x ^ 2 := by
  classical
  -- Sum over all pairs; only the diagonal `(x, x)` contributes `P x · P x`.
  rw [Distribution.mass_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => ite_eq_right (Ne.symm hb))
    (fun ha => absurd (Finset.mem_univ a) ha), ite_eq_left rfl, Distribution.prod_apply, sq]

/-- **Cauchy–Schwarz collision bound**: a normalized distribution on `|X|` points has collision
probability at least `1 / |X|`. -/
theorem pair_collision_mass_ge {X : Type u} [Fintype X] [Nonempty X]
    (P : Distribution X) (hw : P.weight = 1) :
    1 / (Fintype.card X : ℝ) ≤ (P.prod P).mass (fun pair => pair.1 = pair.2) := by
  rw [pair_collision_mass]
  -- `(Σ_x 1 · P x)² ≤ |X| · Σ_x P x²` with `Σ_x P x = 1`.
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset X)
    (fun _ => (1 : ℝ)) (fun x => P x)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Distribution.weight_eq_sum, hw, one_pow] at hc
  exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card X)).mpr
    (by nlinarith only [hc])

/-- Two independent uniform values coincide with probability exactly `1 / |T|`. -/
lemma uniform_pair_collision_mass {T : Type u} [Fintype T] [Nonempty T] :
    (Distribution.uniform (T × T)).mass (fun pair => pair.1 = pair.2) =
      1 / (Fintype.card T : ℝ) := by
  rw [← Distribution.prod_uniform, pair_collision_mass]
  simp only [Distribution.uniform_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hpos : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  field_simp

/-- **Distinct-input collisions of an arbitrary map**: two uniform inputs `(m₀, m₁)` with
`m₀ ≠ m₁` and `f m₀ = f m₁` occur with probability at least `1 / |T| - 1 / |M|`, even for a
biased `f`. -/
theorem distinct_pair_collision_mass_ge {M : Type u} {T : Type v} [Fintype M] [Nonempty M]
    [Fintype T] [Nonempty T] (f : M → T) :
    1 / (Fintype.card T : ℝ) - 1 / (Fintype.card M : ℝ) ≤
      (Distribution.uniform (M × M)).mass
        (fun pair => pair.1 ≠ pair.2 ∧ f pair.1 = f pair.2) := by
  classical
  -- The pushforward `f_* 𝒰(M)` collides with probability at least `1 / |T|`.
  let P := Distribution.fTransform f (Distribution.uniform M)
  have hc := pair_collision_mass_ge P
    ((Distribution.weight_fTransform f _).trans Distribution.weight_uniform)
  rw [← Distribution.fTransform_prod, Distribution.mass_fTransform,
    Distribution.prod_uniform] at hc
  -- Split label collisions into equal and distinct inputs; equal inputs have mass `1 / |M|`.
  have hs := Distribution.mass_and_add_mass_not_and (Distribution.uniform (M × M))
    (fun pair => pair.1 = pair.2) (fun pair => f pair.1 = f pair.2)
  have he : (Distribution.uniform (M × M)).mass
      (fun pair => pair.1 = pair.2 ∧ f pair.1 = f pair.2) =
        1 / (Fintype.card M : ℝ) := by
    rw [Distribution.mass_congr _ (fun pair : M × M =>
      show (pair.1 = pair.2 ∧ f pair.1 = f pair.2) ↔ pair.1 = pair.2 from
        ⟨And.left, fun h => ⟨h, congrArg f h⟩⟩)]
    exact uniform_pair_collision_mass
  rw [he] at hs
  change 1 / (Fintype.card T : ℝ) ≤
    (Distribution.uniform (M × M)).mass (fun pair => f pair.1 = f pair.2) at hc
  linarith only [hc, hs]

/-- Four independent uniform values form two equal pairs with probability `1 / |T|²`. -/
lemma uniform_two_pairs_mass {T : Type u} [Fintype T] [Nonempty T] :
    (Distribution.uniform (Bool ⊕ Bool → T)).mass
      (fun f => f (.inl false) = f (.inl true) ∧ f (.inr false) = f (.inr true)) =
        1 / (Fintype.card T : ℝ) ^ 2 := by
  rw [← Distribution.fTransform_equiv_uniform
    (Equiv.sumArrowEquivProdArrow Bool Bool T).symm, Distribution.mass_fTransform]
  change (Distribution.uniform ((Bool → T) × (Bool → T))).mass
    (fun f => f.1 false = f.1 true ∧ f.2 false = f.2 true) = _
  rw [← Distribution.prod_uniform,
    Distribution.mass_prod_and (Distribution.uniform (Bool → T))
      (Distribution.uniform (Bool → T)) (fun f => f false = f true)
      (fun f => f false = f true)]
  have hm : (Distribution.uniform (Bool → T)).mass (fun f => f false = f true) =
      1 / (Fintype.card T : ℝ) := by
    rw [← Distribution.fTransform_equiv_uniform (Equiv.boolArrowEquivProd T).symm,
      Distribution.mass_fTransform]
    exact uniform_pair_collision_mass
  rw [hm]
  ring

/-! ### Cross collisions between two independent batches -/

/-- One coordinate of a uniform function is uniform. -/
lemma fTransform_eval_uniform {X : Type u} {Y : Type v} [Fintype X] [DecidableEq X]
    [Fintype Y] [Nonempty Y] (x : X) :
    Distribution.fTransform (fun f : X → Y => f x) (Distribution.uniform (X → Y)) =
      Distribution.uniform Y := by
  classical
  have he := fTransform_eval_uniform_eq_uniform (Y := Y) (fun _ : Unit => x)
    (fun _ _ _ => Subsingleton.elim _ _)
  have hh := congrArg (Distribution.fTransform (Equiv.funUnique Unit Y)) he
  rw [Distribution.fTransform_fTransform, Distribution.fTransform_equiv_uniform] at hh
  exact hh

/-- Expectation of a product of functions of independent uniform coordinates. -/
lemma expect_uniform_product_mul {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (g : A → ℝ) (h : B → ℝ) :
    (Distribution.uniform (A × B)).expect (fun pair => g pair.1 * h pair.2) =
      (Distribution.uniform A).expect g * (Distribution.uniform B).expect h := by
  classical
  rw [← Distribution.prod_uniform, Distribution.expect_prod_eq]
  simp only [Distribution.expect_const_mul]
  rw [Distribution.expect_congr_of_support (fun _ _ => mul_comm _ _),
    Distribution.expect_const_mul, mul_comm]

-- `M` carries inputs, `T` labels and `I` batch positions; `f : M → T` is an arbitrary map.
variable {M : Type u} {T : Type v} {I : Type w} [Fintype M] [Nonempty M] [Fintype T]
  [Fintype I] [DecidableEq I]

/-- Number of positions of the batch `seed : I → M` whose label under `f` is `value`. -/
def labelCount (f : M → T) (value : T) (seed : I → M) : ℝ := by
  classical
  exact ∑ i, if f (seed i) = value then 1 else 0

/-- Evaluating one coordinate of a uniform batch averages over a uniform input. -/
lemma expect_uniform_eval (i : I) (g : M → ℝ) :
    (Distribution.uniform (I → M)).expect (fun seed => g (seed i)) =
      (Distribution.uniform M).expect g := by
  classical
  rw [← fTransform_eval_uniform (Y := M) i, Distribution.expect_fTransform]
  rfl

/-- Two distinct coordinates of a uniform batch are independent uniform inputs. -/
lemma expect_uniform_eval_pair (i j : I) (hne : i ≠ j) (g h : M → ℝ) :
    (Distribution.uniform (I → M)).expect (fun seed => g (seed i) * h (seed j)) =
      (Distribution.uniform M).expect g * (Distribution.uniform M).expect h := by
  classical
  let points : Bool → I := fun b => if b then j else i
  have hp : Function.Injective points := by
    intro a b he
    cases a <;> cases b <;>
      simp only [points, Bool.false_eq_true, ↓reduceIte, hne, Ne.symm hne] at he <;> rfl
  have he := Counting.fTransform_eval_uniform_eq_uniform (Y := M) points hp
  have hx := congrArg (fun P : Distribution (Bool → M) =>
    P.expect (fun seed => g (seed false) * h (seed true))) he
  rw [Distribution.expect_fTransform] at hx
  change (Distribution.uniform (I → M)).expect
    (fun seed => g (seed i) * h (seed j)) = _ at hx
  rw [hx, ← Distribution.fTransform_equiv_uniform (Equiv.boolArrowEquivProd M).symm,
    Distribution.expect_fTransform]
  change (Distribution.uniform (M × M)).expect (fun pair => g pair.1 * h pair.2) = _
  exact expect_uniform_product_mul g h

omit [Fintype T] in
/-- The expected label count is `|I| · Pr_{x ← M}[f x = value]`. -/
lemma labelCount_mean (f : M → T) (value : T) :
    (Distribution.uniform (I → M)).expect (labelCount f value) =
      (Fintype.card I : ℝ) * (Distribution.uniform M).mass (fun x => f x = value) := by
  classical
  unfold labelCount
  rw [Distribution.expect_finset_sum]
  have he (i : I) := expect_uniform_eval i (fun x : M => if f x = value then 1 else 0)
  simp only [he, Distribution.expect_indicator,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Fintype T] in
open Classical in
/-- Second mixed moment of label counts: off-diagonal positions are independent, and the
diagonal contributes only when `a = b`. -/
lemma labelCount_product_mean (f : M → T) (a b : T) :
    (Distribution.uniform (I → M)).expect
      (fun seed => labelCount f a seed * labelCount f b seed) =
      (Fintype.card I : ℝ) * (Fintype.card I - 1) *
        (Distribution.uniform M).mass (fun x => f x = a) *
        (Distribution.uniform M).mass (fun x => f x = b) +
      if a = b then (Fintype.card I : ℝ) *
        (Distribution.uniform M).mass (fun x => f x = a) else 0 := by
  classical
  let pa := (Distribution.uniform M).mass (fun x => f x = a)
  let pb := (Distribution.uniform M).mass (fun x => f x = b)
  have hdiag (i : I) : (Distribution.uniform (I → M)).expect
      (fun seed => (if f (seed i) = a then (1 : ℝ) else 0) *
        (if f (seed i) = b then 1 else 0)) = if a = b then pa else 0 := by
    rw [expect_uniform_eval i (fun x : M =>
      (if f x = a then 1 else 0) * (if f x = b then 1 else 0))]
    by_cases hab : a = b
    · subst b
      have hi (x : M) : (if f x = a then (1 : ℝ) else 0) *
          (if f x = a then 1 else 0) = if f x = a then 1 else 0 := by
        split_ifs <;> ring
      simp only [hi, ↓reduceIte, Distribution.expect_indicator, pa]
    · have hz (x : M) : (if f x = a then (1 : ℝ) else 0) *
          (if f x = b then 1 else 0) = 0 := by
        by_cases ha : f x = a
        · rw [ite_eq_left ha, ite_eq_right (fun hb => hab (ha.symm.trans hb)), mul_zero]
        · rw [ite_eq_right ha, zero_mul]
      simp only [hz, Distribution.expect_const, zero_mul, hab, ↓reduceIte]
  have hoff (i j : I) (hne : i ≠ j) : (Distribution.uniform (I → M)).expect
      (fun seed => (if f (seed i) = a then (1 : ℝ) else 0) *
        (if f (seed j) = b then 1 else 0)) = pa * pb := by
    rw [expect_uniform_eval_pair i j hne (fun x : M => if f x = a then 1 else 0)
      (fun x : M => if f x = b then 1 else 0), Distribution.expect_indicator,
      Distribution.expect_indicator]
  have hm (i j : I) : (Distribution.uniform (I → M)).expect
      (fun seed => (if f (seed i) = a then (1 : ℝ) else 0) *
        (if f (seed j) = b then 1 else 0)) =
      pa * pb + if i = j then (if a = b then pa else 0) - pa * pb else 0 := by
    by_cases he : i = j
    · subst j
      rw [hdiag, ite_eq_left rfl]
      ring
    · rw [hoff i j he, ite_eq_right he, add_zero]
  unfold labelCount
  simp only [Finset.sum_mul, Finset.mul_sum, Distribution.expect_finset_sum, hm,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change _ = (Fintype.card I : ℝ) * (Fintype.card I - 1) * pa * pb + _
  split_ifs <;> dsimp only [pa, pb] <;> ring

/-- Number of cross-batch pairs `(i, j)` with `f (seed.1 i) = f (seed.2 j)`. -/
def crossCount (f : M → T) (seed : (I → M) × (I → M)) : ℝ :=
  ∑ t, labelCount f t seed.1 * labelCount f t seed.2

/-- First moment of the cross count: `E[X] = |I|² · Σ_t p_t²`. -/
lemma crossCount_mean (f : M → T) :
    (Distribution.uniform ((I → M) × (I → M))).expect (crossCount f) =
      (Fintype.card I : ℝ) ^ 2 *
        ∑ t, ((Distribution.uniform M).mass (fun x => f x = t)) ^ 2 := by
  classical
  unfold crossCount
  rw [Distribution.expect_finset_sum]
  simp only [expect_uniform_product_mul, labelCount_mean]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Second moment of the cross count, exactly. -/
lemma crossCount_second (f : M → T) :
    (Distribution.uniform ((I → M) × (I → M))).expect (fun seed => crossCount f seed ^ 2) =
      (Fintype.card I : ℝ) ^ 2 * (Fintype.card I - 1) ^ 2 *
        (∑ t, ((Distribution.uniform M).mass (fun x => f x = t)) ^ 2) ^ 2 +
      2 * (Fintype.card I : ℝ) ^ 2 * (Fintype.card I - 1) *
        (∑ t, ((Distribution.uniform M).mass (fun x => f x = t)) ^ 3) +
      (Fintype.card I : ℝ) ^ 2 *
        ∑ t, ((Distribution.uniform M).mass (fun x => f x = t)) ^ 2 := by
  classical
  let P (t : T) := (Distribution.uniform M).mass (fun x => f x = t)
  let m : ℝ := Fintype.card I
  have hterm (a b : T) : (Distribution.uniform ((I → M) × (I → M))).expect
      (fun seed => (labelCount f a seed.1 * labelCount f a seed.2) *
        (labelCount f b seed.1 * labelCount f b seed.2)) =
      m ^ 2 * (m - 1) ^ 2 * P a ^ 2 * P b ^ 2 +
        if a = b then 2 * m ^ 2 * (m - 1) * P a ^ 3 + m ^ 2 * P a ^ 2 else 0 := by
    rw [Distribution.expect_congr_of_support (fun _ _ =>
      mul_mul_mul_comm _ _ _ _), expect_uniform_product_mul
        (fun seed : I → M => labelCount f a seed * labelCount f b seed)
        (fun seed : I → M => labelCount f a seed * labelCount f b seed),
      labelCount_product_mean]
    change (m * (m - 1) * P a * P b + if a = b then m * P a else 0) *
      (m * (m - 1) * P a * P b + if a = b then m * P a else 0) = _
    by_cases he : a = b
    · subst b
      rw [ite_eq_left rfl, ite_eq_left rfl]
      ring
    · rw [ite_eq_right he, ite_eq_right he]
      ring
  simp only [crossCount, pow_two, Finset.sum_mul, Finset.mul_sum,
    Distribution.expect_finset_sum, hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  dsimp only [P, m]
  rw [add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [Fintype M] [Nonempty M] [DecidableEq I] in
/-- The cubic moment is absorbed: `2 m Σ_t P_t³ ≤ m² (Σ_t P_t²)² + Σ_t P_t²`. -/
lemma cubic_moment_le (P : T → ℝ) (m : ℝ) :
    2 * m * (∑ t, P t ^ 3) ≤ m ^ 2 * (∑ t, P t ^ 2) ^ 2 + ∑ t, P t ^ 2 := by
  classical
  have hpoint (t : T) :
      2 * m * P t ^ 3 ≤ m ^ 2 * (∑ s, P s ^ 2) * P t ^ 2 + P t ^ 2 := by
    have hbound : P t ^ 2 ≤ ∑ s, P s ^ 2 :=
      Finset.single_le_sum (fun s _ => sq_nonneg (P s)) (Finset.mem_univ t)
    have hsq := mul_nonneg (sq_nonneg (m * P t - 1)) (sq_nonneg (P t))
    have hmul := mul_le_mul_of_nonneg_left hbound (mul_nonneg (sq_nonneg m) (sq_nonneg (P t)))
    nlinarith only [hsq, hmul]
  calc
    2 * m * (∑ t, P t ^ 3) = ∑ t, 2 * m * P t ^ 3 := Finset.mul_sum ..
    _ ≤ ∑ t, (m ^ 2 * (∑ s, P s ^ 2) * P t ^ 2 + P t ^ 2) :=
      Finset.sum_le_sum (fun t _ => hpoint t)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; ring

/-- Upper bound on the second moment: `E[X²] ≤ 2 m² p₂ (m² p₂ + 1)` with `m = |I|`. -/
lemma crossCount_second_le [Nonempty I] (f : M → T) :
    (Distribution.uniform ((I → M) × (I → M))).expect (fun seed => crossCount f seed ^ 2) ≤
      2 * (Fintype.card I : ℝ) ^ 2 *
        (∑ t, ((Distribution.uniform M).mass (fun x => f x = t)) ^ 2) *
        ((Fintype.card I : ℝ) ^ 2 *
          (∑ t, ((Distribution.uniform M).mass (fun x => f x = t)) ^ 2) + 1) := by
  classical
  let P (t : T) := (Distribution.uniform M).mass (fun x => f x = t)
  let m : ℝ := Fintype.card I
  let p₂ := ∑ t, P t ^ 2
  let p₃ := ∑ t, P t ^ 3
  have hm : 1 ≤ m := by
    dsimp only [m]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := I)))
  have h₂ : 0 ≤ p₂ := Finset.sum_nonneg (fun t _ => sq_nonneg (P t))
  have h₃ : 0 ≤ p₃ := Finset.sum_nonneg (fun t _ =>
    pow_nonneg (Distribution.uniform_nonNeg.mass_nonneg _) _)
  have hc : 2 * m * p₃ ≤ m ^ 2 * p₂ ^ 2 + p₂ := cubic_moment_le P m
  rw [crossCount_second]
  change m ^ 2 * (m - 1) ^ 2 * p₂ ^ 2 + 2 * m ^ 2 * (m - 1) * p₃ + m ^ 2 * p₂ ≤ _
  have hsq : (m - 1) ^ 2 ≤ m ^ 2 := by nlinarith only [hm]
  have hfirst := mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg m) (sq_nonneg p₂))
  have hsecond := mul_le_mul_of_nonneg_left (show m - 1 ≤ m by linarith)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg m)) h₃)
  have hthird := mul_le_mul_of_nonneg_left hc (sq_nonneg m)
  change _ ≤ 2 * m ^ 2 * p₂ * (m ^ 2 * p₂ + 1)
  nlinarith only [hfirst, hsecond, hthird]

/-- **Birthday-scale cross collisions of a biased map**: two independent uniform batches of
size `m = |I|` contain a cross-label equality with probability at least
`m² / (2 (m² + |T|))`. -/
theorem crossCount_nonzero_mass_ge [Nonempty I] [Nonempty T] (f : M → T) :
    (Fintype.card I : ℝ) ^ 2 /
        (2 * ((Fintype.card I : ℝ) ^ 2 + Fintype.card T)) ≤
      (Distribution.uniform ((I → M) × (I → M))).mass
        (fun seed => crossCount f seed ≠ 0) := by
  classical
  let Q := Distribution.uniform ((I → M) × (I → M))
  let P := Distribution.fTransform f (Distribution.uniform M)
  let m : ℝ := Fintype.card I
  let t : ℝ := Fintype.card T
  let p₂ := ∑ a, P a ^ 2
  have hm : 0 < m := by
    dsimp only [m]
    exact_mod_cast Fintype.card_pos (α := I)
  have ht : 0 < t := by
    dsimp only [t]
    exact_mod_cast Fintype.card_pos (α := T)
  -- Cauchy–Schwarz forces collision mass at least `1 / |T|` even for biased labels.
  have hp : 1 / t ≤ p₂ := by
    have h := pair_collision_mass_ge P
      ((Distribution.weight_fTransform f _).trans Distribution.weight_uniform)
    rwa [pair_collision_mass] at h
  have hp' : 0 < p₂ := lt_of_lt_of_le (one_div_pos.mpr ht) hp
  have hc := Distribution.expect_sq_le_mass_ne_zero_mul_second Q
    Distribution.uniform_nonNeg (crossCount f)
  have hsecond := crossCount_second_le (I := I) f
  have hmass : 0 ≤ Q.mass (fun seed => crossCount f seed ≠ 0) :=
    Distribution.uniform_nonNeg.mass_nonneg _
  rw [crossCount_mean] at hc
  have hP (a : T) : P a = (Distribution.uniform M).mass (fun x => f x = a) :=
    Distribution.fTransform_apply_eq_mass f _ a
  simp only [← hP] at hc hsecond
  have hmain : (m ^ 2 * p₂) ^ 2 ≤
      Q.mass (fun seed => crossCount f seed ≠ 0) * (2 * m ^ 2 * p₂ * (m ^ 2 * p₂ + 1)) :=
    hc.trans (mul_le_mul_of_nonneg_left hsecond hmass)
  -- Divide the second-moment bound, then use monotonicity in the collision mass.
  have hden : 0 < 2 * (m ^ 2 * p₂ + 1) := by positivity
  have hratio : m ^ 2 * p₂ / (2 * (m ^ 2 * p₂ + 1)) ≤
      Q.mass (fun seed => crossCount f seed ≠ 0) := by
    apply (div_le_iff₀ hden).mpr
    have hpos : 0 < m ^ 2 * p₂ := mul_pos (sq_pos_of_pos hm) hp'
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [hmain]
  refine le_trans ?_ hratio
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (m ^ 2 + t)) hden).mpr
  have hpt : 1 ≤ p₂ * t := (div_le_iff₀ ht).mp hp
  have hmul := mul_le_mul_of_nonneg_left hpt (sq_nonneg m)
  nlinarith only [hmul]

omit [Fintype M] [Nonempty M] [DecidableEq I] in
open Classical in
/-- The cross count is the number of equal-label pairs `(i, j)`. -/
lemma crossCount_eq_sum (f : M → T) (seed : (I → M) × (I → M)) :
    crossCount f seed = ∑ i, ∑ j, if f (seed.1 i) = f (seed.2 j) then (1 : ℝ) else 0 := by
  classical
  conv_rhs => rw [Finset.sum_comm]
  unfold crossCount labelCount
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [eq_comm]

omit [Fintype M] [Nonempty M] [DecidableEq I] in
/-- The cross count is nonzero exactly when some cross pair has equal labels. -/
lemma crossCount_ne_zero_iff (f : M → T) (seed : (I → M) × (I → M)) :
    crossCount f seed ≠ 0 ↔ ∃ i j, f (seed.1 i) = f (seed.2 j) := by
  classical
  rw [crossCount_eq_sum]
  have hnonneg (i j : I) : 0 ≤ (if f (seed.1 i) = f (seed.2 j) then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hi (i : I) : 0 ≤ ∑ j, if f (seed.1 i) = f (seed.2 j) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun j _ => hnonneg i j)
  rw [← (Finset.sum_nonneg (fun i _ => hi i)).lt_iff_ne',
    Finset.sum_pos_iff_of_nonneg (fun i _ => hi i)]
  have hpos (i j : I) : (0 < if f (seed.1 i) = f (seed.2 j) then (1 : ℝ) else 0) ↔
      f (seed.1 i) = f (seed.2 j) := by
    by_cases he : f (seed.1 i) = f (seed.2 j) <;>
      simp only [he, ↓reduceIte, zero_lt_one, lt_self_iff_false]
  simp only [Finset.mem_univ, true_and,
    Finset.sum_pos_iff_of_nonneg (fun j _ => hnonneg _ j), hpos]

/-- A fixed cross pair of uniform batch positions repeats an input with probability `1 / |M|`. -/
lemma uniform_cross_duplicate_mass (i j : I) :
    (Distribution.uniform ((I → M) × (I → M))).mass
      (fun seed => seed.1 i = seed.2 j) = 1 / (Fintype.card M : ℝ) := by
  classical
  have he : Distribution.fTransform
      (fun seed : (I → M) × (I → M) => (seed.1 i, seed.2 j))
      (Distribution.uniform ((I → M) × (I → M))) = Distribution.uniform (M × M) := by
    rw [← Distribution.prod_uniform]
    change Distribution.fTransform (Prod.map (fun seed : I → M => seed i)
      (fun seed : I → M => seed j)) _ = _
    rw [Distribution.fTransform_prod, fTransform_eval_uniform, fTransform_eval_uniform,
      Distribution.prod_uniform]
  have h := congrArg (fun P : Distribution (M × M) =>
    P.mass (fun pair => pair.1 = pair.2)) he
  rwa [Distribution.mass_fTransform, uniform_pair_collision_mass] at h

/-- Union bound on repeated inputs across the two batches: at most `|I|² / |M|`. -/
lemma cross_duplicate_mass_le :
    (Distribution.uniform ((I → M) × (I → M))).mass
      (fun seed => ∃ i j, seed.1 i = seed.2 j) ≤
        (Fintype.card I : ℝ) ^ 2 / (Fintype.card M : ℝ) := by
  classical
  have h := Distribution.mass_exists_le
    (Distribution.uniform_nonNeg (A := (I → M) × (I → M)))
    (Finset.univ : Finset (I × I)) (fun pair seed => seed.1 pair.1 = seed.2 pair.2)
  simp only [Finset.mem_univ, true_and, Prod.exists, uniform_cross_duplicate_mass,
    Finset.sum_const, Finset.card_univ, Fintype.card_prod, Nat.cast_mul, nsmul_eq_mul] at h
  convert h using 1
  ring

/-- **Distinct-input cross collisions**: two independent uniform batches contain a pair of
distinct inputs with equal labels with probability at least
`m² / (2 (m² + |T|)) - m² / |M|`, subtracting only sampled-input repetitions. -/
theorem distinct_cross_collision_mass_ge [Nonempty I] [Nonempty T] (f : M → T) :
    (Fintype.card I : ℝ) ^ 2 /
        (2 * ((Fintype.card I : ℝ) ^ 2 + Fintype.card T)) -
      (Fintype.card I : ℝ) ^ 2 / (Fintype.card M : ℝ) ≤
      (Distribution.uniform ((I → M) × (I → M))).mass
        (fun seed => ∃ i j, seed.1 i ≠ seed.2 j ∧ f (seed.1 i) = f (seed.2 j)) := by
  classical
  let Q := Distribution.uniform ((I → M) × (I → M))
  let A := fun seed : (I → M) × (I → M) =>
    ∃ i j, seed.1 i ≠ seed.2 j ∧ f (seed.1 i) = f (seed.2 j)
  let B := fun seed : (I → M) × (I → M) => ∃ i j, seed.1 i = seed.2 j
  -- A label equality is a distinct-input collision or a repeated input.
  have hmono : Q.mass (fun seed => crossCount f seed ≠ 0) ≤
      Q.mass (fun seed => A seed ∨ B seed) := by
    apply Distribution.mass_mono Distribution.uniform_nonNeg
    intro seed hs
    obtain ⟨i, j, he⟩ := (crossCount_ne_zero_iff f seed).mp hs
    by_cases hh : seed.1 i = seed.2 j
    · exact Or.inr ⟨i, j, hh⟩
    · exact Or.inl ⟨i, j, hh, he⟩
  have h := hmono.trans (Distribution.mass_or_le Distribution.uniform_nonNeg A B)
  have hlow := crossCount_nonzero_mass_ge (I := I) f
  have hdup := cross_duplicate_mass_le (I := I) (M := M)
  change Q.mass B ≤ _ at hdup
  change _ ≤ Q.mass A
  linarith only [h, hlow, hdup]

end

end Probability.Counting
