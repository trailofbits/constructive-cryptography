import Probability.Distribution
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Kernels

A kernel `f : A → Distribution B` gives a law of a second outcome for every value of a first one.
Its mixture over a law `μ` of the first outcome is the law of the second,

```
  (bindK μ f)(b) = ∑ₐ μ(a) · f(a)(b),
```

the composition of conditional probability distributions [1, §3.6.1, p. 65] (`bindK`). A
pushforward is the point kernel of its function, an independent product samples its factors one
after the other, and kernels of probability laws mix probability laws into probability laws.

## Main definitions

* `Distribution.bindK μ f`: the mixture of the kernel `f` over `μ`
* `Distribution.ProbDist.map f P`: the law of `f a` for `a ← P`
* `Distribution.ProbDist.bind P f`: the law of `b ← f a` for `a ← P`

## Main results

* `Distribution.bindK_bindK`, `Distribution.bindK_single_one`: mixtures compose, and the point
  kernel leaves a law unchanged
* `Distribution.bindK_single_comp`, `Distribution.fTransform_bindK`,
  `Distribution.bindK_fTransform`: a pushforward is the point kernel of its function, and passes
  through mixtures
* `Distribution.weight_bindK_of_weight`, `Distribution.bindK_nonNeg`: kernels of laws preserve the
  weight and nonnegativity
* `Distribution.prod_eq_bindK`, `Distribution.pi_eq_bindK_update`: independent products as
  mixtures
* `Distribution.ProbDist.map_map`: pushing forward twice is pushing forward along the composite

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

namespace Probability.Distribution

open Classical

variable {A B C : Type*}

/-! ### Restriction and pushforward -/

/-- Restricting keeps only mass that was there. -/
theorem support_restrict_subset (μ : Distribution A) (P : A → Prop) :
    (μ.restrict P).support ⊆ μ.support := fun a ha => by
  -- The restriction at `a` is `μ a` or zero; it is nonzero, so it is `μ a`.
  rw [Finsupp.mem_support_iff, restrict_apply] at ha
  rw [Finsupp.mem_support_iff]
  split_ifs at ha
  · exact ha
  · exact absurd rfl ha

/-- Restricting twice is restricting to both events. -/
theorem restrict_restrict (μ : Distribution A) (P Q : A → Prop) :
    (μ.restrict P).restrict Q = μ.restrict fun a => P a ∧ Q a := by
  -- Pointwise: `μ a` exactly when both events hold.
  ext a
  simp only [restrict_apply]
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]

/-- Restriction depends only on the event up to equivalence. -/
theorem restrict_congr (μ : Distribution A) {P Q : A → Prop} (h : ∀ a, P a ↔ Q a) :
    μ.restrict P = μ.restrict Q := by
  -- Pointwise, the two events are the same condition.
  ext a
  simp only [restrict_apply, h]

/-- Restricting to the impossible event leaves nothing. -/
theorem restrict_false (μ : Distribution A) : μ.restrict (fun _ => False) = 0 := by
  -- Pointwise, the condition never holds.
  ext a
  simp

/-- A point mass restricted to an event: itself or nothing. -/
theorem single_restrict (a : A) (w : ℝ) (P : A → Prop) :
    Distribution.restrict (Finsupp.single a w : Distribution A) P =
      if P a then Finsupp.single a w else 0 := by
  -- The only point with mass is `a`: kept if `P a`, dropped otherwise.
  by_cases h : P a
  · simp [restrict, Finsupp.filter_single_of_pos _ h, h]
  · simp [restrict, Finsupp.filter_single_of_neg _ h, h]

/-- The pushforward of a point mass. -/
theorem fTransform_single (f : A → B) (a : A) (w : ℝ) :
    fTransform f (Finsupp.single a w) = Finsupp.single (f a) w :=
  Finsupp.mapDomain_single

/-- Restricting a pushforward is pushing forward the restriction to the preimage. -/
theorem restrict_fTransform (f : A → B) (μ : Distribution A) (P : B → Prop) :
    (fTransform f μ).restrict P = fTransform f (μ.restrict fun a => P (f a)) := by
  -- At `b`, both sides are masses of fibres of `f`.
  ext b
  rw [restrict_apply, fTransform_apply_eq_mass, fTransform_apply_eq_mass, mass_restrict]
  split_ifs with h
  · -- `P b`: on the fibre of `b`, the condition `P (f a)` holds
    exact mass_congr _ fun a => ⟨fun ha => ⟨ha, ha ▸ h⟩, fun ha => ha.1⟩
  · -- not `P b`: the fibre of `b` meets no point with `P (f a)`
    exact (mass_eq_zero_of_forall_not _ fun a (ha : f a = b ∧ P (f a)) => h (ha.1 ▸ ha.2)).symm

/-! ### Kernels -/

/-- **The mixture of a kernel** over a distribution: `∑ a, μ a • f a`. -/
noncomputable def bindK (μ : Distribution A) (f : A → Distribution B) : Distribution B :=
  Finsupp.linearCombination ℝ f μ

/-- Nothing mixes to nothing. -/
@[simp] theorem bindK_zero (f : A → Distribution B) : bindK 0 f = 0 :=
  map_zero _

/-- A point mass of weight `w` mixes to `w` times its kernel law. -/
@[simp] theorem bindK_single (a : A) (w : ℝ) (f : A → Distribution B) :
    bindK (Finsupp.single a w) f = w • f a :=
  Finsupp.linearCombination_single _ _ _

/-- The mixture is additive in the first law. -/
theorem bindK_add (μ ν : Distribution A) (f : A → Distribution B) :
    bindK (μ + ν) f = bindK μ f + bindK ν f :=
  map_add _ _ _

/-- The mixture at `b`: `∑ₐ μ(a) · f(a)(b)`. -/
theorem bindK_apply (μ : Distribution A) (f : A → Distribution B) (b : B) :
    bindK μ f b = μ.sum fun a w => w * f a b := by
  -- A linear combination evaluated at `b` is the combination of the values at `b`.
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  rfl

/-- A kernel that vanishes mixes to nothing. -/
@[simp] theorem bindK_zero_right (μ : Distribution A) :
    bindK μ (fun _ => (0 : Distribution B)) = 0 := by
  -- Induction on `μ` as a sum of point masses.
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν => rw [bindK_add, hμ, hν, add_zero]
  | single a w => simp

/-- A mixture depends only on the kernel on the support. -/
theorem bindK_congr {μ : Distribution A} {f g : A → Distribution B}
    (h : ∀ a ∈ μ.support, f a = g a) : bindK μ f = bindK μ g := by
  -- Both are sums over the support of `μ`, term by term equal.
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  exact Finset.sum_congr rfl fun a ha => by
    show μ a • f a = μ a • g a
    rw [h a ha]

/-- **Mixtures compose**: mixing `g` over the mixture of `f` is mixing, over `μ`, the mixtures of
`g` over each `f a`. -/
theorem bindK_bindK (μ : Distribution A) (f : A → Distribution B) (g : B → Distribution C) :
    bindK (bindK μ f) g = bindK μ fun a => bindK (f a) g := by
  -- Induction on `μ`: both sides are additive in `μ`, and agree on point masses.
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν => rw [bindK_add, bindK_add, bindK_add, hμ, hν]
  | single a w => simp [bindK]

/-- **The point kernel** leaves a distribution unchanged. -/
theorem bindK_single_one (μ : Distribution A) : bindK μ (fun a => Finsupp.single a 1) = μ := by
  -- Induction on `μ`: a point mass of weight `w` mixes to `w` times the point mass.
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add μ ν hμ hν => rw [bindK_add, hμ, hν]
  | single a w => simp

/-- **A point kernel along `φ` is the pushforward** along `φ`. -/
theorem bindK_single_comp (μ : Distribution A) (φ : A → B) :
    bindK μ (fun a => Finsupp.single (φ a) 1) = fTransform φ μ := by
  -- Induction on `μ`: both sides are additive, and move a point mass from `a` to `φ a`.
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    rw [bindK_add, hμ, hν]
    exact (Finsupp.mapDomain_add).symm
  | single a w => simp [fTransform]

/-- **Pushing a mixture forward** pushes each law of the kernel forward. -/
theorem fTransform_bindK (φ : B → C) (μ : Distribution A) (f : A → Distribution B) :
    fTransform φ (bindK μ f) = bindK μ fun a => fTransform φ (f a) := by
  -- Induction on `μ`: the pushforward is linear.
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    rw [bindK_add, bindK_add, ← hμ, ← hν]
    exact Finsupp.mapDomain_add
  | single a w =>
    rw [bindK_single, bindK_single]
    exact Finsupp.mapDomain_smul _ _

/-- **Mixing over a pushforward** is mixing the composite kernel. -/
theorem bindK_fTransform (φ : A → B) (μ : Distribution A) (f : B → Distribution C) :
    bindK (fTransform φ μ) f = bindK μ (f ∘ φ) := by
  -- Induction on `μ`: a point mass at `a` is moved to `φ a`, where the kernel is `f (φ a)`.
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    rw [show fTransform φ (μ + ν) = fTransform φ μ + fTransform φ ν from Finsupp.mapDomain_add,
      bindK_add, bindK_add, hμ, hν]
  | single a w => simp [fTransform]

/-- A pushforward depends only on the function on the support. -/
theorem fTransform_congr_support {f g : A → B} {μ : Distribution A}
    (h : ∀ a ∈ μ.support, f a = g a) : fTransform f μ = fTransform g μ := by
  -- Both are point kernels, which agree on the support.
  rw [← bindK_single_comp, ← bindK_single_comp]
  exact bindK_congr fun a ha => by rw [h a ha]

/-- **Restricting a mixture** restricts each law of the kernel. -/
theorem restrict_bindK (P : B → Prop) (μ : Distribution A) (f : A → Distribution B) :
    (bindK μ f).restrict P = bindK μ fun a => (f a).restrict P := by
  -- Induction on `μ`: restriction is linear.
  induction μ using Finsupp.induction_linear with
  | zero => simp [restrict, Finsupp.filter_zero]
  | add μ ν hμ hν => rw [bindK_add, bindK_add, restrict, Finsupp.filter_add, ← restrict,
      ← restrict, hμ, hν]
  | single a w => simp [restrict, Finsupp.filter_smul]

/-- A kernel that vanishes off an event is the kernel on the restriction to it. -/
theorem bindK_ite (μ : Distribution A) (P : A → Prop) (f : A → Distribution B) :
    bindK μ (fun a => if P a then f a else 0) = bindK (μ.restrict P) f := by
  -- Induction on `μ`: a point mass at `a` contributes `f a` exactly when `P a`.
  induction μ using Finsupp.induction_linear with
  | zero => simp [restrict, Finsupp.filter_zero]
  | add μ ν hμ hν => rw [bindK_add, hμ, hν, ← bindK_add, restrict, restrict, restrict,
      Finsupp.filter_add]
  | single a w =>
    by_cases h : P a
    · simp [h, restrict, Finsupp.filter_single_of_pos _ h]
    · simp [h, restrict, Finsupp.filter_single_of_neg _ h]

/-- **The weight of a mixture**: each weight of the kernel, weighted by `μ`. -/
theorem weight_bindK (μ : Distribution A) (f : A → Distribution B) :
    (bindK μ f).weight = μ.sum fun a w => w * (f a).weight := by
  -- Induction on `μ`: the weight is additive, and scales with a point mass.
  induction μ using Finsupp.induction_linear with
  | zero => simp [weight]
  | add μ ν hμ hν =>
    rw [bindK_add, weight_add, hμ, hν,
      Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _)]
  | single a w => simp [weight_smul]

/-- **A kernel of weight one preserves the weight.** -/
theorem weight_bindK_of_weight {μ : Distribution A} {f : A → Distribution B}
    (hf : ∀ a ∈ μ.support, (f a).weight = 1) : (bindK μ f).weight = μ.weight := by
  -- Each `μ a` is weighted by the weight of `f a`, which is one.
  rw [weight_bindK, weight]
  exact Finset.sum_congr rfl fun a ha => by
    show μ a * (f a).weight = μ a
    rw [hf a ha, mul_one]

/-- **A nonnegative kernel mixed over a nonnegative distribution** is nonnegative. -/
theorem bindK_nonNeg {μ : Distribution A} {f : A → Distribution B} (hμ : μ.NonNeg)
    (hf : ∀ a, (f a).NonNeg) : (bindK μ f).NonNeg := by
  -- At each `b`, a sum of products of nonnegative numbers.
  intro b
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun a _ => by
    simpa [Finsupp.smul_apply] using mul_nonneg (hμ a) (hf a b)

/-- A possible outcome of a mixture is possible under the kernel at a possible first outcome. -/
theorem mem_support_bindK {μ : Distribution A} {f : A → Distribution B} {b : B}
    (hb : b ∈ (bindK μ f).support) : ∃ a ∈ μ.support, b ∈ (f a).support := by
  -- Otherwise every term `μ a · f a b` of the mixture at `b` vanishes.
  by_contra hn
  push Not at hn
  apply Finsupp.mem_support_iff.mp hb
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun a ha => by
    simp [Finsupp.notMem_support_iff.mp (hn a ha)]

/-! ### Independent products -/

/-- **An independent product as a mixture**: sample the first factor, then the second beside it. -/
theorem prod_eq_bindK (μ : Distribution A) (ν : Distribution B) :
    prod μ ν = bindK μ fun a => fTransform (fun b => (a, b)) ν := by
  -- Compare at a pair `(a, b)`: `μ a · ν b` on the left.
  ext ⟨a, b⟩
  rw [prod_apply, bindK_apply, Finsupp.sum]
  -- The law `ν` placed beside `a'` puts `ν b` at `(a, b)` if `a' = a`, and nothing otherwise.
  have hpt : ∀ a', fTransform (fun b' => (a', b')) ν (a, b) = if a' = a then ν b else 0 := by
    intro a'
    rw [fTransform_apply_eq_mass]
    split_ifs with h
    · subst h
      rw [mass, Finsupp.sum]
      simp only [Prod.mk.injEq, true_and]
      rw [Finset.sum_ite_eq']
      split_ifs with hb
      · rfl
      · exact (Finsupp.notMem_support_iff.mp hb).symm
    · exact mass_eq_zero_of_forall_not _ fun b' h' => h (Prod.mk.inj h').1
  -- So the mixture at `(a, b)` keeps only the term `a' = a`: `μ a · ν b`.
  simp only [hpt, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with ha
  · rfl
  · rw [Finsupp.notMem_support_iff.mp ha, zero_mul]

/-- **Disintegration of an independent product** at one coordinate: sample that coordinate first,
then the product with that coordinate fixed. -/
theorem pi_eq_bindK_update {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A)
    (n : ι) : pi μ = bindK (μ n) fun z => pi (Function.update μ n (Finsupp.single z 1)) := by
  -- Compare at a sample `t`: `∏ᵢ μᵢ(tᵢ)` on the left.
  ext t
  -- With coordinate `n` fixed to `z`, the product is `[t n = z] · ∏_{i ≠ n} μᵢ(tᵢ)`.
  have hrest : ∀ z : A, (∏ i, Function.update μ n (Finsupp.single z 1) i (t i)) =
      (Finsupp.single z (1 : ℝ)) (t n) * ∏ i ∈ Finset.univ.erase n, μ i (t i) := by
    intro z
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  -- Mixing over `z ← μ n` keeps the term `z = t n`: `μ n (t n) · ∏_{i ≠ n} μᵢ(tᵢ)`.
  rw [pi_apply, bindK_apply]
  simp only [pi_apply, hrest, Finsupp.single_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n), Finsupp.sum]
  simp only [← mul_assoc, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, zero_mul]

/-- With one coordinate fixed to `z`, every possible sample has `z` there. -/
theorem eq_of_mem_support_pi_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Distribution A) (n : ι) (z : A) {t : ι → A}
    (ht : t ∈ (pi (Function.update μ n (Finsupp.single z 1))).support) : t n = z := by
  -- Otherwise the factor at `n`, the point mass at `z`, vanishes at `t n`.
  rw [Finsupp.mem_support_iff, pi_apply] at ht
  by_contra hne
  apply ht
  refine Finset.prod_eq_zero (Finset.mem_univ n) ?_
  rw [Function.update_self, Finsupp.single_apply, if_neg (Ne.symm hne)]

/-! ### Probability laws -/

namespace ProbDist

/-- **The pushforward** of a law: the law of `f a` for `a ← P`. -/
noncomputable def map (f : A → B) (P : ProbDist A) : ProbDist B :=
  ⟨fTransform f P.1, fTransform_isProbDist f P.2⟩

@[simp] theorem map_val (f : A → B) (P : ProbDist A) : (map f P).1 = fTransform f P.1 := rfl

/-- **Pushing forward twice** is pushing forward along the composite. -/
theorem map_map (f : B → C) (g : A → B) (P : ProbDist A) :
    map f (map g P) = map (f ∘ g) P :=
  -- Both sides have the same underlying distribution: `fTransform f ∘ fTransform g`.
  Subtype.ext (fTransform_fTransform _ _ _)

/-- **Sequential composition**: the law of `b ← f a` for `a ← P`, the mixture of `f` over `P`. -/
noncomputable def bind (P : ProbDist A) (f : A → ProbDist B) : ProbDist B :=
  ⟨bindK P.1 fun a => (f a).1,
    bindK_nonNeg P.2.1 fun a => (f a).2.1,
    (weight_bindK_of_weight fun a _ => (f a).2.2).trans P.2.2⟩

@[simp] theorem bind_val (P : ProbDist A) (f : A → ProbDist B) :
    (bind P f).1 = bindK P.1 fun a => (f a).1 := rfl

end ProbDist

end Probability.Distribution
