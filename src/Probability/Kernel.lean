module

public import Probability.DependentProduct
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Kernels

A kernel `f : A → Distribution B` assigns a law to every first outcome `a : A`.
Its mixture `bindK μ f` draws `a ← μ`, then `b ← f a`:

```text
(bindK μ f)(b) = ∑ₐ μ(a) · f(a)(b).
```

This represents a "conditional probability distribution" `p_{Y|X}` [1, §3.6.1, p. 65].
`bindK_bindK` composes successive draws; `bindK_single_one` removes a point kernel.
`fTransform_bindK` and `bindK_fTransform` move deterministic maps through those draws.

`ProbDist.map` and `ProbDist.bind` retain normalization. `ProbDist.map_map` composes
initializations; `ProbDist.map_pi_apply` selects one coordinate of an independent table.
`prodProbDist_map` combines independent initialized draws:

```text
(f_* P) × (g_* Q) = (f × g)_* (P × Q).
```

For dependent draws, `ProbDist.jointLaw μ K` retains both outcomes with law `μ(h) · K h z`.
`ProbDist.jointLaw_fst` recovers `μ`; `ProbDist.jointLaw_map` transports both coordinates.
For independent tables, `piDep_eq_bindK_update` samples one cell first and fixes it in the
remaining table; `pi_eq_bindK_update` specializes to one common outcome type. Each law has
finite support; the outcome types are arbitrary.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Probability.Distribution

-- `A`, `B`, `C` carry successive outcomes; their laws have finite support.
variable {A B C : Type*}

/-! ### Kernels -/

/-- **The mixture of a kernel** over a distribution: `∑ a, μ a • f a`. -/
noncomputable def bindK (μ : Distribution A) (f : A → Distribution B) : Distribution B :=
  Finsupp.linearCombination ℝ f μ

/-- Nothing mixes to nothing. -/
@[simp] lemma bindK_zero (f : A → Distribution B) : bindK 0 f = 0 :=
  map_zero _

/-- A point mass of weight `w` mixes to `w` times its kernel law. -/
@[simp] lemma bindK_single (a : A) (w : ℝ) (f : A → Distribution B) :
    bindK (Finsupp.single a w) f = w • f a :=
  Finsupp.linearCombination_single _ _ _

/-- The mixture is additive in the first law. -/
lemma bindK_add (μ ν : Distribution A) (f : A → Distribution B) :
    bindK (μ + ν) f = bindK μ f + bindK ν f :=
  map_add _ _ _

/-- The mixture at `b`: `∑ₐ μ(a) · f(a)(b)`. -/
lemma bindK_apply (μ : Distribution A) (f : A → Distribution B) (b : B) :
    bindK μ f b = μ.sum fun a w => w * f a b := by
  -- A linear combination evaluated at `b` is the combination of the values at `b`.
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  rfl

/-- A kernel that vanishes mixes to nothing. -/
@[simp] lemma bindK_zero_right (μ : Distribution A) :
    bindK μ (fun _ => (0 : Distribution B)) = 0 := by
  -- Induction on `μ` as a sum of point masses.
  induction μ using Finsupp.induction_linear with
  | zero => simp
  -- A sum of two laws: the mixture is additive, and `0 + 0 = 0`.
  | add μ ν hμ hν => rw [bindK_add, hμ, hν, add_zero]
  -- A point mass of weight `w`: it mixes to `w • 0 = 0`.
  | single a w => simp

/-- A mixture depends only on the kernel on the support. -/
lemma bindK_congr {μ : Distribution A} {f g : A → Distribution B}
    (h : ∀ a ∈ μ.support, f a = g a) : bindK μ f = bindK μ g := by
  -- Both are sums over the support of `μ`, term by term equal.
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  exact Finset.sum_congr rfl fun a ha => congrArg (μ a • ·) (h a ha)

/-- **Mixtures compose**: mixing `g` over the mixture of `f` is mixing, over `μ`, the mixtures of
`g` over each `f a`. -/
lemma bindK_bindK (μ : Distribution A) (f : A → Distribution B) (g : B → Distribution C) :
    bindK (bindK μ f) g = bindK μ fun a => bindK (f a) g := by
  -- Induction on `μ`: both sides are additive in `μ`, and agree on point masses.
  induction μ using Finsupp.induction_linear with
  | zero => simp
  -- A sum of two laws: every mixture involved is additive in its first law.
  | add μ ν hμ hν => rw [bindK_add, bindK_add, bindK_add, hμ, hν]
  -- A point mass of weight `w` at `a`: both sides are `w • bindK (f a) g`, as the mixture is
  -- linear in its first law.
  | single a w => simp [bindK]

/-- **The point kernel** leaves a distribution unchanged. -/
lemma bindK_single_one (μ : Distribution A) : bindK μ (fun a => Finsupp.single a 1) = μ := by
  -- Induction on `μ`: a point mass of weight `w` mixes to `w` times the point mass.
  induction μ using Finsupp.induction_linear with
  | zero => simp
  -- A sum of two laws: the mixture is additive.
  | add μ ν hμ hν => rw [bindK_add, hμ, hν]
  -- A point mass of weight `w` at `a`: `w • single a 1 = single a w`.
  | single a w => simp

/-- **A point kernel along `φ` is the pushforward** along `φ`. -/
lemma bindK_single_comp (μ : Distribution A) (φ : A → B) :
    bindK μ (fun a => Finsupp.single (φ a) 1) = fTransform φ μ := by
  -- Induction on `μ`: both sides are additive, and move a point mass from `a` to `φ a`.
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    -- the mixture is additive; then the induction hypotheses ...
    rw [bindK_add, hμ, hν]
    -- ... and the pushforward of a sum is the sum of the pushforwards
    exact (Finsupp.mapDomain_add).symm
  -- A point mass of weight `w` at `a`: both sides are the point mass of weight `w` at `φ a`.
  | single a w => simp [fTransform]

/-- **Pushing a mixture forward** pushes each law of the kernel forward. -/
lemma fTransform_bindK (φ : B → C) (μ : Distribution A) (f : A → Distribution B) :
    fTransform φ (bindK μ f) = bindK μ fun a => fTransform φ (f a) := by
  -- Induction on `μ`: the pushforward is linear.
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    -- both mixtures split over `μ + ν`; the right one is folded back by the hypotheses ...
    rw [bindK_add, bindK_add, ← hμ, ← hν]
    -- ... leaving the additivity of the pushforward
    exact Finsupp.mapDomain_add
  | single a w =>
    -- a point mass of weight `w` at `a` mixes to `w • f a` and `w • fTransform φ (f a)` ...
    rw [bindK_single, bindK_single]
    -- ... and the pushforward commutes with scaling by `w`
    exact Finsupp.mapDomain_smul _ _

/-- **Mixing over a pushforward** is mixing the composite kernel. -/
lemma bindK_fTransform (φ : A → B) (μ : Distribution A) (f : B → Distribution C) :
    bindK (fTransform φ μ) f = bindK μ (f ∘ φ) := by
  -- Induction on `μ`: a point mass at `a` is moved to `φ a`, where the kernel is `f (φ a)`.
  induction μ using Finsupp.induction_linear with
  | zero => simp [fTransform]
  | add μ ν hμ hν =>
    -- the pushforward and both mixtures are additive; then the induction hypotheses
    rw [show fTransform φ (μ + ν) = fTransform φ μ + fTransform φ ν from Finsupp.mapDomain_add,
      bindK_add, bindK_add, hμ, hν]
  -- A point mass of weight `w` at `a`: both sides are `w • f (φ a)`.
  | single a w => simp [fTransform]

/-- A pushforward depends only on the function on the support. -/
lemma fTransform_congr_support {f g : A → B} {μ : Distribution A}
    (h : ∀ a ∈ μ.support, f a = g a) : fTransform f μ = fTransform g μ := by
  -- Both are point kernels, which agree on the support.
  rw [← bindK_single_comp, ← bindK_single_comp]
  exact bindK_congr fun a ha => by rw [h a ha]

/-- **Restricting a mixture** restricts each law of the kernel. -/
lemma restrict_bindK (P : B → Prop) (μ : Distribution A) (f : A → Distribution B) :
    (bindK μ f).restrict P = bindK μ fun a => (f a).restrict P := by
  classical
  -- Induction on `μ`: restriction is linear.
  induction μ using Finsupp.induction_linear with
  | zero => simp [restrict, Finsupp.filter_zero]
  -- A sum of two laws: the mixtures and the restriction (a filter) are all additive.
  | add μ ν hμ hν => rw [bindK_add, bindK_add, restrict, Finsupp.filter_add, ← restrict,
      ← restrict, hμ, hν]
  -- A point mass of weight `w` at `a`: restricting `w • f a` is `w •` the restriction of `f a`.
  | single a w => simp [restrict, Finsupp.filter_smul]

open scoped Classical in
/-- A kernel that vanishes off an event is the kernel on the restriction to it. -/
lemma bindK_ite (μ : Distribution A) (P : A → Prop) (f : A → Distribution B) :
    bindK μ (fun a => if P a then f a else 0) = bindK (μ.restrict P) f := by
  -- Induction on `μ`: a point mass at `a` contributes `f a` exactly when `P a`.
  induction μ using Finsupp.induction_linear with
  | zero => simp [restrict, Finsupp.filter_zero]
  -- A sum of two laws: the mixtures are additive, and the restriction of a sum is the sum of
  -- the restrictions.
  | add μ ν hμ hν => rw [bindK_add, hμ, hν, ← bindK_add, restrict, restrict, restrict,
      Finsupp.filter_add]
  | single a w =>
    -- a point mass of weight `w` at `a`: case on the event at `a`
    by_cases h : P a
    -- `P a`: the restriction keeps the point mass, and both sides are `w • f a`
    · simp [h, restrict, Finsupp.filter_single_of_pos _ h]
    -- not `P a`: the restriction drops the point mass, and both sides are zero
    · simp [h, restrict, Finsupp.filter_single_of_neg _ h]

/-- **The weight of a mixture**: each weight of the kernel, weighted by `μ`. -/
lemma weight_bindK (μ : Distribution A) (f : A → Distribution B) :
    (bindK μ f).weight = μ.sum fun a w => w * (f a).weight := by
  -- Induction on `μ`: the weight is additive, and scales with a point mass.
  induction μ using Finsupp.induction_linear with
  | zero => simp [weight]
  | add μ ν hμ hν =>
    -- the mixture and its weight are additive; the sum over `μ + ν` splits, as its summand
    -- `w * (f a).weight` is additive in `w`
    rw [bindK_add, weight_add, hμ, hν,
      Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_mul _ _ _)]
  -- A point mass of weight `w` at `a`: the weight of `w • f a` is `w` times that of `f a`.
  | single a w => simp [weight_smul]

/-- An event's mass in a mixture is the weighted sum of its masses in the component laws. -/
lemma mass_bindK
    -- `μ` samples `a`; `f a` is the next-outcome law, and `E` is an event on that outcome.
    (μ : Distribution A) (f : A → Distribution B) (E : B → Prop) :
    (bindK μ f).mass E = μ.sum (fun a w => w * (f a).mass E) := by
  -- Restrict to the event and sum the conditional weights.
  rw [← weight_restrict, restrict_bindK, weight_bindK]
  simp only [weight_restrict]

/-- **A kernel of weight one preserves the weight.** -/
lemma weight_bindK_of_weight {μ : Distribution A} {f : A → Distribution B}
    (hf : ∀ a ∈ μ.support, (f a).weight = 1) : (bindK μ f).weight = μ.weight := by
  -- Each `μ a` is weighted by the weight of `f a`, which is one.
  rw [weight_bindK, weight]
  -- Term by term over the support of `μ`: `μ(a) · 1 = μ(a)`.
  exact Finset.sum_congr rfl fun a ha => by simp only [hf a ha, mul_one]

/-- **A nonnegative kernel mixed over a nonnegative distribution** is nonnegative. -/
lemma bindK_nonNeg {μ : Distribution A} {f : A → Distribution B} (hμ : μ.NonNeg)
    (hf : ∀ a, (f a).NonNeg) : (bindK μ f).NonNeg := by
  -- At each `b`, a sum of products of nonnegative numbers.
  intro b
  -- The mixture at `b` is `∑ₐ μ(a) · f(a)(b)`.
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  -- Each term is `μ(a) · f(a)(b)`, with `μ(a) ≥ 0` and `f(a)(b) ≥ 0`.
  exact Finset.sum_nonneg fun a _ => by
    simpa [Finsupp.smul_apply] using mul_nonneg (hμ a) (hf a b)

/-- A possible outcome of a mixture is possible under the kernel at a possible first outcome. -/
lemma mem_support_bindK {μ : Distribution A} {f : A → Distribution B} {b : B}
    (hb : b ∈ (bindK μ f).support) : ∃ a ∈ μ.support, b ∈ (f a).support := by
  -- Otherwise every term `μ a · f a b` of the mixture at `b` vanishes.
  by_contra hn
  push Not at hn
  -- So `f(a)(b) = 0` at every possible `a`; we show the mixture at `b` is zero, against `hb`.
  apply Finsupp.mem_support_iff.mp hb
  -- The mixture at `b` is `∑ₐ μ(a) · f(a)(b)` over the support of `μ` ...
  unfold bindK
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  -- ... and every term vanishes, since `f(a)(b) = 0`.
  exact Finset.sum_eq_zero fun a ha => by
    simp [Finsupp.notMem_support_iff.mp (hn a ha)]

/-! ### Independent products -/

/-- **An independent product as a mixture**: sample the first factor, then the second beside it. -/
lemma prod_eq_bindK (μ : Distribution A) (ν : Distribution B) :
    prod μ ν = bindK μ fun a => fTransform (fun b => (a, b)) ν := by
  classical
  -- Compare at a pair `(a, b)`: `μ a · ν b` on the left.
  ext ⟨a, b⟩
  rw [prod_apply, bindK_apply, Finsupp.sum]
  -- The law `ν` placed beside `a'` puts `ν b` at `(a, b)` if `a' = a`, and nothing otherwise.
  have hpt : ∀ a', fTransform (fun b' => (a', b')) ν (a, b) = if a' = a then ν b else 0 := by
    intro a'
    -- The pushforward at `(a, b)` is the `ν`-mass of the event `(a', b') = (a, b)`.
    rw [fTransform_apply_eq_mass]
    split_ifs with h
    -- `a' = a`: the event is `b' = b`, of mass `ν b` (zero when `b` is outside the support).
    · subst h
      rw [mass, Finsupp.sum]
      simp only [Prod.mk.injEq, true_and]
      rw [Finset.sum_ite_eq']
      split_ifs with hb
      · rfl
      · exact (Finsupp.notMem_support_iff.mp hb).symm
    -- `a' ≠ a`: no pair `(a', b')` is `(a, b)`, so the event is empty.
    · exact mass_eq_zero_of_forall_not _ fun b' h' => h (Prod.mk.inj h').1
  -- So the mixture at `(a, b)` keeps only the term `a' = a`: `μ a · ν b`.
  simp only [hpt, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  -- The sum keeps that term if `a` is in the support of `μ`; otherwise `μ a = 0`.
  split_ifs with ha
  · rfl
  · rw [Finsupp.notMem_support_iff.mp ha, zero_mul]

/-- **Disintegration of an independent product** at one coordinate: sample that coordinate first,
then the product with that coordinate fixed. -/
lemma piDep_eq_bindK_update
    -- `ι` indexes outcome types `A i`; `μ i` is the raw law of coordinate `i`.
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    (μ : ∀ i, Distribution (A i))
    -- `n` is revealed first; the remaining law fixes that coordinate to its sampled value.
    (n : ι) :
    piDep μ = bindK (μ n) fun z => piDep (Function.update μ n (Finsupp.single z 1)) := by
  classical
  -- Compare at a sample `t`: `∏ᵢ μᵢ(tᵢ)` on the left.
  ext t
  -- With coordinate `n` fixed to `z`, the product is `[t n = z] · ∏_{i ≠ n} μᵢ(tᵢ)`.
  have hrest : ∀ z : A n, (∏ i, Function.update μ n (Finsupp.single z 1) i (t i)) =
      (Finsupp.single z (1 : ℝ)) (t n) * ∏ i ∈ Finset.univ.erase n, μ i (t i) := by
    intro z
    -- Split off the factor at `n`, which the update sets to the point mass at `z` ...
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n), Function.update_self]
    congr 1
    -- ... and off `n` the update leaves the factors `μ i` unchanged.
    exact Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  -- Mixing over `z ← μ n` keeps the term `z = t n`: `μ n (t n) · ∏_{i ≠ n} μᵢ(tᵢ)`.
  rw [piDep_apply, bindK_apply]
  simp only [piDep_apply, hrest, Finsupp.single_apply]
  -- Split the factor at `n` off the left side too: `μ n (t n) · ∏_{i ≠ n} μᵢ(tᵢ)`.
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n), Finsupp.sum]
  -- On the right, the term at `z` is `μ n z · ∏_{i ≠ n} μᵢ(tᵢ)` if `z = t n`, and zero otherwise.
  simp only [← mul_assoc, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  -- The sum keeps that term if `t n` is in the support of `μ n`; otherwise `μ n (t n) = 0`.
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h, zero_mul]

/-- With one coordinate fixed to `z`, every supported dependent function has `z` there. -/
lemma eq_of_mem_support_piDep_update
    -- `μ i` is the law at coordinate `i : ι`, whose outcomes lie in `A i`.
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    (μ : ∀ i, Distribution (A i))
    -- `n` is the fixed coordinate and `z` its prescribed value.
    (n : ι) (z : A n)
    -- `ht` places the whole function `t` in the product with coordinate `n` fixed.
    {t : ∀ i, A i}
    (ht : t ∈ (piDep (Function.update μ n (Finsupp.single z 1))).support) : t n = z := by
  classical
  rw [Finsupp.mem_support_iff, piDep_apply] at ht
  by_contra hne
  apply ht
  -- A different value at `n` makes that coordinate's point-mass factor zero.
  refine Finset.prod_eq_zero (Finset.mem_univ n) ?_
  rw [Function.update_self, Finsupp.single_apply, ite_eq_right (Ne.symm hne)]

/-- Disintegration at one coordinate for independent laws with a common outcome type. -/
lemma pi_eq_bindK_update {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Distribution A)
    (n : ι) : pi μ = bindK (μ n) fun z => pi (Function.update μ n (Finsupp.single z 1)) := by
  simpa only [piDep_eq_pi] using piDep_eq_bindK_update μ n

/-- With one coordinate fixed to `z`, every possible sample has `z` there. -/
lemma eq_of_mem_support_pi_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Distribution A) (n : ι) (z : A) {t : ι → A}
    (ht : t ∈ (pi (Function.update μ n (Finsupp.single z 1))).support) : t n = z := by
  apply eq_of_mem_support_piDep_update μ n z
  simpa only [piDep_eq_pi] using ht

/-! ### Probability laws -/

namespace ProbDist

/-- The pushforward `f_* P`: draw `a ← P` and return `f a`. -/
noncomputable def map
    -- `f : A → B` transforms the outcome; `P` supplies its law on `A`.
    (f : A → B) (P : ProbDist A) : ProbDist B :=
  ⟨fTransform f P.1, fTransform_isProbDist f P.2⟩

/-- The underlying distribution of `f_* P` is `fTransform f P.1`. -/
@[simp] lemma map_val (f : A → B) (P : ProbDist A) : (map f P).1 = fTransform f P.1 := rfl

/-- Successive deterministic maps compose: `f_* (g_* P) = (f ∘ g)_* P`. -/
lemma map_map
    -- `g` transforms the draw from `P` first, then `f` transforms that result.
    (f : B → C) (g : A → B) (P : ProbDist A) :
    map f (map g P) = map (f ∘ g) P :=
  -- Both sides have the same underlying distribution: `fTransform f ∘ fTransform g`.
  Subtype.ext (fTransform_fTransform _ _ _)

/-- Selecting coordinate `i` has law `μ i`: `(ProbDist.pi μ).map (fun f => f i) = μ i`. -/
lemma map_pi_apply
    -- `ι` indexes the finite table of independent coordinates.
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    -- `μ j` is the law of coordinate `j`; `i` selects the observed coordinate.
    (μ : ι → ProbDist A) (i : ι) :
    (ProbDist.pi μ).map (fun f => f i) = μ i := by
  apply Subtype.ext
  change marginalAt (Distribution.pi (fun j => (μ j).1)) i = _
  -- Every unobserved coordinate has weight one in the product-marginal equation.
  rw [marginalAt_pi]
  simp only [IsProbability.weight_eq_one, Finset.prod_const_one, one_smul]

/-- Mapping `g` over table coordinate `i` gives the pushforward of that coordinate's law. -/
lemma map_pi_apply_comp
    -- `ι` indexes independent table entries; `g : A → B` transforms the selected entry.
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    -- `μ j` is the law of entry `j`; `i` selects the observed entry.
    (μ : ι → ProbDist A) (i : ι) (g : A → B) :
    (ProbDist.pi μ).map (fun f => g (f i)) = (μ i).map g :=
  (map_map g (fun f : ι → A => f i) (ProbDist.pi μ)).symm.trans
    (congrArg (ProbDist.map g) (map_pi_apply μ i))

/-- Sequential sampling: `bind P f (b) = ∑ₐ P(a) · f(a)(b)`. -/
noncomputable def bind
    -- `P` samples `a : A`; `f a` is the normalized law of the next outcome in `B`.
    (P : ProbDist A) (f : A → ProbDist B) : ProbDist B :=
  ⟨bindK P.1 fun a => (f a).1,
    -- nonnegative: a mixture of nonnegative laws over the nonnegative law `P`
    bindK_nonNeg P.2.1 fun a => (f a).2.1,
    -- weight one: each `f a` has weight one, so the mixture keeps the weight of `P`, which is one
    (weight_bindK_of_weight fun a _ => (f a).2.2).trans P.2.2⟩

/-- Forgetting normalization gives the underlying kernel mixture. -/
@[simp] lemma bind_val (P : ProbDist A) (f : A → ProbDist B) :
    (bind P f).1 = bindK P.1 fun a => (f a).1 := rfl

/-- Sampling a constant probability kernel gives its law: `P.bind (fun _ => Q) = Q`. -/
lemma bind_const
    -- `P` is the first-outcome law on `A`; `Q` is the same second-outcome law on `B` each time.
    (P : ProbDist A) (Q : ProbDist B) : P.bind (fun _ => Q) = Q := by
  apply Subtype.ext
  ext b
  -- Every summand has the factor `Q(b)`; the remaining weights sum to one.
  rw [bind_val, bindK_apply, Finsupp.sum, ← Finset.sum_mul]
  change P.1.weight * Q.1 b = Q.1 b
  rw [P.2.weight_eq, one_mul]

/-! ### Joint laws -/

-- `H` carries the first outcome `h`; `Z` the second outcome `z`, drawn given `h`.
-- Both are arbitrary types; each law has finite support.
variable {H Z : Type*}

/-- The joint law of successive draws `h ← μ`, then `z ← K h`, retaining both:
`jointLaw μ K (h, z) = μ(h) · K h z`. Its weight is `∑_h μ(h) · 1 = 1`. -/
noncomputable def jointLaw
    -- `μ`: the law of `h`; `K h`: the conditional law of `z` given `h` [1, §3.6.1, p. 65].
    (μ : ProbDist H) (K : H → ProbDist Z) : ProbDist (H × Z) :=
  μ.bind fun h => ProbDist.map (fun z => (h, z)) (K h)

/-- The first marginal of the joint law is the original law,
`fst_* (jointLaw μ K) = μ`: summing out `z` uses only that each `K h` has weight one. -/
lemma jointLaw_fst
    -- `μ` is the law of the first outcome `h`; `K h` is the conditional law of `z` given `h`.
    (μ : ProbDist H) (K : H → ProbDist Z) :
    ProbDist.map Prod.fst (jointLaw μ K) = μ := by
  apply Subtype.ext
  change fTransform Prod.fst (μ.1.bindK _) = _
  rw [fTransform_bindK]
  -- Forgetting `z` collapses `K h` to its weight one at `h`: `(z ↦ h)_* K h = δ_h`.
  have hconst : ∀ h : H, fTransform (fun _ : Z => h) (K h).1 = Finsupp.single h 1 := by
    intro h
    change (K h).1.sum (fun _ w => Finsupp.single h w) = _
    rw [Finsupp.sum, ← Finsupp.single_finsetSum]
    congr 1
    exact (K h).2.weight_eq
  -- Then `∑_h μ(h) · δ_h = μ`.
  simp only [ProbDist.map_val, fTransform_fTransform, Function.comp_def, hconst, bindK_single_one]

/-- Joint laws commute with pushforward along a product map: if `decodeH_* μ' = μ` and
`decodeZ_* (K' h) = K (decodeH h)` for every `h`, then
`(decodeH × decodeZ)_* (jointLaw μ' K') = jointLaw μ K`. -/
lemma jointLaw_map
    -- `H'`, `Z'`: the source outcome types; `decodeH : H' → H` and `decodeZ : Z' → Z` are
    -- arbitrary maps.
    {H' Z' : Type*} (decodeH : H' → H) (decodeZ : Z' → Z)
    -- `μ`, `K`: the target first law and conditional laws on `H`, `Z`; `μ'`, `K'`: the
    -- source ones on `H'`, `Z'`.
    (μ : ProbDist H) (μ' : ProbDist H') (K : H → ProbDist Z) (K' : H' → ProbDist Z')
    -- `hμ`: the first laws correspond, `decodeH_* μ' = μ`.
    (hμ : ProbDist.map decodeH μ' = μ)
    -- `hK`: at every `h : H'`, `K' h` maps to the target conditional law at `decodeH h`.
    (hK : ∀ h, ProbDist.map decodeZ (K' h) = K (decodeH h)) :
    ProbDist.map (Prod.map decodeH decodeZ) (jointLaw μ' K') = jointLaw μ K := by
  apply Subtype.ext
  change fTransform _ (μ'.1.bindK _) = μ.1.bindK _
  -- Replace `μ` by `decodeH_* μ'`; both sides then draw `h ← μ'` first.
  rw [← congrArg Subtype.val hμ]
  simp only [ProbDist.map, bindK_fTransform, fTransform_bindK]
  apply bindK_congr
  intro h _
  -- Given `h : H'`, decoding `(h, z')` gives `(decodeH h, decodeZ z')`, and
  -- `decodeZ_* (K' h) = K (decodeH h)` is `hK h`.
  rw [fTransform_fTransform]
  change fTransform ((fun z => (decodeH h, z)) ∘ decodeZ) (K' h).1 = _
  rw [← fTransform_fTransform]
  exact congrArg (fTransform (fun z => (decodeH h, z))) (congrArg Subtype.val (hK h))

end ProbDist

/-! ### Independent normalized laws -/

/-- Independent pushforwards form the pushforward of the product:
`(f_* P) × (g_* Q) = (f × g)_* (P × Q)`. -/
lemma prodProbDist_map
    -- `A`, `B` carry independent draws; `S`, `T` carry their images under `f`, `g`.
    {S T : Type*} (f : A → S) (g : B → T)
    -- `P`, `Q` are normalized laws; `prodProbDist P Q` samples their coordinates independently.
    (P : ProbDist A) (Q : ProbDist B) :
    prodProbDist (ProbDist.map f P) (ProbDist.map g Q) =
      ProbDist.map (Prod.map f g) (prodProbDist P Q) :=
  Subtype.ext (fTransform_prod f g P.1 Q.1).symm

end Probability.Distribution
