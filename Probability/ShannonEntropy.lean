/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Entropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Shannon entropy, conditional entropy and mutual information (tower level L2)

The second information-theory module, and the one `Probability.Entropy`
deferred: *Maurer, "Cryptography Foundations" lecture notes (CR18)* Appendix
A.2, Definitions A.7-A.9 and Theorems A.1-A.3.  CR18 is the **R8 fallback**
source here and is flagged as such: no primary (MauRen16, Jost, LiuMau20,
Lanzenberger) develops the Shannon calculus.  Everything is stated on the
library's own `Distribution A = A →₀ ℝ` and built only out of
`Probability.Distribution` and `Probability.Expectation`.

## Contents

* `Distribution.entropy` — `H(X) = −∑ₓ P(x)·log₂ P(x)`, written as the
  expectation `𝔼_X[−log₂ P_X]` of the self-information.  **Joint entropy needs
  no separate definition**: `H(XY)` is `entropy` of a law on a product alphabet.
* `Distribution.condEntropy` — `H(X|Y) = −∑ₓ,ᵧ P(x,y)·log₂ (P(x,y)/P_Y(y))`,
  for a joint law on `α × γ`, conditioning on the **second** coordinate.  This
  is the convention `Distribution.condGuessProb` / `Distribution.condMinEntropy`
  already fixed in `Probability.Entropy` (guess the first component from the
  second).
* `Distribution.mutualInfo` — `I(X;Y) = H(X) − H(X|Y)` (CR18 Def. A.9 as
  printed).
* `Distribution.condMutualInfo` — `I(X;Y|Z) = H(X|Z) − H(X|YZ)`, on a law over
  `α × γ × ζ`.
* the chain rule `H(XY) = H(Y) + H(X|Y)`, sub-additivity, "conditioning reduces
  entropy", `0 ≤ H ≤ log₂|𝒳|`, data processing `H(f(X)) ≤ H(X)`, strong
  sub-additivity (`condMutualInfo_nonneg`), and the equality condition of each
  bound: uniformity at `H = log₂|𝒳|`, determinism at `H = 0`, and independence
  at each of `H(XY) = H(X)+H(Y)`, `H(X|Y) = H(X)`, `I(X;Y) = 0`.

## What mathlib has, and what this module adds

mathlib has **no** entropy of a distribution: `Mathlib/InformationTheory/`
contains Hamming distance, coding theory and the measure-theoretic
Kullback-Leibler divergence, and a `grep` for `shannon` across `Mathlib/` hits
only doc comments.  What it does have, and what this module is built on, is the
scalar function `Real.negMulLog x = −x·log x`
(`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`) with its concavity and
its `negMulLog_zero`/`negMulLog_one` junk-value normalisation, and
`Real.log_le_sub_one_of_pos` / `Real.log_lt_sub_one_of_pos`, which are the
whole engine of the log-sum inequality below.
`entropy_eq_sum_negMulLog_div_log_two` is the bridge:
`H(X) = (∑ₐ negMulLog (X a)) / log 2`, so a future mathlib entropy can be
aligned with this one without restating anything.  `Real.binEntropy`
(`Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`) is the two-point
special case and is *not* used here — it is stated on a probability parameter,
not on a distribution.

**Base 2, not nats.**  `Real.negMulLog` is a natural-log object;
`Distribution.minEntropy` and `Distribution.collisionEntropy` in
`Probability.Entropy` are base 2, as is CR18.  Consistency inside the
information-theory layer wins, so `entropy` is base 2 and the natural-log form
is available as the `negMulLog` bridge.  (`Probability.Divergence`'s `klDiv` is
in nats, which is where its own docstring records the convention: Pinsker's
constant `½` is a nats constant.)

## Composition with `Probability.Entropy`, not duplication

`collisionEntropy_le_entropy` and `minEntropy_le_entropy` close the Rényi ladder
`H_∞(X) ≤ R(X) ≤ H(X)` whose first link (`minEntropy_le_collisionEntropy`) is
already there, and `entropy_le_logb_card` is the Shannon companion of
`collisionEntropy_le_logb_card`.  Both new links are the same log-sum inequality
that powers sub-additivity, evaluated at a different comparison law.

## Hypothesis discipline (PHI-SPEC R1/R9)

The carrier is signed (R1) and the honest slice is `NonNeg` plus a weight
hypothesis (R9).  Each statement carries the *weakest* of signed / `NonNeg` /
`isProbDist` at which it is true.  The three layers are genuinely separated
here, and the separating examples are one line each:

* **signed** (no hypothesis): `entropy_eq_sum`,
  `entropy_eq_sum_negMulLog_div_log_two`, `entropy_zero`,
  `entropy_fTransform_of_injective`, `expect_neg_logb_fTransform_comp`.
* **`NonNeg` alone** — no normalization at all: `condEntropy_nonneg`, the
  **chain rule** `entropy_eq_entropy_marginalSnd_add_condEntropy`, the identity
  forms of `mutualInfo` and `condMutualInfo`, `mutualInfo_fTransform_swap`,
  and data processing `entropy_fTransform_le_entropy`.  Conditional entropy is
  nonnegative one layer *below* plain entropy because its integrand is
  `−log₂(P(x,y)/P_Y(y))` and the ratio is bounded by 1 pointwise, whatever the
  total weight.
* **`NonNeg` + `weight ≤ 1`** (sub-probability, strictly weaker than
  `isProbDist`): `entropy_nonneg`, sub-additivity,
  `condEntropy_le_entropy_marginal`, `mutualInfo_nonneg`.  Dropping `NonNeg`:
  the single atom `X a = −1/2` has `H(X) = −½ < 0`.  Dropping `weight ≤ 1`: the
  single atom `X a = 2` has `H(X) = −2 < 0`.
* **`isProbDist`**: `entropy_le_logb_card` and every equality condition.  The
  bound `H ≤ log₂|𝒳|` genuinely needs `weight = 1`, not `weight ≤ 1`: on a
  one-point carrier the sub-probability `X a = 1/2` has `H(X) = 1/2 > 0 = log₂ 1`.

**A logarithm carries its own side conditions**, exactly as in
`Probability.Entropy`: `Real.logb` is total and junk-valued off the positives,
so `log₂ 0 = 0` rather than `−∞`.  Two consequences are visible in the
signatures below.  First, `entropy` needs no support-restriction convention:
the `x·log x` shape kills the zero terms by itself.  Second, **Gibbs' inequality
is false without an absolute-continuity hypothesis**: on `𝒳 = {a,b}` with
`P = (½,½)` and `Q = (0,1)`, the junk value gives `𝔼_P[−log₂ Q] = 0 < 1 = H(P)`.
Every comparison statement therefore carries `hac : ∀ a, X a ≠ 0 → Y a ≠ 0`,
and each caller discharges it from a pointwise mass bound rather than assuming it.

## Facts staged in this file that belong one layer down

`expect_fTransform`, `expect_congr_of_support` and `expect_add_right'` belong in
`Probability.Expectation`; `sum_le_weight`, `sum_apply_eq_marginalSnd` and the
`marginalSnd` abbreviation belong in `Probability.Distribution`.  They are
collected in §0b and marked for relocation.  The pushforward mass bound the file
needs is **not** restated here: it is the landed
`Distribution.apply_le_fTransform_apply` (`Probability/FiberCoupling.lean`),
consumed directly at `Prod.fst`/`Prod.snd`.
-/

noncomputable section

open scoped BigOperators

namespace Probability

/-! ## 0a. The log-sum inequality — a pure `Finset` fact

`∑ᵢ pᵢ·log(qᵢ/pᵢ) ≤ 0` whenever `q` has no more total mass than `p` and `q`
does not vanish where `p` does not.  Everything in this file that is an
*inequality* is this lemma evaluated at a different comparison weight `q`:
`H ≤ log₂|𝒳|` at uniform `q`, sub-additivity at the product of marginals,
strong sub-additivity at `P_{XZ}·P_{YZ}/P_Z`, and `R(X) ≤ H(X)` at `p²/p_coll`.

Stated on a bare `Finset` and a bare pair of weight functions rather than on
`Distribution`, because two of those four comparison weights are not distributions the
caller has in hand — the `Distribution`-level Gibbs inequality
`Distribution.entropy_le_expect_neg_logb` is the corollary, not the primitive. -/

/-- Termwise form of the log-sum inequality: `p·log(q/p) ≤ q − p`.

At `p = 0` both `log (q/0) = log 0 = 0` and the left side vanish, so no
support-restriction convention is needed; at `p > 0` this is
`Real.log_le_sub_one_of_pos` applied to `q/p`, which is why `q` must not vanish.

UPSTREAM-CANDIDATE. -/
theorem mul_log_div_le_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : p ≠ 0 → q ≠ 0) :
    p * Real.log (q / p) ≤ q - p := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · simp [← hp0, hq]
  · have hq0 : 0 < q := lt_of_le_of_ne hq (Ne.symm (hac hp0.ne'))
    have hlog := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
    have := mul_le_mul_of_nonneg_left hlog hp0.le
    calc p * Real.log (q / p) ≤ p * (q / p - 1) := this
      _ = q - p := by field_simp

/-- Equality in `mul_log_div_le_sub` holds exactly at `q = p`; this is
`Real.log_lt_sub_one_of_pos`, i.e. strict concavity of `log` at `1`.

UPSTREAM-CANDIDATE. -/
theorem mul_log_div_eq_sub_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : p ≠ 0 → q ≠ 0) :
    p * Real.log (q / p) = q - p ↔ q = p := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · constructor
    · intro h; rw [← hp0] at h ⊢; simpa using h.symm
    · intro h; rw [← hp0] at h ⊢; simp [h]
  · have hq0 : 0 < q := lt_of_le_of_ne hq (Ne.symm (hac hp0.ne'))
    constructor
    · intro h
      by_contra hne
      have hne1 : q / p ≠ 1 := fun h1 => hne (by
        field_simp at h1
        exact h1)
      have hlt := Real.log_lt_sub_one_of_pos (div_pos hq0 hp0) hne1
      have := (mul_lt_mul_of_pos_left hlt hp0)
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hp0.ne'] at this
      exact absurd h (ne_of_lt this)
    · intro h
      subst h
      rw [div_self hp0.ne', Real.log_one, mul_zero, sub_self]

/-- **The log-sum inequality** (natural log): `∑ᵢ pᵢ·log(qᵢ/pᵢ) ≤ 0`.

`hac` is absolute continuity of `p` with respect to `q`, and it is not
removable: `Real.log 0 = 0` is junk, so a `q` that vanishes where `p` does not
would make the left side spuriously large.

UPSTREAM-CANDIDATE: the finite-sum Gibbs inequality, with no measure theory and
no normalization — only `∑ q ≤ ∑ p`. -/
theorem sum_mul_log_div_nonpos {ι : Type*} {s : Finset ι} {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hac : ∀ i ∈ s, p i ≠ 0 → q i ≠ 0)
    (hle : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    ∑ i ∈ s, p i * Real.log (q i / p i) ≤ 0 := by
  have h1 : ∑ i ∈ s, p i * Real.log (q i / p i) ≤ ∑ i ∈ s, (q i - p i) :=
    Finset.sum_le_sum fun i hi => mul_log_div_le_sub (hp i hi) (hq i hi) (hac i hi)
  have h2 : ∑ i ∈ s, (q i - p i) = (∑ i ∈ s, q i) - ∑ i ∈ s, p i := by
    rw [Finset.sum_sub_distrib]
  linarith

/-- **Equality in the log-sum inequality**: the sum vanishes exactly when `q`
agrees with `p` on the whole index set.

This is the single source of every equality condition in this file — uniformity
of the entropy maximiser, independence at equality in sub-additivity, and
`I(X;Y) = 0 ↔` independence.

UPSTREAM-CANDIDATE. -/
theorem sum_mul_log_div_eq_zero_iff {ι : Type*} {s : Finset ι} {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hac : ∀ i ∈ s, p i ≠ 0 → q i ≠ 0)
    (hle : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    ∑ i ∈ s, p i * Real.log (q i / p i) = 0 ↔ ∀ i ∈ s, q i = p i := by
  constructor
  · intro h
    have hstep : ∑ i ∈ s, p i * Real.log (q i / p i) ≤ ∑ i ∈ s, (q i - p i) :=
      Finset.sum_le_sum fun i hi => mul_log_div_le_sub (hp i hi) (hq i hi) (hac i hi)
    have h2 : ∑ i ∈ s, (q i - p i) = (∑ i ∈ s, q i) - ∑ i ∈ s, p i := by
      rw [Finset.sum_sub_distrib]
    have hsum0 : ∑ i ∈ s, (q i - p i) = 0 := le_antisymm (by rw [h2]; linarith)
      (by linarith)
    have hgapnn : ∀ i ∈ s, 0 ≤ (q i - p i) - p i * Real.log (q i / p i) :=
      fun i hi => sub_nonneg.mpr (mul_log_div_le_sub (hp i hi) (hq i hi) (hac i hi))
    have hgap : ∑ i ∈ s, ((q i - p i) - p i * Real.log (q i / p i)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum0, h, sub_zero]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hgapnn).mp hgap
    intro i hi
    refine (mul_log_div_eq_sub_iff (hp i hi) (hq i hi) (hac i hi)).mp ?_
    have := hzero i hi
    linarith
  · intro h
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [h i hi]
    rcases eq_or_ne (p i) 0 with h0 | h0
    · rw [h0]; ring
    · rw [div_self h0, Real.log_one, mul_zero]

/-- The base-2 form of `sum_mul_log_div_nonpos`, which is the shape every
statement in this file consumes (`Distribution.entropy` is base 2). -/
theorem sum_mul_logb_div_nonpos {ι : Type*} {s : Finset ι} {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hac : ∀ i ∈ s, p i ≠ 0 → q i ≠ 0)
    (hle : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    ∑ i ∈ s, p i * Real.logb 2 (q i / p i) ≤ 0 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hrw : ∑ i ∈ s, p i * Real.logb 2 (q i / p i)
      = (∑ i ∈ s, p i * Real.log (q i / p i)) / Real.log 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Real.logb]; ring
  rw [hrw]
  exact div_nonpos_of_nonpos_of_nonneg (sum_mul_log_div_nonpos hp hq hac hle) hlog2.le

/-- The base-2 form of `sum_mul_log_div_eq_zero_iff`. -/
theorem sum_mul_logb_div_eq_zero_iff {ι : Type*} {s : Finset ι} {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hac : ∀ i ∈ s, p i ≠ 0 → q i ≠ 0)
    (hle : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    ∑ i ∈ s, p i * Real.logb 2 (q i / p i) = 0 ↔ ∀ i ∈ s, q i = p i := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hrw : ∑ i ∈ s, p i * Real.logb 2 (q i / p i)
      = (∑ i ∈ s, p i * Real.log (q i / p i)) / Real.log 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Real.logb]; ring
  rw [hrw, div_eq_zero_iff]
  simp only [hlog2.ne', or_false]
  exact sum_mul_log_div_eq_zero_iff hp hq hac hle

namespace Distribution

variable {A B : Type*} {α γ ζ : Type*}

/-! ## 0b. `Distribution` / `Distribution.expect` facts staged here

Each of these belongs one layer down and is marked for relocation.  They are
kept here so that adding this module does not force a rebuild of the tree's
base modules while other work is in flight. -/

/-- Expectation transports along a pushforward: `𝔼_{f_*X}[g] = 𝔼_X[g ∘ f]`.
Signed layer.

**L1 (`Probability.Expectation`).** -/
theorem expect_fTransform (X : Distribution A) (f : A → B) (g : B → ℝ) :
    (fTransform f X).expect g = X.expect (g ∘ f) := by
  classical
  unfold expect fTransform
  rw [Finsupp.sum_sum_index (fun _ => zero_mul (g _))
    (fun _ m₁ m₂ => add_mul m₁ m₂ (g _))]
  exact Finsupp.sum_congr fun a _ => by simp

/-- Two integrands agreeing on the support have the same expectation.  Signed
layer.

**L1 (`Probability.Expectation`).**  `Finsupp.sum_congr` in expectation
clothing; the file uses it at every step where a logarithm identity is only
available where the mass is nonzero. -/
theorem expect_congr_of_support {X : Distribution A} {f g : A → ℝ}
    (h : ∀ a ∈ X.support, f a = g a) :
    X.expect f = X.expect g :=
  Finsupp.sum_congr fun a ha => by rw [h a ha]

/-- `expect_add_right` in the eta-expanded shape `fun a => f a + g a`, which is
what every logarithm rewrite in this file produces (`rw` will not match the
`Pi.add` spelling `f + g`).  Signed layer.

**L1 (`Probability.Expectation`).** -/
theorem expect_add_right' (X : Distribution A) (f g : A → ℝ) :
    (X.expect fun a => f a + g a) = X.expect f + X.expect g :=
  expect_add_right X f g

/-- A partial sum of a nonnegative distribution is at most its total weight.
`NonNeg` layer.

**L0 (`Probability.Distribution`).**  The `Finset` companion of `mass_le_weight`. -/
theorem sum_le_weight {X : Distribution A} (hX : X.NonNeg) (s : Finset A) :
    ∑ a ∈ s, X a ≤ X.weight := by
  classical
  have h1 : ∑ a ∈ s, X a = ∑ a ∈ s ∩ X.support, X a :=
    (Finset.sum_subset Finset.inter_subset_left fun a _ ha => by
      by_contra hne
      exact ha (Finset.mem_inter.mpr ⟨‹a ∈ s›, Finsupp.mem_support_iff.mpr hne⟩)).symm
  rw [h1, weight, Finsupp.sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    fun a _ _ => hX a

/-- The second marginal.  `Distribution.marginal` is the pushforward along `Prod.fst`;
this is the `Prod.snd` companion, which the conditional quantities of this file
need on every line.

Deliberately an `abbrev`, i.e. *reducible*: it introduces no new API, every
`fTransform` lemma applies to it unchanged, and when `Probability.Distribution`
acquires a real second marginal next to `marginal` this line is deleted with no
proof churn. -/
abbrev marginalSnd (X : Distribution (α × γ)) : Distribution γ := fTransform Prod.snd X

/-! ## 1. Shannon entropy — CR18 Def. A.7

`H(X) = −∑ₓ P(x)·log₂ P(x)`, written as the L1 expectation of the
*self-information* `−log₂ P_X`.  Summing over the finite support carried by
`Distribution A = A →₀ ℝ` means no `Fintype` hypothesis is needed, and the zero terms
take care of themselves: `Real.log 0 = 0`, so a point of zero mass contributes
`0·0`. -/

/-- **Shannon entropy** `H(X) = −∑ₓ P_X(x)·log₂ P_X(x)` (CR18 App. A.2,
Def. A.7), as the expectation `𝔼_X[−log₂ P_X]` of the self-information.

The unqualified name is Shannon's, matching `Probability.Entropy`'s
`minEntropy` and `collisionEntropy`, which qualify theirs.  **Joint entropy is
not a separate definition**: `H(XY)` is this function at a law on `α × γ`. -/
def entropy (X : Distribution A) : ℝ := X.expect fun a => -Real.logb 2 (X a)

/-- `H` as an ordinary sum over a finite carrier. -/
theorem entropy_eq_sum [Fintype A] (X : Distribution A) :
    X.entropy = ∑ a : A, -(X a * Real.logb 2 (X a)) := by
  rw [entropy, expect_eq_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **The bridge to mathlib**: `H(X)·log 2 = ∑ₐ negMulLog (X a)`, where
`Real.negMulLog x = −x·log x` is
`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`.  mathlib has no entropy
of a distribution, but it does have that scalar function together with its
concavity and its junk-value normalisation; this identity is what lets a future
mathlib `entropy` be aligned with this one instead of colliding with it.

Signed layer: a pointwise rewriting of the definition. -/
theorem entropy_eq_sum_negMulLog_div_log_two (X : Distribution A) :
    X.entropy = (X.sum fun _ w => Real.negMulLog w) / Real.log 2 := by
  rw [entropy, expect, Finsupp.sum, Finsupp.sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ => by
    simp only [Real.negMulLog, Real.logb]; ring

@[simp]
theorem entropy_zero : (0 : Distribution A).entropy = 0 := by
  rw [entropy, expect_zero_left]

/-- A point mass has no entropy — the `←` half of `entropy_eq_zero_iff_exists_eq_single`,
and true on the signed carrier because it is a computation. -/
@[simp]
theorem entropy_single_one (a : A) : entropy (Finsupp.single a (1 : ℝ) : Distribution A) = 0 := by
  unfold entropy expect
  rw [Finsupp.sum_single_index (by simp)]
  simp

/-- Entropy is invariant under an **injective** relabelling of the alphabet.
Signed layer: no hypothesis on the distribution at all.

(Injectivity is essential, not cosmetic: a non-injective pushforward merges
masses, and `entropy_fTransform_le_entropy` shows it can only lose entropy.) -/
theorem entropy_fTransform_of_injective {X : Distribution A} {f : A → B}
    (hf : Function.Injective f) :
    (fTransform f X).entropy = X.entropy := by
  unfold entropy
  rw [expect_fTransform]
  refine congrArg X.expect (funext fun a => ?_)
  simp only [Function.comp_apply, fTransform_injective_apply X f hf]

/-- `𝔼_X[−log₂ ((f_*X)(f ·))] = H(f_*X)`: the self-information of a pushforward,
pulled back to the source.  Signed layer.

This one identity is the whole mechanism behind the chain rule, sub-additivity
and strong sub-additivity: each of those rewrites a joint expectation of a
marginal's self-information into that marginal's entropy. -/
theorem expect_neg_logb_fTransform_comp (X : Distribution A) (g : A → B) :
    (X.expect fun a => -Real.logb 2 (fTransform g X (g a))) = (fTransform g X).entropy := by
  unfold entropy
  rw [expect_fTransform]
  rfl

/-! ### Nonnegativity — the sub-probability layer -/

/-- `0 ≤ H(X)`.  Weakest layer: `NonNeg` **plus `weight ≤ 1`**, i.e. any
sub-probability distribution; `isProbDist` would be strictly stronger than the
mathematics.  Both hypotheses are load-bearing, with one-atom counterexamples:
`X a = −1/2` gives `H = −1/2` (signed), and `X a = 2` gives `H = −2`
(`NonNeg`, weight 2). -/
theorem entropy_nonneg {X : Distribution A} (hX : X.NonNeg) (hw : X.weight ≤ 1) :
    0 ≤ X.entropy :=
  expect_nonneg hX fun a =>
    neg_nonneg.mpr (Real.logb_nonpos one_lt_two (hX a) ((apply_le_weight hX a).trans hw))

/-! ## 2. Gibbs' inequality — CR18 App. A.2

`H(X) ≤ 𝔼_X[−log₂ Q]` for any comparison law `Q` of no greater total weight,
with equality exactly at `Q = X`.  Every bound below is this statement at a
particular `Q`. -/

/-- The Gibbs difference as a log-sum: `𝔼_X[−log₂ P_X] − 𝔼_X[−log₂ Q]`
is `∑_{a ∈ supp X} X(a)·log₂(Q(a)/X(a))`.  Signed layer given absolute
continuity — the only role of `hac` is to license `log₂(Q/X) = log₂ Q − log₂ X`
on the support. -/
theorem entropy_sub_expect_neg_logb_eq_sum {X Y : Distribution A}
    (hac : ∀ a, X a ≠ 0 → Y a ≠ 0) :
    X.entropy - (X.expect fun a => -Real.logb 2 (Y a))
      = ∑ a ∈ X.support, X a * Real.logb 2 (Y a / X a) := by
  rw [entropy, expect, expect, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hx : X a ≠ 0 := Finsupp.mem_support_iff.mp ha
  rw [Real.logb_div (hac a hx) hx]
  ring

/-- Absolute continuity plus a weight comparison is enough to bound
`∑_{supp X} Y` by `∑_{supp X} X`, the hypothesis the log-sum inequality
consumes.  `NonNeg` on `Y` only. -/
theorem sum_support_le {X Y : Distribution A} (hY : Y.NonNeg)
    (hw : Y.weight ≤ X.weight) :
    ∑ a ∈ X.support, Y a ≤ ∑ a ∈ X.support, X a := by
  have h : ∑ a ∈ X.support, X a = X.weight := by rw [weight, Finsupp.sum]
  rw [h]
  exact (sum_le_weight hY _).trans hw

/-- **Gibbs' inequality**: `H(X) ≤ 𝔼_X[−log₂ Q]` — the entropy is the smallest
achievable average code length, and any other law `Q` scores worse.

`NonNeg` on both laws plus `Q`'s weight not exceeding `X`'s; no normalization.
`hac` is not removable — see the module docstring for the two-point
counterexample the junk value `log₂ 0 = 0` produces without it. -/
theorem entropy_le_expect_neg_logb {X Y : Distribution A} (hX : X.NonNeg) (hY : Y.NonNeg)
    (hac : ∀ a, X a ≠ 0 → Y a ≠ 0) (hw : Y.weight ≤ X.weight) :
    X.entropy ≤ X.expect fun a => -Real.logb 2 (Y a) := by
  have hsum := sum_mul_logb_div_nonpos (s := X.support) (p := (X : A → ℝ)) (q := (Y : A → ℝ))
    (fun a _ => hX a) (fun a _ => hY a) (fun a _ h => hac a h) (sum_support_le hY hw)
  have := entropy_sub_expect_neg_logb_eq_sum (X := X) (Y := Y) hac
  linarith

/-- **Equality in Gibbs' inequality holds exactly at `Q = X`.**  `NonNeg` on
both laws plus equal weights.

The equal-weight hypothesis does two jobs: it feeds the log-sum equality
condition on `supp X`, and it forces `Q` to vanish off `supp X`, which is what
upgrades "agrees on the support" to genuine equality of distributions. -/
theorem entropy_eq_expect_neg_logb_iff_eq {X Y : Distribution A} (hX : X.NonNeg) (hY : Y.NonNeg)
    (hac : ∀ a, X a ≠ 0 → Y a ≠ 0) (hw : Y.weight = X.weight) :
    (X.entropy = X.expect fun a => -Real.logb 2 (Y a)) ↔ X = Y := by
  classical
  have hdiff := entropy_sub_expect_neg_logb_eq_sum (X := X) (Y := Y) hac
  have hiff := sum_mul_logb_div_eq_zero_iff (s := X.support) (p := (X : A → ℝ))
    (q := (Y : A → ℝ)) (fun a _ => hX a) (fun a _ => hY a) (fun a _ h => hac a h)
    (sum_support_le hY hw.le)
  constructor
  · intro h
    have hzero : ∑ a ∈ X.support, X a * Real.logb 2 (Y a / X a) = 0 := by
      rw [← hdiff, h, sub_self]
    have hagree : ∀ a ∈ X.support, Y a = X a := hiff.mp hzero
    -- `Y` vanishes off `supp X`, because it already spends all its weight there.
    have hXw : ∑ a ∈ X.support, X a = X.weight := by rw [weight, Finsupp.sum]
    have hsupp : ∑ a ∈ X.support, Y a = Y.weight := by
      rw [Finset.sum_congr rfl hagree, hXw, hw]
    have hunion : ∑ a ∈ X.support ∪ Y.support, Y a = Y.weight := by
      rw [weight, Finsupp.sum]
      exact (Finset.sum_subset Finset.subset_union_right
        fun a _ ha => Finsupp.notMem_support_iff.mp ha).symm
    have hsd : ∑ a ∈ (X.support ∪ Y.support) \ X.support, Y a + ∑ a ∈ X.support, Y a
        = ∑ a ∈ X.support ∪ Y.support, Y a :=
      Finset.sum_sdiff (f := (Y : A → ℝ))
        (Finset.subset_union_left : X.support ⊆ X.support ∪ Y.support)
    have hout : ∑ a ∈ (X.support ∪ Y.support) \ X.support, Y a = 0 := by linarith
    have hzeros := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hY a).mp hout
    refine Finsupp.ext fun a => ?_
    by_cases ha : a ∈ X.support
    · exact (hagree a ha).symm
    · have hXa : X a = 0 := Finsupp.notMem_support_iff.mp ha
      by_cases hb : a ∈ Y.support
      · exact absurd (hzeros a (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hb, ha⟩))
          (Finsupp.mem_support_iff.mp hb)
      · rw [hXa, Finsupp.notMem_support_iff.mp hb]
  · intro h
    subst h
    rfl

/-! ## 3. The maximum-entropy bound — CR18 Thm A.1

`0 ≤ H(X) ≤ log₂|𝒳|`, with equality on the right exactly at the uniform
distribution.  Gibbs at `Q = uniform`. -/

/-- Expectation of the uniform self-information: `𝔼_X[−log₂ (1/|𝒳|)] = log₂|𝒳|·|X|`.
Signed layer — the constant comes out of the expectation and `X`'s total weight
is all that is left. -/
theorem expect_neg_logb_uniform [Fintype A] [Nonempty A] (X : Distribution A) :
    (X.expect fun a => -Real.logb 2 ((uniform A) a))
      = Real.logb 2 (Fintype.card A) * X.weight := by
  have hpt : ∀ a : A, -Real.logb 2 ((uniform A) a) = Real.logb 2 (Fintype.card A) := fun a => by
    rw [uniform_apply, one_div, Real.logb_inv, neg_neg]
  simp only [hpt]
  exact expect_const X _

/-- `H(U) = log₂|𝒳|`: the uniform distribution attains the bound. -/
theorem entropy_uniform [Fintype A] [Nonempty A] :
    (uniform A).entropy = Real.logb 2 (Fintype.card A) := by
  rw [entropy, expect_neg_logb_uniform, weight_uniform, mul_one]

/-- **CR18 Thm A.1**: `H(X) ≤ log₂|𝒳|`.  The Shannon companion of
`Distribution.collisionEntropy_le_logb_card` in `Probability.Entropy`.

`isProbDist` layer, and `weight = 1` is genuinely needed, not `weight ≤ 1`: on a
one-point carrier the sub-probability `X a = 1/2` has `H(X) = 1/2 > 0 = log₂ 1`. -/
theorem entropy_le_logb_card [Fintype A] [Nonempty A] {X : Distribution A} (hX : X.isProbDist) :
    X.entropy ≤ Real.logb 2 (Fintype.card A) := by
  have h := entropy_le_expect_neg_logb hX.1 uniform_nonNeg
    (fun a _ => by rw [uniform_apply]; positivity)
    (by rw [weight_uniform, hX.2])
  rwa [expect_neg_logb_uniform, hX.2, mul_one] at h

/-- **Equality in the maximum-entropy bound characterises the uniform
distribution.**  `isProbDist` layer. -/
theorem entropy_eq_logb_card_iff_eq_uniform [Fintype A] [Nonempty A] {X : Distribution A}
    (hX : X.isProbDist) :
    X.entropy = Real.logb 2 (Fintype.card A) ↔ X = uniform A := by
  have h := entropy_eq_expect_neg_logb_iff_eq hX.1 uniform_nonNeg
    (fun a _ => by rw [uniform_apply]; positivity)
    (by rw [weight_uniform, hX.2])
  rwa [expect_neg_logb_uniform, hX.2, mul_one] at h

/-- **`H(X) = 0` exactly for a deterministic `X`.**  The equality condition of
`entropy_nonneg`, at the `isProbDist` layer: every term of `H` is nonnegative,
so the sum vanishes only if each mass is `0` or `1`, and total weight one then
forces a single atom. -/
theorem entropy_eq_zero_iff_exists_eq_single {X : Distribution A} (hX : X.isProbDist) :
    X.entropy = 0 ↔ ∃ a, X = Finsupp.single a (1 : ℝ) := by
  classical
  constructor
  · intro h
    have hterm : ∀ a ∈ X.support, 0 ≤ X a * -Real.logb 2 (X a) := fun a _ =>
      mul_nonneg (hX.1 a)
        (neg_nonneg.mpr (Real.logb_nonpos one_lt_two (hX.1 a)
          ((apply_le_weight hX.1 a).trans_eq hX.2)))
    have hsum : ∑ a ∈ X.support, X a * -Real.logb 2 (X a) = 0 := by
      rw [← h, entropy, expect, Finsupp.sum]
    have hzeros := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum
    have hone : ∀ a ∈ X.support, X a = 1 := by
      intro a ha
      have hne : X a ≠ 0 := Finsupp.mem_support_iff.mp ha
      have hpos : 0 < X a := lt_of_le_of_ne (hX.1 a) (Ne.symm hne)
      have hlog : Real.logb 2 (X a) = 0 := by
        have := hzeros a ha
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hne
        · linarith [neg_eq_zero.mp h0]
      have hl : Real.log (X a) = 0 := by
        have hdiv : Real.log (X a) / Real.log 2 = 0 := hlog
        have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
        exact (div_eq_zero_iff.mp hdiv).resolve_right h2
      have := Real.exp_log hpos
      rw [hl, Real.exp_zero] at this
      exact this.symm
    have hcard : X.support.card = 1 := by
      have hw : X.weight = (X.support.card : ℝ) := by
        rw [weight, Finsupp.sum, Finset.sum_congr rfl hone, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      rw [hX.2] at hw
      exact_mod_cast hw.symm
    obtain ⟨a, hasupp⟩ := Finset.card_eq_one.mp hcard
    refine ⟨a, Finsupp.ext fun b => ?_⟩
    by_cases hb : b ∈ X.support
    · have : b = a := by simpa [hasupp] using hb
      subst this
      rw [hone b hb, Finsupp.single_eq_same]
    · have hba : b ≠ a := fun hba => hb (by simp [hasupp, hba])
      rw [Finsupp.notMem_support_iff.mp hb, Finsupp.single_eq_of_ne hba]
  · rintro ⟨a, rfl⟩
    exact entropy_single_one a

/-! ## 4. Composition with the Rényi ladder of `Probability.Entropy`

`H_∞(X) ≤ R(X) ≤ H(X)`.  The first link is `Distribution.minEntropy_le_collisionEntropy`;
this section adds the second and chains them. -/

/-- **`R(X) ≤ H(X)`**: the collision (Rényi-2) entropy of `Probability.Entropy`
never exceeds the Shannon entropy.  Together with
`Distribution.minEntropy_le_collisionEntropy` this closes the ladder
`H_∞ ≤ R ≤ H ≤ log₂|𝒳|`.

The log-sum inequality at `Q(x) = P(x)²/p_coll(X)`, which is the "escort"
distribution of order 2; `isProbDist` layer, since `p_coll > 0` is what makes
`R` a logarithm of something positive. -/
theorem collisionEntropy_le_entropy {X : Distribution A} (hX : X.isProbDist) :
    X.collisionEntropy ≤ X.entropy := by
  classical
  have hcoll : 0 < X.collProb := collProb_pos hX
  have hsum := sum_mul_logb_div_nonpos (s := X.support) (p := (X : A → ℝ))
    (q := fun a => X a ^ 2 / X.collProb)
    (fun a _ => hX.1 a) (fun a _ => by positivity)
    (fun a _ h => by
      have : (0 : ℝ) < X a ^ 2 / X.collProb :=
        div_pos (pow_pos (lt_of_le_of_ne (hX.1 a) (Ne.symm h)) 2) hcoll
      exact this.ne')
    (by
      have hq : ∀ a ∈ X.support, X a ^ 2 / X.collProb = X a * X a / X.collProb :=
        fun a _ => by ring_nf
      rw [Finset.sum_congr rfl hq, ← Finset.sum_div]
      have hcp : ∑ a ∈ X.support, X a * X a = X.collProb := by
        rw [collProb, expect, Finsupp.sum]
      rw [hcp, div_self hcoll.ne']
      have : ∑ a ∈ X.support, X a = X.weight := by rw [weight, Finsupp.sum]
      rw [this, hX.2])
  -- On the support the summand is `X a · (log₂ X a − log₂ p_coll)`.
  have hexp : ∀ a ∈ X.support,
      X a * Real.logb 2 (X a ^ 2 / X.collProb / X a)
        = X a * Real.logb 2 (X a) - X a * Real.logb 2 X.collProb := by
    intro a ha
    have hne : X a ≠ 0 := Finsupp.mem_support_iff.mp ha
    have hrw : X a ^ 2 / X.collProb / X a = X a / X.collProb := by
      field_simp
    rw [hrw, Real.logb_div hne hcoll.ne']
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  have hw : ∑ a ∈ X.support, X a = 1 := by
    have : ∑ a ∈ X.support, X a = X.weight := by rw [weight, Finsupp.sum]
    rw [this, hX.2]
  have hent : X.entropy + ∑ a ∈ X.support, X a * Real.logb 2 (X a) = 0 := by
    rw [entropy, expect, Finsupp.sum, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun a _ => by ring
  rw [hw, one_mul] at hsum
  rw [collisionEntropy]
  linarith

/-- **`H_∞(X) ≤ H(X)`**: min-entropy is the most pessimistic of the three
entropies the L2 layer carries.  Chains `Distribution.minEntropy_le_collisionEntropy`
with `collisionEntropy_le_entropy`. -/
theorem minEntropy_le_entropy {X : Distribution A} (hX : X.isProbDist) :
    X.minEntropy ≤ X.entropy :=
  (minEntropy_le_collisionEntropy hX).trans (collisionEntropy_le_entropy hX)

/-! ## 5. Conditional entropy and the chain rule — CR18 Def. A.8, Thm A.3 -/

/-- **Conditional entropy** `H(X|Y) = −∑ₓ,ᵧ P(x,y)·log₂ (P(x,y)/P_Y(y))`
(CR18 App. A.2, Def. A.8), for the joint law of a pair, **conditioning on the
second coordinate**.

This is CR18's `∑ᵧ P_Y(y)·H(X|Y=y)` written without naming the family of
conditional laws: the ratio `P(x,y)/P_Y(y)` *is* `P_{X|Y=y}(x)`, and the outer
`P(x,y)` splits as `P_Y(y)·P_{X|Y=y}(x)`.  Writing it this way keeps the chain
rule `H(XY) = H(Y) + H(X|Y)` a theorem rather than a definition, and keeps the
definition on the L1 expectation.

The first/second convention matches `Distribution.condGuessProb` and
`Distribution.condMinEntropy` in `Probability.Entropy`: the first component is the
unknown, the second is the side information. -/
def condEntropy (X : Distribution (α × γ)) : ℝ :=
  X.expect fun p => -Real.logb 2 (X p / X.marginalSnd p.2)

/-- **`H(X|Y) ≥ 0`.**  Weakest layer: **`NonNeg` alone** — one layer below
`entropy_nonneg`, and with no weight hypothesis whatsoever.  The reason is
structural: the integrand is `−log₂(P(x,y)/P_Y(y))` and the ratio is bounded by
`1` pointwise no matter what the total mass is. -/
theorem condEntropy_nonneg {X : Distribution (α × γ)} (hX : X.NonNeg) : 0 ≤ X.condEntropy := by
  refine expect_nonneg hX fun p => ?_
  have h2 := apply_le_fTransform_apply Prod.snd hX p
  have hden : 0 ≤ X.marginalSnd p.2 := (hX p).trans h2
  exact neg_nonneg.mpr (Real.logb_nonpos one_lt_two (div_nonneg (hX p) hden)
    (div_le_one_of_le₀ h2 hden))

/-- `H(X|Y) = H(XY) − H(Y)`.  **`NonNeg` layer**: no normalization is used, only
`P(x,y) > 0 ⟹ P_Y(y) > 0`, which is a mass bound. -/
theorem condEntropy_eq_entropy_sub_entropy_marginalSnd {X : Distribution (α × γ)} (hX : X.NonNeg) :
    X.condEntropy = X.entropy - X.marginalSnd.entropy := by
  have hkey : X.condEntropy
      = X.expect fun p => (-Real.logb 2 (X p)) - (-Real.logb 2 (X.marginalSnd p.2)) := by
    refine expect_congr_of_support fun p hp => ?_
    have hx : X p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hy : X.marginalSnd p.2 ≠ 0 := by
      have hpos : 0 < X p := lt_of_le_of_ne (hX p) (Ne.symm hx)
      exact (hpos.trans_le (apply_le_fTransform_apply Prod.snd hX p)).ne'
    rw [Real.logb_div hx hy]
    ring
  rw [hkey, expect_sub_right, ← entropy, expect_neg_logb_fTransform_comp]

/-- **The chain rule** `H(XY) = H(Y) + H(X|Y)` (CR18 App. A.2, Thm A.3).
`NonNeg` layer. -/
theorem entropy_eq_entropy_marginalSnd_add_condEntropy {X : Distribution (α × γ)} (hX : X.NonNeg) :
    X.entropy = X.marginalSnd.entropy + X.condEntropy := by
  rw [condEntropy_eq_entropy_sub_entropy_marginalSnd hX]
  ring

/-- **Data processing at the entropy level**: a deterministic function of `X`
carries no more entropy than `X`, `H(f(X)) ≤ H(X)`.  `NonNeg` layer.

Proved the way the textbooks do: pair `X` with `f(X)`, which is an *injective*
relabelling and so preserves entropy, then read the chain rule on that pair and
drop the nonnegative conditional term. -/
theorem entropy_fTransform_le_entropy {X : Distribution A} (hX : X.NonNeg) (f : A → B) :
    (fTransform f X).entropy ≤ X.entropy := by
  have hinj : Function.Injective fun a : A => (a, f a) := fun a b h => congrArg Prod.fst h
  set J : Distribution (A × B) := fTransform (fun a : A => (a, f a)) X with hJdef
  have hJnn : J.NonNeg := hX.fTransform _
  have hJent : J.entropy = X.entropy := entropy_fTransform_of_injective hinj
  have hJsnd : J.marginalSnd = fTransform f X := by
    rw [hJdef]
    exact fTransform_comp Prod.snd (fun a : A => (a, f a)) X
  have hchain := entropy_eq_entropy_marginalSnd_add_condEntropy hJnn
  rw [hJent, hJsnd] at hchain
  linarith [condEntropy_nonneg hJnn]

/-- `H(X) ≤ H(XY)`: a joint law is at least as uncertain as either of its
marginals.  `NonNeg` layer, `Prod.fst` case of `entropy_fTransform_le_entropy`. -/
theorem entropy_marginal_le_entropy {X : Distribution (α × γ)} (hX : X.NonNeg) :
    X.marginal.entropy ≤ X.entropy :=
  entropy_fTransform_le_entropy hX Prod.fst

/-- `H(Y) ≤ H(XY)`.  `NonNeg` layer. -/
theorem entropy_marginalSnd_le_entropy {X : Distribution (α × γ)} (hX : X.NonNeg) :
    X.marginalSnd.entropy ≤ X.entropy :=
  entropy_fTransform_le_entropy hX Prod.snd

/-! ## 6. Sub-additivity and its equality condition — CR18 Thm A.2 -/

/-- The product of the two marginals, as the comparison law of Gibbs'
inequality.  Its absolute-continuity and weight side conditions are what the
sub-additivity statements below discharge. -/
theorem expect_neg_logb_prod_marginal {X : Distribution (α × γ)} (hX : X.NonNeg) :
    (X.expect fun p => -Real.logb 2 ((X.marginal.prod X.marginalSnd) p))
      = X.marginal.entropy + X.marginalSnd.entropy := by
  have hkey : (X.expect fun p => -Real.logb 2 ((X.marginal.prod X.marginalSnd) p))
      = X.expect fun p => (-Real.logb 2 (X.marginal p.1))
          + -Real.logb 2 (X.marginalSnd p.2) := by
    refine expect_congr_of_support fun p hp => ?_
    have hx : X p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hpos : 0 < X p := lt_of_le_of_ne (hX p) (Ne.symm hx)
    have h1 : X.marginal p.1 ≠ 0 := (hpos.trans_le (apply_le_fTransform_apply Prod.fst hX p)).ne'
    have h2 : X.marginalSnd p.2 ≠ 0 := (hpos.trans_le (apply_le_fTransform_apply Prod.snd hX p)).ne'
    rw [show ((X.marginal.prod X.marginalSnd) p)
        = X.marginal p.1 * X.marginalSnd p.2 from prod_apply _ _ p.1 p.2,
      Real.logb_mul h1 h2]
    ring
  have e1 : (X.expect fun p : α × γ => -Real.logb 2 (X.marginal p.1)) = X.marginal.entropy :=
    expect_neg_logb_fTransform_comp X Prod.fst
  have e2 : (X.expect fun p : α × γ => -Real.logb 2 (X.marginalSnd p.2))
      = X.marginalSnd.entropy :=
    expect_neg_logb_fTransform_comp X Prod.snd
  rw [hkey, expect_add_right', e1, e2]

/-- Absolute continuity of a joint law with respect to the product of its
marginals.  `NonNeg` layer. -/
theorem prod_marginal_ne_zero {X : Distribution (α × γ)} (hX : X.NonNeg) (p : α × γ)
    (h : X p ≠ 0) : (X.marginal.prod X.marginalSnd) p ≠ 0 := by
  have hpos : 0 < X p := lt_of_le_of_ne (hX p) (Ne.symm h)
  have h1 : 0 < X.marginal p.1 := hpos.trans_le (apply_le_fTransform_apply Prod.fst hX p)
  have h2 : 0 < X.marginalSnd p.2 := hpos.trans_le (apply_le_fTransform_apply Prod.snd hX p)
  rw [show ((X.marginal.prod X.marginalSnd) p)
      = X.marginal p.1 * X.marginalSnd p.2 from prod_apply _ _ p.1 p.2]
  exact (mul_pos h1 h2).ne'

/-- **Sub-additivity** `H(XY) ≤ H(X) + H(Y)` (CR18 App. A.2, Thm A.2).

Weakest layer: **`NonNeg` plus `weight ≤ 1`** — the product of the marginals has
weight `|X|²`, which is what has to stay below `|X|`, so sub-probability
suffices and `isProbDist` would be stronger than the mathematics. -/
theorem entropy_le_entropy_marginal_add_entropy_marginalSnd {X : Distribution (α × γ)}
    (hX : X.NonNeg) (hw : X.weight ≤ 1) :
    X.entropy ≤ X.marginal.entropy + X.marginalSnd.entropy := by
  have hm1 : X.marginal.weight = X.weight := weight_fTransform Prod.fst X
  have hm2 : X.marginalSnd.weight = X.weight := weight_fTransform Prod.snd X
  have hwprod : (X.marginal.prod X.marginalSnd).weight ≤ X.weight := by
    rw [weight_prod, hm1, hm2]
    nlinarith [hX.weight_nonneg]
  have hnn : (X.marginal.prod X.marginalSnd).NonNeg :=
    (hX.fTransform Prod.fst).prod (hX.fTransform Prod.snd)
  have h := entropy_le_expect_neg_logb hX hnn (prod_marginal_ne_zero hX) hwprod
  rwa [expect_neg_logb_prod_marginal hX] at h

/-- **Equality in sub-additivity characterises independence**: `H(XY) = H(X) + H(Y)`
exactly when the joint law is the product of its marginals (CR18 App. A.2,
Thm A.2).  `isProbDist` layer — equality of weights is what forces the product
law to vanish wherever the joint one does. -/
theorem entropy_eq_entropy_marginal_add_entropy_marginalSnd_iff_eq_prod
    {X : Distribution (α × γ)} (hX : X.isProbDist) :
    X.entropy = X.marginal.entropy + X.marginalSnd.entropy
      ↔ X = X.marginal.prod X.marginalSnd := by
  have hm1 : X.marginal.weight = X.weight := weight_fTransform Prod.fst X
  have hm2 : X.marginalSnd.weight = X.weight := weight_fTransform Prod.snd X
  have hwprod : (X.marginal.prod X.marginalSnd).weight = X.weight := by
    rw [weight_prod, hm1, hm2, hX.2, mul_one]
  have hnn : (X.marginal.prod X.marginalSnd).NonNeg :=
    (hX.1.fTransform Prod.fst).prod (hX.1.fTransform Prod.snd)
  have h := entropy_eq_expect_neg_logb_iff_eq hX.1 hnn (prod_marginal_ne_zero hX.1) hwprod
  rwa [expect_neg_logb_prod_marginal hX.1] at h

/-- **Conditioning reduces entropy**: `H(X|Y) ≤ H(X)` (CR18 App. A.2, Thm A.2).
`NonNeg` plus `weight ≤ 1`, inherited from sub-additivity through the chain
rule. -/
theorem condEntropy_le_entropy_marginal {X : Distribution (α × γ)} (hX : X.NonNeg)
    (hw : X.weight ≤ 1) :
    X.condEntropy ≤ X.marginal.entropy := by
  rw [condEntropy_eq_entropy_sub_entropy_marginalSnd hX]
  linarith [entropy_le_entropy_marginal_add_entropy_marginalSnd hX hw]

/-! ## 7. Mutual information — CR18 Def. A.9 -/

/-- **Mutual information** `I(X;Y) = H(X) − H(X|Y)` (CR18 App. A.2, Def. A.9,
as printed).  The symmetric form `H(X) + H(Y) − H(XY)` is
`mutualInfo_eq_entropy_marginal_add_entropy_marginalSnd_sub_entropy`, and
symmetry itself is `mutualInfo_fTransform_swap`. -/
def mutualInfo (X : Distribution (α × γ)) : ℝ := X.marginal.entropy - X.condEntropy

/-- `I(X;Y) = H(X) + H(Y) − H(XY)`, the symmetric form.  `NonNeg` layer (the
chain rule). -/
theorem mutualInfo_eq_entropy_marginal_add_entropy_marginalSnd_sub_entropy
    {X : Distribution (α × γ)} (hX : X.NonNeg) :
    X.mutualInfo = X.marginal.entropy + X.marginalSnd.entropy - X.entropy := by
  rw [mutualInfo, condEntropy_eq_entropy_sub_entropy_marginalSnd hX]
  ring

/-- **`I(X;Y) ≥ 0`** — the information-theoretic content of sub-additivity.
`NonNeg` plus `weight ≤ 1`. -/
theorem mutualInfo_nonneg {X : Distribution (α × γ)} (hX : X.NonNeg) (hw : X.weight ≤ 1) :
    0 ≤ X.mutualInfo := by
  rw [mutualInfo_eq_entropy_marginal_add_entropy_marginalSnd_sub_entropy hX]
  linarith [entropy_le_entropy_marginal_add_entropy_marginalSnd hX hw]

/-- `I(X;Y) ≤ H(X)`: a variable tells you at most everything about itself.
`NonNeg` layer (nonnegativity of the conditional entropy). -/
theorem mutualInfo_le_entropy_marginal {X : Distribution (α × γ)} (hX : X.NonNeg) :
    X.mutualInfo ≤ X.marginal.entropy := by
  rw [mutualInfo]
  linarith [condEntropy_nonneg hX]

/-- **`I(X;Y) = I(Y;X)`.**  `NonNeg` layer: both sides reduce to the symmetric
form, and swapping coordinates is an injective relabelling, so the joint entropy
is untouched. -/
theorem mutualInfo_fTransform_swap {X : Distribution (α × γ)} (hX : X.NonNeg) :
    (fTransform Prod.swap X).mutualInfo = X.mutualInfo := by
  have hswapnn : (fTransform Prod.swap X).NonNeg := hX.fTransform _
  have h1 : (fTransform Prod.swap X).marginal = X.marginalSnd :=
    fTransform_comp Prod.fst Prod.swap X
  have h2 : (fTransform Prod.swap X).marginalSnd = X.marginal :=
    fTransform_comp Prod.snd Prod.swap X
  have h3 : (fTransform Prod.swap X).entropy = X.entropy :=
    entropy_fTransform_of_injective Prod.swap_injective
  rw [mutualInfo_eq_entropy_marginal_add_entropy_marginalSnd_sub_entropy hswapnn,
    mutualInfo_eq_entropy_marginal_add_entropy_marginalSnd_sub_entropy hX, h1, h2, h3]
  ring

/-- **`I(X;Y) = 0` exactly at independence.**  `isProbDist` layer; the equality
condition of `mutualInfo_nonneg`, read off `entropy_eq_..._iff_eq_prod`. -/
theorem mutualInfo_eq_zero_iff_eq_prod {X : Distribution (α × γ)} (hX : X.isProbDist) :
    X.mutualInfo = 0 ↔ X = X.marginal.prod X.marginalSnd := by
  rw [mutualInfo_eq_entropy_marginal_add_entropy_marginalSnd_sub_entropy hX.1,
    sub_eq_zero]
  exact ⟨fun h => (entropy_eq_entropy_marginal_add_entropy_marginalSnd_iff_eq_prod hX).mp h.symm,
    fun h => ((entropy_eq_entropy_marginal_add_entropy_marginalSnd_iff_eq_prod hX).mpr h).symm⟩

/-- `H(X|Y) = H(X)` exactly at independence — the equality condition of
"conditioning reduces entropy".  `isProbDist` layer. -/
theorem condEntropy_eq_entropy_marginal_iff_eq_prod {X : Distribution (α × γ)} (hX : X.isProbDist) :
    X.condEntropy = X.marginal.entropy ↔ X = X.marginal.prod X.marginalSnd := by
  rw [← mutualInfo_eq_zero_iff_eq_prod hX, mutualInfo, sub_eq_zero]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-! ## 8. Conditional mutual information and strong sub-additivity

`I(X;Y|Z) = H(X|Z) − H(X|YZ)`, on a law over `α × γ × ζ` read right-associated:
the first component is `X`, the second pair is `(Y,Z)`, so `X.condEntropy` is
already `H(X|YZ)` and `H(X|Z)` is the conditional entropy of the law of `(X,Z)`. -/

/-- **Conditional mutual information** `I(X;Y|Z) = H(X|Z) − H(X|YZ)`
(CR18 App. A.2, Def. A.9). -/
def condMutualInfo (X : Distribution (α × γ × ζ)) : ℝ :=
  (fTransform (fun p : α × γ × ζ => (p.1, p.2.2)) X).condEntropy - X.condEntropy

/-- `I(X;Y|Z) = H(XZ) + H(YZ) − H(XYZ) − H(Z)`.  `NonNeg` layer (two
applications of the chain rule); this is the form in which strong
sub-additivity is read off. -/
theorem condMutualInfo_eq_entropy_add_entropy_sub_entropy_sub_entropy
    {X : Distribution (α × γ × ζ)} (hX : X.NonNeg) :
    X.condMutualInfo
      = (fTransform (fun p : α × γ × ζ => (p.1, p.2.2)) X).entropy
        + X.marginalSnd.entropy - X.entropy
        - (fTransform (fun p : α × γ × ζ => p.2.2) X).entropy := by
  have hXZnn : (fTransform (fun p : α × γ × ζ => (p.1, p.2.2)) X).NonNeg := hX.fTransform _
  have hXZsnd : (fTransform (fun p : α × γ × ζ => (p.1, p.2.2)) X).marginalSnd
      = fTransform (fun p : α × γ × ζ => p.2.2) X :=
    fTransform_comp Prod.snd (fun p : α × γ × ζ => (p.1, p.2.2)) X
  rw [condMutualInfo, condEntropy_eq_entropy_sub_entropy_marginalSnd hXZnn,
    condEntropy_eq_entropy_sub_entropy_marginalSnd hX, hXZsnd]
  ring

/-- Summing a joint law over its first coordinate gives the second marginal.
`[Fintype α]` only.

**L0 (`Probability.Distribution`).**  The coordinate-sum form of `fTransform Prod.snd`. -/
theorem sum_apply_eq_marginalSnd [Fintype α] [Fintype γ] (J : Distribution (α × γ)) (c : γ) :
    ∑ a : α, J (a, c) = J.marginalSnd c := by
  classical
  rw [marginalSnd, fTransform_apply_eq_mass, mass_eq_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => by
    simp [Finset.sum_ite_eq' Finset.univ c fun b => J (a, b)]

/-- **Strong sub-additivity**, `0 ≤ I(X;Y|Z)`, equivalently
`H(XYZ) + H(Z) ≤ H(XZ) + H(YZ)` (CR18 App. A.2, Thm A.2 in its conditional
form).

The log-sum inequality at the comparison weight
`Q(x,y,z) = P_{XZ}(x,z)·P_{YZ}(y,z)/P_Z(z)`, which is not a distribution the
caller has in hand — this is exactly why the primitive of §0a is stated on bare
weight functions rather than on `Distribution`.  `Q` has total mass `∑_z P_Z(z)` over
the `z` it charges, hence at most `1`.

`isProbDist` plus finiteness of all three alphabets (the comparison weight is
summed over the whole carrier). -/
theorem condMutualInfo_nonneg [Fintype α] [Fintype γ] [Fintype ζ]
    {X : Distribution (α × γ × ζ)} (hX : X.isProbDist) :
    0 ≤ X.condMutualInfo := by
  classical
  set XZ : Distribution (α × ζ) := fTransform (fun p : α × γ × ζ => (p.1, p.2.2)) X with hXZ
  set YZ : Distribution (γ × ζ) := X.marginalSnd with hYZ
  set Z : Distribution ζ := fTransform (fun p : α × γ × ζ => p.2.2) X with hZ
  have hXZnn : XZ.NonNeg := hX.1.fTransform _
  have hYZnn : YZ.NonNeg := hX.1.fTransform _
  have hZnn : Z.NonNeg := hX.1.fTransform _
  have hYZsnd : YZ.marginalSnd = Z := fTransform_comp Prod.snd Prod.snd X
  have hXZsnd : XZ.marginalSnd = Z :=
    fTransform_comp Prod.snd (fun p : α × γ × ζ => (p.1, p.2.2)) X
  -- The comparison weight.
  set Q : α × γ × ζ → ℝ := fun t => XZ (t.1, t.2.2) * YZ t.2 / Z t.2.2 with hQ
  have hQnn : ∀ t : α × γ × ζ, 0 ≤ Q t := fun t =>
    div_nonneg (mul_nonneg (hXZnn _) (hYZnn _)) (hZnn _)
  -- Pointwise mass bounds: a joint mass is dominated by each of its images.
  have hXZle : ∀ t : α × γ × ζ, X t ≤ XZ (t.1, t.2.2) := fun t =>
    apply_le_fTransform_apply (fun p : α × γ × ζ => (p.1, p.2.2)) hX.1 t
  have hYZle : ∀ t : α × γ × ζ, X t ≤ YZ t.2 := fun t => apply_le_fTransform_apply Prod.snd hX.1 t
  have hZle : ∀ t : α × γ × ζ, X t ≤ Z t.2.2 := fun t =>
    apply_le_fTransform_apply (fun p : α × γ × ζ => p.2.2) hX.1 t
  -- `∑_carrier Q ≤ 1`.
  have hQsum : ∑ t : α × γ × ζ, Q t ≤ 1 := by
    have einner : ∀ a : α, ∑ w : γ × ζ, Q (a, w) = ∑ b : γ, ∑ c : ζ, Q (a, b, c) :=
      fun a => Fintype.sum_prod_type (f := fun w : γ × ζ => Q (a, w))
    have e1 : ∑ t : α × γ × ζ, Q t = ∑ a : α, ∑ b : γ, ∑ c : ζ, Q (a, b, c) := by
      rw [Fintype.sum_prod_type (f := Q)]
      exact Finset.sum_congr rfl fun a _ => einner a
    have eswap : ∀ a : α, ∑ b : γ, ∑ c : ζ, Q (a, b, c) = ∑ c : ζ, ∑ b : γ, Q (a, b, c) :=
      fun a => Finset.sum_comm
    have e2 : ∑ a : α, ∑ b : γ, ∑ c : ζ, Q (a, b, c)
        = ∑ c : ζ, ∑ a : α, ∑ b : γ, Q (a, b, c) := by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ (Finset.univ : Finset α)) => eswap a]
      exact Finset.sum_comm
    have eperc : ∀ c : ζ, ((∑ a : α, XZ (a, c)) * ∑ b : γ, YZ (b, c)) / Z c
        = ∑ a : α, ∑ b : γ, Q (a, b, c) := by
      intro c
      rw [Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div]
    have hstep : ∑ t : α × γ × ζ, Q t
        = ∑ c : ζ, ((∑ a : α, XZ (a, c)) * ∑ b : γ, YZ (b, c)) / Z c := by
      rw [e1, e2]
      exact (Finset.sum_congr rfl fun c _ => eperc c).symm
    rw [hstep]
    have hbd : ∀ c : ζ, ((∑ a : α, XZ (a, c)) * ∑ b : γ, YZ (b, c)) / Z c ≤ Z c := by
      intro c
      rw [sum_apply_eq_marginalSnd XZ c, sum_apply_eq_marginalSnd YZ c, hXZsnd, hYZsnd]
      rcases eq_or_lt_of_le (hZnn c) with h0 | h0
      · rw [← h0]; simp
      · rw [mul_div_assoc, div_self h0.ne', mul_one]
    refine (Finset.sum_le_sum fun c _ => hbd c).trans ?_
    rw [← weight_eq_sum, hZ, weight_fTransform, hX.2]
  -- The log-sum inequality on the support of `X`.
  have hle : ∑ t ∈ X.support, Q t ≤ ∑ t ∈ X.support, X t := by
    have h1 : ∑ t ∈ X.support, Q t ≤ ∑ t : α × γ × ζ, Q t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun t _ _ => hQnn t
    have h2 : ∑ t ∈ X.support, X t = 1 := by
      have : ∑ t ∈ X.support, X t = X.weight := by rw [weight, Finsupp.sum]
      rw [this, hX.2]
    linarith
  have hsum := sum_mul_logb_div_nonpos (s := X.support) (p := (X : α × γ × ζ → ℝ)) (q := Q)
    (fun t _ => hX.1 t) (fun t _ => hQnn t)
    (fun t _ h => by
      have hpos : 0 < X t := lt_of_le_of_ne (hX.1 t) (Ne.symm h)
      exact (div_pos (mul_pos (hpos.trans_le (hXZle t)) (hpos.trans_le (hYZle t)))
        (hpos.trans_le (hZle t))).ne')
    hle
  -- Expand the summand.
  have hexp : ∀ t ∈ X.support, X t * Real.logb 2 (Q t / X t)
      = X t * -Real.logb 2 (X t) - X t * -Real.logb 2 (XZ (t.1, t.2.2))
        - X t * -Real.logb 2 (YZ t.2) + X t * -Real.logb 2 (Z t.2.2) := by
    intro t ht
    have hx : X t ≠ 0 := Finsupp.mem_support_iff.mp ht
    have hpos : 0 < X t := lt_of_le_of_ne (hX.1 t) (Ne.symm hx)
    have h1 : XZ (t.1, t.2.2) ≠ 0 := (hpos.trans_le (hXZle t)).ne'
    have h2 : YZ t.2 ≠ 0 := (hpos.trans_le (hYZle t)).ne'
    have h3 : Z t.2.2 ≠ 0 := (hpos.trans_le (hZle t)).ne'
    rw [hQ, Real.logb_div (by exact div_ne_zero (mul_ne_zero h1 h2) h3) hx,
      Real.logb_div (mul_ne_zero h1 h2) h3, Real.logb_mul h1 h2]
    ring
  rw [Finset.sum_congr rfl hexp] at hsum
  -- Each of the four sums is an entropy.
  have hentX : ∑ t ∈ X.support, X t * -Real.logb 2 (X t) = X.entropy := by
    rw [entropy, expect, Finsupp.sum]
  have hentXZ : ∑ t ∈ X.support, X t * -Real.logb 2 (XZ (t.1, t.2.2)) = XZ.entropy := by
    rw [← expect_neg_logb_fTransform_comp X (fun p : α × γ × ζ => (p.1, p.2.2)), expect,
      Finsupp.sum]
  have hentYZ : ∑ t ∈ X.support, X t * -Real.logb 2 (YZ t.2) = YZ.entropy := by
    rw [hYZ, marginalSnd, ← expect_neg_logb_fTransform_comp X Prod.snd, expect, Finsupp.sum]
  have hentZ : ∑ t ∈ X.support, X t * -Real.logb 2 (Z t.2.2) = Z.entropy := by
    rw [hZ, ← expect_neg_logb_fTransform_comp X (fun p : α × γ × ζ => p.2.2), expect,
      Finsupp.sum]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hentX, hentXZ, hentYZ, hentZ] at hsum
  rw [condMutualInfo_eq_entropy_add_entropy_sub_entropy_sub_entropy hX.1, ← hXZ, ← hYZ, ← hZ]
  linarith

end Distribution

end Probability
