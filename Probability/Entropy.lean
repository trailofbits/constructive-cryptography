/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.StatisticalDistance
import Probability.FiberCoupling
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Min-entropy, collision entropy and distance from uniform (tower level L2)

The first information-theory module of the tree: mathlib has no entropy of a
distribution at all (`Mathlib/InformationTheory/` is Hamming distance, coding
theory and the measure-theoretic Kullback-Leibler divergence), so these
quantities are stated on the library's own `Distribution A = A →₀ ℝ` and built
only out of `Probability.Distribution` and `Probability.Expectation`.

## Contents

*Maurer, "Cryptography Foundations" lecture notes (CR18) §7.2.3, printed
pp. 138-139.*  CR18 is the **R8 fallback** source here and is flagged as such:
none of the primaries (MauRen16, Jost, LiuMau20, Lanzenberger) treats the
collision/guessing calculus.  For a random variable `X` over a finite alphabet
`𝒳`, the three quantities

* `Distribution.guessProb` — `p_max(X) = max_x P_X(x)`;
* `Distribution.collProb` — `p_coll(X) = ∑_x P_X(x)²`, the probability that two
  independent copies of `X` collide;
* `Distribution.distFromUniform` — `d(X) = ½ ∑_x |P_X(x) − 1/|𝒳||`;

their logarithms `Distribution.minEntropy` (`H_∞(X) = −log₂ p_max(X)`) and
`Distribution.collisionEntropy` (CR18's Rényi entropy `R(X) = −log₂ p_coll(X)`);
and the two lemmas CR18 leaves as exercises,

* **Lemma 7.6** — `Distribution.one_div_card_le_collProb`,
  `Distribution.collProb_le_guessProb`: `1/|𝒳| ≤ p_coll(X) ≤ p_max(X)`;
* **Lemma 7.7** —
  `Distribution.distFromUniform_le_half_sqrt_card_mul_collProb_sub_one`:
  `d(X) ≤ ½√(|𝒳|·p_coll(X) − 1)`.

Both are Cauchy-Schwarz against the constant function, i.e. the `NonNeg`-layer
`Distribution.expect_mul_sq_le_sq_mul_sq` evaluated on `Distribution.uniform`.

*Maurer-Renner, "From Indifferentiability to Constructive Cryptography (and
Back)" (MauRen16), Appendix, "Min-entropy sampling" — a **primary** source.*
The guessing formulation of conditional min-entropy and its chain rule:

* `Distribution.condGuessProb` — `2^{−H_∞(X|Y)} = max_f Pr[X = f(Y)]`;
* `Distribution.condMinEntropy` — `H_∞(X|Y) = −log₂ max_f Pr[X = f(Y)]`;
* `Distribution.minEntropy_marginal_sub_logb_card_le_condMinEntropy` —
  MauRen16 eq. (11), `H_∞(X|Y) ≥ H_∞(X) − log₂|𝒴|`, together with its
  exponentiated, logarithm-free form
  `Distribution.condGuessProb_le_card_mul_guessProb_marginal`.

The Shannon layer (CR18 App. A.2: `H(X)`, conditional entropy, mutual
information) is deliberately *not* here; it is `Probability.ShannonEntropy`,
which imports this module.

## Naming: two different tasks, and mathlib's prefixes

*Guessing* — recovering an unknown **value**, possibly from correlated side
information — and *testing* — deciding **which of two distributions** produced a
sample — are different tasks with different optimal probabilities, and the tree
carries both.  They are separated by mathlib's own conventions rather than by
invented adjectives:

* `Distribution.guessProb X = max_x P_X(x)` and
  `Distribution.condGuessProb X = max_f Pr[X = f(Y)]` — the `cond` prefix is
  mathlib's marker for a conditional version (`condExp`, `condVar`,
  `condDistrib`, `condCount`), so the pair spells itself, and it lines up with
  `minEntropy` / `condMinEntropy`.  `guessProb` is CR18's `p_max`; the two names
  are the same number and only one of them is defined.
* `Probability.avgSuccessProb X Y g` (`Probability/StatisticalDistance.lean`) —
  the *testing* quantity.  It is prior-averaged over a **given** rule, which is
  mathlib's `avgRisk` register (`Mathlib/Probability/Decision/Risk/Defs.lean`)
  rather than `bayesRisk`, since `bayes` there names the *optimum*; the optimum
  is `sSup_avgSuccessProb_eq_half_add_half_statDist`.

## Hypothesis discipline (PHI-SPEC R1/R9)

The carrier is signed (`Distribution A = A →₀ ℝ`, R1) and the honest slice is
cut out by `Distribution.NonNeg` plus a weight hypothesis (R9).  Each statement
below carries the **weakest** of signed / `NonNeg` / `isProbDist` at which it is
true — entropy of a signed object is not a thing, but several of these
quantities are honest one layer below `isProbDist`:

* **signed**: `collProb_nonneg` — a sum of squares needs no hypothesis at all;
  `marginal_apply`, `mass_graph_eq_sum` — pointwise identities.
* **`weight = 1` alone**: Lemma 7.6's *lower* bound and the whole of Lemma 7.7.
  Neither uses nonnegativity of `X`: the only nonnegative weights the
  Cauchy-Schwarz step needs are the uniform ones it is evaluated against, and
  `|·|` handles the signs.  Requiring `isProbDist` there would have been
  strictly stronger than the mathematics.
* **`NonNeg`**: `guessProb_nonneg`, `le_condGuessProb`,
  `condGuessProb_le_card_mul_guessProb_marginal` — the chain rule is an order
  argument about masses, and normalization plays no part in it.
* **`isProbDist`**: Lemma 7.6's *upper* bound (`p(x)² ≤ p(x)·p_max` needs
  `p(x) ≥ 0`, and `∑ p = 1` closes it) and every statement whose conclusion
  mentions a logarithm.

**A logarithm carries its own side conditions.**  `Real.logb` is a junk-valued
total function, so an inequality between logarithms is only the inequality
between their arguments when those arguments are *positive*.  The positivity
facts (`guessProb_pos`, `collProb_pos`, `condGuessProb_pos`) are therefore proved
here and discharged explicitly at each logarithmic statement, rather than being
absorbed into a blanket hypothesis.

## Facts staged in this file that belong one layer down

`bddAbove_range`, `marginal_apply`, `marginal_isProbDist`,
`exists_pos_of_isProbDist`, `apply_le_weight` and `mass_graph_eq_sum` are facts
about `Distribution` itself and belong in `Probability.Distribution`;
`expect_uniform_eq_sum_div` belongs in `Probability.Expectation`.  They are kept
here so that adding this module does not force a rebuild of the tree's base
modules while other work is in flight; §0 marks them for relocation.
-/

noncomputable section

open scoped BigOperators

namespace Probability

namespace Distribution

variable {A : Type*} {α γ : Type*}

/-! ## 0. `Distribution` facts this module needs — staged here, belong in `Probability.Distribution` -/

/-- A finitely supported function takes finitely many values, so its range is
bounded above.  This is what makes `⨆ a, X a` an honest maximum rather than a
junk value.  Signed layer.

UPSTREAM-CANDIDATE (`Finsupp`): the range of a `Finsupp` into a
conditionally complete lattice is bounded. -/
theorem bddAbove_range (X : Distribution A) : BddAbove (Set.range (X : A → ℝ)) := by
  classical
  have hsub : Set.range (X : A → ℝ) ⊆ insert 0 ((X : A → ℝ) '' (X.support : Set A)) := by
    rintro _ ⟨a, rfl⟩
    by_cases ha : a ∈ X.support
    · exact Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩
    · exact Set.mem_insert_iff.mpr (Or.inl (Finsupp.notMem_support_iff.mp ha))
  exact (((X.support.finite_toSet.image (X : A → ℝ)).insert 0).subset hsub).bddAbove

/-- No single point of a nonnegative distribution carries more than its total
weight.  `NonNeg` layer, no `Fintype`. -/
theorem apply_le_weight {X : Distribution A} (hX : X.NonNeg) (a : A) : X a ≤ X.weight := by
  classical
  by_cases ha : a ∈ X.support
  · exact Finset.single_le_sum (f := (X : A → ℝ)) (fun b _ => hX b) ha
  · rw [Finsupp.notMem_support_iff.mp ha]
    exact hX.weight_nonneg

/-- A probability distribution charges some point.  `isProbDist` layer: total
weight one forces the support to be nonempty. -/
theorem exists_pos_of_isProbDist {X : Distribution A} (hX : X.isProbDist) : ∃ a, 0 < X a := by
  by_contra h
  have hzero : ∀ a ∈ X.support, X a = 0 := fun a _ =>
    le_antisymm (not_lt.mp fun hlt => h ⟨a, hlt⟩) (hX.1 a)
  have : X.weight = 0 := Finset.sum_eq_zero hzero
  rw [hX.2] at this
  exact one_ne_zero this

/-- Pointwise form of the first marginal: `P_X(a) = Pr[(X, Y) ∈ {a} × 𝒴]`
(CR18 Def. A.4).  `Distribution.marginal` is the pushforward along `Prod.fst`, so this
is `fTransform_apply_eq_mass`.  Signed layer. -/
theorem marginal_apply (X : Distribution (α × γ)) (a : α) :
    X.marginal a = X.mass fun p => p.1 = a :=
  fTransform_apply_eq_mass Prod.fst X a

/-- The first marginal of a probability distribution is a probability
distribution. -/
theorem marginal_isProbDist {X : Distribution (α × γ)} (hX : X.isProbDist) :
    X.marginal.isProbDist :=
  ⟨hX.1.fTransform Prod.fst, (weight_fTransform Prod.fst X).trans hX.2⟩

/-- The mass of the **graph of a function** `f : 𝒴 → 𝒳` inside a joint law is
the sum of the joint law along that graph.  Signed layer; `Fintype 𝒴` is what
makes the sum finite, and the first alphabet stays arbitrary. -/
theorem mass_graph_eq_sum [Fintype γ] (X : Distribution (α × γ)) (f : γ → α) :
    (X.mass fun p => p.1 = f p.2) = ∑ c : γ, X (f c, c) := by
  classical
  have hinj : ∀ c ∈ (Finset.univ : Finset γ), ∀ c' ∈ (Finset.univ : Finset γ),
      ((f c, c) : α × γ) = (f c', c') → c = c' := fun c _ c' _ h => by
    simpa using congrArg Prod.snd h
  rw [mass, Finsupp.sum, ← Finset.sum_filter, Finset.sum_image hinj |>.symm]
  refine Finset.sum_subset (fun p hp => ?_) (fun p _ hp => ?_)
  · rw [Finset.mem_filter] at hp
    refine Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, ?_⟩
    rw [← hp.2]
  · rw [Finset.mem_filter] at hp
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp ‹p ∈ Finset.image _ _›
    exact Finsupp.notMem_support_iff.mp fun hs => hp ⟨hs, rfl⟩

/-! ## 1. Maximal probability, a.k.a. the guessing probability — CR18 §7.2.3

`p_max(X) := max_x P_X(x)`.  Written as `⨆ a, X a` rather than a
`Finset.max'`: `Distribution A` already carries finite support (`bddAbove_range`), so
the supremum is attained without a `Fintype` hypothesis, and on an empty
carrier `Real.iSup_of_isEmpty` gives the right junk value `0`. -/

/-- **Maximal probability** `p_max(X) = max_x P_X(x)` (CR18 §7.2.3, printed
p. 139), equivalently the optimal probability of **guessing** `X` with no side
information — the unconditional companion of `condGuessProb`, exactly as
`minEntropy` is the unconditional companion of `condMinEntropy`.

The identifier follows mathlib's `cond`-prefix convention rather than CR18's
glyph `p_max`, so that the pair `guessProb` / `condGuessProb` spells the
distinction on its own; CR18's name is recorded here and nowhere duplicated. -/
def guessProb (X : Distribution A) : ℝ := ⨆ a, X a

/-- Every point is charged at most `p_max`.  Signed layer. -/
theorem le_guessProb (X : Distribution A) (a : A) : X a ≤ X.guessProb :=
  le_ciSup X.bddAbove_range a

/-- A uniform nonnegative bound on the point masses bounds `p_max`.  The
nonnegativity of the bound covers the empty carrier, where `p_max = 0`. -/
theorem guessProb_le {X : Distribution A} {c : ℝ} (h : ∀ a, X a ≤ c) (hc : 0 ≤ c) :
    X.guessProb ≤ c :=
  Real.iSup_le h hc

/-- `p_max` is nonnegative.  `NonNeg` layer. -/
theorem guessProb_nonneg {X : Distribution A} (hX : X.NonNeg) : 0 ≤ X.guessProb :=
  Real.iSup_nonneg hX

/-- `p_max(X) ≤ 1` for a probability distribution. -/
theorem guessProb_le_one {X : Distribution A} (hX : X.isProbDist) : X.guessProb ≤ 1 :=
  guessProb_le (fun a => (apply_le_weight hX.1 a).trans_eq hX.2) zero_le_one

/-- `p_max(X) > 0`: a probability distribution charges some point.
`isProbDist` layer — this is the side condition `minEntropy`'s logarithm
needs. -/
theorem guessProb_pos {X : Distribution A} (hX : X.isProbDist) : 0 < X.guessProb :=
  let ⟨a, ha⟩ := exists_pos_of_isProbDist hX
  ha.trans_le (le_guessProb X a)

/-! ## 2. Collision probability — CR18 §7.2.3 -/

/-- **Collision probability** `p_coll(X) = ∑_x P_X(x)²` (CR18 §7.2.3, printed
p. 139), written as the expectation of the law under itself.  CR18 introduces
it as `Pr[X₁ = X₂]` for two independent copies, which is
`collProb_eq_mass_prod_diag`. -/
def collProb (X : Distribution A) : ℝ := X.expect fun a => X a

/-- `p_coll` as an ordinary sum of squares over a finite carrier. -/
theorem collProb_eq_sum [Fintype A] (X : Distribution A) : X.collProb = ∑ a : A, X a ^ 2 := by
  rw [collProb, expect_eq_sum]
  exact Finset.sum_congr rfl fun a _ => (sq (X a)).symm

/-- `p_coll` is nonnegative.  **Signed layer**: it is a sum of squares, so
unlike the other order facts of this file it needs no hypothesis at all. -/
theorem collProb_nonneg (X : Distribution A) : 0 ≤ X.collProb :=
  Finset.sum_nonneg fun a _ => mul_self_nonneg (X a)

/-- `p_coll(X) > 0`.  `isProbDist` layer — the side condition
`collisionEntropy`'s logarithm needs. -/
theorem collProb_pos {X : Distribution A} (hX : X.isProbDist) : 0 < X.collProb := by
  classical
  obtain ⟨a, ha⟩ := exists_pos_of_isProbDist hX
  refine Finset.sum_pos' (fun b _ => mul_self_nonneg (X b)) ⟨a, ?_, mul_pos ha ha⟩
  exact Finsupp.mem_support_iff.mpr ha.ne'

/-- CR18's own reading of the name (§7.2.3, printed p. 139): `p_coll(X)` is
`Pr[X₁ = X₂]` for two **independent** copies of `X`, i.e. the diagonal mass of
the product law. -/
theorem collProb_eq_mass_prod_diag [DecidableEq A] (X : Distribution A) :
    ((X.prod X).mass fun p => p.1 = p.2) = X.collProb := by
  classical
  rw [mass_prod_eq_double_sum, collProb, expect]
  refine Finsupp.sum_congr fun a ha => ?_
  rw [Finsupp.sum]
  refine (Finset.sum_eq_single_of_mem a ha fun b _ hb => ?_).trans ?_
  · exact if_neg (Ne.symm hb)
  · simp

/-! ## 3. Distance from uniform — CR18 §7.2.3 -/

/-- **Distance from uniform** `d(X) = ½ ∑_x |P_X(x) − 1/|𝒳||` (CR18 §7.2.3,
printed p. 139), the quantity privacy amplification bounds. -/
def distFromUniform [Fintype A] (X : Distribution A) : ℝ :=
  (∑ a : A, |X a - 1 / (Fintype.card A : ℝ)|) / 2

/-- `d(X) ≥ 0`.  Signed layer: a sum of absolute values. -/
theorem distFromUniform_nonneg [Fintype A] (X : Distribution A) : 0 ≤ X.distFromUniform :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_le_two

/-- `d(X)` **is** the statistical distance to the uniform distribution — the
bridge from this module's CR18 vocabulary to the tree's `statDist` calculus.
Weakest layer: `weight = 1`, which is exactly what
`statDist_eq_half_sum_abs_of_weight_eq` needs to identify the one-sided excess
with the half-`L¹` form. -/
theorem distFromUniform_eq_statDist_uniform [Fintype A] [Nonempty A] {X : Distribution A}
    (hw : X.weight = 1) :
    X.distFromUniform = statDist X (uniform A) := by
  rw [statDist_eq_half_sum_abs_of_weight_eq X (uniform A) (hw.trans weight_uniform.symm),
    distFromUniform]
  exact congrArg (· / 2) (Finset.sum_congr rfl fun a _ => by rw [uniform_apply])

/-! ## 4. CR18 Lemmas 7.6 and 7.7

Both are left as exercises in the source (printed p. 139) and both are the same
step: **Cauchy–Schwarz against the constant function `1`**, which is
`Distribution.expect_mul_sq_le_sq_mul_sq` evaluated on `Distribution.uniform A`.  The uniform
distribution is where the `NonNeg` hypothesis of Cauchy–Schwarz is discharged,
which is why neither lemma needs `X` itself to be nonnegative. -/

/-- Expectation against the uniform distribution is the average.  Local to the
Cauchy–Schwarz step below; the general statement belongs at L1 in
`Probability.Expectation`. -/
theorem expect_uniform_eq_sum_div [Fintype A] [Nonempty A] (f : A → ℝ) :
    (uniform A).expect f = (∑ a : A, f a) / (Fintype.card A : ℝ) := by
  rw [expect_eq_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ => by rw [uniform_apply]; ring

/-- **Cauchy–Schwarz against the constant function**:
`(∑ f)² ≤ |𝒳| · ∑ f²`.  Proved by evaluating the `NonNeg`-layer
`Distribution.expect_mul_sq_le_sq_mul_sq` on `Distribution.uniform`, which is where the
nonnegative weights come from; `f` itself is arbitrary.

Stated at the root of `RandomSystems` rather than in the `Distribution` namespace: the
conclusion is about a `Finset` sum of an arbitrary real function, and mentions
no distribution.

UPSTREAM-CANDIDATE: mathlib has the general `Finset.sum_mul_sq_le_sq_mul_sq`
but no named specialization to the constant second factor. -/
theorem _root_.Probability.sq_sum_le_card_mul_sum_sq [Fintype A] [Nonempty A] (f : A → ℝ) :
    (∑ a : A, f a) ^ 2 ≤ (Fintype.card A : ℝ) * ∑ a : A, f a ^ 2 := by
  have hm : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcs := expect_mul_sq_le_sq_mul_sq (X := uniform A) uniform_nonNeg f fun _ => (1 : ℝ)
  simp only [mul_one, one_pow] at hcs
  rw [expect_uniform_eq_sum_div, expect_uniform_eq_sum_div, expect_uniform_eq_sum_div,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_self hm.ne',
    mul_one, div_pow, div_le_div_iff₀ (by positivity) hm] at hcs
  nlinarith [hcs, hm]

/-- **CR18 Lemma 7.6, lower bound** (printed p. 139, left as an exercise):
`1/|𝒳| ≤ p_coll(X)`.  Uniform minimises the collision probability.

Weakest layer: `weight = 1` alone.  Nonnegativity of `X` is *not* used —
Cauchy–Schwarz is applied with the uniform weights, not with `X`'s. -/
theorem one_div_card_le_collProb [Fintype A] [Nonempty A] {X : Distribution A}
    (hw : X.weight = 1) :
    1 / (Fintype.card A : ℝ) ≤ X.collProb := by
  have hm : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ a : A, X a = 1 := (weight_eq_sum X).symm.trans hw
  have h := sq_sum_le_card_mul_sum_sq (A := A) fun a => X a
  rw [hsum, one_pow, ← collProb_eq_sum] at h
  rw [div_le_iff₀ hm]
  linarith [h]

/-- **CR18 Lemma 7.6, upper bound** (printed p. 139, left as an exercise):
`p_coll(X) ≤ p_max(X)`.  An upper bound on the maximal probability is an upper
bound on the collision probability, which is what privacy amplification uses.

`isProbDist` layer, and both halves are load-bearing: nonnegativity turns
`P(x)² ≤ P(x)·p_max` into a pointwise inequality, and `∑ P = 1` collapses the
resulting `p_max · |X|`.  No `Fintype`. -/
theorem collProb_le_guessProb {X : Distribution A} (hX : X.isProbDist) : X.collProb ≤ X.guessProb := by
  have h := expect_le_mul_weight hX.1 (f := (X : A → ℝ)) (c := X.guessProb)
    fun a _ => le_guessProb X a
  rwa [hX.2, mul_one] at h

/-- **CR18 Lemma 7.7** (printed p. 139, left as an exercise):
`d(X) ≤ ½√(|𝒳| · p_coll(X) − 1)`.  The bound that converts a collision-entropy
guarantee into a distance-from-uniform guarantee, and hence the engine of the
privacy-amplification theorem (CR18 Thm 7.9).

Weakest layer: `weight = 1` alone — the absolute values absorb the signs and,
as in Lemma 7.6's lower bound, the nonnegative weights that Cauchy–Schwarz
needs are the uniform ones.  The radicand is nonnegative by Lemma 7.6. -/
theorem distFromUniform_le_half_sqrt_card_mul_collProb_sub_one [Fintype A] [Nonempty A]
    {X : Distribution A} (hw : X.weight = 1) :
    X.distFromUniform ≤ Real.sqrt ((Fintype.card A : ℝ) * X.collProb - 1) / 2 := by
  have hm : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ a : A, X a = 1 := (weight_eq_sum X).symm.trans hw
  -- The radicand, via Lemma 7.6.
  have hrad : 0 ≤ (Fintype.card A : ℝ) * X.collProb - 1 := by
    have := one_div_card_le_collProb (A := A) hw
    rw [div_le_iff₀ hm] at this
    linarith
  -- `∑ (P(x) − 1/m)² = p_coll(X) − 1/m`.
  have hexp : ∑ a : A, |X a - 1 / (Fintype.card A : ℝ)| ^ 2
      = X.collProb - 1 / (Fintype.card A : ℝ) := by
    have hpt : ∀ a : A, |X a - 1 / (Fintype.card A : ℝ)| ^ 2
        = X a ^ 2 - 2 * (1 / (Fintype.card A : ℝ)) * X a
            + (1 / (Fintype.card A : ℝ)) ^ 2 := fun a => by
      rw [sq_abs]; ring
    rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← collProb_eq_sum]
    field_simp
    ring
  -- Cauchy–Schwarz on `|P(x) − 1/m|`.
  have hcs := sq_sum_le_card_mul_sum_sq (A := A) fun a => |X a - 1 / (Fintype.card A : ℝ)|
  rw [hexp] at hcs
  have hkey : (∑ a : A, |X a - 1 / (Fintype.card A : ℝ)|) ^ 2
      ≤ (Fintype.card A : ℝ) * X.collProb - 1 := by
    have : (Fintype.card A : ℝ) * (X.collProb - 1 / (Fintype.card A : ℝ))
        = (Fintype.card A : ℝ) * X.collProb - 1 := by
      field_simp
    linarith [hcs, this.ge, this.le]
  have hle : ∑ a : A, |X a - 1 / (Fintype.card A : ℝ)|
      ≤ Real.sqrt ((Fintype.card A : ℝ) * X.collProb - 1) :=
    (Real.le_sqrt (Finset.sum_nonneg fun a _ => abs_nonneg _) hrad).mpr hkey
  rw [distFromUniform]
  linarith [hle]

/-! ## 5. The two entropies — CR18 §7.2.3

`H_∞(X) = −log₂ p_max(X)` and, in CR18's naming, the *Rényi entropy*
`R(X) = −log₂ p_coll(X)`.  `Real.logb` is total and junk-valued off the
positives, so each statement below discharges its own positivity side
condition rather than assuming one globally. -/

/-- **Min-entropy** `H_∞(X) = −log₂ p_max(X)` (CR18 §7.2.3, printed p. 139;
MauRen16 Appendix).  This is the tree's canonical min-entropy: the `PMF`-carrier
copy that used to sit in `RandomSystemsCC/MauRen16Impossibility.lean` is gone. -/
def minEntropy (X : Distribution A) : ℝ := -Real.logb 2 X.guessProb

/-- **Collision entropy** `R(X) = −log₂ p_coll(X)` (CR18 §7.2.3, printed
p. 139, where it is called the *Rényi entropy* of `X`; it is the Rényi entropy
of order 2). -/
def collisionEntropy (X : Distribution A) : ℝ := -Real.logb 2 X.collProb

/-- `H_∞(X) ≥ 0`: no distribution has negative min-entropy. -/
theorem minEntropy_nonneg {X : Distribution A} (hX : X.isProbDist) : 0 ≤ X.minEntropy := by
  have h := Real.logb_le_logb_of_le one_lt_two (guessProb_pos hX) (guessProb_le_one hX)
  rw [Real.logb_one] at h
  simpa [minEntropy] using h

/-- **CR18 Lemma 7.6 in logarithmic form, upper half**:
`H_∞(X) ≤ R(X)`.  Min-entropy is the more pessimistic of the two measures,
which is why a min-entropy bound may be fed to privacy amplification. -/
theorem minEntropy_le_collisionEntropy {X : Distribution A} (hX : X.isProbDist) :
    X.minEntropy ≤ X.collisionEntropy := by
  have h := Real.logb_le_logb_of_le one_lt_two (collProb_pos hX) (collProb_le_guessProb hX)
  simp only [minEntropy, collisionEntropy]
  linarith

/-- **CR18 Lemma 7.6 in logarithmic form, lower half**:
`R(X) ≤ log₂|𝒳|`, with equality exactly at the uniform distribution.  `weight = 1`
layer, matching `one_div_card_le_collProb`. -/
theorem collisionEntropy_le_logb_card [Fintype A] [Nonempty A] {X : Distribution A}
    (hw : X.weight = 1) :
    X.collisionEntropy ≤ Real.logb 2 (Fintype.card A) := by
  have hm : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := Real.logb_le_logb_of_le one_lt_two (by positivity : (0 : ℝ) < 1 / (Fintype.card A : ℝ))
    (one_div_card_le_collProb (A := A) hw)
  rw [one_div, Real.logb_inv] at h
  simp only [collisionEntropy]
  linarith

/-! ## 6. Guessing `X` from `Y`, and the min-entropy chain rule

MauRen16, Appendix "Min-entropy sampling":

> `H_min(X|Y) = −log₂ max_f Pr[X = f(Y)]`, where the maximum ranges over all
> functions `f` from the alphabet `𝒴` of `Y` to the alphabet `𝒳` of `X`.  …
> Among them is a chain rule, which implies `H_min(X|Y) ≥ H_min(X) − log₂|𝒴|`.

Promoted here off mathlib `PMF (α × γ)`/`ℝ≥0∞`, where it used to live inside
the impossibility proof that first needed it (`DESIGN.md` §12 point 1). -/

/-- **Conditional guessing probability** `2^{−H_∞(X|Y)} = max_f Pr[X = f(Y)]`
(MauRen16 Appendix): the best chance of guessing the first component of a joint
law from the second, over deterministic guessing functions — the maximum as
MauRen16 prints it.

Bounded above whenever the law is nonnegative (`le_condGuessProb`); on an empty
strategy space `Real.iSup_of_isEmpty` gives the junk value `0`. -/
def condGuessProb (X : Distribution (α × γ)) : ℝ := ⨆ f : γ → α, X.mass fun p => p.1 = f p.2

/-- Every guessing function is dominated by the optimum.  `NonNeg` layer: total
weight is the upper bound that makes the supremum finite. -/
theorem le_condGuessProb {X : Distribution (α × γ)} (hX : X.NonNeg) (f : γ → α) :
    (X.mass fun p => p.1 = f p.2) ≤ X.condGuessProb :=
  le_ciSup (f := fun g : γ → α => X.mass fun p => p.1 = g p.2)
    ⟨X.weight, by rintro _ ⟨g, rfl⟩; exact mass_le_weight hX _⟩ f

/-- The optimal guessing probability is nonnegative.  `NonNeg` layer. -/
theorem condGuessProb_nonneg {X : Distribution (α × γ)} (hX : X.NonNeg) : 0 ≤ X.condGuessProb :=
  Real.iSup_nonneg fun _ => hX.mass_nonneg _

/-- The optimal guessing probability is positive: guessing a fixed heavy value
already succeeds with positive probability.  `isProbDist` layer — the side
condition `condMinEntropy`'s logarithm needs. -/
theorem condGuessProb_pos {X : Distribution (α × γ)} (hX : X.isProbDist) : 0 < X.condGuessProb := by
  obtain ⟨a, ha⟩ := exists_pos_of_isProbDist (marginal_isProbDist hX)
  refine ha.trans_le ?_
  rw [marginal_apply]
  exact le_condGuessProb hX.1 fun _ => a

/-- **MauRen16 eq. (11), exponentiated**: `2^{−H_∞(X|Y)} ≤ |𝒴| · 2^{−H_∞(X)}`,
i.e. `max_f Pr[X = f(Y)] ≤ |𝒴| · p_max(P_X)`.

This is the logarithm-free — and therefore edge-case-free — form, and it is the
whole content of the chain rule instance: on each value `y` a guess is right
with probability at most `p_max(P_X)`, and there are `|𝒴|` values of `y`.

`NonNeg` layer: normalization plays no part, so the bound holds for
sub-distributions too.  The alphabet `𝒳` stays arbitrary; only `𝒴` is finite,
which is what the `|𝒴|` factor is. -/
theorem condGuessProb_le_card_mul_guessProb_marginal [Fintype γ] {X : Distribution (α × γ)}
    (hX : X.NonNeg) :
    X.condGuessProb ≤ (Fintype.card γ : ℝ) * X.marginal.guessProb := by
  refine Real.iSup_le (fun f => ?_)
    (mul_nonneg (Nat.cast_nonneg _) (guessProb_nonneg (hX.fTransform Prod.fst)))
  rw [mass_graph_eq_sum]
  calc ∑ c : γ, X (f c, c)
      ≤ ∑ _c : γ, X.marginal.guessProb :=
        Finset.sum_le_sum fun c _ =>
          (apply_le_fTransform_apply Prod.fst hX (f c, c)).trans (le_guessProb _ _)
    _ = (Fintype.card γ : ℝ) * X.marginal.guessProb := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Conditional min-entropy** `H_∞(X|Y) = −log₂ max_f Pr[X = f(Y)]`
(MauRen16 Appendix). -/
def condMinEntropy (X : Distribution (α × γ)) : ℝ := -Real.logb 2 X.condGuessProb

/-- **MauRen16 eq. (11) as printed**: `H_∞(X|Y) ≥ H_∞(X) − log₂|𝒴|` —
conditioning on a `k`-bit value cannot cost more than `k` bits of min-entropy.

The logarithmic form of `condGuessProb_le_card_mul_guessProb_marginal`.
`isProbDist` layer, and it is the logarithm that asks for it: the two
positivity side conditions `guessProb_pos` and `condGuessProb_pos` are discharged
here, not assumed. -/
theorem minEntropy_marginal_sub_logb_card_le_condMinEntropy [Fintype γ] [Nonempty γ]
    {X : Distribution (α × γ)} (hX : X.isProbDist) :
    X.marginal.minEntropy - Real.logb 2 (Fintype.card γ) ≤ X.condMinEntropy := by
  have hcard : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hmax : 0 < X.marginal.guessProb := guessProb_pos (marginal_isProbDist hX)
  have h := Real.logb_le_logb_of_le one_lt_two (condGuessProb_pos hX)
    (condGuessProb_le_card_mul_guessProb_marginal hX.1)
  rw [Real.logb_mul hcard.ne' hmax.ne'] at h
  simp only [minEntropy, condMinEntropy]
  linarith

end Distribution

end Probability
