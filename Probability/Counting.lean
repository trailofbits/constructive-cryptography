/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Distribution
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The counting kernel

Concrete-security bounds bottom out in arithmetic and in fiber counts, not in
systems: once a proof technique has factored the adversary out, what is left is
"how many of the `N!` permutations are consistent with these `q` constraints",
"how far is `(N)_q/N^q` from `1`", "how many pairs does a gated union bound
charge".  This module is that layer — **carrier-free and metric-free**, over
`ℕ`, `ℝ`, `NNReal` and `Distribution.uniform`, with no system, transcript, or
distance anywhere in it.

Four groups, in the order later layers consume them:

* **falling factorials** — the Weierstrass product inequality, `(N)_q` as a
  real product, the birthday bound `1 − (N)_q/N^q ≤ q(q−1)/2N`, and the
  PRP/PRF switching ratio;
* **permutation-consistency mass** — the number of permutations extending a
  prescribed injective assignment is `(N−q)!`, hence the uniform-permutation
  mass of "π realizes these constraints" is exactly `1/(N)_q` and at least
  `N^{−q}`, in both the injective-tuple and the partial-injection form;
* **gate sums** — head/tail sums over a fixed cap `Fin K` gated by a
  per-instance bound, the counting side of a gated union bound;
* **the sum-of-permutations fiber ratio** — the normalized fiber lower bound
  under the cubic query condition `q³ ≤ N²`.

## Provenance

The arithmetic is standard.  The one statement with a named source is the
fiber-ratio bound `sop_ratio_counting_bound`, which the quarry attributes to
"Jha–Nandi Proposition 8.1" as a bare author name — no bibliography entry,
year, or page exists there, and no such paper is on disk.  That attribution is
**recorded, not verified**, and it sits outside the source hierarchy
(MauRen16 / Jost / LiuMau20 / Lanzenberger).  The birthday bound's two-sided
form is Boneh–Shoup, *A Graduate Course in Applied Cryptography*, Theorem B.1;
only the one-sided half is needed here and is proved outright.

Every declaration below is an architecture transplant from the quarry
(READ-ONLY): `RandomSystems/Counting.lean` and
`RandomSystems/HTechnique/{Counting,Derivation}.lean`.  Statements are
restated on this tree's objects (`Probability.Distribution`, not the quarry's
`Dist`); none of them mentions a distance, so no metric re-basing arises.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Probability

namespace Counting

/-! ## The Weierstrass product inequality

`1 − ∑ aᵢ ≤ ∏ (1 − aᵢ)`, equivalently the union bound in product form: the
chance that some step of an independent chain fails is at most the sum of the
per-step failure probabilities. -/

/-- **Weierstrass product inequality.**  `1 − ∑ᵢ f i ≤ ∏ᵢ (1 − f i)` over an
arbitrary `Finset`, whenever every `f i` lies in `[0, 1]`.

Both hypotheses are needed: `f ≡ 4` on a three-element set has `1 − ∑ f = −11`
and `∏ (1 − f) = −27`, so `f i ≤ 1` cannot be dropped.

**UPSTREAM-CANDIDATE.**  mathlib has the exact expansion
`Finset.prod_one_sub_ordered` but not this inequality, and that expansion needs
a `LinearOrder` on the index which this proof does not. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h_nonneg : ∀ i ∈ s, 0 ≤ f i) (h_le_one : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      have hmem : ∀ i ∈ s, i ∈ insert x s := fun i hi => Finset.mem_insert_of_mem hi
      have hxs : x ∈ insert x s := Finset.mem_insert_self x s
      have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun i hi => h_nonneg i (hmem i hi)
      have hih := ih (fun i hi => h_nonneg i (hmem i hi)) (fun i hi => h_le_one i (hmem i hi))
      rw [Finset.sum_insert hx, Finset.prod_insert hx]
      nlinarith [h_nonneg x hxs, h_le_one x hxs,
        mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr (h_le_one x hxs))]

/-- `Finset.range` specialization of `one_sub_sum_le_prod_one_sub`, stated in
the `≥` direction its callers use. -/
theorem chain_product_lower_bound {q : ℕ} (f : ℕ → ℝ)
    (h_nonneg : ∀ k < q, 0 ≤ f k) (h_le_one : ∀ k < q, f k ≤ 1) :
    ∏ k ∈ Finset.range q, (1 - f k) ≥ 1 - ∑ k ∈ Finset.range q, f k :=
  one_sub_sum_le_prod_one_sub _ f
    (fun k hk => h_nonneg k (Finset.mem_range.mp hk))
    (fun k hk => h_le_one k (Finset.mem_range.mp hk))

/-- `NNReal` form of `one_sub_sum_le_prod_one_sub`, carrying **no**
hypotheses: `NNReal` subtraction truncates at zero, so `f i ≤ 1` is discharged
by the statement itself — when `∑ aᵢ > 1` the left-hand side is `0`.  A
corollary of the real form, not a second proof of it. -/
theorem nnreal_one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → NNReal) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  rcases le_or_gt (∑ i ∈ s, a i) 1 with hsum | hsum
  · have hle : ∀ i ∈ s, a i ≤ 1 := fun i hi =>
      le_trans (Finset.single_le_sum (f := a) (fun j _ => zero_le (a j)) hi) hsum
    rw [← NNReal.coe_le_coe, NNReal.coe_sub hsum, NNReal.coe_prod, NNReal.coe_sum]
    refine le_trans (one_sub_sum_le_prod_one_sub s (fun i => (a i : ℝ))
      (fun i _ => (a i).coe_nonneg) (fun i hi => by exact_mod_cast hle i hi))
      (le_of_eq ?_)
    exact Finset.prod_congr rfl fun i hi => (NNReal.coe_sub (hle i hi)).symm
  · simp [tsub_eq_zero_of_le hsum.le]

/-! ## Falling-factorial arithmetic -/

/-- Closed form for `(0 + … + (q−1))/N`. -/
theorem sum_div_range (N q : ℕ) (h_N_pos : (0 : ℝ) < N) :
    ∑ k ∈ Finset.range q, ((k : ℝ) / N) = (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
  induction q with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; field_simp; ring

/-- The falling factorial `(N)_q` as a real product, valid when `q ≤ N`. -/
theorem cast_descFactorial_eq_prod {N q : ℕ} (h_le : q ≤ N) :
    ((N.descFactorial q : ℕ) : ℝ) = ∏ k ∈ Finset.range q, ((N : ℝ) - k) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun k hk => ?_)
  rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) h_le))]

/-- The falling-factorial ratio `(N)_q/N^q` as the no-collision product
`∏_{k<q} (1 − k/N)` — the shape every estimate below works in. -/
theorem prod_sub_div_pow_eq (N q : ℕ) (h_pos : 0 < N) :
    (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q
      = ∏ k ∈ Finset.range q, (1 - (k : ℝ) / N) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h_pos.ne'
  have h : ∏ k ∈ Finset.range q, ((N : ℝ) - k)
      = (N : ℝ) ^ q * ∏ k ∈ Finset.range q, (1 - (k : ℝ) / N) := by
    conv_lhs =>
      arg 2; ext k
      rw [show (N : ℝ) - (k : ℝ) = (N : ℝ) * (1 - (k : ℝ) / N) from by field_simp]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [h, mul_div_cancel_left₀ _ (pow_ne_zero q hN)]

/-- Falling-factorial lower bound: `(N)_q ≥ N^q·(1 − q(q−1)/2N)`. -/
theorem falling_factorial_lower_bound {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    (∏ k ∈ Finset.range q, ((N : ℝ) - k)) ≥
      (N : ℝ) ^ q * (1 - (q : ℝ) * ((q : ℝ) - 1) / (2 * N)) := by
  have h_N_pos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  have h_factor : ∏ k ∈ Finset.range q, ((N : ℝ) - k) =
      (N : ℝ) ^ q * ∏ k ∈ Finset.range q, (1 - (k : ℝ) / N) := by
    rw [← prod_sub_div_pow_eq N q h_pos]
    field_simp
  rw [h_factor]
  have h_chain := chain_product_lower_bound (fun k => (k : ℝ) / N)
    (fun k _ => div_nonneg (Nat.cast_nonneg k) (le_of_lt h_N_pos))
    (fun k hk => by
      rw [div_le_one h_N_pos]
      exact_mod_cast (Nat.lt_of_lt_of_le hk h_le).le)
  rw [sum_div_range N q h_N_pos] at h_chain
  exact mul_le_mul_of_nonneg_left (GE.ge.le h_chain) (pow_nonneg (le_of_lt h_N_pos) q)

/-- **Birthday bound**: `1 − (N)_q/N^q ≤ q(q−1)/2N`.  The left-hand side is
exactly the probability that `q` independent uniform draws from an `N`-element
set collide. -/
theorem birthday_bound {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    1 - (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
  have h_N_pos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  have h_Nq_pos : (0 : ℝ) < (N : ℝ) ^ q := pow_pos h_N_pos q
  have h_ffact := falling_factorial_lower_bound h_le h_pos
  have h_div : (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q ≥
      1 - (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
    rw [ge_iff_le, le_div_iff₀ h_Nq_pos]
    linarith
  linarith

/-! ## The switching ratio -/

/-- The ideal/real mass ratio as a falling factorial: `(N−q)!/N! = (N)_q⁻¹`,
in `NNReal` for PRP/PRF switching arguments. -/
theorem factorial_ratio_eq_descFactorial_inv {N q : ℕ} (h_le : q ≤ N) :
    ((N - q).factorial : NNReal) / (N.factorial : NNReal)
      = ((N.descFactorial q : NNReal))⁻¹ := by
  have hN : (N.factorial : NNReal)
      = ((N - q).factorial : NNReal) * (N.descFactorial q : NNReal) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial h_le]
  rw [hN, div_mul_eq_div_div, div_self (by exact_mod_cast (N - q).factorial_pos.ne'), one_div]

/-- `N^{−q} ≤ 1/(N)_q`: a uniform permutation consistent with `q` distinct
constraints is at least as likely as `q` independent uniform coincidences. -/
theorem pow_inv_le_descFactorial_inv {N k : ℕ} (h_le : k ≤ N) :
    ((N : NNReal) ^ k)⁻¹ ≤ ((N.descFactorial k : NNReal))⁻¹ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · omega
  · have hdposR : (0 : NNReal) < N.descFactorial k := by
      exact_mod_cast Nat.descFactorial_pos.mpr h_le
    have hle : (N.descFactorial k : NNReal) ≤ (N : NNReal) ^ k := by
      exact_mod_cast Nat.descFactorial_le_pow N k
    gcongr

/-- **The switching ratio**: `(1−ε)·((N−q)!/N!) ≤ 1/N^q` with birthday slack
`ε = q(q−1)/2N`.  This is the arithmetic core of every PRP/PRF switching
step: the permutation law dominates the function law on distinct transcripts,
up to the birthday defect. -/
theorem switching_ratio_le {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N)
    (h_eps : (((q * (q - 1) : ℕ) : NNReal)) / (((2 * N : ℕ)) : NNReal) ≤ 1) :
    (1 - (((q * (q - 1) : ℕ) : NNReal)) / (((2 * N : ℕ)) : NNReal))
        * (((N - q).factorial : NNReal) / (N.factorial : NNReal))
      ≤ 1 / (N : NNReal) ^ q := by
  rw [factorial_ratio_eq_descFactorial_inv h_le, ← one_div, mul_one_div,
    div_le_div_iff₀ (by exact_mod_cast Nat.descFactorial_pos.mpr h_le)
      (pow_pos (by exact_mod_cast h_pos) q), one_mul, ← NNReal.coe_le_coe]
  have hdesc : ((N.descFactorial q : NNReal) : ℝ) = ∏ k ∈ Finset.range q, ((N : ℝ) - k) := by
    rw [NNReal.coe_natCast]; exact cast_descFactorial_eq_prod h_le
  have heps : ((q * (q - 1) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)
      = (q : ℝ) * ((q : ℝ) - 1) / (2 * (N : ℝ)) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; norm_num
    · rw [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_mul]
      push_cast
      ring
  rw [hdesc, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_sub h_eps,
    NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast, heps]
  have hfall := falling_factorial_lower_bound h_le h_pos
  nlinarith [hfall]

/-! ## Permutation fibers and the permutation-consistency mass -/

/-- The number of permutations extending a prescribed injective finite
assignment is `(|X|−q)!`.

The proof is the multiply-pretransitive action argument: `Equiv.Perm X` acts
transitively on injective `q`-tuples, so every fiber of `π ↦ π ∘ inputs` has
the same size, and there are `(|X|)_q` fibers covering all `|X|!`
permutations. -/
theorem card_perm_fiber {X : Type*} [Fintype X] [DecidableEq X] {q : ℕ}
    (inputs : Fin q → X) (h_inj : Function.Injective inputs)
    (ys : Fin q → X) (h_ys_inj : Function.Injective ys)
    (h_q_le : q ≤ Fintype.card X) :
    ((Finset.univ : Finset (Equiv.Perm X)).filter
      (fun π => ∀ i, π (inputs i) = ys i)).card =
    (Fintype.card X - q).factorial := by
  classical
  set S := Finset.univ.image inputs with hS_def
  have hS_card : S.card = q := by
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_fin]
  have h_desc_pos : 0 < (Fintype.card X).descFactorial q :=
    Nat.descFactorial_pos.mpr h_q_le
  suffices h_prod : ((Finset.univ : Finset (Equiv.Perm X)).filter
      (fun π => ∀ i, π (inputs i) = ys i)).card *
      (Fintype.card X).descFactorial q = (Fintype.card X).factorial by
    have h_eq := Nat.factorial_mul_descFactorial h_q_le
    exact Nat.eq_of_mul_eq_mul_right h_desc_pos (h_prod.trans h_eq.symm)
  set Φ : Equiv.Perm X → (Fin q ↪ X) :=
    fun π => ⟨fun i => π (inputs i), (π.injective.comp h_inj)⟩
  set injTuples := (Finset.univ : Finset (Fin q ↪ X))
  have h_partition : (Finset.univ : Finset (Equiv.Perm X)).card =
      ∑ z ∈ injTuples, (Finset.univ.filter (fun π => Φ π = z)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  set ys_emb : Fin q ↪ X := ⟨ys, h_ys_inj⟩
  have h_fiber_eq : ∀ z ∈ injTuples,
      (Finset.univ.filter (fun π => Φ π = z)).card =
      (Finset.univ.filter (fun π => Φ π = ys_emb)).card := by
    intro z _
    have h_pt : MulAction.IsPretransitive (Equiv.Perm X) (Fin q ↪ X) :=
      Equiv.Perm.isMultiplyPretransitive X q
    obtain ⟨τ, hτ⟩ := h_pt.exists_smul_eq ys_emb z
    have hτ_app : ∀ i, τ (ys i) = z i := fun i => congr_fun (congr_arg (↑·) hτ) i
    apply Finset.card_bij'
      (fun π _ => τ⁻¹ * π)
      (fun σ _ => τ * σ)
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      ext i
      show τ⁻¹ (π (inputs i)) = ys i
      have : π (inputs i) = z i := congr_fun (congr_arg (↑·) hπ) i
      rw [this, ← hτ_app i]
      simp
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      ext i
      show τ (σ (inputs i)) = z i
      have : σ (inputs i) = ys i := congr_fun (congr_arg (↑·) hσ) i
      rw [this, hτ_app i]
    · intro π _
      simp
    · intro σ _
      simp
  have h_fiber_match : (Finset.univ.filter (fun π : Equiv.Perm X =>
        ∀ i, π (inputs i) = ys i)) =
      (Finset.univ.filter (fun π => Φ π = ys_emb)) := by
    ext π
    simp [Finset.mem_filter, Φ, ys_emb, Function.Embedding.ext_iff]
  have h_inj_card : injTuples.card = (Fintype.card X).descFactorial q := by
    simp only [injTuples, Finset.card_univ]
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
  rw [h_fiber_match]
  have h_sum_eq : ∑ z ∈ injTuples,
      (Finset.univ.filter (fun π => Φ π = z)).card =
      (Finset.univ.filter (fun π => Φ π = ys_emb)).card * injTuples.card := by
    rw [Finset.sum_const_nat (fun z hz => h_fiber_eq z hz), mul_comm]
  have h_card_perm : (Finset.univ : Finset (Equiv.Perm X)).card =
      Fintype.card (Equiv.Perm X) :=
    Finset.card_univ
  rw [mul_comm]
  calc (Fintype.card X).descFactorial q *
        (Finset.univ.filter (fun π => Φ π = ys_emb)).card
      = injTuples.card * (Finset.univ.filter (fun π => Φ π = ys_emb)).card := by
          rw [h_inj_card]
    _ = (Finset.univ.filter (fun π => Φ π = ys_emb)).card * injTuples.card := by
          rw [mul_comm]
    _ = ∑ z ∈ injTuples, (Finset.univ.filter (fun π => Φ π = z)).card := h_sum_eq.symm
    _ = (Finset.univ : Finset (Equiv.Perm X)).card := h_partition.symm
    _ = Fintype.card (Equiv.Perm X) := h_card_perm
    _ = (Fintype.card X).factorial := Fintype.card_perm

/-- The permutation-fiber count over an actual finite input set rather than an
injective tuple: the queried set is `S`, the prescribed outputs an embedding
`S ↪ X`. -/
theorem card_perm_fiber_finset {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (g : S ↪ X) :
    ((Finset.univ : Finset (Equiv.Perm X)).filter (fun π => ∀ x : S, π x.1 = g x)).card =
      (Fintype.card X - S.card).factorial := by
  classical
  let eS := (Fintype.equivFin S).symm
  let inputs : Fin (Fintype.card S) → X := fun i => (eS i).1
  let ys : Fin (Fintype.card S) → X := fun i => g (eS i)
  have hinputs : Function.Injective inputs := by
    intro i j hij
    have hsub : eS i = eS j := Subtype.ext hij
    exact eS.injective hsub
  have hys : Function.Injective ys := by
    intro i j hij
    exact eS.injective (g.injective hij)
  have hle : Fintype.card S ≤ Fintype.card X :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hbase := card_perm_fiber inputs hinputs ys hys hle
  have hfilter : ((Finset.univ : Finset (Equiv.Perm X)).filter
        (fun π => ∀ i, π (inputs i) = ys i)) =
      ((Finset.univ : Finset (Equiv.Perm X)).filter (fun π => ∀ x : S, π x.1 = g x)) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h x
      let i := Fintype.equivFin S x
      have hi : eS i = x := by
        dsimp [eS, i]
        simp
      simpa [inputs, ys, hi] using h i
    · intro h i
      exact h (eS i)
  rw [← hfilter]
  simpa [Fintype.card_coe] using hbase

/-- **Exact permutation-consistency mass.**  For a uniformly sampled
`π : Equiv.Perm X` and an injective assignment of `q` inputs to `q` distinct
outputs, the mass of "π realizes it" is `(|X|−q)!/|X|! = 1/(|X|)_q`. -/
theorem uniform_perm_consistent_mass_eq {X : Type*} [Fintype X] [DecidableEq X]
    {q : ℕ} (xs : Fin q → X) (hx : Function.Injective xs)
    (ys : Fin q → X) (hy : Function.Injective ys) (h_le : q ≤ Fintype.card X) :
    (Distribution.uniform (Equiv.Perm X)).mass (fun π => ∀ i, π (xs i) = ys i) =
      ((Fintype.card X - q).factorial : ℝ) / ((Fintype.card X).factorial) := by
  classical
  rw [Distribution.uniform_mass_eq_card_filter, card_perm_fiber xs hx ys hy h_le,
    show (Fintype.card (Equiv.Perm X) : ℝ)
        = ((Fintype.card X).factorial : ℝ) from by exact_mod_cast Fintype.card_perm]

/-- **The permutation-consistency lower bound**: `|X|^{−q}` is a valid lower
bound on the exact mass — a uniform permutation is at least as likely to
realize `q` distinct constraints as `q` independent uniform draws are. -/
theorem uniform_perm_consistent_mass_ge {X : Type*} [Fintype X] [DecidableEq X]
    {q : ℕ} (xs : Fin q → X) (hx : Function.Injective xs)
    (ys : Fin q → X) (hy : Function.Injective ys) (h_le : q ≤ Fintype.card X) :
    ((Fintype.card X : ℝ) ^ q)⁻¹ ≤
      (Distribution.uniform (Equiv.Perm X)).mass (fun π => ∀ i, π (xs i) = ys i) := by
  classical
  rw [uniform_perm_consistent_mass_eq xs hx ys hy h_le]
  have h := le_trans (pow_inv_le_descFactorial_inv (N := Fintype.card X) h_le)
    (le_of_eq (factorial_ratio_eq_descFactorial_inv h_le).symm)
  exact_mod_cast h

/-- Reduce a partial-injection constraint family to an injective tuple on the
image of the inputs.  The bookkeeping shared by the two `_finset` forms
below: `(a i, b i)` is a partial injection exactly when it factors through an
injective assignment indexed by `image a`. -/
theorem exists_injective_tuple_of_partialInjection {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (a b : ι → X)
    (h_pf : ∀ i j, a i = a j → b i = b j)
    (h_inj : ∀ i j, b i = b j → a i = a j) :
    ∃ (xs ys : Fin (Finset.univ.image a).card → X),
      Function.Injective xs ∧ Function.Injective ys ∧
        ∀ π : Equiv.Perm X, (∀ i, π (a i) = b i) ↔ (∀ j, π (xs j) = ys j) := by
  classical
  set S := Finset.univ.image a with hS
  let e : ↥S ≃ Fin S.card := (Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))
  let xs : Fin S.card → X := fun j => (e.symm j).1
  have hxs_inj : Function.Injective xs :=
    fun p q h => e.symm.injective (Subtype.ext h)
  have hmem : ∀ j : Fin S.card, (e.symm j).1 ∈ S := fun j => (e.symm j).2
  choose pre hpre using fun j : Fin S.card => Finset.mem_image.mp (hmem j)
  let ys : Fin S.card → X := fun j => b (pre j)
  have hys_inj : Function.Injective ys := by
    intro p q h
    have hab := h_inj _ _ h
    have hxy : xs p = xs q := by
      simp only [xs]
      rw [← (hpre p).2, ← (hpre q).2, hab]
    exact hxs_inj hxy
  refine ⟨xs, ys, hxs_inj, hys_inj, fun π => ?_⟩
  constructor
  · intro h j
    simp only [xs, ys]
    rw [← (hpre j).2]
    exact h (pre j)
  · intro h i
    have hai : a i ∈ S := Finset.mem_image_of_mem a (Finset.mem_univ i)
    have hx : xs (e ⟨a i, hai⟩) = a i := by simp [xs]
    have hh := h (e ⟨a i, hai⟩)
    rw [hx] at hh
    rw [hh]
    simp only [ys]
    apply h_pf
    rw [(hpre _).2]
    exact hx

/-- **Exact permutation-consistency mass, partial-injection form** (repeats
allowed): only the number of *distinct* inputs is charged. -/
theorem uniform_perm_consistent_mass_eq_finset {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (a b : ι → X)
    (h_pf : ∀ i j, a i = a j → b i = b j)
    (h_inj : ∀ i j, b i = b j → a i = a j)
    (h_le : (Finset.univ.image a).card ≤ Fintype.card X) :
    (Distribution.uniform (Equiv.Perm X)).mass (fun π => ∀ i, π (a i) = b i) =
      ((Fintype.card X - (Finset.univ.image a).card).factorial : ℝ) /
        ((Fintype.card X).factorial) := by
  classical
  obtain ⟨xs, ys, hxs, hys, hiff⟩ :=
    exists_injective_tuple_of_partialInjection a b h_pf h_inj
  rw [Distribution.mass_congr _ hiff]
  exact uniform_perm_consistent_mass_eq xs hxs ys hys h_le

/-- **Permutation-consistency lower bound, partial-injection form**: the mass
of permutations realizing every constraint is at least `N^{−|image a|}`. -/
theorem uniform_perm_consistent_mass_ge_finset {X ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]
    (a b : ι → X)
    (h_pf : ∀ i j, a i = a j → b i = b j)
    (h_inj : ∀ i j, b i = b j → a i = a j)
    (h_le : (Finset.univ.image a).card ≤ Fintype.card X) :
    ((Fintype.card X : ℝ) ^ (Finset.univ.image a).card)⁻¹ ≤
      (Distribution.uniform (Equiv.Perm X)).mass (fun π => ∀ i, π (a i) = b i) := by
  classical
  obtain ⟨xs, ys, hxs, hys, hiff⟩ :=
    exists_injective_tuple_of_partialInjection a b h_pf h_inj
  rw [Distribution.mass_congr _ hiff]
  exact uniform_perm_consistent_mass_ge xs hxs ys hys h_le

/-! ## Gate sums

A union bound over a fixed cap `Fin K` charges only the indices a
per-instance validity bound `· < m` admits, and charges the head index
(`= 0`) differently from the tail.  These are the evaluation lemmas for that
shape, generic in the charged values: an `AddCommMonoid` and nothing else. -/

/-- `2·C(n,2) = n(n−1)`. -/
theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega

/-- The strict upper triangle of `α × α` under an injective rank has `C(|α|,2)`
cells. -/
theorem card_filter_rank_lt {α : Type*} [Fintype α] [DecidableEq α]
    (rank : α → ℕ) (hinj : Function.Injective rank) :
    (Finset.univ.filter (fun p : α × α => rank p.1 < rank p.2)).card
      = (Fintype.card α).choose 2 := by
  classical
  have hswap : (Finset.univ.filter (fun p : α × α => rank p.1 < rank p.2)).card
      = (Finset.univ.filter (fun p : α × α => rank p.2 < rank p.1)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨(p.2, p.1), by simpa using hp, rfl⟩
  have hdiag : (Finset.univ.filter (fun p : α × α => rank p.1 = rank p.2)).card
      = Fintype.card α := by
    rw [show (Finset.univ.filter (fun p : α × α => rank p.1 = rank p.2))
        = Finset.univ.filter (fun p : α × α => p.1 = p.2) from
      Finset.filter_congr (fun p _ => by
        constructor
        · exact fun h => hinj h
        · exact fun h => congrArg rank h)]
    refine (Finset.card_bij (fun (a : α) _ => (a, a)) ?_ ?_ ?_).symm
    · intro a _
      simp
    · intro a _ b _ h
      exact congrArg Prod.fst h
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨p.1, Finset.mem_univ _, Prod.ext rfl hp⟩
  have htotal : (Finset.univ.filter (fun p : α × α => rank p.1 < rank p.2)).card
      + (Finset.univ.filter (fun p : α × α => rank p.2 < rank p.1)).card
      + (Finset.univ.filter (fun p : α × α => rank p.1 = rank p.2)).card
      = Fintype.card α * Fintype.card α := by
    rw [← Fintype.card_prod, ← Finset.card_univ]
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (by
        intro p hp1 hp2
        have h1 := (Finset.mem_filter.mp hp1).2
        have h2 := (Finset.mem_filter.mp hp2).2
        omega)),
      ← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (by
        intro p hp1 hp2
        have h2 := (Finset.mem_filter.mp hp2).2
        rcases Finset.mem_union.mp hp1 with h | h <;>
          · have h1 := (Finset.mem_filter.mp h).2
            omega))]
    have hcover : ((Finset.univ.filter (fun p : α × α => rank p.1 < rank p.2) ∪
        Finset.univ.filter (fun p : α × α => rank p.2 < rank p.1)) ∪
        Finset.univ.filter (fun p : α × α => rank p.1 = rank p.2)) = Finset.univ := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      omega
    rw [hcover]
  have h2 := two_mul_choose_two (Fintype.card α)
  have h3 : Fintype.card α * (Fintype.card α - 1)
      = Fintype.card α * Fintype.card α - Fintype.card α := Nat.mul_pred _ _
  omega

/-- A filter by independent component predicates on a product counts as the
product of the component counts. -/
theorem card_filter_prod {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter (fun x : α × β => P x.1 ∧ Q x.2)).card
      = (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
  rw [show Finset.univ.filter (fun x : α × β => P x.1 ∧ Q x.2)
      = (Finset.univ.filter P) ×ˢ (Finset.univ.filter Q) from ?_,
    Finset.card_product]
  ext x
  simp [Finset.mem_product]

/-- The strict upper triangle of `Fin n × Fin n` has `C(n,2)` cells. -/
theorem card_filter_fin_lt (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card
      = n.choose 2 := by
  rw [Finset.filter_congr (fun p _ => Fin.lt_def (a := p.1) (b := p.2)),
    card_filter_rank_lt (fun x : Fin n => x.val) (fun _ _ h => Fin.ext h),
    Fintype.card_fin]

/-- Only the head index of `Fin n` has `val = 0`: count `1`. -/
theorem card_filter_fin_val_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    (Finset.univ.filter (fun j : Fin n => j.val = 0)).card = 1 := by
  rw [show Finset.univ.filter (fun j : Fin n => j.val = 0) = {⟨0, hn⟩} from ?_,
    Finset.card_singleton]
  ext j
  simp [Fin.ext_iff]

/-- Count of the gated tail indices: `#{j : Fin K ∣ j ≠ 0 ∧ j < m} = m − 1`. -/
theorem card_filter_fin_pos_lt {K m : ℕ} (hmK : m ≤ K) :
    (Finset.univ.filter (fun j : Fin K => j.val ≠ 0 ∧ j.val < m)).card
      = m - 1 := by
  rw [show Finset.univ.filter (fun j : Fin K => j.val ≠ 0 ∧ j.val < m)
      = (Finset.Ico 1 m).attachFin (fun k hk =>
          lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hmK) from ?_,
    Finset.card_attachFin, Nat.card_Ico]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
    Finset.mem_Ico]
  omega

/-- **Gated head/tail sum**: `Σ_{j < m} (head/tail value) = X + (m−1)·Y`. -/
theorem sum_fin_gate {K m : ℕ} {M : Type*} [AddCommMonoid M]
    (hm : 1 ≤ m) (hmK : m ≤ K) (X Y : M) :
    ∑ j : Fin K, (if j.val < m then (if j.val = 0 then X else Y) else 0)
      = X + (m - 1) • Y := by
  classical
  have hsplit : ∀ j : Fin K,
      (if j.val < m then (if j.val = 0 then X else Y) else 0)
        = (if j.val = 0 ∧ j.val < m then X else 0)
          + (if j.val ≠ 0 ∧ j.val < m then Y else 0) := by
    intro j
    by_cases h0 : j.val = 0 <;> by_cases hlt : j.val < m <;> simp [h0, hlt]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    card_filter_fin_pos_lt hmK]
  congr 2
  rw [show Finset.univ.filter (fun j : Fin K => j.val = 0 ∧ j.val < m)
      = {(⟨0, lt_of_lt_of_le hm hmK⟩ : Fin K)} from ?_, Finset.card_singleton,
    one_smul]
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Fin.ext_iff]
  omega

/-- **Gated product head/tail sum** — the cross-instance pair family. -/
theorem sum_fin_gate_prod {K m₁ m₂ : ℕ} {M : Type*} [AddCommMonoid M]
    (h₁ : 1 ≤ m₁) (hK₁ : m₁ ≤ K) (h₂ : 1 ≤ m₂) (hK₂ : m₂ ≤ K) (P Q R S : M) :
    ∑ p : Fin K × Fin K, (if p.1.val < m₁ ∧ p.2.val < m₂ then
        (if p.1.val = 0 then (if p.2.val = 0 then P else Q)
         else (if p.2.val = 0 then R else S)) else 0)
      = (P + (m₂ - 1) • Q) + (m₁ - 1) • (R + (m₂ - 1) • S) := by
  classical
  rw [Fintype.sum_prod_type]
  have hinner : ∀ i : Fin K,
      (∑ j : Fin K, if i.val < m₁ ∧ j.val < m₂ then
          (if i.val = 0 then (if j.val = 0 then P else Q)
           else (if j.val = 0 then R else S)) else 0)
        = if i.val < m₁ then
            (if i.val = 0 then P + (m₂ - 1) • Q else R + (m₂ - 1) • S) else 0 := by
    intro i
    by_cases hi : i.val < m₁
    · by_cases hi0 : i.val = 0
      · rw [if_pos hi, if_pos hi0, ← sum_fin_gate h₂ hK₂ P Q]
        exact Finset.sum_congr rfl (fun j _ => by
          simp [hi0, show 0 < m₁ from h₁])
      · rw [if_pos hi, if_neg hi0, ← sum_fin_gate h₂ hK₂ R S]
        exact Finset.sum_congr rfl (fun j _ => by simp [hi, hi0])
    · rw [if_neg hi]
      exact Finset.sum_eq_zero (fun j _ => by simp [hi])
  rw [Finset.sum_congr rfl (fun i _ => hinner i), ← sum_fin_gate h₁ hK₁
    (P + (m₂ - 1) • Q) (R + (m₂ - 1) • S)]

/-- **Gated sorted head/tail sum** — the same-instance pair family:
`Σ_{i<j, j<m} (head/tail-of-i value) = (m−1)·X + C(m−1,2)·Y`. -/
theorem sum_fin_gate_sorted {K m : ℕ} {M : Type*} [AddCommMonoid M]
    (hmK : m ≤ K) (X Y : M) :
    ∑ p : Fin K × Fin K,
        (if p.1.val < p.2.val ∧ p.2.val < m then
          (if p.1.val = 0 then X else Y) else 0)
      = (m - 1) • X + (m - 1).choose 2 • Y := by
  classical
  have hsplit : ∀ p : Fin K × Fin K,
      (if p.1.val < p.2.val ∧ p.2.val < m then
          (if p.1.val = 0 then X else Y) else 0)
        = (if p.1.val = 0 ∧ (p.2.val ≠ 0 ∧ p.2.val < m) then X else 0)
          + (if p.1.val ≠ 0 ∧ p.1.val < p.2.val ∧ p.2.val < m then Y else 0) := by
    intro p
    split_ifs <;> first | omega | simp
  rw [Finset.sum_congr rfl (fun p _ => hsplit p), Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const]
  congr 2
  · -- head fiber: `p.1 = 0`, `0 < p.2 < m` — count `m − 1`
    rw [card_filter_prod (fun i : Fin K => i.val = 0)
      (fun j : Fin K => j.val ≠ 0 ∧ j.val < m), card_filter_fin_pos_lt hmK]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · rw [card_filter_fin_val_eq_zero (lt_of_lt_of_le hm hmK), one_mul]
  · -- tail–tail fiber: `1 ≤ p.1 < p.2 < m` — count `C(m−1, 2)`
    rw [show Finset.univ.filter (fun p : Fin K × Fin K =>
          p.1.val ≠ 0 ∧ p.1.val < p.2.val ∧ p.2.val < m)
        = Finset.map ⟨fun p : Fin (m - 1) × Fin (m - 1) =>
            ((⟨p.1.val + 1, by omega⟩ : Fin K), (⟨p.2.val + 1, by omega⟩ : Fin K)),
            by
              intro p p' h
              simp only [Prod.ext_iff, Fin.ext_iff] at h ⊢
              omega⟩
          (Finset.univ.filter (fun p : Fin (m - 1) × Fin (m - 1) => p.1 < p.2))
        from ?_, Finset.card_map, card_filter_fin_lt]
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, Prod.ext_iff, Fin.ext_iff, Fin.lt_def]
    constructor
    · rintro ⟨h0, hij, hm'⟩
      exact ⟨(⟨p.1.val - 1, by omega⟩, ⟨p.2.val - 1, by omega⟩),
        by dsimp only; omega, by dsimp only; omega⟩
    · rintro ⟨p', hp', h1, h2⟩
      omega

/-! ## Cubic query-bound arithmetic

The estimates a fiber-ratio bound needs under the paper-side condition
`q³ ≤ N²`: they say the largest queried index is small enough that every
denominator `N − k` stays within a constant factor of `N`. -/

/-- `3·∑_{k<q} k² ≤ q³`. -/
theorem three_sum_sq_le_cube (q : ℕ) :
    3 * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
  induction q with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add]
      have h_cube_expand :
          ((m : ℝ) + 1) ^ 3 = (m : ℝ) ^ 3 + 3 * (m : ℝ) ^ 2 + 3 * (m : ℝ) + 1 := by
        ring
      push_cast at h_cube_expand ⊢
      nlinarith [sq_nonneg (m : ℝ)]

/-- The cubic condition `q³ ≤ N²` implies `q ≤ N`. -/
theorem q_le_of_cube_le_sq {size q : ℕ} (h_cube : q ^ 3 ≤ size ^ 2) :
    q ≤ size := by
  by_cases hq0 : q = 0
  · omega
  · have hq_one : 1 ≤ q := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq0)
    have hq2_real : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
      have hq_real : (1 : ℝ) ≤ q := by
        exact_mod_cast hq_one
      nlinarith
    have h_cube_real : (q : ℝ) ^ 3 ≤ (size : ℝ) ^ 2 := by
      exact_mod_cast h_cube
    have hq2_le : (q : ℝ) ^ 2 ≤ (size : ℝ) ^ 2 := le_trans hq2_real h_cube_real
    have hq_nonneg : (0 : ℝ) ≤ q := by positivity
    have hsize_nonneg : (0 : ℝ) ≤ size := by positivity
    exact_mod_cast (sq_le_sq₀ hq_nonneg hsize_nonneg).mp hq2_le

/-- Under the cubic condition, the largest queried index is small enough for
the denominator estimates: `2(q−1) ≤ N`. -/
theorem two_mul_pred_le_of_cube_sq {size q : ℕ}
    (h_pos : 0 < size) (h_cube : q ^ 3 ≤ size ^ 2) :
    2 * (q - 1) ≤ size := by
  by_contra hbad
  have hbad_nat : size + 2 < 2 * q := by
    omega
  have hbad_real : (size : ℝ) + 2 < 2 * q := by
    exact_mod_cast hbad_nat
  have h_cube_lt : ((size : ℝ) + 2) ^ 3 < (2 * q) ^ 3 :=
    pow_lt_pow_left₀ hbad_real (by positivity) (by decide : (3 : ℕ) ≠ 0)
  have h_cube_gt : (((size : ℝ) + 2) ^ 3) / 8 < (q : ℝ) ^ 3 := by
    nlinarith [h_cube_lt]
  have h_poly : (size : ℝ) ^ 2 < (((size : ℝ) + 2) ^ 3) / 8 := by
    nlinarith [show (0 : ℝ) < size by exact_mod_cast h_pos]
  have h_cube_real : (q : ℝ) ^ 3 ≤ (size : ℝ) ^ 2 := by
    exact_mod_cast h_cube
  linarith

/-- `25k² < 4(k+1)³`. -/
theorem twentyfive_sq_lt_four_cube (k : ℕ) :
    (25 : ℝ) * k ^ 2 < 4 * ((k + 1 : ℕ) : ℝ) ^ 3 := by
  by_cases hk : k < 4
  · interval_cases k <;> norm_num
  · have hk4 : (4 : ℝ) ≤ k := by
      exact_mod_cast Nat.le_of_not_lt hk
    have h_cast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
      exact_mod_cast (show (k + 1 : ℕ) = k + 1 by rfl)
    rw [h_cast]
    nlinarith [hk4]

/-- The cubic condition at `k+1` bounds `k` linearly: `5k ≤ 2N`. -/
theorem five_mul_le_two_of_cube {size k : ℕ} (h : (k + 1) ^ 3 ≤ size ^ 2) :
    5 * k ≤ 2 * size := by
  by_contra hbad
  have hbad_nat : 2 * size + 1 ≤ 5 * k := Nat.succ_le_of_lt (lt_of_not_ge hbad)
  have hbad_real : (2 : ℝ) * size + 1 ≤ 5 * k := by
    exact_mod_cast hbad_nat
  have h1 : (4 : ℝ) * size ^ 2 < (25 : ℝ) * k ^ 2 := by
    nlinarith
  have h2 : (25 : ℝ) * k ^ 2 < 4 * ((k + 1 : ℕ) : ℝ) ^ 3 :=
    twentyfive_sq_lt_four_cube k
  have h3 : (4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 3 ≤ (4 : ℝ) * size ^ 2 := by
    gcongr
    exact_mod_cast h
  linarith

/-- `5k ≤ 2N` keeps the gap `N − k` within a `√3` factor of `N`. -/
theorem gap_sq_bound_of_five_mul {size k : ℕ} (h : 5 * k ≤ 2 * size) :
    (size : ℝ) ^ 2 ≤ 3 * ((size : ℝ) - k) ^ 2 := by
  have h_real : (5 : ℝ) * k ≤ 2 * size := by
    exact_mod_cast h
  nlinarith [h_real, show (0 : ℝ) ≤ k by positivity, show (0 : ℝ) ≤ size by positivity]

/-! ## The sum-of-permutations fiber ratio -/

/-- **The normalized fiber lower bound.**  Under the cubic query condition
`q³ ≤ N²`, the sum-of-permutations fiber ratio dominates
`(1 − q³/N²)·N^{−q}`:

  `(1 − q³/N²)·(1/N^q) ≤ ((N−q)!²·∏_{k<q}(N − 2k)) / (N!)²`.

This is the counting core a good-transcript ratio hypothesis is discharged
by; the `(1 − ·)` factor is the ratio defect the H-technique charges.

*Provenance, flagged*: the quarry attributes this to "Jha–Nandi Proposition
8.1" as a bare author name — no bibliography entry, year, or page, and no such
paper on disk.  Recorded, not verified; outside the source hierarchy. -/
theorem sop_ratio_counting_bound {size q : ℕ} (h_pos : 0 < size)
    (h_cube : q ^ 3 ≤ size ^ 2) :
    (1 - (q : NNReal) ^ 3 / ((size : NNReal)) ^ 2) * (1 / (size : NNReal) ^ q) ≤
      (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : NNReal)
        / ((size.factorial : NNReal) ^ 2) := by
  have hq_le : q ≤ size := q_le_of_cube_le_sq h_cube
  have hstep : 2 * (q - 1) ≤ size := two_mul_pred_le_of_cube_sq h_pos h_cube
  have h_nonneg : ∀ k < q, 0 ≤ ((k : ℝ) / ((size : ℝ) - k)) ^ 2 := by
    intro k _
    positivity
  have h_le_one : ∀ k < q, ((k : ℝ) / ((size : ℝ) - k)) ^ 2 ≤ 1 := by
    intro k hk
    have hk_le_pred : k ≤ q - 1 := Nat.le_pred_of_lt hk
    have h2k : 2 * k ≤ size := le_trans (Nat.mul_le_mul_left _ hk_le_pred) hstep
    have hk_size : k < size := lt_of_lt_of_le hk hq_le
    have hk_real : (k : ℝ) < size := by
      exact_mod_cast hk_size
    have hsk_pos : (0 : ℝ) < (size : ℝ) - k := by
      linarith
    have h2k_real : (2 : ℝ) * k ≤ size := by
      exact_mod_cast h2k
    have h_div_le : (k : ℝ) / ((size : ℝ) - k) ≤ 1 := by
      rw [div_le_one hsk_pos]
      nlinarith
    have h_div_nonneg : 0 ≤ (k : ℝ) / ((size : ℝ) - k) := by positivity
    nlinarith
  have h_chain := chain_product_lower_bound
    (fun k => ((k : ℝ) / ((size : ℝ) - k)) ^ 2) h_nonneg h_le_one
  have hNq1 : (size : ℝ) ^ 2 ≤ 3 * (((size : ℝ) - q + 1) ^ 2) := by
    cases q with
    | zero =>
        simp
        nlinarith [show (0 : ℝ) ≤ size by positivity]
    | succ m =>
        have hfive : 5 * m ≤ 2 * size := five_mul_le_two_of_cube (size := size) (k := m) h_cube
        have hgap : (size : ℝ) ^ 2 ≤ 3 * ((size : ℝ) - m) ^ 2 :=
          gap_sq_bound_of_five_mul (size := size) (k := m) hfive
        have hs : ((size : ℝ) - Nat.succ m + 1) = (size : ℝ) - m := by
          have hm : ((Nat.succ m : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
          rw [hm]
          ring
        rw [hs]
        exact hgap
  have hterm :
      ∀ k ∈ Finset.range q,
        ((k : ℝ) / ((size : ℝ) - k)) ^ 2 ≤ (3 : ℝ) * (k : ℝ) ^ 2 / (size : ℝ) ^ 2 := by
    intro k hk
    have hk_lt : k < q := Finset.mem_range.mp hk
    have hkq_real : (k : ℝ) + 1 ≤ q := by
      exact_mod_cast Nat.succ_le_of_lt hk_lt
    have hq_real : (q : ℝ) ≤ size := by
      exact_mod_cast hq_le
    have hk_den_real : ((size : ℝ) - q + 1) ≤ (size : ℝ) - k := by
      nlinarith
    have hgap_pos : (0 : ℝ) < (size : ℝ) - q + 1 := by
      nlinarith
    have hk_size : k < size := lt_of_lt_of_le hk_lt hq_le
    have hk_real : (k : ℝ) < size := by
      exact_mod_cast hk_size
    have hsk_pos : (0 : ℝ) < (size : ℝ) - k := by
      linarith
    have hgap_nonneg : 0 ≤ (size : ℝ) - q + 1 := by linarith
    have hsk_nonneg : 0 ≤ (size : ℝ) - k := by linarith
    have h_sq : (((size : ℝ) - q + 1) ^ 2) ≤ ((size : ℝ) - k) ^ 2 :=
      (sq_le_sq₀ hgap_nonneg hsk_nonneg).2 hk_den_real
    have hgap_sq_pos : (0 : ℝ) < (((size : ℝ) - q + 1) ^ 2) := by
      nlinarith
    have h_inv_sq : (1 : ℝ) / (((size : ℝ) - k) ^ 2) ≤ 1 / (((size : ℝ) - q + 1) ^ 2) :=
      one_div_le_one_div_of_le hgap_sq_pos h_sq
    have hsize_sq_pos : (0 : ℝ) < (size : ℝ) ^ 2 := by
      have hsize_pos_real : (0 : ℝ) < size := by
        exact_mod_cast h_pos
      nlinarith
    have h_bound : 1 / (((size : ℝ) - q + 1) ^ 2) ≤ 3 / (size : ℝ) ^ 2 := by
      have h_div : (size : ℝ) ^ 2 / (((size : ℝ) - q + 1) ^ 2) ≤ 3 := by
        rw [div_le_iff₀ hgap_sq_pos]
        nlinarith [hNq1]
      rw [le_div_iff₀ hsize_sq_pos]
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h_div
    have h_inv : (1 : ℝ) / (((size : ℝ) - k) ^ 2) ≤ 3 / (size : ℝ) ^ 2 :=
      le_trans h_inv_sq h_bound
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
    have h_eq :
        ((k : ℝ) / ((size : ℝ) - k)) ^ 2
          = (k : ℝ) ^ 2 * ((1 : ℝ) / (((size : ℝ) - k) ^ 2)) := by
      have hsk_ne : (size : ℝ) - k ≠ 0 := by linarith
      field_simp [hsk_ne]
    rw [h_eq]
    have hmul := mul_le_mul_of_nonneg_left h_inv hk_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have h_sum_bound :
      ∑ k ∈ Finset.range q, ((k : ℝ) / ((size : ℝ) - k)) ^ 2 ≤ (q : ℝ) ^ 3 / (size : ℝ) ^ 2 := by
    have hscaled :
        (3 * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2) * (1 / (size : ℝ) ^ 2)
          ≤ (q : ℝ) ^ 3 * (1 / (size : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (three_sum_sq_le_cube q) (by positivity)
    calc
      ∑ k ∈ Finset.range q, ((k : ℝ) / ((size : ℝ) - k)) ^ 2
          ≤ ∑ k ∈ Finset.range q, (3 : ℝ) * (k : ℝ) ^ 2 / (size : ℝ) ^ 2 :=
            Finset.sum_le_sum hterm
      _ = (3 / (size : ℝ) ^ 2) * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k _
            ring
      _ = (3 * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2) * (1 / (size : ℝ) ^ 2) := by
            ring
      _ ≤ (q : ℝ) ^ 3 * (1 / (size : ℝ) ^ 2) := hscaled
      _ = (q : ℝ) ^ 3 / (size : ℝ) ^ 2 := by
            simp [div_eq_mul_inv]
  have h_prod :
      (1 : ℝ) - (q : ℝ) ^ 3 / (size : ℝ) ^ 2 ≤
        ∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2) := by
    linarith [h_chain, h_sum_bound]
  have h_ident :
      (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : ℝ)
        / ((size.factorial : ℝ) ^ 2)
      = (1 / (size : ℝ) ^ q) * ∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2) := by
    have h_fact :
        (((size - q).factorial : ℝ) * ∏ k ∈ Finset.range q, ((size : ℝ) - k))
          = (size.factorial : ℝ) := by
      have h_nat : (size - q).factorial * ∏ k ∈ Finset.range q, (size - k) = size.factorial := by
        rw [← Nat.descFactorial_eq_prod_range, Nat.factorial_mul_descFactorial hq_le]
      norm_num [Finset.prod_range_natCast_sub] at h_nat ⊢
      exact_mod_cast h_nat
    have h_prod_pos : (0 : ℝ) < ((size - q).factorial : ℝ) := by positivity
    calc
      (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : ℝ)
          / ((size.factorial : ℝ) ^ 2)
        = ((((size - q).factorial : ℝ) ^ 2) * ∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ))
            / ((size.factorial : ℝ) ^ 2) := by
              norm_num [Nat.cast_mul, Nat.cast_pow]
      _ = ((((size - q).factorial : ℝ) ^ 2) * ∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ))
            / ((((size - q).factorial : ℝ) * ∏ k ∈ Finset.range q, ((size : ℝ) - k)) ^ 2) := by
              rw [h_fact]
      _ = (∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ))
            / (∏ k ∈ Finset.range q, ((size : ℝ) - k)) ^ 2 := by
            field_simp [h_prod_pos.ne']
      _ = (∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ))
            / (∏ k ∈ Finset.range q, (((size : ℝ) - k) ^ 2)) := by
            rw [← Finset.prod_pow]
      _ = ∏ k ∈ Finset.range q, (((size - 2 * k : ℕ) : ℝ) / (((size : ℝ) - k) ^ 2)) := by
            rw [← Finset.prod_div_distrib]
      _ = ∏ k ∈ Finset.range q, ((1 / (size : ℝ)) * (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2)) := by
            refine Finset.prod_congr rfl ?_
            intro k hk
            have hk_lt : k < q := Finset.mem_range.mp hk
            have hk_le_pred : k ≤ q - 1 := Nat.le_pred_of_lt hk_lt
            have h2k : 2 * k ≤ size := le_trans (Nat.mul_le_mul_left _ hk_le_pred) hstep
            have hk_size : k < size := lt_of_lt_of_le hk_lt hq_le
            have hsize_pos_nat : 0 < size := lt_of_le_of_lt (Nat.zero_le _) hk_size
            have hsize_ne : (size : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt hsize_pos_nat)
            have hk_real : (k : ℝ) < size := by
              exact_mod_cast hk_size
            have hsk_ne : (size : ℝ) - k ≠ 0 := by
              linarith
            rw [Nat.cast_sub h2k]
            field_simp [hsize_ne, hsk_ne]
            norm_num
            ring
      _ = (∏ _k ∈ Finset.range q, (1 / (size : ℝ))) *
            ∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2) := by
            rw [Finset.prod_mul_distrib]
      _ = (1 / (size : ℝ) ^ q) * ∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2) := by
            simp [Finset.prod_const]
  have h_real :
      (1 - (q : ℝ) ^ 3 / (size : ℝ) ^ 2) * (1 / (size : ℝ) ^ q) ≤
        (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : ℝ)
          / ((size.factorial : ℝ) ^ 2) := by
    calc
      (1 - (q : ℝ) ^ 3 / (size : ℝ) ^ 2) * (1 / (size : ℝ) ^ q)
          ≤ (∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2))
              * (1 / (size : ℝ) ^ q) := by
              have hNq_nonneg : 0 ≤ (1 / (size : ℝ) ^ q) := by positivity
              gcongr
      _ = (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : ℝ)
            / ((size.factorial : ℝ) ^ 2) := by
            rw [h_ident, mul_comm]
  have h_frac_le_one : (q : NNReal) ^ 3 / ((size : NNReal) ^ 2) ≤ 1 := by
    rw [div_le_one₀ (by positivity : (0 : NNReal) < (size : NNReal) ^ 2)]
    exact_mod_cast h_cube
  have h_prod_eq :
      ∏ k ∈ Finset.range q, (((size : NNReal) - 2 * k : NNReal) : ℝ)
        = ∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ) := by
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hk_lt : k < q := Finset.mem_range.mp hk
    have hk_le_pred : k ≤ q - 1 := Nat.le_pred_of_lt hk_lt
    have h2k : 2 * k ≤ size := le_trans (Nat.mul_le_mul_left _ hk_le_pred) hstep
    have h2k_nn : (2 * k : NNReal) ≤ size := by
      exact_mod_cast h2k
    rw [NNReal.coe_sub h2k_nn]
    norm_num [Nat.cast_sub h2k]
  have h_goal_real :
      (((1 - (q : NNReal) ^ 3 / ((size : NNReal)) ^ 2) * (1 / (size : NNReal) ^ q) : NNReal) : ℝ)
        ≤ (((((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : NNReal)
          / ((size.factorial : NNReal) ^ 2) : NNReal) : ℝ) := by
    simpa [NNReal.coe_mul, NNReal.coe_sub h_frac_le_one, NNReal.coe_div, NNReal.coe_pow,
      Nat.cast_mul, Nat.cast_pow, h_prod_eq] using h_real
  exact_mod_cast h_goal_real

end Counting

end Probability
