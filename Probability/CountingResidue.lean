/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Counting
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The counting kernel, part two

**STAGING MODULE — merge target `Probability/Counting.lean`.**  Everything here
is in namespace `Probability.Counting`, the namespace of that module, and
belongs in it: this is the residue the T0 counting transplant left behind (the
LEDGER's T4.10 closure names it as "two-sided birthday, sorted-pair sums,
function fibers, block-major encoding, re-randomisation fibers").  It sits in
its own file only because `Probability/Counting.lean` was under another leg's
file ownership when this landed.  The merge is a verbatim append followed by
deleting this file: no declaration is renamed, no proof changes, and no
consumer sees a difference, since both files export into the same namespace.

Five groups, matching the reference development's own section order:

* **the birthday bound, two-sided** — Boneh-Shoup Theorem B.1 in both
  directions.  `Probability/Counting.lean` carries only the one-sided
  `birthday_bound` (`1 − (N)_q/N^q ≤ q(q−1)/2N`), which is the direction that
  proves security; the *lower* bound is what an attack argument needs.  Plus
  the `k = 2` case of Corollary B.2 (`inv_card_le_sum_sq`);
* **sorted-pair sum identities** — exact closed forms for sums over the sorted
  pairs `p.1 < p.2` of a linearly ordered `Fintype`: the pen-and-paper
  `(Σx)² = Σx² + 2Σ_{r<s}xᵣxₛ` and `Σ_{r<s}(xᵣ+xₛ) = (q−1)Σx`;
* **function fibers** — how many functions agree with a prescribed map on a
  finite input set, in the plain, multipoint, curried and injective-on-a-set
  forms.  The permutation-fiber counterparts are already in
  `Probability/Counting.lean`;
* **block-major pair encoding** — `(i,j) ↦ j·q + i`, the index bookkeeping for
  two-dimensional birthday union bounds;
* **re-randomisation fibers** — the multi-point additive shift and the generic
  balanced-fiber count: a free, `φ`-equivariant action of a finite additive
  group on a finite set makes every `φ`-fiber the same size.

## Provenance

The arithmetic is standard; the one named source is Boneh-Shoup,
*A Graduate Course in Applied Cryptography*, Appendix B, cited per statement.
Every declaration is transported from the reference repository's
`RandomSystems/Counting.lean` (READ-ONLY), restated on this tree's namespace.
None of them mentions a distribution, a distance or a system, so no carrier or
metric re-basing arises — the transport is a namespace change.

`inv_card_le_sum_sq` is the one exception to "verbatim": the reference proves
it from a local Cauchy-Schwarz-against-the-constant lemma, which is mathlib's
`sq_sum_le_card_mul_sum_sq` (`Mathlib/Algebra/Order/Chebyshev.lean`) under
another name.  mathlib's is consumed directly here.
-/

namespace Probability

namespace Counting

/-! ## The birthday bound, two-sided (Boneh–Shoup Appendix B)

Boneh and Shoup, *A Graduate Course in Applied Cryptography*, Theorem B.1
(book p. 1101).  With `N` the alphabet size,
`q` the number of independent uniform draws and `C` the event that two of them
collide,

* `Pr[C] ≥ 1 - e^{-q(q-1)/2N} ≥ min{q(q-1)/4N, 0.63}`, and
* `Pr[C] ≤ 1 - e^{-q(q-1)/N}` when `q < N/2`.

Boneh and Shoup derive both from `1 - x ≤ e^{-x} ≤ 1 - x/2` on `[0,1]`: the left
half is mathlib's `Real.add_one_le_exp`, the right half is
`exp_neg_le_one_sub_half` below.  They are stated here on the falling-factorial
ratio `(N)_q / N^q = Pr[¬C]`; no consumer in this tree transports them onto a
collision probability yet.

A collision *upper* bound proves security; the *lower* bound is what an attack
argument needs, and is the direction the tree previously had nowhere. -/

/-- `e^{-x} ≤ 1 - x/2` for `x ∈ [0,1]` — the right half of Boneh–Shoup's
`1 - x ≤ e^{-x} ≤ 1 - x/2` (Theorem B.1's proof, book p. 1101).  Proved without any analysis: `e^{-x} ≤ 1/(1+x)` is `1 + x ≤ e^x`
divided through, and `1/(1+x) ≤ 1 - x/2` is `x(1-x) ≥ 0`.

**UPSTREAM-CANDIDATE.** -/
theorem exp_neg_le_one_sub_half {x : ℝ} (h_nonneg : 0 ≤ x) (h_le_one : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  have hE : Real.exp (-x) * (1 + x) ≤ 1 := by
    calc Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp x]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  refine le_trans ((le_div_iff₀ hx1).mpr hE) ?_
  rw [div_le_iff₀ hx1]
  nlinarith

/-- `min (x/2) 0.63 ≤ 1 - e^{-x}` for `x ≥ 0` — the second inequality of
Boneh–Shoup Theorem B.1(i).  Below `x = 1` it is `exp_neg_le_one_sub_half`;
above it, `1 - e^{-x} ≥ 1 - e^{-1} > 0.632`.

**UPSTREAM-CANDIDATE.** -/
theorem min_le_one_sub_exp_neg {x : ℝ} (h_nonneg : 0 ≤ x) :
    min (x / 2) 0.63 ≤ 1 - Real.exp (-x) := by
  rcases le_or_gt x 1 with h1 | h1
  · exact le_trans (min_le_left _ _) (by linarith [exp_neg_le_one_sub_half h_nonneg h1])
  · refine le_trans (min_le_right _ _) ?_
    have hmono : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have he : Real.exp (-1 : ℝ) ≤ 0.37 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      nlinarith [Real.exp_one_gt_d9]
    linarith

/-- **Boneh–Shoup Theorem B.1(i), the no-collision half**:
`(N)_q / N^q ≤ e^{-q(q-1)/(2N)}`.  Termwise `1 - k/N ≤ e^{-k/N}`. -/
theorem prod_sub_div_pow_le_exp {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q
      ≤ Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / (2 * N))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  rw [prod_sub_div_pow_eq N q h_pos]
  have hnn : ∀ k ∈ Finset.range q, (0 : ℝ) ≤ 1 - (k : ℝ) / N := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by
      exact_mod_cast (lt_of_lt_of_le (Finset.mem_range.mp hk) h_le).le
    rw [sub_nonneg, div_le_one hNpos]; exact hkN
  have hstep : ∀ k ∈ Finset.range q, (1 : ℝ) - (k : ℝ) / N ≤ Real.exp (-((k : ℝ) / N)) := by
    intro k _; linarith [Real.add_one_le_exp (-((k : ℝ) / N))]
  calc ∏ k ∈ Finset.range q, (1 - (k : ℝ) / N)
      ≤ ∏ k ∈ Finset.range q, Real.exp (-((k : ℝ) / N)) := Finset.prod_le_prod hnn hstep
    _ = Real.exp (∑ k ∈ Finset.range q, -((k : ℝ) / N)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / (2 * N))) := by
        rw [Finset.sum_neg_distrib, sum_div_range N q hNpos]

/-- **Boneh–Shoup Theorem B.1(ii), the no-collision half**:
`e^{-q(q-1)/N} ≤ (N)_q / N^q` when `2q ≤ N` (the paper's `q < N/2`).  Termwise
`e^{-2k/N} ≤ 1 - k/N`, which is `exp_neg_le_one_sub_half` at `x = 2k/N`; that is
where the `q < N/2` side condition comes from, since `x` must not exceed `1`. -/
theorem exp_le_prod_sub_div_pow {N q : ℕ} (h : 2 * q ≤ N) (h_pos : 0 < N) :
    Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / N))
      ≤ (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  rw [prod_sub_div_pow_eq N q h_pos]
  have hstep : ∀ k ∈ Finset.range q,
      Real.exp (-(2 * ((k : ℝ) / N))) ≤ 1 - (k : ℝ) / N := by
    intro k hk
    have hkq : k < q := Finset.mem_range.mp hk
    have hk2 : 2 * (k : ℝ) ≤ N := by
      have : 2 * k ≤ N := by omega
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ 2 * ((k : ℝ) / N) := by positivity
    have h1 : 2 * ((k : ℝ) / N) ≤ 1 := by
      rw [mul_div_assoc'] at *; exact (div_le_one hNpos).mpr hk2
    calc Real.exp (-(2 * ((k : ℝ) / N))) ≤ 1 - (2 * ((k : ℝ) / N)) / 2 :=
          exp_neg_le_one_sub_half h0 h1
      _ = 1 - (k : ℝ) / N := by ring
  calc Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / N))
      = Real.exp (∑ k ∈ Finset.range q, -(2 * ((k : ℝ) / N))) := by
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum, sum_div_range N q hNpos]
        ring_nf
    _ = ∏ k ∈ Finset.range q, Real.exp (-(2 * ((k : ℝ) / N))) := Real.exp_sum _ _
    _ ≤ ∏ k ∈ Finset.range q, (1 - (k : ℝ) / N) :=
        Finset.prod_le_prod (fun k _ => (Real.exp_pos _).le) hstep

/-- **Boneh–Shoup Theorem B.1(i)**, the collision lower bound:
`1 - e^{-q(q-1)/(2N)} ≤ 1 - (N)_q/N^q`. -/
theorem one_sub_exp_le_one_sub_prod_sub_div_pow {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    1 - Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / (2 * N)))
      ≤ 1 - (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q :=
  sub_le_sub_left (prod_sub_div_pow_le_exp h_le h_pos) 1

/-- **Boneh–Shoup Theorem B.1(i)**, in the explicit form an attack argument
uses: the collision probability of `q` uniform draws from `N` values is at least
`min {q(q-1)/(4N), 0.63}`. -/
theorem min_le_one_sub_prod_sub_div_pow {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    min ((q : ℝ) * ((q : ℝ) - 1) / (4 * N)) 0.63
      ≤ 1 - (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  have hq : (0 : ℝ) ≤ (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · norm_num
    · have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
      have : (0 : ℝ) ≤ (q : ℝ) * ((q : ℝ) - 1) := by nlinarith
      positivity
  refine le_trans (le_of_eq ?_) (le_trans (min_le_one_sub_exp_neg hq)
    (one_sub_exp_le_one_sub_prod_sub_div_pow h_le h_pos))
  congr 1
  field_simp
  ring

/-- **Boneh–Shoup Theorem B.1(ii)**, the collision upper bound:
`1 - (N)_q/N^q ≤ 1 - e^{-q(q-1)/N}` when `2q ≤ N`. -/
theorem one_sub_prod_sub_div_pow_le_one_sub_exp {N q : ℕ} (h : 2 * q ≤ N) (h_pos : 0 < N) :
    1 - (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q
      ≤ 1 - Real.exp (-((q : ℝ) * ((q : ℝ) - 1) / N)) :=
  sub_le_sub_left (exp_le_prod_sub_div_pow h h_pos) 1

/-- **Uniformity minimises the collision probability, at two draws**
(the `k = 2` case of Boneh–Shoup Corollary B.2, book p. 1103): for any probability vector `p` on a finite set, the chance that two
i.i.d. draws agree is `∑ pᵢ²`, and that is at least `1/|s|`, the uniform value.

This is Cauchy–Schwarz.  The general-`k` Corollary B.2 needs Maclaurin's
inequality on elementary symmetric polynomials, which mathlib does not carry. -/
theorem inv_card_le_sum_sq {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (h_sum : ∑ i ∈ s, p i = 1) :
    1 / (s.card : ℝ) ≤ ∑ i ∈ s, (p i) ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp at h_sum
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hne
  have h := _root_.sq_sum_le_card_mul_sum_sq (s := s) (f := p)
  rw [h_sum, one_pow] at h
  rw [div_le_iff₀ hcard]
  linarith

/-- **Sum-of-collision-pairs bound**: if the fiber counts `n i` sum to at most
`N`, then `Σ_i n_i(n_i − 1) ≤ N(N − 1)`.  Each fiber count is at most the total,
so each summand `n_i(n_i − 1)` is at most `n_i(N − 1)` and the sum telescopes. -/
theorem sum_mul_pred_le {ι : Type*} [Fintype ι] (n : ι → ℕ) (N : ℕ)
    (h : ∑ i, n i ≤ N) :
    ∑ i, n i * (n i - 1) ≤ N * (N - 1) :=
  calc ∑ i, n i * (n i - 1)
      ≤ ∑ i, n i * (N - 1) :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.sub_le_sub_right
          (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)) h) 1)
    _ = (∑ i, n i) * (N - 1) := (Finset.sum_mul _ _ _).symm
    _ ≤ N * (N - 1) := Nat.mul_le_mul_right _ h

/-! ## Sorted-pair sum identities

The §3.4.3-style aggregation toolkit: exact identities relating a sum over
the *sorted* pairs `p.1 < p.2` of a linearly ordered `Fintype` to closed
forms in the underlying one-index sums.  These are the pen-and-paper
"`(Σx)² = Σx² + 2Σ_{r<s} xᵣxₛ`" and "`Σ_{r<s}(xᵣ+xₛ) = (q−1)Σx`" steps,
stated once at full generality; consumers instantiate. -/

/-- Swap re-indexing of the lower triangle onto the upper triangle. -/
theorem sum_sorted_swap {ι M : Type*} [Fintype ι] [LinearOrder ι]
    [AddCommMonoid M] (f : ι → ι → M) :
    ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.2 < p.1), f p.1 p.2
      = ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 < p.2), f p.2 p.1 := by
  classical
  apply Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl

/-- Trichotomy split of a full product-square sum: diagonal, upper triangle,
lower triangle. -/
theorem sum_prod_trichotomy {ι M : Type*} [Fintype ι] [LinearOrder ι]
    [AddCommMonoid M] (g : ι × ι → M) :
    ∑ p : ι × ι, g p
      = (∑ i, g (i, i))
        + (∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 < p.2), g p
           + ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.2 < p.1), g p) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : ι × ι => p.1 = p.2) g]
  congr 1
  · apply Finset.sum_nbij' (fun p => p.1) (fun i => (i, i))
    · intro p hp; exact Finset.mem_univ _
    · intro i _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Prod.ext_iff, hp]
    · intro i _; rfl
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨a, b⟩ := p
      cases hp
      rfl
  · rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun p : ι × ι => ¬ p.1 = p.2))
      (fun p : ι × ι => p.1 < p.2) g, Finset.filter_filter, Finset.filter_filter]
    congr 1
    · exact Finset.sum_congr (Finset.filter_congr (fun p _ => by
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨ne_of_lt h, h⟩)) (fun _ _ => rfl)
    · exact Finset.sum_congr (Finset.filter_congr (fun p _ => by
        constructor
        · intro h
          rcases lt_trichotomy p.1 p.2 with h1 | h1 | h1
          · exact absurd h1 h.2
          · exact absurd h1 h.1
          · exact h1
        · exact fun h => ⟨ne_of_gt h, not_lt_of_gt h⟩)) (fun _ _ => rfl)

/-- **Square-of-sum split** over sorted pairs:
`(Σx)² = Σᵢ xᵢ² + 2·Σ_{r<s} xᵣxₛ`. -/
theorem sq_sum_eq_sum_sq_add_two_mul_sorted {ι : Type*} [Fintype ι]
    [LinearOrder ι] (x : ι → ℕ) :
    (∑ i, x i) * (∑ i, x i)
      = (∑ i, x i * x i)
        + 2 * ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 < p.2),
            x p.1 * x p.2 := by
  classical
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  rw [sum_prod_trichotomy (fun p : ι × ι => x p.1 * x p.2)]
  rw [sum_sorted_swap (fun a b => x a * x b)]
  have : ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 < p.2), x p.2 * x p.1
      = ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 < p.2), x p.1 * x p.2 :=
    Finset.sum_congr rfl (fun p _ => mul_comm _ _)
  rw [this]
  ring

/-- `k(k−1) + k = k²` (ℕ, monus-safe; the pointwise atom relating the
`k(k−1)` collision counts to the square-of-sum identity). -/
theorem mul_pred_add (k : ℕ) : k * (k - 1) + k = k * k := by
  cases k with
  | zero => rfl
  | succ k' =>
    simp only [Nat.succ_sub_one]
    ring

/-- **Linear sorted-pair sum**: `Σ_{r<s}(xᵣ + xₛ) = (card ι − 1)·Σx`. -/
theorem sum_sorted_add {ι : Type*} [Fintype ι] [LinearOrder ι] (x : ι → ℕ) :
    ∑ p ∈ Finset.univ.filter (fun p : ι × ι => p.1 < p.2), (x p.1 + x p.2)
      = (Fintype.card ι - 1) * ∑ i, x i := by
  classical
  have hfull : ∑ p : ι × ι, x p.1 = Fintype.card ι * ∑ i, x i := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Finset.mul_sum]
  have htri := sum_prod_trichotomy (fun p : ι × ι => x p.1)
  rw [hfull, sum_sorted_swap (fun a b => x a)] at htri
  rw [Finset.sum_add_distrib, Nat.sub_one_mul, htri, Nat.add_sub_cancel_left]

/-! ## Function fibers -/

/-- The number of functions agreeing with a prescribed map on a finite input
subset.

This is the shared finite-set function-fiber count used by transcript
normalization arguments. -/
theorem card_function_fiber_finset {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (S : Finset X) (g : S → Y) :
    (Finset.univ.filter (fun f : X → Y => ∀ x : S, f x.1 = g x)).card =
      Fintype.card Y ^ (Fintype.card X - S.card) := by
  classical
  rw [show Fintype.card Y ^ (Fintype.card X - S.card) = Fintype.card (↥Sᶜ → Y) from by
    rw [Fintype.card_fun, Fintype.card_coe, Finset.card_compl]]
  refine Finset.card_bij (fun f _ => fun ⟨x, hx⟩ => f x) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
    ext x
    by_cases hx : x ∈ S
    · rw [hf₁ ⟨x, hx⟩, hf₂ ⟨x, hx⟩]
    · exact congr_fun h ⟨x, Finset.mem_compl.mpr hx⟩
  · intro h _
    refine Exists.intro
      (fun x => if hx : x ∈ S then g ⟨x, hx⟩ else h ⟨x, Finset.mem_compl.mpr hx⟩) ?_
    refine Exists.intro ?_ ?_
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ _
      · intro x
        simp [x.2]
    · ext x
      simp [Finset.mem_compl.mp x.2]

/-- The number of functions matching a prescribed output tuple on an injective
input tuple is `|Y|^(|X|-q)`. -/
theorem card_function_fiber_multipoint {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {q : ℕ} (xs : Fin q → X) (ys : Fin q → Y)
    (hxs : Function.Injective xs) :
    ((Finset.univ : Finset (X → Y)).filter
        (fun f : X → Y => (fun i : Fin q => f (xs i)) = ys)).card =
      Fintype.card Y ^ (Fintype.card X - q) := by
  classical
  set S : Finset X := Finset.univ.image xs
  have hS_card : S.card = q := by
    rw [Finset.card_image_of_injective _ hxs, Finset.card_fin]
  let C : Finset X := Finset.univ \ S
  rw [show Fintype.card Y ^ (Fintype.card X - q) = Fintype.card (C → Y) from by
    have hC_card : C.card = Fintype.card X - S.card := by
      exact Finset.card_sdiff_of_subset (by intro x _; exact Finset.mem_univ x)
    rw [Fintype.card_fun, Fintype.card_coe, hC_card, hS_card]]
  refine Finset.card_bij (fun f _ => fun ⟨x, hx⟩ => f x)
    (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
    ext x
    by_cases hx : x ∈ S
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [congr_fun hf₁ i, congr_fun hf₂ i]
    · exact congr_fun h ⟨x, by simp [C, hx]⟩
  · intro g _
    have h_ext : ∀ x ∈ S, ∃! i : Fin q, xs i = x := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl, fun j hj => hxs hj⟩
    refine ⟨fun x =>
        if hx : x ∈ S then ys ((h_ext x hx).choose)
        else g ⟨x, by simp [C, hx]⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext i
      have h_mem : xs i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      show dite (xs i ∈ S) _ _ = ys i
      rw [dif_pos h_mem]
      have hcs := (h_ext (xs i) h_mem).choose_spec
      congr 1
      exact hxs hcs.1
    · ext ⟨x, hx⟩
      show dite (x ∈ S) _ _ = g ⟨x, hx⟩
      rw [dif_neg ((Finset.mem_sdiff.mp hx).2)]

/-- The curried form of `card_function_fiber_multipoint`.  Prescribing a
tuple of outputs at distinct pairs leaves every other coordinate of a
curried finite function free. -/
theorem card_curried_function_fiber_multipoint {U X Y : Type*}
    [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    {q : ℕ} (xs : Fin q → U × X) (ys : Fin q → Y)
    (hxs : Function.Injective xs) :
    ((Finset.univ : Finset (U → X → Y)).filter
        (fun f => (fun i : Fin q => f (xs i).1 (xs i).2) = ys)).card =
      Fintype.card Y ^ (Fintype.card (U × X) - q) := by
  classical
  set S : Finset (U × X) := Finset.univ.image xs
  have hS_card : S.card = q := by
    rw [Finset.card_image_of_injective _ hxs, Finset.card_fin]
  let C : Finset (U × X) := Finset.univ \ S
  rw [show Fintype.card Y ^ (Fintype.card (U × X) - q) = Fintype.card (C → Y) from by
    have hC_card : C.card = Fintype.card (U × X) - S.card := by
      exact Finset.card_sdiff_of_subset (by intro x _; exact Finset.mem_univ x)
    rw [Fintype.card_fun, Fintype.card_coe, hC_card, hS_card]]
  refine Finset.card_bij
    (fun f _ => fun x : C => f x.1.1 x.1.2)
    (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
    funext u x
    by_cases hx : (u, x) ∈ S
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      have hu : (xs i).1 = u := congrArg Prod.fst hi
      have hx' : (xs i).2 = x := congrArg Prod.snd hi
      simpa [hu, hx'] using congr_fun hf₁ i |>.trans (congr_fun hf₂ i).symm
    · exact congr_fun h ⟨(u, x), by simp [C, hx]⟩
  · intro g _
    have h_ext : ∀ x ∈ S, ∃! i : Fin q, xs i = x := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl, fun j hj => hxs hj⟩
    refine ⟨fun u x =>
        if hx : (u, x) ∈ S then ys ((h_ext (u, x) hx).choose)
        else g ⟨(u, x), by simp [C, hx]⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext i
      have h_mem : xs i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      show dite (xs i ∈ S) _ _ = ys i
      rw [dif_pos h_mem]
      have hcs := (h_ext (xs i) h_mem).choose_spec
      congr 1
      exact hxs hcs.1
    · ext ⟨⟨u, x⟩, hx⟩
      show dite ((u, x) ∈ S) _ _ = g ⟨(u, x), hx⟩
      rw [dif_neg ((Finset.mem_sdiff.mp hx).2)]

/-- Balanced-cardinality form of
`card_curried_function_fiber_multipoint`: fixing `q` distinct coordinates
removes exactly the `|Y|^q` choices carried by their output tuple. -/
theorem card_curried_function_fiber_multipoint_mul {U X Y : Type*}
    [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {q : ℕ} (xs : Fin q → U × X) (ys : Fin q → Y)
    (hxs : Function.Injective xs) :
    ((Finset.univ : Finset (U → X → Y)).filter
        (fun f => (fun i : Fin q => f (xs i).1 (xs i).2) = ys)).card *
        Fintype.card (Fin q → Y) =
      Fintype.card (U → X → Y) := by
  classical
  have hq : q ≤ Fintype.card (U × X) := by
    simpa using Fintype.card_le_of_injective xs hxs
  rw [card_curried_function_fiber_multipoint xs ys hxs,
    Fintype.card_fun, Fintype.card_fin,
    show Fintype.card (U → X → Y) = Fintype.card (U × X → Y) from
      Fintype.card_congr (Equiv.curry U X Y).symm,
    Fintype.card_fun, ← pow_add, Nat.sub_add_cancel hq]

/-- The number of functions that are injective on a finite set of inputs.

A function injective on `S` is equivalently an embedding `S ↪ Y` plus arbitrary
values on `Sᶜ`. -/
theorem card_function_injOn_finset {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (S : Finset X)
    [DecidablePred (fun f : X → Y => Set.InjOn f (fun x => x ∈ S))] :
    ((Finset.univ : Finset (X → Y)).filter (fun f => Set.InjOn f (fun x => x ∈ S))).card =
      (Fintype.card Y).descFactorial S.card * Fintype.card Y ^ (Fintype.card X - S.card) := by
  classical
  have e : {f : X → Y // Set.InjOn f (fun x => x ∈ S)} ≃ (S ↪ Y) × (↥Sᶜ → Y) :=
    { toFun := fun f =>
        (⟨fun x : S => f.1 x.1, by
          intro x y hxy
          exact Subtype.ext (f.2 x.2 y.2 hxy)⟩,
         fun x : ↥Sᶜ => f.1 x.1)
      invFun := fun p =>
        ⟨fun x => if hx : x ∈ S then p.1 ⟨x, hx⟩ else p.2 ⟨x, Finset.mem_compl.mpr hx⟩, by
          intro x hx y hy hxy
          change x ∈ S at hx
          change y ∈ S at hy
          dsimp at hxy
          rw [dif_pos hx, dif_pos hy] at hxy
          exact congr_arg Subtype.val (p.1.injective hxy)⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ S <;> simp [hx]
      right_inv := by
        intro p
        rcases p with ⟨emb, comp⟩
        ext x
        · simp
        · simp [Finset.mem_compl.mp x.2] }
  rw [← Fintype.card_subtype (p := fun f : X → Y => Set.InjOn f (fun x => x ∈ S))]
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_coe]
  rw [Fintype.card_fun, Fintype.card_coe, Finset.card_compl]

/-! ## Block-major pair encoding

Coordinates `(i, j)` with `i < q`, `j < L` encoded block-major into `Fin (q·L)` as `j·q + i` —
the index bookkeeping for two-dimensional birthday union bounds. -/

theorem siteCode_lt {q L i j : ℕ} (hi : i < q) (hj : j < L) : j * q + i < q * L :=
  calc j * q + i < j * q + q := Nat.add_lt_add_left hi _
    _ = (j + 1) * q := (Nat.succ_mul j q).symm
    _ ≤ L * q := Nat.mul_le_mul_right q hj
    _ = q * L := Nat.mul_comm L q

theorem siteCode_strictMono {q i₁ j₁ i₂ j₂ : ℕ} (hi₁ : i₁ < q)
    (h : j₁ < j₂ ∨ j₁ = j₂ ∧ i₁ < i₂) : j₁ * q + i₁ < j₂ * q + i₂ := by
  rcases h with h | ⟨rfl, h⟩
  · calc j₁ * q + i₁ < j₁ * q + q := Nat.add_lt_add_left hi₁ _
      _ = (j₁ + 1) * q := (Nat.succ_mul j₁ q).symm
      _ ≤ j₂ * q := Nat.mul_le_mul_right q h
      _ ≤ j₂ * q + i₂ := Nat.le_add_right _ _
  · exact Nat.add_lt_add_left h _

theorem siteCode_fst {q i j : ℕ} (hi : i < q) : (j * q + i) % q = i := by
  rw [Nat.mul_comm j q, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

theorem siteCode_snd {q i j : ℕ} (hi : i < q) (hq : 0 < q) : (j * q + i) / q = j := by
  rw [Nat.mul_comm j q, Nat.mul_add_div hq, Nat.div_eq_of_lt hi, Nat.add_zero]

/-! ## Re-randomisation fibers -/

/-- **Multi-point additive shift** — the generic re-randomisation gadget: translate `f : X → X` by
`δ s` at each site `u s`.  Away from the sites nothing changes; at an injectively-placed site exactly
`δ s` is added; shifts over the same site family compose additively and vanish at `δ = 0` — precisely
the free-action package `card_filter_shift` consumes. -/
def multiShift {ι D A : Type*} [Fintype ι] [DecidableEq D] [AddCommMonoid A]
    (u : ι → D) (δ : ι → A) (f : D → A) : D → A :=
  fun x => f x + ∑ s, if u s = x then δ s else 0

theorem multiShift_apply_of_ne {ι D A : Type*} [Fintype ι] [DecidableEq D]
    [AddCommMonoid A] {u : ι → D} (δ : ι → A) (f : D → A) {x : D}
    (h : ∀ s, u s ≠ x) :
    multiShift u δ f x = f x := by
  rw [multiShift, Finset.sum_eq_zero fun s _ => if_neg (h s), add_zero]

theorem multiShift_apply_site {ι D A : Type*} [Fintype ι] [DecidableEq D]
    [AddCommMonoid A] {u : ι → D} (δ : ι → A) (f : D → A)
    (hu : Function.Injective u) (s₀ : ι) :
    multiShift u δ f (u s₀) = f (u s₀) + δ s₀ := by
  rw [multiShift]
  congr 1
  rw [Finset.sum_eq_single s₀ (fun s _ hs => if_neg fun hc => hs (hu hc))
    (fun hns => absurd (Finset.mem_univ s₀) hns), if_pos rfl]

theorem multiShift_zero {ι D A : Type*} [Fintype ι] [DecidableEq D]
    [AddCommMonoid A] (u : ι → D) (f : D → A) :
    multiShift u 0 f = f := by
  funext x; simp [multiShift]

/-- Shifts over the same site family compose additively. -/
theorem multiShift_multiShift {ι D A : Type*} [Fintype ι] [DecidableEq D]
    [AddCommMonoid A] (u : ι → D) (δ δ' : ι → A) (f : D → A) :
    multiShift u δ' (multiShift u δ f) = multiShift u (δ + δ') f := by
  funext x
  show (f x + ∑ s, if u s = x then δ s else 0) + (∑ s, if u s = x then δ' s else 0)
    = f x + ∑ s, if u s = x then (δ + δ') s else 0
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by by_cases h : u s = x <;> simp [h]

/-- **Generic balanced-fiber count.** A free, `φ`-equivariant action of a finite additive group `A`
on a finite set `G` makes every `φ`-fiber the same size: `|fiber| · |A| = |G|`.  This is the shared
counting principle behind re-randomisation arguments (e.g. the CBC-MAC's joint-MAC count and its
birthday per-pair count). -/
theorem card_filter_shift {F A : Type*} [Fintype F] [DecidableEq F]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    (G : Finset F) (φ : F → A) (act : A → F → F)
    (hmem : ∀ δ, ∀ f ∈ G, act δ f ∈ G)
    (hφ : ∀ δ, ∀ f ∈ G, φ (act δ f) = φ f + δ)
    (hcomp : ∀ δ δ', ∀ f ∈ G, act δ' (act δ f) = act (δ + δ') f)
    (hzero : ∀ f ∈ G, act 0 f = f) (c : A) :
    (G.filter (fun f => φ f = c)).card * Fintype.card A = G.card := by
  classical
  have hbij : ∀ c' : A,
      (G.filter (fun f => φ f = c')).card = (G.filter (fun f => φ f = c)).card := by
    intro c'
    refine Finset.card_bij' (fun f _ => act (c - c') f) (fun g _ => act (c' - c) g) ?_ ?_ ?_ ?_
    · intro f hf
      rw [Finset.mem_filter] at hf ⊢
      exact ⟨hmem _ _ hf.1, by rw [hφ _ _ hf.1, hf.2]; abel⟩
    · intro g hg
      rw [Finset.mem_filter] at hg ⊢
      exact ⟨hmem _ _ hg.1, by rw [hφ _ _ hg.1, hg.2]; abel⟩
    · intro f hf
      rw [Finset.mem_filter] at hf
      show act (c' - c) (act (c - c') f) = f
      rw [hcomp _ _ _ hf.1, show c - c' + (c' - c) = (0 : A) by abel, hzero _ hf.1]
    · intro g hg
      rw [Finset.mem_filter] at hg
      show act (c - c') (act (c' - c) g) = g
      rw [hcomp _ _ _ hg.1, show c' - c + (c - c') = (0 : A) by abel, hzero _ hg.1]
  calc (G.filter (fun f => φ f = c)).card * Fintype.card A
      = ∑ c' : A, (G.filter (fun f => φ f = c')).card := by
        rw [Finset.sum_congr rfl fun c' _ => hbij c', Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_comm]
    _ = G.card := (Finset.card_eq_sum_card_fiberwise fun f _ => Finset.mem_univ (φ f)).symm

/-- **Predicate form of `card_filter_shift`** over `univ`: a free, `φ`-equivariant `A`-action on the
`Good` subtype balances the `φ`-fibers within it.  Phrased on the predicate `Good` so consumers avoid
`Finset`-membership plumbing. -/
theorem card_filter_shift_univ {F A : Type*} [Fintype F] [DecidableEq F]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    (Good : F → Prop) [DecidablePred Good] (φ : F → A) (act : A → F → F)
    (hmem : ∀ δ f, Good f → Good (act δ f))
    (hφ : ∀ δ f, Good f → φ (act δ f) = φ f + δ)
    (hcomp : ∀ δ δ' f, Good f → act δ' (act δ f) = act (δ + δ') f)
    (hzero : ∀ f, Good f → act 0 f = f) (c : A) :
    (Finset.univ.filter (fun f => φ f = c ∧ Good f)).card * Fintype.card A
      = (Finset.univ.filter Good).card := by
  have hgood : ∀ f, f ∈ Finset.univ.filter Good ↔ Good f := by
    intro f; simp
  have key := card_filter_shift (Finset.univ.filter Good) φ act
    (fun δ f hf => (hgood _).mpr (hmem δ f ((hgood f).mp hf)))
    (fun δ f hf => hφ δ f ((hgood f).mp hf))
    (fun δ δ' f hf => hcomp δ δ' f ((hgood f).mp hf))
    (fun f hf => hzero f ((hgood f).mp hf)) c
  rw [Finset.filter_filter] at key
  rw [← key]
  congr 2
  ext f
  simp [and_comm]

end Counting

end Probability
