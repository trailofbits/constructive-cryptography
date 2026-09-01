/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Lift

/-!
# Conditional probability at the distribution level

`Probability.Distribution` carries the *partial* conditioning operation
`Distribution.cond` (`Part`-valued, undefined exactly on a null conditioning
event) together with `condPMF`/`condPMFOf` for random variables, but none of
the *laws* the sources use.  This module adds them, all stated on
`Distribution A = A →₀ ℝ`:

* **the multiplication rule** `X(P ∧ Q) = X(P | Q)·X(Q)` (`condProb_mul_mass`);
* **Bayes' rule** (`condProb_eq_condProb_mul_mass_div_mass`, and its
  division-free form `condProb_mul_mass_eq_condProb_mul_mass`);
* **the law of total probability** over a finite partition
  (`mass_eq_sum_mass_and`, `mass_eq_sum_condProb_mul_mass`, and the
  complement form `mass_eq_condProb_mul_mass_add_condProb_mul_mass_not`);
* **the chain rule** — the event form (`mass_biForall_lt_eq_prod_condProb`),
  the input/output-interleaved form of an interaction transcript
  (`mass_biForall_lt_eq_prod_condProb_mul_condProb`) and the conditional form
  `p_{Yⁿ|Xⁿ} = ∏_j p_{Y_j | X^j Y^{j-1}}` of MPR07 eq. (1)
  (`condProb_biForall_lt_eq_prod_condProb`);
* **the cross-multiplied (division-free) comparison of two conditional
  probabilities** (`condProb_eq_condProb_iff_mul_eq_mul`) and the normalized
  conditional distribution `condDist` it compares.

## Total conditioning, and why (`Distribution.cond` is `Part`-valued)

`Distribution.cond X P Q : Part ℝ` is undefined exactly on the null
conditioning event.  A `Part`-valued factor cannot appear under a `∏` — the
body of a `Finset.prod` may not depend on the membership proof that would
discharge its domain — which is why `Distribution.mass_biForall_lt_eq_prod`
spells its chain rule with a raw quotient of masses, and pays for it with a
positivity hypothesis on every prefix.  `Distribution.condProb` is that
quotient, named: a *total* operation whose value on a null conditioning event
is `0` (Lean's `x / 0 = 0`), matching mathlib's total
`ProbabilityTheory.cond` (`μ[|s] = (μ s)⁻¹ • μ.restrict s`, junk when
`μ s ∈ {0, ∞}`).  `condProb_eq_cond_get` identifies the two wherever
`Distribution.cond` is defined, so no convention is forked; and because
`X(P ∧ Q) = 0` whenever `X(Q) = 0` on a non-negative distribution, the
multiplication rule and *both* chain rules hold with **no** positivity
hypothesis at all — strictly stronger than the `Part`-shaped statements.

## Division-free comparison

The technique layer compares two conditional distributions — a conditioned
output law against a plain one — and does it *cross-multiplied*, never by
dividing: `X(P ∧ R)·Y(S) = Y(Q ∧ S)·X(R)`.
`condProb_eq_condProb_iff_mul_eq_mul` is that equivalence, and it is the
shape the conditional-equivalence layer is expected to state its definition
in (the two nonvanishing normalizers are exactly its guards).

## Hypothesis discipline

Each statement carries the weakest of signed / `Distribution.NonNeg` /
`Distribution.isProbDist` at which it is true:

* **signed**: the multiplication rule *given* `X(Q) ≠ 0`, Bayes' rule given
  `X(P) ≠ 0`, and the partition form of total probability;
* **`NonNeg`**: the hypothesis-free multiplication rule and the
  hypothesis-free forms of Bayes and of total probability — non-negativity is
  exactly what makes a null conditioning event harmless, since `mass_mono`
  then forces `X(P ∧ Q) = 0` there;
* **`isProbDist`**: the chain rules, whose base case is `X(True) = 1`, and
  everything stated for `ProbDist`-indexed random variables.

## Naming

`condProb` and `condDist` are **COINAGES** in the three-layer naming sense: no
source names them.  They are house-pattern continuations of the existing
`Distribution.cond`/`condPMF`/`condPMFOf` family — `cond` plus what the
operation returns — and mathlib's own total conditioning
(`ProbabilityTheory.cond`) is the grammar being followed.

## Sources

Maurer–Pietrzak–Renner, *Indistinguishability Amplification* (CRYPTO 2007),
eq. (1); Maurer–Pietrzak, *Composition of Random Systems* (TCC 2004) §2.1.
CR18 eq. (3.2) is cited for the event chain rule as historical provenance
only (CR18 is fallback-only under the source hierarchy; the identity itself
is standard).
-/

noncomputable section

open scoped BigOperators

namespace Probability

namespace Distribution

/-! ## Total conditional probability -/

/-- Conditional probability of `P` given `Q`, as a **total** real-valued
operation: `X(P ∧ Q) / X(Q)`, with Lean's `x / 0 = 0` supplying the value on a
null conditioning event.

This is the value of the `Part`-valued `Distribution.cond` wherever that is
defined (`condProb_eq_cond_get`); the total form is the one that can appear
under a `∏` (see the chain rules below), and it mirrors mathlib's total
`ProbabilityTheory.cond`.  COINAGE — see the module docstring. -/
def condProb {A : Type*} (X : Distribution A) (P Q : A → Prop) : ℝ :=
  X.mass (fun a => P a ∧ Q a) / X.mass Q

/-- `Distribution.cond` is defined exactly off the null conditioning event. -/
theorem cond_dom_iff {A : Type*} (X : Distribution A) (P Q : A → Prop) :
    (X.cond P Q).Dom ↔ X.mass Q ≠ 0 := Iff.rfl

/-- The total `condProb` agrees with the partial `Distribution.cond` wherever
the latter is defined. -/
theorem condProb_eq_cond_get {A : Type*} (X : Distribution A) (P Q : A → Prop)
    (h : (X.cond P Q).Dom) :
    X.condProb P Q = (X.cond P Q).get h := rfl

/-- On a null conditioning event the total conditional probability is `0`. -/
@[simp]
theorem condProb_of_mass_eq_zero {A : Type*} (X : Distribution A) (P Q : A → Prop)
    (hQ : X.mass Q = 0) : X.condProb P Q = 0 := by
  simp [condProb, hQ]

/-- Conditional probability depends only on the two events up to logical
equivalence. -/
theorem condProb_congr {A : Type*} (X : Distribution A) {P P' Q Q' : A → Prop}
    (hP : ∀ a, P a ↔ P' a) (hQ : ∀ a, Q a ↔ Q' a) :
    X.condProb P Q = X.condProb P' Q' := by
  unfold condProb
  rw [mass_congr X (fun a => and_congr (hP a) (hQ a)), mass_congr X hQ]

/-- Conditional probability under a non-negative distribution is non-negative.
`NonNeg` layer. -/
theorem condProb_nonneg {A : Type*} {X : Distribution A} (hX : X.NonNeg)
    (P Q : A → Prop) : 0 ≤ X.condProb P Q :=
  div_nonneg (hX.mass_nonneg _) (hX.mass_nonneg _)

/-- Conditional probability under a non-negative distribution is at most one —
including on a null conditioning event, where it is `0`.  `NonNeg` layer. -/
theorem condProb_le_one {A : Type*} {X : Distribution A} (hX : X.NonNeg)
    (P Q : A → Prop) : X.condProb P Q ≤ 1 := by
  rcases eq_or_lt_of_le (hX.mass_nonneg Q) with h | h
  · simp [condProb, ← h]
  · exact (div_le_one h).mpr (mass_mono hX fun a ha => ha.2)

/-- Conditional probability is monotone in the conditioned event.  `NonNeg`
layer. -/
theorem condProb_mono {A : Type*} {X : Distribution A} (hX : X.NonNeg)
    {P P' : A → Prop} (Q : A → Prop) (h : ∀ a, P a → P' a) :
    X.condProb P Q ≤ X.condProb P' Q := by
  unfold condProb
  gcongr
  · exact hX.mass_nonneg Q
  · exact mass_mono hX fun a ha => ⟨h a ha.1, ha.2⟩

/-- Conditioning on the whole space is not conditioning. -/
theorem condProb_true {A : Type*} (X : Distribution A) (P : A → Prop) :
    X.condProb P (fun _ => True) = X.mass P / X.weight := by
  unfold condProb
  congr 1
  · exact mass_congr X fun a => by simp
  · exact mass_true X

/-! ## The multiplication rule and Bayes' rule -/

/-- **Multiplication rule**, signed layer: `X(P | Q)·X(Q) = X(P ∧ Q)` whenever
the conditioning event is not null.  (mathlib: `cond_mul_eq_inter`.) -/
theorem condProb_mul_mass_of_ne_zero {A : Type*} (X : Distribution A) (P Q : A → Prop)
    (hQ : X.mass Q ≠ 0) :
    X.condProb P Q * X.mass Q = X.mass (fun a => P a ∧ Q a) :=
  div_mul_cancel₀ _ hQ

/-- **Multiplication rule**, `NonNeg` layer: `X(P | Q)·X(Q) = X(P ∧ Q)` with
*no* side condition.  On a null conditioning event both sides vanish, because
`X(P ∧ Q) ≤ X(Q) = 0` and `X(P ∧ Q) ≥ 0`.  This hypothesis-freedom is what
propagates into the chain rules below. -/
theorem condProb_mul_mass {A : Type*} {X : Distribution A} (hX : X.NonNeg)
    (P Q : A → Prop) :
    X.condProb P Q * X.mass Q = X.mass (fun a => P a ∧ Q a) := by
  by_cases hQ : X.mass Q = 0
  · have h0 : X.mass (fun a => P a ∧ Q a) = 0 :=
      le_antisymm (hQ ▸ mass_mono hX fun a ha => ha.2) (hX.mass_nonneg _)
    simp [condProb, hQ, h0]
  · exact condProb_mul_mass_of_ne_zero X P Q hQ

/-- **Bayes' rule**, signed layer: `X(P | Q) = X(Q | P)·X(P) / X(Q)`, valid as
soon as the *hypothesis* event `P` is not null.  (mathlib:
`ProbabilityTheory.cond_eq_inv_mul_cond_mul`.) -/
theorem condProb_eq_condProb_mul_mass_div_mass {A : Type*} (X : Distribution A)
    (P Q : A → Prop) (hP : X.mass P ≠ 0) :
    X.condProb P Q = X.condProb Q P * X.mass P / X.mass Q := by
  rw [condProb_mul_mass_of_ne_zero X Q P hP,
    mass_congr X (P := fun a => Q a ∧ P a) (Q := fun a => P a ∧ Q a) (fun _ => and_comm)]
  rfl

/-- **Bayes' rule, division-free**, `NonNeg` layer:
`X(P | Q)·X(Q) = X(Q | P)·X(P)`, with no side condition — both sides are
`X(P ∧ Q)`. -/
theorem condProb_mul_mass_eq_condProb_mul_mass {A : Type*} {X : Distribution A}
    (hX : X.NonNeg) (P Q : A → Prop) :
    X.condProb P Q * X.mass Q = X.condProb Q P * X.mass P := by
  rw [condProb_mul_mass hX, condProb_mul_mass hX]
  exact mass_congr X fun _ => and_comm

/-! ## Division-free comparison of two conditional probabilities -/

/-- **Cross-multiplication**: two conditional probabilities, possibly of two
different distributions, agree iff the division-free identity
`X(P ∧ R)·Y(S) = Y(Q ∧ S)·X(R)` holds — under the two guards that neither
normalizer vanishes.

This is the shape a conditional-equivalence statement is written in: the
conditioned law of one system against the plain law of another, compared
without ever dividing.  (mathlib: `div_eq_div_iff`.) -/
theorem condProb_eq_condProb_iff_mul_eq_mul {A B : Type*}
    (X : Distribution A) (Y : Distribution B) (P R : A → Prop) (Q S : B → Prop)
    (hR : X.mass R ≠ 0) (hS : Y.mass S ≠ 0) :
    X.condProb P R = Y.condProb Q S ↔
      X.mass (fun a => P a ∧ R a) * Y.mass S = Y.mass (fun b => Q b ∧ S b) * X.mass R := by
  unfold condProb
  exact div_eq_div_iff hR hS

/-! ## The conditional distribution -/

/-- The distribution `X` **conditioned on** the event `Q`: restrict to `Q` and
normalize.  A total operation — on a null conditioning event `normalize`
scales by `0⁻¹ = 0` and the result is the zero distribution — whose event
masses are exactly `condProb` (`mass_condDist`).

COINAGE (see the module docstring); it is the composite
`Distribution.restrict` then `Distribution.normalize`, named because the
technique layer compares such objects. -/
def condDist {A : Type*} (X : Distribution A) (Q : A → Prop) : Distribution A :=
  (X.restrict Q).normalize

/-- Unfolding: conditioning is restriction followed by normalization. -/
theorem condDist_eq_normalize_restrict {A : Type*} (X : Distribution A) (Q : A → Prop) :
    X.condDist Q = (X.restrict Q).normalize := rfl

/-- **The bridge**: the event masses of the conditional distribution are the
conditional probabilities.  No hypothesis — on a null conditioning event both
sides are `0`. -/
theorem mass_condDist {A : Type*} (X : Distribution A) (P Q : A → Prop) :
    (X.condDist Q).mass P = X.condProb P Q := by
  rw [condDist, mass_normalize, weight_restrict, mass_restrict, condProb, div_eq_inv_mul]

/-- Conditioning preserves non-negativity. -/
theorem NonNeg.condDist {A : Type*} {X : Distribution A} (hX : X.NonNeg) (Q : A → Prop) :
    (X.condDist Q).NonNeg :=
  nonNeg_normalize (hX.restrict Q)

/-- Conditioning a non-negative distribution on a non-null event gives a
probability distribution. -/
theorem isProbDist_condDist {A : Type*} {X : Distribution A} (hX : X.NonNeg)
    {Q : A → Prop} (hQ : X.mass Q ≠ 0) : (X.condDist Q).isProbDist :=
  isProbDist_normalize (hX.restrict Q) (by rwa [weight_restrict])

/-! ## The law of total probability -/

/-- **Law of total probability, partition form.**  Signed layer: over a finite
pairwise-disjoint family of events covering the sample space, every event mass
splits as the sum of its intersections with the blocks.  The disjointness and
covering conventions are those of
`Distribution.sum_mass_eq_weight_of_pairwise_disjoint_of_cover`. -/
theorem mass_eq_sum_mass_and {A ι : Type*} [Fintype ι] (X : Distribution A) (P : A → Prop)
    (B : ι → A → Prop) (hdisj : ∀ i j, i ≠ j → ∀ a, B i a → B j a → False)
    (hcover : ∀ a, ∃ i, B i a) :
    X.mass P = ∑ i, X.mass (fun a => P a ∧ B i a) := by
  have h := sum_mass_eq_weight_of_pairwise_disjoint_of_cover (X.restrict P) B hdisj hcover
  rw [weight_restrict] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by
    rw [mass_restrict]
    exact mass_congr X fun _ => and_comm

/-- **Law of total probability**, `NonNeg` layer: `X(P) = ∑ᵢ X(P | Bᵢ)·X(Bᵢ)`
over a finite partition, with no positivity hypothesis on the blocks — a null
block contributes `0`. -/
theorem mass_eq_sum_condProb_mul_mass {A ι : Type*} [Fintype ι] {X : Distribution A}
    (hX : X.NonNeg) (P : A → Prop) (B : ι → A → Prop)
    (hdisj : ∀ i j, i ≠ j → ∀ a, B i a → B j a → False) (hcover : ∀ a, ∃ i, B i a) :
    X.mass P = ∑ i, X.condProb P (B i) * X.mass (B i) := by
  rw [mass_eq_sum_mass_and X P B hdisj hcover]
  exact Finset.sum_congr rfl fun i _ => (condProb_mul_mass hX P (B i)).symm

/-- **Law of total probability, two-block form**:
`X(P) = X(P|Q)·X(Q) + X(P|¬Q)·X(¬Q)`.  `NonNeg` layer.  (mathlib:
`ProbabilityTheory.cond_add_cond_compl_eq`.) -/
theorem mass_eq_condProb_mul_mass_add_condProb_mul_mass_not {A : Type*}
    {X : Distribution A} (hX : X.NonNeg) (P Q : A → Prop) :
    X.mass P = X.condProb P Q * X.mass Q
      + X.condProb P (fun a => ¬ Q a) * X.mass (fun a => ¬ Q a) := by
  rw [condProb_mul_mass hX, condProb_mul_mass hX,
    mass_congr X (P := fun a => P a ∧ Q a) (Q := fun a => Q a ∧ P a) (fun _ => and_comm),
    mass_congr X (P := fun a => P a ∧ ¬ Q a) (Q := fun a => ¬ Q a ∧ P a) (fun _ => and_comm),
    ← mass_restrict X Q P, ← mass_restrict X (fun a => ¬ Q a) P,
    mass_add_compl (X.restrict P) Q, weight_restrict]

/-! ## The chain rule -/

/-- **Chain rule, event form**: the mass of a nested conjunction is the product
of the one-step conditional probabilities,

`X(⋀_{k<n} Eₖ) = ∏_{j<n} X(Eⱼ | ⋀_{k<j} Eₖ)`.

`isProbDist` layer — `NonNeg` for the multiplication rule, `weight = 1` for
the empty prefix.  Unlike `Distribution.mass_biForall_lt_eq_prod`, which
spells the factors as raw quotients, this form needs **no** positivity
hypothesis on the prefixes: a null prefix makes both sides `0`.  (CR18
eq. (3.2) is the historical citation.) -/
theorem mass_biForall_lt_eq_prod_condProb {A : Type*} {X : Distribution A}
    (hX : X.isProbDist) (E : ℕ → A → Prop) (n : ℕ) :
    X.mass (fun a => ∀ k, k < n → E k a)
      = ∏ j ∈ Finset.range n, X.condProb (E j) (fun a => ∀ k, k < j → E k a) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_zero, mass_congr X (Q := fun _ => True) (fun a => by simp),
        mass_true]
      exact hX.weight_eq
  | succ n ih =>
      rw [Finset.prod_range_succ, ← ih, mul_comm, condProb_mul_mass hX.nonNeg]
      refine mass_congr X fun a => ⟨fun h => ⟨h n (Nat.lt_succ_self n),
        fun k hk => h k (Nat.lt_succ_of_lt hk)⟩, ?_⟩
      rintro ⟨hn, h⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact h k hk'
      · exact hn

/-- **Chain rule for an interaction transcript** (MauPie04 §2.1): the
probability of an input/output transcript factors into the alternating product
of one-step conditional probabilities,

`Pr[Xⁿ = xⁿ, Yⁿ = yⁿ]
  = ∏_{j<n} Pr[Xⱼ = xⱼ | X^{j-1}Y^{j-1}] · Pr[Yⱼ = yⱼ | X^jY^{j-1}]`.

The `Y`-factors are the system's own conditional distributions
`p^S_{Yⱼ|X^jY^{j-1}}`; the `X`-factors belong to whatever chooses the inputs.
No positivity hypothesis (see `condProb_mul_mass`).  The prefix convention is
that of `Distribution.mass_biForall_lt_eq_prod`; the current input is written
*first* in the `Y`-factor's conditioning event, so that the two applications
of the multiplication rule compose without reassociating. -/
theorem mass_biForall_lt_eq_prod_condProb_mul_condProb {Ω 𝒳 𝒴 : Type*}
    (p : ProbDist Ω) (Xv : ℕ → RV (Ω := Ω) (A := 𝒳)) (Yv : ℕ → RV (Ω := Ω) (A := 𝒴))
    (x : ℕ → 𝒳) (y : ℕ → 𝒴) (n : ℕ) :
    p.val.mass (fun ω => ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)
      = ∏ j ∈ Finset.range n,
          p.val.condProb (fun ω => Xv j ω = x j)
              (fun ω => ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k)
            * p.val.condProb (fun ω => Yv j ω = y j)
              (fun ω => Xv j ω = x j ∧ ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_zero,
        mass_congr p.val (Q := fun _ => True) (fun ω => by simp), mass_true]
      exact p.property.weight_eq
  | succ n ih =>
      have hstep : p.val.mass (fun ω => ∀ k, k < n + 1 → Xv k ω = x k ∧ Yv k ω = y k)
          = p.val.condProb (fun ω => Yv n ω = y n)
                (fun ω => Xv n ω = x n ∧ ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)
              * (p.val.condProb (fun ω => Xv n ω = x n)
                  (fun ω => ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)
                * p.val.mass (fun ω => ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)) := by
        rw [condProb_mul_mass p.property.nonNeg, condProb_mul_mass p.property.nonNeg]
        refine mass_congr p.val fun ω => ⟨fun h => ⟨(h n (Nat.lt_succ_self n)).2,
          (h n (Nat.lt_succ_self n)).1, fun k hk => h k (Nat.lt_succ_of_lt hk)⟩, ?_⟩
        rintro ⟨hy, hx, h⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
        · exact h k hk'
        · exact ⟨hx, hy⟩
      rw [Finset.prod_range_succ, ← ih, hstep]
      ring

/-- **The defining identity of a random system** (MPR07 eq. (1)):

`p_{Yⁿ|Xⁿ}(yⁿ, xⁿ) = ∏_{j<n} p_{Yⱼ|X^jY^{j-1}}(yⱼ, x^j y^{j-1})`.

The identity is *not* unconditional in a general random experiment: dividing
the transcript chain rule
(`mass_biForall_lt_eq_prod_condProb_mul_condProb`) by the input chain rule
cancels the input factors only under `hfree`, which says the `j`-th input is
chosen without feedback from the past outputs.  That is exactly the regime in
which `p^S_{Yⁱ|Xⁱ}` is a property of the system alone.  `hx` says the
conditioning input transcript is possible; without it the left-hand side is
the junk value `0`. -/
theorem condProb_biForall_lt_eq_prod_condProb {Ω 𝒳 𝒴 : Type*}
    (p : ProbDist Ω) (Xv : ℕ → RV (Ω := Ω) (A := 𝒳)) (Yv : ℕ → RV (Ω := Ω) (A := 𝒴))
    (x : ℕ → 𝒳) (y : ℕ → 𝒴) (n : ℕ)
    (hfree : ∀ j ∈ Finset.range n,
      p.val.condProb (fun ω => Xv j ω = x j)
          (fun ω => ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k)
        = p.val.condProb (fun ω => Xv j ω = x j) (fun ω => ∀ k, k < j → Xv k ω = x k))
    (hx : p.val.mass (fun ω => ∀ k, k < n → Xv k ω = x k) ≠ 0) :
    p.val.condProb (fun ω => ∀ k, k < n → Yv k ω = y k)
        (fun ω => ∀ k, k < n → Xv k ω = x k)
      = ∏ j ∈ Finset.range n,
          p.val.condProb (fun ω => Yv j ω = y j)
            (fun ω => Xv j ω = x j ∧ ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k) := by
  have hjoint :
      p.val.mass (fun ω => (∀ k, k < n → Yv k ω = y k) ∧ ∀ k, k < n → Xv k ω = x k)
        = p.val.mass (fun ω => ∀ k, k < n → Xv k ω = x k)
          * ∏ j ∈ Finset.range n,
              p.val.condProb (fun ω => Yv j ω = y j)
                (fun ω => Xv j ω = x j ∧ ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k) := by
    rw [mass_congr p.val (Q := fun ω => ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)
        (fun ω => ⟨fun h k hk => ⟨h.2 k hk, h.1 k hk⟩,
          fun h => ⟨fun k hk => (h k hk).2, fun k hk => (h k hk).1⟩⟩),
      mass_biForall_lt_eq_prod_condProb_mul_condProb p Xv Yv x y n,
      Finset.prod_mul_distrib, Finset.prod_congr rfl hfree,
      ← mass_biForall_lt_eq_prod_condProb p.property (fun k ω => Xv k ω = x k) n]
  rw [condProb, hjoint, mul_comm, mul_div_assoc, div_self hx, mul_one]

end Distribution

end Probability
