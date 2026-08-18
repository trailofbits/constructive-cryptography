/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Distribution
import Probability.Expectation
import Mathlib.Algebra.Order.Sub.Basic

/-!
# Statistical Distance

Lean 4 formalization of Definition 3, Lemma 2, Lemma 3 from
Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `statDist X Y` — statistical distance `δ(X, Y)`
* `avgSuccessProb X Y g` — success probability of the binary hypothesis test
  `g` at telling `X` from `Y` under equal prior ½.  Deciding *which of two
  distributions* produced a sample; the different task of guessing an unknown
  *value* from correlated side information is `Distribution.condGuessProb`
  (`RandomSystems/Entropy.lean`)

## Main Results

* `statDist_self` — `δ(X, X) = 0` (proved)
* `statDist_symm_of_eq_weight` — `δ(X, Y) = δ(Y, X)` when `|X| = |Y|`
* `statDist_eq_weight_sub_sum_min` — min form `δ(X, Y) = |X| - ∑ a, min (X a) (Y a)`
* `statDist_eq_half_sum_abs_of_weight_eq` — half-`L1` form for equal weight
* `sSup_avgSuccessProb_eq_half_add_half_statDist` — optimal-test identity
  (mathlib decision theory: `1 - bayesRisk` at 0-1 loss and uniform prior)
* `statDist_triangle` — triangle inequality
* `statDist_partition` — Lemma 2: partition of statistical distance
* `statDist_fTransform_le` — Lemma 3: data processing inequality
* `statDist_eq_mass_on_zero_support` — when Y=0 on S and X≤Y on Sᶜ, statDist = ∑_S X

## Design note (ℝ carrier)

Over the `NNReal` carrier the paper's `max(0, X(a) − Y(a))` was expressed by
truncating subtraction.  Over the signed carrier the truncation is spelled out:
every summand is `max (X a - Y a) 0`, which denotes exactly what the truncated
`X a - Y a` denoted before.  Inequalities that silently used the structural
non-negativity of `NNReal` now take explicit `Distribution.NonNeg` hypotheses.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Probability

/-! ### Supremum helpers for advantage definitions -/

/-- If an index type is empty, then the image of `Set.univ` under any function
out of it is empty. -/
theorem image_univ_eq_empty_of_not_nonempty {ι : Type*} {α : Type*}
    (f : ι → α) (hι : ¬ Nonempty ι) :
    f '' Set.univ = (∅ : Set α) := by
  ext x
  constructor
  · rintro ⟨i, _hi, rfl⟩
    exact (hι ⟨i⟩).elim
  · intro hx
    simp at hx

/-- A pointwise upper bound on an `sSup` image over `Set.univ` also covers the
empty-index case when the upper bound is nonnegative. -/
theorem sSup_image_univ_le_of_forall {ι : Type*} (f : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ i, f i ≤ a) :
    sSup (f '' Set.univ) ≤ a := by
  by_cases hι : Nonempty ι
  · refine csSup_le ?nonempty ?upper
    · rcases hι with ⟨i⟩
      exact ⟨f i, ⟨i, Set.mem_univ i, rfl⟩⟩
    · rintro b ⟨i, _hi, rfl⟩
      exact h i
  · rw [image_univ_eq_empty_of_not_nonempty f hι, Real.sSup_empty]
    exact ha

/-- The `sSup` of a nonnegative image over `Set.univ` is nonnegative, with
`sSup ∅ = 0` covering the empty-index case. -/
theorem sSup_image_univ_nonneg_of_forall {ι : Type*} (f : ι → ℝ)
    (hbdd : BddAbove (f '' Set.univ)) (h : ∀ i, 0 ≤ f i) :
    0 ≤ sSup (f '' Set.univ) := by
  by_cases hι : Nonempty ι
  · rcases hι with ⟨i⟩
    exact le_trans (h i) (le_csSup hbdd ⟨i, Set.mem_univ i, rfl⟩)
  · rw [image_univ_eq_empty_of_not_nonempty f hι, Real.sSup_empty]

/-- A supremum indexed by `ι` is bounded by a supremum indexed by `κ` when every
left value appears on the right. The nonnegativity premise handles the case
where the left index type is empty. -/
theorem sSup_image_univ_le_sSup_image_univ_of_forall_exists
    {ι : Type*} {κ : Type*} (f : ι → ℝ) (g : κ → ℝ)
    (hg_bdd : BddAbove (g '' Set.univ))
    (hg_nonneg : ∀ k, 0 ≤ g k)
    (hmap : ∀ i, ∃ k, f i = g k) :
    sSup (f '' Set.univ) ≤ sSup (g '' Set.univ) := by
  by_cases hι : Nonempty ι
  · refine csSup_le ?nonempty ?upper
    · rcases hι with ⟨i⟩
      exact ⟨f i, ⟨i, Set.mem_univ i, rfl⟩⟩
    · rintro b ⟨i, _hi, rfl⟩
      rcases hmap i with ⟨k, hk⟩
      rw [hk]
      exact le_csSup hg_bdd ⟨k, Set.mem_univ k, rfl⟩
  · rw [image_univ_eq_empty_of_not_nonempty f hι, Real.sSup_empty]
    exact sSup_image_univ_nonneg_of_forall g hg_bdd hg_nonneg

/-- A finite `NNReal` supremum coerced to `ℝ` is bounded by any nonnegative
real upper bound on its elements. -/
theorem coe_finset_sup_le {ι : Type*} (s : Finset ι) (f : ι → NNReal) {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ i ∈ s, (f i : ℝ) ≤ a) :
    ((s.sup f : NNReal) : ℝ) ≤ a := by
  let aNN : NNReal := ⟨a, ha⟩
  have hNN : s.sup f ≤ aNN := by
    apply Finset.sup_le
    intro i hi
    exact NNReal.coe_le_coe.mp (h i hi)
  exact NNReal.coe_le_coe.mp hNN

/-! ### H-coefficient kernel — three-layer architecture (PHI-SPEC R10)
Layer 1 (here): partition bounds (`statDist_sum_of_disjoint_support` family).
Layer 2 (here): the good/bad ratio kernel (`hTechnique_*`).
Layer 3 (system level, `RandomSystems/`): the transcript factorization
`Pr[τ] = η(e,τ)·σ(S,τ)` and its environment-uniform corollary — the only
part of the method that mentions systems.  Do not re-prove layers 1-2. -/

/-- Statistical distance between two distributions.

Paper Definition 3:
  `δ(X, Y) := ∑_{a} max(0, X(a) - Y(a))`

Over the `NNReal` carrier the truncating subtraction spelled the `max`; over
the signed carrier it is written out.  The value is the same one-sided excess
the paper defines.

**No `Fintype` is needed, and requiring one was a spurious restriction.**
`Distribution A = A →₀ ℝ` already carries finite support, and a summand `max (X a - Y a) 0` can
only be nonzero where `X a ≠ Y a`, i.e. on `(X - Y).support`.  So the sum below has the
same value as the sum over `Finset.univ` *unconditionally* — `statDist_eq_sum_univ` —
while also being defined on infinite carriers such as a transcript space.  Indexing by
`(X - Y).support` rather than `X.support ∪ Y.support` additionally avoids a `DecidableEq`
hypothesis, which would have been the same mistake one level down.

This is the difference from `δ` (`RandomSystem.lean`), which sums over `μ.support` alone
and therefore agrees with this only when `ν ≥ 0`; the two are one metric at two
generalities, both one-sided. -/
noncomputable def statDist {A : Type*} (X Y : Distribution A) : ℝ :=
  ∑ a ∈ (X - Y).support, max (X a - Y a) 0

/-- On a `Fintype` carrier, `statDist` is the sum over everything — the old definition,
kept as the unfolding lemma for proofs that reason over `Finset.univ`. -/
theorem statDist_eq_sum_univ {A : Type*} [Fintype A] (X Y : Distribution A) :
    statDist X Y = ∑ a : A, max (X a - Y a) 0 := by
  classical
  rw [statDist]
  refine Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_
  rw [Finsupp.notMem_support_iff] at ha
  have h : X a - Y a = 0 := by simpa using ha
  rw [h, max_self]

/-- `statDist` is the same sum over **any** finite set containing the support
of the difference: the summand `max (X a - Y a) 0` vanishes wherever
`X a = Y a`.  This is the `Fintype`-free companion of `statDist_eq_sum_univ`,
and the working form on carriers that are genuinely infinite — transcript
spaces `List (X × Option Y)`, system laws `Distribution (DDS X Y)`.  Taking
`s = Finset.univ` recovers `statDist_eq_sum_univ`. -/
theorem statDist_eq_sum_of_support_subset {A : Type*} (X Y : Distribution A)
    {s : Finset A} (hs : (X - Y).support ⊆ s) :
    statDist X Y = ∑ a ∈ s, max (X a - Y a) 0 := by
  rw [statDist]
  refine Finset.sum_subset hs fun a _ ha => ?_
  rw [Finsupp.notMem_support_iff] at ha
  have h : X a - Y a = 0 := by simpa using ha
  rw [h, max_self]

/-- Each summand of `statDist` is nonnegative, so the whole sum is. -/
theorem statDist_nonneg {A : Type*} (X Y : Distribution A) :
    0 ≤ statDist X Y :=
  Finset.sum_nonneg fun a _ => le_max_right _ _

/-- `δ(X, X) = 0`. -/
theorem statDist_self {A : Type*} (X : Distribution A) :
    statDist X X = 0 := by
  simp [statDist]

/-- `δ(X, Y) = δ(Y, X)` when `|X| = |Y|`.

Paper: For distributions of equal weight,
  δ(X,Y) = (1/2) ∑_a |X(a) - Y(a)| = δ(Y,X).

No `Fintype`: the two sums run over `X.support ∪ Y.support`, which already
covers both differences. -/
theorem statDist_symm_of_eq_weight {A : Type*}
    (X Y : Distribution A) (h : X.weight = Y.weight) :
    statDist X Y = statDist Y X := by
  haveI : DecidableEq A := Classical.decEq A
  have hXY : (X - Y).support ⊆ X.support ∪ Y.support := Finsupp.support_sub
  have hYX : (Y - X).support ⊆ X.support ∪ Y.support := by
    intro a ha
    rcases Finset.mem_union.mp (Finsupp.support_sub ha) with h' | h'
    · exact Finset.mem_union_right _ h'
    · exact Finset.mem_union_left _ h'
  rw [statDist_eq_sum_of_support_subset X Y hXY,
    statDist_eq_sum_of_support_subset Y X hYX]
  have key : ∀ a : A, max (X a - Y a) 0 = max (Y a - X a) 0 + (X a - Y a) := by
    intro a
    rcases le_total (X a) (Y a) with hle | hle
    · rw [max_eq_right (sub_nonpos.mpr hle), max_eq_left (sub_nonneg.mpr hle)]
      ring
    · rw [max_eq_left (sub_nonneg.mpr hle), max_eq_right (sub_nonpos.mpr hle)]
      ring
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_add_distrib,
    Finset.sum_sub_distrib,
    ← Distribution.weight_eq_sum_of_support_subset X Finset.subset_union_left,
    ← Distribution.weight_eq_sum_of_support_subset Y Finset.subset_union_right, h,
    sub_self, add_zero]

/-! ### Alternative forms of statistical distance

LanMau20 Definition 3 (= FOUNDATIONS.md Definition 2.4) presents `δ` in two
forms, `δ(X, Y) = ∑_a max(0, X(a) - Y(a)) = |X| - ∑_a min(X(a), Y(a))`, and
notes the half-`L1` form `δ(X, Y) = ½ ∑_a |X(a) - Y(a)|` for equal weight.
`statDist` is the max form; the other two are derived here. -/

/-- **Min form of statistical distance** (LanMau20 Definition 3, second form):
`δ(X, Y) = |X| - ∑_a min(X(a), Y(a))`.

The identity is the pointwise lattice identity `max (x - y) 0 = x - min x y`
summed over the carrier, so it holds for *arbitrary* signed distributions:
neither `Distribution.NonNeg` nor equal weight is needed.  The asymmetry the paper
notes for unequal weight is visible here — the right-hand side carries `|X|`,
not `|Y|`. -/
theorem statDist_eq_weight_sub_sum_min {A : Type*} [Fintype A] (X Y : Distribution A) :
    statDist X Y = X.weight - ∑ a : A, min (X a) (Y a) := by
  simp only [statDist_eq_sum_univ]
  have key : ∀ a : A, max (X a - Y a) 0 = X a - min (X a) (Y a) := by
    intro a
    rcases le_total (X a) (Y a) with h | h
    · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h, sub_self]
    · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h]
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_sub_distrib,
    ← Distribution.weight_eq_sum]

/-- Weight-one specialization of the min form (MaPiRe07 equation (3), used in
the proof of their Lemma 5): `δ(X, Y) = 1 - ∑_a min(X(a), Y(a))`.

Only the *first* argument needs weight one — the min form charges `|X|`, so
`Y` may be an arbitrary signed distribution. -/
theorem statDist_eq_one_sub_sum_min {A : Type*} [Fintype A]
    (X Y : Distribution A) (hX : X.weight = 1) :
    statDist X Y = 1 - ∑ a : A, min (X a) (Y a) := by
  rw [statDist_eq_weight_sub_sum_min, hX]

/-- **Half-`L1` form of statistical distance** (LanMau20 Definition 3 remark;
PorRen22 Definition 4): for distributions of equal weight,
`δ(X, Y) = ½ ∑_a |X(a) - Y(a)|`.

Equal weight is exactly what is needed: pointwise
`max (x - y) 0 = ((x - y) + |x - y|) / 2`, and summing makes the linear term
contribute `(|X| - |Y|) / 2`, which vanishes precisely under the equal-weight
hypothesis (the library's idiom for symmetry, cf.
`statDist_symm_of_eq_weight`). -/
theorem statDist_eq_half_sum_abs_of_weight_eq {A : Type*} [Fintype A]
    (X Y : Distribution A) (h : X.weight = Y.weight) :
    statDist X Y = (∑ a : A, |X a - Y a|) / 2 := by
  simp only [statDist_eq_sum_univ]
  have key : ∀ a : A, max (X a - Y a) 0 = ((X a - Y a) + |X a - Y a|) / 2 := by
    intro a
    rcases le_total (X a) (Y a) with hle | hle
    · rw [max_eq_right (sub_nonpos.mpr hle), abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    · rw [max_eq_left (sub_nonneg.mpr hle), abs_of_nonneg (sub_nonneg.mpr hle)]
      ring
  rw [Finset.sum_congr rfl (fun a _ => key a)]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Distribution.weight_eq_sum X, ← Distribution.weight_eq_sum Y, h, sub_self, zero_add]

/-- Triangle inequality for statistical distance.

`δ(X, Z) ≤ δ(X, Y) + δ(Y, Z)`.

No `Fintype`: all three sums run over the union of the three difference
supports, and the estimate is the pointwise
`max (a - c) 0 ≤ max (a - b) 0 + max (b - c) 0`. -/
theorem statDist_triangle {A : Type*}
    (X Y Z : Distribution A) :
    statDist X Z ≤ statDist X Y + statDist Y Z := by
  haveI : DecidableEq A := Classical.decEq A
  rw [statDist_eq_sum_of_support_subset X Z
      (Finset.subset_union_left :
        (X - Z).support ⊆ (X - Z).support ∪ ((X - Y).support ∪ (Y - Z).support)),
    statDist_eq_sum_of_support_subset X Y
      (Finset.subset_union_left.trans Finset.subset_union_right),
    statDist_eq_sum_of_support_subset Y Z
      (Finset.subset_union_right.trans Finset.subset_union_right),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  apply max_le
  · calc X a - Z a = (X a - Y a) + (Y a - Z a) := by ring
      _ ≤ max (X a - Y a) 0 + max (Y a - Z a) 0 :=
          add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- **Convexity of `δ` along a mixture**:
`δ(∑ᵢ wᵢ Xᵢ, ∑ᵢ wᵢ Yᵢ) ≤ ∑ᵢ wᵢ δ(Xᵢ, Yᵢ)` for non-negative weights.

This is the estimate a mixture decomposition needs: a law that samples an
index and then runs the indexed pair is no further apart than the average of
the indexed distances.

Non-negativity of the weights is exactly the hypothesis, and it cannot be
dropped.  The pointwise step is `max (∑ᵢ wᵢ dᵢ) 0 ≤ ∑ᵢ wᵢ max dᵢ 0`, which
is the same one-sided fiber estimate as the data processing inequality — a
negative weight flips a cancelling summand into a growing one.  On the
signed carrier that is a real restriction, not bookkeeping.

No `Fintype`: all sums run over the union of the difference supports. -/
theorem statDist_sum_le {A ι : Type*} (t : Finset ι) (w : ι → ℝ)
    (X Y : ι → Distribution A) (hw : ∀ i ∈ t, 0 ≤ w i) :
    statDist (∑ i ∈ t, w i • X i) (∑ i ∈ t, w i • Y i) ≤
      ∑ i ∈ t, w i * statDist (X i) (Y i) := by
  classical
  set s : Finset A := t.biUnion fun i => (X i - Y i).support with hs
  have hcomp : ∀ (Z : ι → Distribution A) (a : A),
      (∑ i ∈ t, w i • Z i) a = ∑ i ∈ t, w i * Z i a := by
    intro Z a
    rw [Finset.sum_apply']
    exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.smul_apply, smul_eq_mul]
  have hzero : ∀ a ∉ s, ∀ i ∈ t, X i a - Y i a = 0 := by
    intro a ha i hi
    by_contra hne
    exact ha (Finset.mem_biUnion.mpr ⟨i, hi,
      Finsupp.mem_support_iff.mpr (by simpa using hne)⟩)
  have hsub : (∑ i ∈ t, w i • X i - ∑ i ∈ t, w i • Y i).support ⊆ s := by
    intro a ha
    by_contra hna
    refine Finsupp.mem_support_iff.mp ha ?_
    rw [Finsupp.sub_apply, hcomp, hcomp, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← mul_sub, hzero a hna i hi, mul_zero]
  rw [statDist_eq_sum_of_support_subset _ _ hsub]
  calc
    ∑ a ∈ s, max ((∑ i ∈ t, w i • X i) a - (∑ i ∈ t, w i • Y i) a) 0
        = ∑ a ∈ s, max (∑ i ∈ t, w i * (X i a - Y i a)) 0 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hcomp, hcomp, ← Finset.sum_sub_distrib]
          exact congrArg (max · 0) (Finset.sum_congr rfl fun i _ => (mul_sub ..).symm)
    _ ≤ ∑ a ∈ s, ∑ i ∈ t, w i * max (X i a - Y i a) 0 := by
          refine Finset.sum_le_sum fun a _ => max_le ?_ ?_
          · exact Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_left (le_max_left _ _) (hw i hi)
          · exact Finset.sum_nonneg fun i hi =>
              mul_nonneg (hw i hi) (le_max_right _ _)
    _ = ∑ i ∈ t, w i * ∑ a ∈ s, max (X i a - Y i a) 0 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum ..).symm
    _ = ∑ i ∈ t, w i * statDist (X i) (Y i) :=
          Finset.sum_congr rfl fun i hi =>
            congrArg (w i * ·)
              (statDist_eq_sum_of_support_subset (X i) (Y i)
                fun a ha => Finset.mem_biUnion.mpr ⟨i, hi, ha⟩).symm

/-- Statistical distance is bounded by total weight (for non-negative laws).

`δ(X, Y) ≤ |X|`.

No `Fintype`: both sides are read on `X.support ∪ Y.support`, which already
covers the difference's support.  The generality is what lets the bound reach
the carriers the random-systems layer uses, where no `Fintype` exists. -/
theorem statDist_le_weight {A : Type*}
    {X Y : Distribution A} (hX : X.NonNeg) (hY : Y.NonNeg) :
    statDist X Y ≤ X.weight := by
  haveI : DecidableEq A := Classical.decEq A
  rw [statDist_eq_sum_of_support_subset X Y Finsupp.support_sub,
    Distribution.weight_eq_sum_of_support_subset X Finset.subset_union_left
      (s := X.support ∪ Y.support)]
  apply Finset.sum_le_sum
  intro a _
  exact max_le (sub_le_self _ (hY a)) (hX a)

/-- **Support lemma forced by the CR18/thesis advantage bridge; candidate for upstream.**
For any event, the one-sided gap between its masses is bounded by statistical distance. -/
theorem mass_tsub_mass_le_statDist {A : Type*}
    (X Y : Distribution A) (P : A → Prop) :
    X.mass P - Y.mass P ≤ statDist X Y := by
  classical
  set s : Finset A := X.support ∪ Y.support ∪ (X - Y).support with hs
  have hsub : (X - Y).support ⊆ s := Finset.subset_union_right
  rw [Distribution.mass_eq_sum_of_support_subset X
        (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left) P,
    Distribution.mass_eq_sum_of_support_subset Y
        (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left) P,
    statDist_eq_sum_of_support_subset X Y hsub, ← Finset.sum_sub_distrib]
  have hfilter : ∑ a ∈ s.filter P, (X a - Y a) ≤ ∑ a ∈ s.filter P, max (X a - Y a) 0 :=
    Finset.sum_le_sum fun a _ => le_max_left _ _
  exact hfilter.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun a _ _ => le_max_right _ _)

/-- **Support lemma forced by the CR18/thesis advantage bridge; candidate for upstream.**
Real-valued form of `mass_tsub_mass_le_statDist`, convenient for signed CR18 advantages.
(Over the `ℝ` carrier the two coincide; kept for call-site compatibility.) -/
theorem mass_sub_mass_le_statDist {A : Type*}
    (X Y : Distribution A) (P : A → Prop) :
    ((X.mass P : ℝ) - (Y.mass P : ℝ)) ≤ (statDist X Y : ℝ) :=
  mass_tsub_mass_le_statDist X Y P

/-- **Two pushforwards of one law that agree off a bad event are within its
mass.**  If `F` and `G` differ only on `P`, then the laws they induce from a
common non-negative `μ` are at statistical distance at most `μ(P)`.

This is the "identical-until-bad" step in its distributional form: the coupling
is the shared source `μ`, and the bound is the probability that the two
readings of one sampled atom part company.  Both sides are pushforwards of the
*same* `μ` — that is what makes it an equality of couplings rather than a
triangle inequality, and it is why no weight or `Fintype` hypothesis appears.

UPSTREAM-CANDIDATE (Definition 3 toolkit; the game-playing lemma's kernel). -/
theorem statDist_fTransform_le_mass_of_eq_off {A B : Type*} {μ : Distribution A}
    (hμ : μ.NonNeg) (F G : A → B) (P : A → Prop)
    (hoff : ∀ a ∈ μ.support, ¬ P a → F a = G a) :
    statDist (Distribution.fTransform F μ) (Distribution.fTransform G μ)
      ≤ μ.mass P := by
  classical
  set s : Finset B := (μ.support.image F) ∪ (μ.support.image G) ∪
    (Distribution.fTransform F μ - Distribution.fTransform G μ).support with hs
  have hsub : (Distribution.fTransform F μ - Distribution.fTransform G μ).support ⊆ s :=
    Finset.subset_union_right
  have hcover : ∀ a ∈ μ.support, F a ∈ s := fun a ha =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem F ha))
  have hterm : ∀ b ∈ s,
      max (Distribution.fTransform F μ b - Distribution.fTransform G μ b) 0
        ≤ μ.mass (fun a => P a ∧ F a = b) := by
    intro b _
    have hsplit : μ.mass (fun a => P a ∧ F a = b)
        + μ.mass (fun a => ¬ P a ∧ F a = b) = μ.mass (fun a => F a = b) :=
      Distribution.mass_and_add_mass_not_and μ P (fun a => F a = b)
    have hle : μ.mass (fun a => ¬ P a ∧ F a = b) ≤ μ.mass (fun a => G a = b) :=
      Distribution.mass_mono_on_support hμ fun a ha hcase => by
        rw [← hoff a ha hcase.1]; exact hcase.2
    refine max_le ?_ (hμ.mass_nonneg _)
    rw [Distribution.fTransform_apply_eq_mass, Distribution.fTransform_apply_eq_mass,
      ← hsplit]
    linarith
  calc statDist (Distribution.fTransform F μ) (Distribution.fTransform G μ)
      = ∑ b ∈ s, max (Distribution.fTransform F μ b
          - Distribution.fTransform G μ b) 0 :=
        statDist_eq_sum_of_support_subset _ _ hsub
    _ ≤ ∑ b ∈ s, μ.mass (fun a => P a ∧ F a = b) := Finset.sum_le_sum hterm
    _ = μ.mass P := (Distribution.mass_eq_sum_mass_fiber μ P F s hcover).symm

/-! ### The distance/expectation bridge

CR18_LN Exercise 4.4 (p. 83): perturbing the instance distribution by `d` in
statistical distance changes a solver's performance by at most `2d`, "and the
same statement holds for games, without the factor 2" (their footnote 12).  The
two constants are one lemma: a game's performance is an indicator, taking values
in `[0, 1]`, while a bit-guessing performance is calibrated to `[-1, 1]`, and the
bound is `(sup f − inf f) · d` in both cases.  So the sharp constant is the
*range* of `f`, not `2 · sup |f|` — which would give `2` for a game — and the
tree's existing indicator case (`mass_sub_mass_le_statDist`) is the `[0, 1]`
instance.

**Layer.**  All three statements below hold on the bare **signed** layer: no
`Distribution.NonNeg`, no `Distribution.isProbDist`.  What the two-sided range form does need is
`|X| = |Y|`, and that hypothesis is not cosmetic — at `X = single a 1`, `Y = 0`
and `f ≡ 5` the left side is `5` while `(sup f − inf f) · δ(X, Y) = 0`.  Equal
weight is exactly the hypothesis under which the constant term `m · (|X| − |Y|)`
of the general estimate vanishes, and it is the same hypothesis that makes `δ`
symmetric (`statDist_symm_of_eq_weight`).  The one-sided `[0, 1]` form needs no
weight hypothesis at all, matching `mass_sub_mass_le_statDist`. -/

/-- **The `[0, 1]` case of CR18_LN Exercise 4.4** (their footnote 12, the "games,
without the factor 2" form): a functional with values in `[0, 1]` moves by at
most `δ(X, Y)`.  This is `mass_sub_mass_le_statDist` with the indicator of an
event replaced by an arbitrary `[0, 1]`-valued observable, and like it, it needs
no weight hypothesis — the one-sided distance already charges the excess of `X`
over `Y`.  Signed layer, and no `Fintype`.

UPSTREAM-CANDIDATE: the duality between the half-`L¹` distance of two finitely
supported signed measures and `[0, 1]`-valued test functions. -/
theorem expect_sub_expect_le_statDist {A : Type*} (X Y : Distribution A) (f : A → ℝ)
    (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) :
    X.expect f - Y.expect f ≤ statDist X Y := by
  rw [← Distribution.expect_sub_left]
  refine Finset.sum_le_sum fun a _ => ?_
  have hd : (X - Y) a = X a - Y a := by simp
  rw [hd]
  rcases le_total 0 (X a - Y a) with h | h
  · rw [max_eq_left h]
    nlinarith [h0 a, h1 a]
  · rw [max_eq_right h]
    nlinarith [h0 a]

/-- **CR18_LN Exercise 4.4**, one-sided: a functional taking values in `[m, M]`
moves by at most `(M − m) · δ(X, Y)`.

The proof is the exercise's: recentre `f` by the constant `m`, which is free
because equal weight makes `𝔼_X[m] − 𝔼_Y[m] = 0`, and then bound the recentred
functional pointwise by the one-sided excess.  Signed layer plus `|X| = |Y|`;
no `Fintype`. -/
theorem expect_sub_expect_le_mul_statDist {A : Type*} (X Y : Distribution A) (f : A → ℝ)
    {m M : ℝ} (hw : X.weight = Y.weight) (hm : ∀ a, m ≤ f a) (hM : ∀ a, f a ≤ M) :
    X.expect f - Y.expect f ≤ (M - m) * statDist X Y := by
  have hconst : (X - Y).expect (fun _ => m) = 0 := by
    rw [Distribution.expect_sub_left, Distribution.expect_const, Distribution.expect_const, hw, sub_self]
  rw [← Distribution.expect_sub_left, ← sub_zero ((X - Y).expect f), ← hconst, statDist,
    Finset.mul_sum, Distribution.expect, Distribution.expect, Finsupp.sum, Finsupp.sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  have hd : (X - Y) a = X a - Y a := by simp
  have hmM : m ≤ M := (hm a).trans (hM a)
  rw [hd]
  rcases le_total 0 (X a - Y a) with h | h
  · rw [max_eq_left h]
    nlinarith [hM a]
  · rw [max_eq_right h]
    nlinarith [hm a]

/-- **CR18_LN Exercise 4.4**, the two-sided form the exercise asks to "state
formally": for distributions of equal weight, a functional taking values in
`[m, M]` satisfies `|𝔼_X[f] − 𝔼_Y[f]| ≤ (M − m) · δ(X, Y)`.

At `[m, M] = [-1, 1]` — the calibration CR18_LN Definition 2.9 puts on a
bit-guessing advantage — this is the printed constant `2d`; at `[m, M] = [0, 1]`
it is footnote 12's `d`.  Signed layer plus `|X| = |Y|`.  `Fintype` enters only
through `statDist_symm_of_eq_weight`, which is how the tree states symmetry of
`δ`; the one-sided forms above are free of it. -/
theorem abs_expect_sub_expect_le_mul_statDist {A : Type*} [Fintype A]
    (X Y : Distribution A) (f : A → ℝ) {m M : ℝ} (hw : X.weight = Y.weight)
    (hm : ∀ a, m ≤ f a) (hM : ∀ a, f a ≤ M) :
    |X.expect f - Y.expect f| ≤ (M - m) * statDist X Y := by
  refine abs_sub_le_iff.mpr ⟨expect_sub_expect_le_mul_statDist X Y f hw hm hM, ?_⟩
  rw [statDist_symm_of_eq_weight X Y hw]
  exact expect_sub_expect_le_mul_statDist Y X f hw.symm hm hM

/-- Statistical distance is exactly the one-sided mass gap on the points where
the first distribution is heavier.  This is the canonical statistical test
used to turn a transcript distance into a signed CR18 distinguisher advantage. -/
theorem statDist_eq_mass_sub_mass_pos {A : Type*} [Fintype A]
    (X Y : Distribution A) :
    (statDist X Y : ℝ) =
      (X.mass (fun a => Y a < X a) : ℝ) -
        (Y.mass (fun a => Y a < X a) : ℝ) := by
  classical
  rw [statDist_eq_sum_univ, Distribution.mass_eq_sum, Distribution.mass_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : Y a < X a
  · rw [if_pos h, if_pos h, max_eq_left (sub_nonneg.mpr h.le)]
  · rw [if_neg h, if_neg h, max_eq_right (sub_nonpos.mpr (not_lt.mp h))]
    simp

/-! ### The optimal-test identity

PorRen22 Theorem 8 (classical case, sketched on their p. 50; also the
`½(1-p) + p = ½ + ½p` step in the proof of MaPiRe07 Lemma 4): a sample is
drawn from `X` or from `Y`, each with prior ½, and a decision rule
`g : A → Bool` guesses the source (`true` = "the sample came from `X`").
The best achievable success probability is `½ + ½ δ(X, Y)`, attained by the
Bayes rule "guess `X` iff `X(a) > Y(a)`".  This is the distribution-level
statement only; the random-system version (the mixed system `⟨S/T⟩_Z` of
MaPiRe07) is separate work. -/

/-- Success probability of the **binary hypothesis test** `g` at identifying
the source of a sample drawn from `X` or `Y` with equal prior ½: with
probability ½ the sample is drawn from `X` and the answer is correct iff `g`
answers `true`, with probability ½ it is drawn from `Y` and the answer is
correct iff `g` answers `false`.  Meaningful as a probability when `X` and `Y`
are probability distributions; defined for arbitrary signed distributions.

**Named for the task, not for "guessing" — and `avg`, not `bayes`.**  This
decides *which of two hypotheses* produced the sample; the different task of
recovering an unknown *value* from correlated side information is
`Distribution.guessProb` / `Distribution.condGuessProb` (`RandomSystems/Entropy.lean`), the
quantities paired with min-entropy.  In mathlib's decision-theory vocabulary
(`Mathlib/Probability/Decision/Risk/Defs.lean`) the quantity here is
`1 - avgRisk` at 0-1 loss under the uniform prior — prior-averaged over a
**given** rule `g`, which is what `avgRisk` names.  `bayesRisk` there is the
*optimum* over rules, so the Bayes-flavoured statement is the supremum
`sSup_avgSuccessProb_eq_half_add_half_statDist` below, which is `1 - bayesRisk`
and hence the classical Bayes-error identity `bayesRisk = ½ − ½·δ(X, Y)`. -/
noncomputable def avgSuccessProb {A : Type*} (X Y : Distribution A) (g : A → Bool) : ℝ :=
  (X.mass (fun a => g a = true) + Y.mass (fun a => g a = false)) / 2

/-- Structural form of `avgSuccessProb`: eliminating the complement event turns the
success probability into the signed mass gap of the acceptance set of `g`,
shifted by the total weight of `Y`.  Unconditional. -/
theorem avgSuccessProb_eq_mass_sub_mass_add_weight_div_two {A : Type*}
    (X Y : Distribution A) (g : A → Bool) :
    avgSuccessProb X Y g =
      (X.mass (fun a => g a = true) - Y.mass (fun a => g a = true) +
        Y.weight) / 2 := by
  have hcompl := Distribution.mass_add_compl Y (fun a => g a = true)
  have hfalse : Y.mass (fun a => ¬ (g a = true)) =
      Y.mass (fun a => g a = false) :=
    Distribution.mass_congr Y (fun a => by simp)
  unfold avgSuccessProb
  rw [← hfalse]
  linarith

/-- **No decision rule beats `½ + ½ δ(X, Y)`** (optimality half of PorRen22
Theorem 8).  Only `|Y| = 1` is needed: the acceptance-set mass gap is bounded
by `δ(X, Y)` for arbitrary signed `X`, `Y` (`mass_tsub_mass_le_statDist`),
and the weight of `Y` is the only normalization the bound consumes. -/
theorem avgSuccessProb_le_half_add_half_statDist {A : Type*} [Fintype A]
    (X Y : Distribution A) (hY : Y.weight = 1) (g : A → Bool) :
    avgSuccessProb X Y g ≤ 1 / 2 + statDist X Y / 2 := by
  rw [avgSuccessProb_eq_mass_sub_mass_add_weight_div_two, hY]
  have := mass_tsub_mass_le_statDist X Y (fun a => g a = true)
  linarith

/-- **The Bayes rule attains `½ + ½ δ(X, Y)`** (attainment half of PorRen22
Theorem 8): any rule that guesses `X` exactly on `{a | Y(a) < X(a)}` — the
Bayes-optimal rule for equal prior ½ — succeeds with probability exactly
`½ + ½ δ(X, Y)`.  The rule is taken as an abstract `g` with a specification
hypothesis so the statement does not fix a `Decidable` instance. -/
theorem avgSuccessProb_eq_half_add_half_statDist_of_forall_eq_true_iff_lt
    {A : Type*} [Fintype A] (X Y : Distribution A) (hY : Y.weight = 1) (g : A → Bool)
    (hg : ∀ a, g a = true ↔ Y a < X a) :
    avgSuccessProb X Y g = 1 / 2 + statDist X Y / 2 := by
  rw [avgSuccessProb_eq_mass_sub_mass_add_weight_div_two, hY,
    Distribution.mass_congr X hg, Distribution.mass_congr Y hg,
    ← statDist_eq_mass_sub_mass_pos]
  ring

/-- **Optimal-test identity** (PorRen22 Theorem 8, classical case; the
`½ + ½p` computation of MaPiRe07 Lemma 4): the best success probability over
all decision rules `A → Bool` of deciding which of `X`, `Y` (equal prior ½) a
sample came from is exactly `½ + ½ δ(X, Y)`.  In mathlib's decision-theory
vocabulary this is `1 - bayesRisk` at 0-1 loss and uniform prior.

Stated as a genuine supremum over all decision rules, in the library's
`sSup`-over-image idiom; `avgSuccessProb_le_half_add_half_statDist` gives the upper
bound for every rule and the Bayes rule attains it.  Only `|Y| = 1` is
required, matching the min-form asymmetry of `δ`; for the intended reading
both `X` and `Y` are probability distributions. -/
theorem sSup_avgSuccessProb_eq_half_add_half_statDist {A : Type*} [Fintype A]
    (X Y : Distribution A) (hY : Y.weight = 1) :
    sSup ((fun g : A → Bool => avgSuccessProb X Y g) '' Set.univ) =
      1 / 2 + statDist X Y / 2 := by
  have hbound : ∀ g : A → Bool, avgSuccessProb X Y g ≤ 1 / 2 + statDist X Y / 2 :=
    avgSuccessProb_le_half_add_half_statDist X Y hY
  have hbdd : BddAbove ((fun g : A → Bool => avgSuccessProb X Y g) '' Set.univ) := by
    refine ⟨1 / 2 + statDist X Y / 2, ?_⟩
    rintro x ⟨g, -, rfl⟩
    exact hbound g
  have hnonneg : (0 : ℝ) ≤ 1 / 2 + statDist X Y / 2 := by
    have := statDist_nonneg X Y
    linarith
  refine le_antisymm (sSup_image_univ_le_of_forall _ hnonneg hbound) ?_
  classical
  calc 1 / 2 + statDist X Y / 2
      = avgSuccessProb X Y (fun a => decide (Y a < X a)) :=
        (avgSuccessProb_eq_half_add_half_statDist_of_forall_eq_true_iff_lt X Y hY _
          (fun a => by simp)).symm
    _ ≤ sSup ((fun g : A → Bool => avgSuccessProb X Y g) '' Set.univ) :=
        le_csSup hbdd ⟨_, Set.mem_univ _, rfl⟩

/-- If every pointwise deficit `X a - Y a` is bounded by a non-negative charge
function, then statistical distance is bounded by the total charge. -/
theorem statDist_le_sum_of_forall_tsub_le {A : Type*} [Fintype A]
    (X Y : Distribution A) (charge : A → ℝ)
    (h0 : ∀ a, 0 ≤ charge a)
    (h : ∀ a, X a - Y a ≤ charge a) :
    statDist X Y ≤ ∑ a, charge a := by
  rw [statDist_eq_sum_univ]
  exact Finset.sum_le_sum (fun a _ => max_le (h a) (h0 a))

/-- A one-sided ratio lower bound controls the pointwise deficit. -/
theorem sub_le_mul_of_one_sub_mul_le {a b eps : ℝ}
    (h_lower : (1 - eps) * b ≤ a) :
    b - a ≤ eps * b := by
  nlinarith [h_lower]

/-- One-sided density lower bound for statistical distance.

If `real` and `ideal` have equal total weight, `ideal` is a non-negative
subdistribution, and `(1 - eps) * ideal a <= real a` pointwise, then
`statDist real ideal <= eps`.  This is the distribution-level core of the
one-sided H-technique. -/
theorem statDist_le_of_one_sub_mul_le {A : Type*} [Fintype A]
    (real ideal : Distribution A)
    (eps : NNReal)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ eps := by
  rw [statDist_symm_of_eq_weight real ideal h_weight]
  refine le_trans
    (statDist_le_sum_of_forall_tsub_le ideal real (fun a => eps * ideal a)
      (fun a => mul_nonneg eps.coe_nonneg (h_ideal_nonneg a))
      (fun a => sub_le_mul_of_one_sub_mul_le (h_lower a))) ?_
  calc ∑ a, (eps : ℝ) * ideal a
    _ = (eps : ℝ) * ∑ a, ideal a := by rw [← Finset.mul_sum]
    _ = (eps : ℝ) * ideal.weight := by rw [← Distribution.weight_eq_sum ideal]
    _ ≤ (eps : ℝ) * 1 := mul_le_mul_of_nonneg_left h_ideal_le eps.coe_nonneg
    _ = eps := mul_one _

/-! ### Distribution-level H-technique bounds -/

/-- The mass of the bad event `B` under distribution `D`. -/
noncomputable def probBad {A : Type*}
    (D : Distribution A) (B : A → Prop) :
    ℝ :=
  D.mass B

/-- UPSTREAM-CANDIDATE: adding deterministic terminal side information does
not change the mass of a bad event that ignores that terminal component. -/
@[simp]
theorem probBad_const_pair {A U : Type*}
    (D : Distribution A) (B : A → Prop) (u : U) :
    probBad (Distribution.fTransform (fun a : A => (a, u)) D)
        (fun p : A × U => B p.1) =
      probBad D B := by
  unfold probBad
  rw [Distribution.mass_fTransform]

/-- UPSTREAM-CANDIDATE: `probBad` is the finite-carrier predicate mass. -/
theorem probBad_eq_evalPred {A : Type*} [Fintype A] (D : Distribution A) (B : A → Prop) :
    probBad D B = D.evalPred B := by
  unfold probBad Distribution.evalPred
  rw [Distribution.mass_eq_sum, Finset.sum_filter]

/-- UPSTREAM-CANDIDATE: finite union bound for `probBad` events decomposed into
per-index predicates. -/
theorem probBad_iUnion_le {A ι : Type*} [Fintype A] [Fintype ι]
    {D : Distribution A} (hD : D.NonNeg) (B : A → Prop) (P : ι → A → Prop)
    [∀ p, DecidablePred (P p)]
    (hB : ∀ a, B a → ∃ p, P p a) :
    probBad D B ≤ ∑ p, D.evalPred (P p) := by
  rw [probBad_eq_evalPred]
  refine le_trans ?_ (Distribution.evalPred_iUnion_le hD P)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact hB a ha
  · intro a _ _
    exact hD a

/-- Extended H-technique: if the real/ideal density ratio is at least
`1 - eps` on good points, then statistical distance is bounded by bad mass plus
`eps`. -/
theorem hTechnique_ratio {A : Type*} [Fintype A]
    (real ideal : Distribution A)
    (B : A → Prop)
    (eps : NNReal)
    (h_real_nonneg : real.NonNeg)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ probBad ideal B + eps := by
  classical
  rw [statDist_symm_of_eq_weight real ideal h_weight]
  let charge : A → ℝ := fun a => (if B a then ideal a else 0) + eps * ideal a
  have h_charge_nonneg : ∀ a, 0 ≤ charge a := by
    intro a
    refine add_nonneg ?_ (mul_nonneg eps.coe_nonneg (h_ideal_nonneg a))
    by_cases h : B a <;> simp [h, h_ideal_nonneg a]
  have h_term_bound : ∀ a, ideal a - real a ≤ charge a := by
    intro a
    by_cases h_bad : B a
    · simp only [charge, h_bad, if_true]
      have := h_real_nonneg a
      have := mul_nonneg eps.coe_nonneg (h_ideal_nonneg a)
      linarith
    · simp only [charge, h_bad, if_false, zero_add]
      exact sub_le_mul_of_one_sub_mul_le (h_ratio a h_bad)
  have h_eps_weight_le : (eps : ℝ) * ideal.weight ≤ eps := by
    calc (eps : ℝ) * ideal.weight ≤ (eps : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h_ideal_le eps.coe_nonneg
      _ = eps := mul_one _
  refine le_trans
    (statDist_le_sum_of_forall_tsub_le ideal real charge h_charge_nonneg h_term_bound) ?_
  calc ∑ a, charge a
    _ = (∑ a, if B a then ideal a else 0) + ∑ a, (eps : ℝ) * ideal a := by
        simp only [charge]
        rw [Finset.sum_add_distrib]
    _ = (∑ a, if B a then ideal a else 0) + (eps : ℝ) * ∑ a, ideal a := by
        rw [← Finset.mul_sum]
    _ = probBad ideal B + (eps : ℝ) * ideal.weight := by
        rw [probBad, Distribution.mass_eq_sum, ← Distribution.weight_eq_sum ideal]
    _ ≤ probBad ideal B + eps :=
        add_le_add le_rfl h_eps_weight_le

/-- Expectation-method H-technique bound with a point-dependent error term. -/
theorem hTechnique_expectation {A : Type*} [Fintype A]
    (real ideal : Distribution A)
    (B : A → Prop) [DecidablePred B]
    (eps : A → NNReal)
    (h_real_nonneg : real.NonNeg)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ratio : ∀ a, ¬ B a → (1 - eps a) * ideal a ≤ real a) :
    statDist real ideal ≤ probBad ideal B +
      ideal.sum (fun a w => if ¬ B a then w * eps a else 0) := by
  classical
  rw [statDist_symm_of_eq_weight real ideal h_weight]
  let charge : A → ℝ :=
    fun a => (if B a then ideal a else 0) + if ¬ B a then ideal a * eps a else 0
  have h_charge_nonneg : ∀ a, 0 ≤ charge a := by
    intro a
    refine add_nonneg ?_ ?_
    · by_cases h : B a <;> simp [h, h_ideal_nonneg a]
    · by_cases h : B a <;>
        simp [h, mul_nonneg (h_ideal_nonneg a) (eps a).coe_nonneg]
  have h_term_bound : ∀ a, ideal a - real a ≤ charge a := by
    intro a
    by_cases h_bad : B a
    · simp only [charge, h_bad, if_true, not_true_eq_false, if_false, add_zero]
      have := h_real_nonneg a
      linarith
    · simp only [charge, h_bad, if_false, not_false_eq_true, if_true, zero_add]
      calc ideal a - real a ≤ (eps a : ℝ) * ideal a :=
            sub_le_mul_of_one_sub_mul_le (h_ratio a h_bad)
        _ = ideal a * eps a := mul_comm _ _
  refine le_trans
    (statDist_le_sum_of_forall_tsub_le ideal real charge h_charge_nonneg h_term_bound) ?_
  have hsum :
      ideal.sum (fun a w => if ¬ B a then w * (eps a : ℝ) else 0) =
        ∑ a, if ¬ B a then ideal a * eps a else 0 := by
    exact Finsupp.sum_fintype _ _ (fun a => by by_cases h : B a <;> simp [h])
  calc ∑ a, charge a
    _ = (∑ a, if B a then ideal a else 0) +
          ∑ a, if ¬ B a then ideal a * (eps a : ℝ) else 0 := by
        simp only [charge]
        rw [Finset.sum_add_distrib]
    _ = probBad ideal B + ideal.sum (fun a w => if ¬ B a then w * eps a else 0) := by
        rw [probBad, Distribution.mass_eq_sum, hsum]
        congr 1
        apply Finset.sum_congr rfl
        intro a _ha
        by_cases h : B a <;> simp [h]
    _ ≤ probBad ideal B + ideal.sum (fun a w => if ¬ B a then w * eps a else 0) := le_rfl

/-! ### The partition refinement of the good/bad kernel

Good/bad is not fundamental.  Partition the carrier into cells `cell : A → ι`,
give each cell its own ratio defect `εᵢ`, and the distance is bounded by the
`ideal`-average of the defects.  The good/bad lemma is the two-cell case
(`hTechnique_ratio_via_partition`): the bad cell has defect `1`, the good cell
has defect `ε`.

Both statements are **derived here** from `hTechnique_expectation`, the
layer-2 kernel already in this file — the partition shape is a refinement of
that kernel, not a second proof of it.

*Provenance, flagged.*  The quarry calls this shape "Layer D′, the
Chen–Steinberger partition form" and cites `Chen–Steinberger` as a bare author
name: no bibliography entry, year, or page exists anywhere in its
`HTechnique/` tree, and no such paper is on disk.  The name is therefore
recorded here as the quarry's attribution, **not** as a verified citation, and
it sits outside the source hierarchy (MauRen16 / Jost / LiuMau20 /
Lanzenberger) entirely.  Upgrading it to a page-verified citation is owed. -/

/-- **The partition bound.**  With a per-cell ratio defect,

  `(∀ a, (1 − ε_{cell a})·ideal a ≤ real a)  ⟹  δ(real, ideal) ≤ Σᵢ εᵢ·Pr_ideal[cell = i]`.

The hypothesis is still a pointwise ratio, so it is still checked
non-adaptively and cell by cell; what the refinement buys is that a cell whose
ratio is nearly exact contributes nearly nothing, where the good/bad split
would have had to charge it the full bad mass. -/
theorem hTechnique_partition {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (real ideal : Distribution A) (cell : A → ι) (eps : ι → NNReal)
    (h_real_nonneg : real.NonNeg)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ratio : ∀ a, (1 - eps (cell a)) * ideal a ≤ real a) :
    statDist real ideal ≤ ∑ i, (eps i : ℝ) * probBad ideal (fun a => cell a = i) := by
  classical
  -- Expectation form at `Bad := ∅` and `ε(a) := ε_{cell a}`, then regroup the
  -- `ideal`-expectation of `ε_{cell ·}` by cell.
  have h := hTechnique_expectation real ideal (fun _ => False) (fun a => eps (cell a))
    h_real_nonneg h_ideal_nonneg h_weight (fun a _ => h_ratio a)
  refine le_trans h (le_of_eq ?_)
  have hbad : probBad ideal (fun _ => False) = 0 :=
    Distribution.mass_eq_zero_of_forall_not ideal (fun _ => id)
  rw [hbad, zero_add]
  have hright : ∑ i : ι, (eps i : ℝ) * probBad ideal (fun a => cell a = i)
      = ∑ a : A, ideal a * (eps (cell a) : ℝ) := by
    have hexp : ∀ i : ι, (eps i : ℝ) * probBad ideal (fun a => cell a = i)
        = ∑ a : A, (if cell a = i then ideal a * (eps i : ℝ) else 0) := by
      intro i
      unfold probBad
      rw [Distribution.mass_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by
        by_cases h : cell a = i <;> simp [h, mul_comm]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hexp i), Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (cell a) (fun i => ideal a * (eps i : ℝ))]
    simp
  refine Eq.trans ?_ hright.symm
  simp only [not_false_eq_true, if_true]
  exact Finsupp.sum_of_support_subset ideal (Finset.subset_univ _) _ (fun a _ => by simp)

/-- **Good/bad is the two-cell case** of `hTechnique_partition`: the bad cell
carries defect `1` (no ratio is claimed there, and it is charged its full
mass), the good cell carries defect `ε`, and
`1·Pr[Bad] + ε·Pr[good] ≤ Pr[Bad] + ε` recovers `hTechnique_ratio`.

This is a consistency statement about the refinement, not a new bound: it
re-derives the kernel lemma from the partition form, so the two can never
drift apart. -/
theorem hTechnique_ratio_via_partition {A : Type*} [Fintype A]
    (real ideal : Distribution A) (B : A → Prop) (eps : NNReal)
    (h_real_nonneg : real.NonNeg)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ probBad ideal B + eps := by
  classical
  have h := hTechnique_partition real ideal
    (fun a => if B a then (0 : Fin 2) else 1)
    (fun i => if i = 0 then 1 else eps)
    h_real_nonneg h_ideal_nonneg h_weight
    (by
      intro a
      by_cases hB : B a
      · simpa [hB] using h_real_nonneg a
      · simpa [hB] using h_ratio a hB)
  refine le_trans h ?_
  rw [Fin.sum_univ_two]
  simp only [reduceIte, NNReal.coe_one, one_mul]
  have h0 : probBad ideal (fun a => (if B a then (0 : Fin 2) else 1) = 0) = probBad ideal B := by
    unfold probBad
    exact Distribution.mass_congr _ fun a => by by_cases hB : B a <;> simp [hB]
  have h1 : (eps : ℝ) * probBad ideal (fun a => (if B a then (0 : Fin 2) else 1) = 1) ≤ eps := by
    have hm : probBad ideal (fun a => (if B a then (0 : Fin 2) else 1) = 1) ≤ 1 :=
      le_trans (Distribution.mass_le_weight h_ideal_nonneg _) h_ideal_le
    have hnn : 0 ≤ probBad ideal (fun a => (if B a then (0 : Fin 2) else 1) = 1) :=
      h_ideal_nonneg.mass_nonneg _
    nlinarith [eps.coe_nonneg]
  rw [h0]
  exact add_le_add le_rfl h1

/-- When real and ideal agree exactly on good points, statistical distance is
bounded by the ideal bad probability. -/
theorem hTechnique_eq_on_good {A : Type*} [Fintype A]
    (real ideal : Distribution A)
    (B : A → Prop)
    (h_real_nonneg : real.NonNeg)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_eq : ∀ a, ¬ B a → real a = ideal a) :
    statDist real ideal ≤ probBad ideal B := by
  classical
  rw [statDist_symm_of_eq_weight real ideal h_weight]
  refine le_trans
    (statDist_le_sum_of_forall_tsub_le ideal real (fun a => if B a then ideal a else 0)
      ?_ ?_) ?_
  · intro a
    by_cases h_bad : B a <;> simp [h_bad, h_ideal_nonneg a]
  · intro a
    by_cases h_bad : B a
    · simp only [h_bad, if_true]
      have := h_real_nonneg a
      linarith
    · simp [h_bad, h_eq a h_bad]
  · rw [probBad, Distribution.mass_eq_sum]

/-- One-sided H-technique: if `(1 - eps) * ideal(a) <= real(a)` for all points,
then `statDist real ideal <= eps`. -/
theorem oneSided_hTechnique {A : Type*} [Fintype A]
    (real ideal : Distribution A)
    (eps : NNReal)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ eps := by
  exact statDist_le_of_one_sub_mul_le real ideal eps h_ideal_nonneg h_weight
    h_ideal_le h_lower

/-- The one-sided H-technique is stable under a common deterministic
post-processing. -/
theorem oneSided_hTechnique_fTransform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (real ideal : Distribution A) (f : A → B)
    (eps : NNReal)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist (Distribution.fTransform f real) (Distribution.fTransform f ideal) ≤ eps := by
  refine oneSided_hTechnique (Distribution.fTransform f real)
    (Distribution.fTransform f ideal) eps (h_ideal_nonneg.fTransform f) ?_ ?_ ?_
  · rw [Distribution.weight_fTransform, Distribution.weight_fTransform, h_weight]
  · rwa [Distribution.weight_fTransform]
  · intro b
    exact Distribution.mul_fTransform_le_fTransform_of_forall_mul_le
      ideal real f (1 - eps) h_lower b

/-- One-sided H-technique with probability-distribution hypotheses. -/
theorem oneSided_hTechnique_proper {A : Type*} [Fintype A]
    (real ideal : Distribution A)
    (eps : NNReal)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_real_proper : real.weight = 1)
    (h_ideal_proper : ideal.weight = 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ eps := by
  exact oneSided_hTechnique real ideal eps h_ideal_nonneg
    (by rw [h_real_proper, h_ideal_proper]) (by rw [h_ideal_proper]) h_lower

/-- Ratio-form H-technique applied to finite mass functions rather than
explicit `Distribution` objects. -/
theorem hTechnique_ratio_massFunction {A : Type*} [Fintype A]
    (real ideal : A → ℝ)
    (B : A → Prop)
    (eps : NNReal)
    (h_real_nonneg : ∀ a, 0 ≤ real a)
    (h_ideal_nonneg : ∀ a, 0 ≤ ideal a)
    (h_weight :
      (Distribution.ofFiniteMassFunction real).weight =
        (Distribution.ofFiniteMassFunction ideal).weight)
    (h_ideal_le : (Distribution.ofFiniteMassFunction ideal).weight ≤ 1)
    (h_ratio : ∀ a, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    statDist (Distribution.ofFiniteMassFunction real)
        (Distribution.ofFiniteMassFunction ideal) ≤
      probBad (Distribution.ofFiniteMassFunction ideal) B + eps := by
  exact hTechnique_ratio (Distribution.ofFiniteMassFunction real)
    (Distribution.ofFiniteMassFunction ideal) B eps
    (fun a => by simpa using h_real_nonneg a)
    (fun a => by simpa using h_ideal_nonneg a)
    h_weight h_ideal_le (by
      intro a ha
      simpa using h_ratio a ha)

/-- One-sided H-technique applied to finite mass functions rather than explicit
`Distribution` objects. -/
theorem oneSided_hTechnique_massFunction {A : Type*} [Fintype A]
    (real ideal : A → ℝ)
    (eps : NNReal)
    (h_ideal_nonneg : ∀ a, 0 ≤ ideal a)
    (h_weight :
      (Distribution.ofFiniteMassFunction real).weight =
        (Distribution.ofFiniteMassFunction ideal).weight)
    (h_ideal_le : (Distribution.ofFiniteMassFunction ideal).weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist (Distribution.ofFiniteMassFunction real)
      (Distribution.ofFiniteMassFunction ideal) ≤ eps := by
  exact oneSided_hTechnique (Distribution.ofFiniteMassFunction real)
    (Distribution.ofFiniteMassFunction ideal) eps
    (fun a => by simpa using h_ideal_nonneg a)
    h_weight h_ideal_le (by
      intro a
      simpa using h_lower a)

/-- Lemma 2 (Partition of statistical distance).

For any partition {Aⱼ} of A:
  δ(X, Y) = ∑_j δ(X_j, Y_j)
where X_j, Y_j are X, Y restricted to Aⱼ. -/
theorem statDist_partition {A : Type*} [Fintype A] {n : ℕ}
    (X Y : Distribution A) (P : A → Fin n) :
    statDist X Y =
      ∑ j : Fin n, ∑ a ∈ Finset.univ.filter (fun a => P a = j),
        max (X a - Y a) 0 := by
  simp only [statDist_eq_sum_univ]
  exact (Finset.sum_fiberwise Finset.univ P _).symm

/-- Lemma 3 (Data processing inequality).

For any function f : A → B:
  δ(f(X), f(Y)) ≤ δ(X, Y).

Applying a function can only decrease statistical distance.

Paper proof (Appendix A): δ(f(X), f(Y)) = ∑_b max(0, ∑_{f(a)=b} (X(a) - Y(a)))
  ≤ ∑_b ∑_{f(a)=b} max(0, X(a) - Y(a)) = ∑_a max(0, X(a) - Y(a)) = δ(X,Y).

The one step that is about the **signed** carrier is the fiber estimate
`max (0, ∑ᵢ dᵢ) ≤ ∑ᵢ max (0, dᵢ)`: a pushforward sums a fiber, and
cancellation inside a fiber can only shrink the one-sided excess.

No `Fintype`, no `DecidableEq`: the source sum runs over `X.support ∪
Y.support` and the image sum over its image under `f`, which is where the
pushed-forward difference is supported. -/
theorem statDist_fTransform_le {A B : Type*}
    (X Y : Distribution A) (f : A → B) :
    statDist (Distribution.fTransform f X) (Distribution.fTransform f Y) ≤ statDist X Y := by
  haveI : DecidableEq A := Classical.decEq A
  haveI : DecidableEq B := Classical.decEq B
  -- A pushforward evaluates as the sum over the fiber, taken inside any finite
  -- set covering the support.
  have hval : ∀ (Z : Distribution A), Z.support ⊆ X.support ∪ Y.support →
      ∀ b : B, Distribution.fTransform f Z b =
        ∑ a ∈ (X.support ∪ Y.support).filter (fun a => f a = b), Z a := by
    intro Z hZ b
    rw [Distribution.fTransform_apply_eq_mass]
    simp only [Distribution.mass]
    rw [Finsupp.sum_of_support_subset Z hZ _ (fun i _ => by simp), Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : f a = b <;> simp [h]
  have himg : ∀ (Z : Distribution A), Z.support ⊆ X.support ∪ Y.support →
      (Distribution.fTransform f Z).support ⊆ (X.support ∪ Y.support).image f := by
    intro Z hZ b hb
    obtain ⟨a, ha, rfl⟩ := Distribution.mem_support_fTransform f Z hb
    exact Finset.mem_image_of_mem f (hZ ha)
  have hsupp :
      (Distribution.fTransform f X - Distribution.fTransform f Y).support ⊆
        (X.support ∪ Y.support).image f := by
    intro b hb
    rcases Finset.mem_union.mp (Finsupp.support_sub hb) with h | h
    · exact himg X Finset.subset_union_left h
    · exact himg Y Finset.subset_union_right h
  rw [statDist_eq_sum_of_support_subset _ _ hsupp,
    statDist_eq_sum_of_support_subset X Y Finsupp.support_sub,
    ← Finset.sum_fiberwise_of_maps_to
      (fun a ha => Finset.mem_image_of_mem f ha) (fun a => max (X a - Y a) 0)]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [hval X Finset.subset_union_left b, hval Y Finset.subset_union_right b]
  refine max_le ?_ (Finset.sum_nonneg fun a _ => le_max_right _ _)
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun a _ => le_max_left _ _

/-! ### The extension refinement: run the ratio on a richer law

An *extension* of a law `P` is any law `P'` on a richer carrier that pushes
forward to `P`.  Data processing says a pushforward can only shrink the
distance, so the distance between the coarse laws is bounded by the distance
between any pair of extensions — and the ratio hypothesis may therefore be
checked on the richer carrier, where it is typically exactly computable
(reveal a key, a hash value, a fresh coordinate after the fact).

`statDist_fTransform_le` above is the inequality; these two lemmas are the
*shape* the technique uses it in, where the extensions are the data and the
projection identities are hypotheses rather than definitions.  This is what
makes them consumable by a technique layer that constructs its extensions
per environment.  Nothing here needs a finite carrier. -/

/-- **Extension along a common map.**  If `P` and `Q` are the pushforwards of
`P'` and `Q'` along one map `f`, then `δ(P, Q) ≤ δ(P', Q')`. -/
theorem statDist_le_of_fTransform_eq {A B : Type*}
    (P Q : Distribution A) (P' Q' : Distribution B) (f : B → A)
    (hP : Distribution.fTransform f P' = P) (hQ : Distribution.fTransform f Q' = Q) :
    statDist P Q ≤ statDist P' Q' := by
  rw [← hP, ← hQ]
  exact statDist_fTransform_le P' Q' f

/-- **Extension by side information** — the shape the H-technique uses:
revealing extra data `Z` after the fact can only increase the distance, so a
ratio proved on the extended laws bounds the distance between the originals.

  `π₁⋆P' = P  ∧  π₁⋆Q' = Q  ⟹  δ(P, Q) ≤ δ(P', Q')`. -/
theorem statDist_le_of_extension {A Z : Type*}
    (P Q : Distribution A) (P' Q' : Distribution (A × Z))
    (hP : Distribution.fTransform Prod.fst P' = P)
    (hQ : Distribution.fTransform Prod.fst Q' = Q) :
    statDist P Q ≤ statDist P' Q' :=
  statDist_le_of_fTransform_eq P Q P' Q' Prod.fst hP hQ

/-- Exact-on-good H-technique bounds are stable under common deterministic
post-processing.

This is the exact-agreement version of `hTechnique_ratio_fTransform`: prove
that real and ideal agree on good points of a richer finite law, then apply a
projection or any other deterministic map. -/
theorem hTechnique_eq_on_good_fTransform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (real ideal : Distribution A) (f : A → B)
    (Bad : A → Prop)
    (h_real_nonneg : real.NonNeg)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_eq : ∀ a, ¬ Bad a → real a = ideal a) :
    statDist (Distribution.fTransform f real) (Distribution.fTransform f ideal) ≤
      probBad ideal Bad := by
  exact le_trans
    (statDist_fTransform_le real ideal f)
    (hTechnique_eq_on_good real ideal Bad h_real_nonneg h_ideal_nonneg
      h_weight h_eq)

/-- Ratio-form H-technique bounds are stable under common deterministic
post-processing.

This is the generic data-processing step for richer observations: prove the
H-coefficient ratio on the richer finite law, then apply any deterministic
stripping map.  Nothing in the statement is specific to transcripts or product
carriers. -/
theorem hTechnique_ratio_fTransform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (real ideal : Distribution A) (f : A → B)
    (Bad : A → Prop)
    (eps : NNReal)
    (h_real_nonneg : real.NonNeg)
    (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ Bad a → (1 - eps) * ideal a ≤ real a) :
    statDist (Distribution.fTransform f real) (Distribution.fTransform f ideal) ≤
      probBad ideal Bad + eps := by
  exact le_trans
    (statDist_fTransform_le real ideal f)
    (hTechnique_ratio real ideal Bad eps h_real_nonneg h_ideal_nonneg
      h_weight h_ideal_le h_ratio)

/-- If Y = 0 on S and X ≤ Y pointwise on Sᶜ, then statDist(X, Y) = ∑_{S} X(a),
for a non-negative X.

This is the core pattern for "zero on bad, dominated on good" arguments in
switching-style proofs (e.g., PRP/PRF switching, CBC-MAC). -/
theorem statDist_eq_mass_on_zero_support {A : Type*} [Fintype A] [DecidableEq A]
    {X : Distribution A} (Y : Distribution A) (hX : X.NonNeg) (S : Finset A)
    (h_zero : ∀ a ∈ S, Y a = 0)
    (h_le : ∀ a ∉ S, X a ≤ Y a) :
    statDist X Y = ∑ a ∈ S, X a := by
  simp only [statDist_eq_sum_univ]
  rw [show ∑ a : A, max (X a - Y a) 0 =
      ∑ a ∈ S, max (X a - Y a) 0 + ∑ a ∈ Sᶜ, max (X a - Y a) 0 from by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]]
  have h_on_S : ∑ a ∈ S, max (X a - Y a) 0 = ∑ a ∈ S, X a := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [h_zero a ha, sub_zero, max_eq_left (hX a)]
  have h_on_Sc : ∑ a ∈ Sᶜ, max (X a - Y a) 0 = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact max_eq_right (sub_nonpos.mpr (h_le a (Finset.mem_compl.mp ha)))
  rw [h_on_S, h_on_Sc, add_zero]

/-- Compatibility alias: the owner is `Distribution.fTransform_injective_apply` in
`Probability.Distribution`.  Kept because several legacy application files reference
the unqualified `RandomSystems`-level name; retire with the legacy tree
cleanup. -/
theorem fTransform_injective_apply {A B : Type*} [Fintype A] [DecidableEq B]
    (X : Distribution A) (f : A → B) (hf : Function.Injective f) (a : A) :
    (Distribution.fTransform f X) (f a) = X a :=
  Distribution.fTransform_injective_apply X f hf a

/-- Lemma 3+ (Data processing equality for injective functions).

For any injective function f : A → B:
  δ(f(X), f(Y)) = δ(X, Y).

An injective function preserves statistical distance exactly (not just ≤).

**No `Fintype`, no `DecidableEq`** — as for `statDist` itself, requiring them
was a spurious restriction.  The `≤` half is the data processing inequality,
which never needed them; the `≥` half re-indexes the source sum along `f`,
which is a `Finset.sum_image` on the *support* of the difference and lands
inside any finite superset of the image law's own difference support.  The
generality is what lets the lemma reach the carriers this repository actually
uses — transcript spaces `List (X × Option Y)`, system laws
`Distribution (System.DDS X Y)` — where no `Fintype` exists. -/
theorem statDist_fTransform_injective {A B : Type*}
    (X Y : Distribution A) (f : A → B) (hf : Function.Injective f) :
    statDist (Distribution.fTransform f X) (Distribution.fTransform f Y) = statDist X Y := by
  classical
  refine le_antisymm (statDist_fTransform_le X Y f) ?_
  have himg : statDist X Y =
      ∑ b ∈ (X - Y).support.image f,
        max (Distribution.fTransform f X b - Distribution.fTransform f Y b) 0 := by
    rw [statDist, Finset.sum_image (fun a _ b _ h => hf h)]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Distribution.fTransform_injective_apply X f hf,
        Distribution.fTransform_injective_apply Y f hf]
  rw [himg,
    statDist_eq_sum_of_support_subset (Distribution.fTransform f X)
      (Distribution.fTransform f Y)
      (Finset.subset_union_left (s₂ := (X - Y).support.image f))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    fun b _ _ => le_max_right _ _

/-- UPSTREAM-CANDIDATE: adding a deterministic terminal component preserves
statistical distance exactly.

This is the conservative-extension test for terminal side-information
arguments: when the side-information variable is constant, the extended law is
isometric to the original law. -/
theorem statDist_fTransform_const_pair {A U : Type*} [Fintype A] [Fintype U]
    (X Y : Distribution A) (u : U) :
    statDist
        (Distribution.fTransform (fun a : A => (a, u)) X)
        (Distribution.fTransform (fun a : A => (a, u)) Y) =
      statDist X Y := by
  classical
  exact statDist_fTransform_injective X Y (fun a : A => (a, u))
    (fun _ _ h => congrArg Prod.fst h)

/-- UPSTREAM-CANDIDATE: adding deterministic terminal side information and
then projecting it away recovers the original statistical distance.

This is the conservative-extension regression for extended H-technique
arguments: when the terminal side-information variable is constant, the
projected extended law is exactly the original law. -/
theorem statDist_project_const_pair {A U : Type*} [Fintype A] [Fintype U]
    (X Y : Distribution A) (u : U) :
    statDist
        (Distribution.fTransform (fun p : A × U => p.1)
          (Distribution.fTransform (fun a : A => (a, u)) X))
        (Distribution.fTransform (fun p : A × U => p.1)
          (Distribution.fTransform (fun a : A => (a, u)) Y)) =
      statDist X Y := by
  rw [Distribution.fTransform_fst_const_pair, Distribution.fTransform_fst_const_pair]

/-- Statistical distance between product distributions with a shared left factor.

If `U` is a non-negative distribution on `A` and `X,Y` are distributions on
`B`, then:

`δ(U × X, U × Y) = |U| * δ(X, Y)`.

In particular, if `U` is a probability distribution (`|U| = 1`), then taking an
independent product with `U` does not change statistical distance. -/
theorem statDist_prod_left {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [DecidableEq A] [DecidableEq B]
    {U : Distribution A} (hU : U.NonNeg) (X Y : Distribution B) :
    statDist (Distribution.prod U X) (Distribution.prod U Y) = U.weight * statDist X Y := by
  classical
  -- Expand both `statDist`s and the shared weight `|U| = ∑ U`, then match the
  -- product distributions summand-by-summand (`prod_apply`).
  simp only [statDist_eq_sum_univ, Fintype.sum_prod_type]
  rw [Distribution.weight_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Distribution.prod_apply, Distribution.prod_apply, ← mul_sub,
    mul_max_of_nonneg _ _ (hU a), mul_zero]

/-! ### Additivity across disjoint cells (Lanzenberger Lemma 2.5)

`statDist_partition` above is Lemma 2.5 read on a `Fintype` carrier through an
explicit fibering map.  The form the attainment induction consumes is the
*family* form on an arbitrary carrier: two families of laws, each pair
supported inside its own cell of a pairwise disjoint system, and the distance
of the sums is the sum of the distances.

Unlike the quarry's `δ`-level statement, no non-negativity hypothesis appears:
`statDist` indexes its sum by `(X − Y).support` rather than by `X.support`, so
a cell where the first law vanishes and the second is negative contributes
nothing on either side, which is exactly the failure the `δ` form had to
exclude. -/

/-- **Lanzenberger Lemma 2.5 (family form)**: for families supported on
pairwise disjoint cells, statistical distance is additive,
`δ(∑ᵢ Xᵢ, ∑ᵢ Yᵢ) = ∑ᵢ δ(Xᵢ, Yᵢ)`. -/
theorem statDist_sum_of_disjoint_support {A ι : Type*} [DecidableEq A]
    {t : Finset ι} (Xf Yf : ι → Distribution A)
    (hdisj : (t : Set ι).PairwiseDisjoint
      fun i => (Xf i).support ∪ (Yf i).support) :
    statDist (∑ i ∈ t, Xf i) (∑ i ∈ t, Yf i) = ∑ i ∈ t, statDist (Xf i) (Yf i) := by
  classical
  -- Off the cells both sums vanish, so the whole distance lives on their union.
  have hcell : ∀ (Zf : ι → Distribution A),
      (∀ j, (Zf j).support ⊆ (Xf j).support ∪ (Yf j).support) →
      ∀ i ∈ t, ∀ a ∈ (Xf i).support ∪ (Yf i).support, (∑ j ∈ t, Zf j) a = Zf i a := by
    intro Zf hZ i hi a ha
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_single_of_mem i hi fun j hj hne => ?_
    refine Finsupp.notMem_support_iff.mp fun hmem => ?_
    exact Finset.disjoint_left.mp
      (hdisj (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) (Ne.symm hne))
      ha (hZ j hmem)
  have hsub : (∑ i ∈ t, Xf i - ∑ i ∈ t, Yf i).support
      ⊆ t.biUnion fun i => (Xf i).support ∪ (Yf i).support := by
    intro a ha
    rcases Finset.mem_union.mp (Finsupp.support_sub ha) with h | h
    · obtain ⟨i, hi, hia⟩ := Finset.mem_biUnion.mp
        (Finsupp.support_finset_sum h)
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_left _ hia⟩
    · obtain ⟨i, hi, hia⟩ := Finset.mem_biUnion.mp
        (Finsupp.support_finset_sum h)
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_right _ hia⟩
  rw [statDist_eq_sum_of_support_subset _ _ hsub, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [statDist_eq_sum_of_support_subset (Xf i) (Yf i)
    (Finsupp.support_sub.trans (Finset.union_subset_union
      (Finset.Subset.refl _) (Finset.Subset.refl _)))]
  exact Finset.sum_congr rfl fun a ha => by
    rw [hcell Xf (fun _ => Finset.subset_union_left) i hi a ha,
      hcell Yf (fun _ => Finset.subset_union_right) i hi a ha]

/-- The distance of two point masses at the **same** atom is the one-sided
excess of their weights.  This is the depth-zero leaf of the attainment
induction, where both systems have collapsed onto the nowhere-defined
deterministic system. -/
theorem statDist_single_single {A : Type*} (a : A) (p q : ℝ) :
    statDist (Finsupp.single a p) (Finsupp.single a q) = max (p - q) 0 := by
  classical
  have hsub : (Finsupp.single a p - Finsupp.single a q : Distribution A).support ⊆ {a} := by
    intro b hb
    rcases Finset.mem_union.mp (Finsupp.support_sub hb) with h | h <;>
      exact Finsupp.support_single_subset h
  rw [statDist_eq_sum_of_support_subset _ _ hsub, Finset.sum_singleton,
    Finsupp.single_eq_same, Finsupp.single_eq_same]

end Probability
