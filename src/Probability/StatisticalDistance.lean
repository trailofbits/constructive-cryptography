import Probability.Distribution
import Probability.Expectation
import Mathlib.Algebra.Order.Sub.Basic

/-!
# Statistical distance

The statistical distance `δ(X, Y) = ∑ₐ max (X(a) − Y(a), 0)`. Source:
Lanzenberger–Maurer, *Coupling of Random Systems*, Definition 3, Lemmas 2 and 3.

## Main definitions

* `statDist X Y`: the statistical distance `δ(X, Y)`
* `avgSuccessProb X Y g`: the success probability of the test `g` in telling
  `X` from `Y` under a uniform prior
* `probBad D B`: the mass of a bad event, for H-coefficient bounds

## Main results

* `statDist_nonneg`, `statDist_self`, `statDist_symm_of_eq_weight`,
  `statDist_triangle`, `statDist_le_weight`
* equivalent forms: `statDist_eq_weight_sub_sum_min`,
  `statDist_eq_half_sum_abs_of_weight_eq`, `statDist_eq_mass_sub_mass_pos`
* event gaps: `mass_sub_mass_le_statDist`; expectation gaps:
  `abs_expect_sub_expect_le_mul_statDist`
* the optimal-test identity `sSup_avgSuccessProb_eq_half_add_half_statDist`
* the H-coefficient bound `statDist_le_probBad_add_of_ratio_on_good`
* `statDist_partition` (Lemma 2), `statDist_fTransform_le` (Lemma 3, data
  processing), `statDist_fTransform_injective`, `statDist_sum_of_disjoint_support`
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

/-! ### Definition and basic properties -/

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

/-- On a `Fintype` carrier, `statDist` is the sum over all points. -/
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
  Finset.sum_nonneg fun _ _ => le_max_right _ _

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
  have : DecidableEq A := Classical.decEq A
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

/-! ### Alternative forms of statistical distance -/

/-- **Min form of statistical distance on an arbitrary carrier**
(LanMau20 Definition 3, second form; **MaPiRe07 equation (3), printed p. 140**,
used in the proof of their Lemma 5): `δ(P,Q) = |P| − ∑ min(P,Q)`, the sum taken
over any finite set containing both supports.

`Distribution` is `A →₀ ℝ`, so finite support is already in the carrier and no
`Fintype A` is needed; the `[Fintype]` form below is the instance at
`s = Finset.univ`.  The carriers that force the general form are the genuinely
infinite ones — transcript spaces `List (X × Option Y)`, system laws
`Distribution (DDS X Y)`; this is the companion of
`statDist_eq_sum_of_support_subset` and
`Distribution.weight_eq_sum_of_support_subset` one level up.

Like the `Fintype` form it needs neither non-negativity nor equal weight: the
pointwise lattice identity `max (x − y) 0 = x − min x y` is all it uses.  The
asymmetry the paper notes for unequal weight is visible — the right-hand side
carries `|P|`, not `|Q|`. -/
theorem statDist_eq_weight_sub_sum_min_of_support_subset {A : Type*}
    (P Q : Distribution A) {s : Finset A} (hP : P.support ⊆ s)
    (hQ : Q.support ⊆ s) :
    statDist P Q = P.weight - ∑ a ∈ s, min (P a) (Q a) := by
  have : DecidableEq A := Classical.decEq A
  have hsub : (P - Q).support ⊆ s := fun a ha => by
    rcases Finset.mem_union.mp (Finsupp.support_sub ha) with h | h
    · exact hP h
    · exact hQ h
  rw [statDist_eq_sum_of_support_subset P Q hsub]
  have key : ∀ a : A, max (P a - Q a) 0 = P a - min (P a) (Q a) := by
    intro a
    rcases le_total (P a) (Q a) with h | h
    · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h, sub_self]
    · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h]
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_sub_distrib,
    ← Distribution.weight_eq_sum_of_support_subset P hP]

/-- The `Fintype` instance of the min form: take `s = Finset.univ`. -/
theorem statDist_eq_weight_sub_sum_min {A : Type*} [Fintype A] (X Y : Distribution A) :
    statDist X Y = X.weight - ∑ a : A, min (X a) (Y a) :=
  statDist_eq_weight_sub_sum_min_of_support_subset X Y
    (fun a _ => Finset.mem_univ a) (fun a _ => Finset.mem_univ a)

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
  have : DecidableEq A := Classical.decEq A
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

/-- Statistical distance is bounded by total weight (for non-negative laws).

`δ(X, Y) ≤ |X|`.

No `Fintype`: both sides are read on `X.support ∪ Y.support`, which already
covers the difference's support.  The generality is what lets the bound reach
the carriers the random-systems layer uses, where no `Fintype` exists. -/
theorem statDist_le_weight {A : Type*}
    {X Y : Distribution A} (hX : X.NonNeg) (hY : Y.NonNeg) :
    statDist X Y ≤ X.weight := by
  have : DecidableEq A := Classical.decEq A
  rw [statDist_eq_sum_of_support_subset X Y Finsupp.support_sub,
    Distribution.weight_eq_sum_of_support_subset X Finset.subset_union_left
      (s := X.support ∪ Y.support)]
  apply Finset.sum_le_sum
  intro a _
  exact max_le (sub_le_self _ (hY a)) (hX a)

/-- **Event-mass bound by statistical distance.**
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

/-- **Real-valued event-mass bound by statistical distance.**
This is the real-valued form of `mass_tsub_mass_le_statDist`. -/
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
triangle inequality, and it is why no weight or `Fintype` hypothesis appears. -/
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

/-! ### The distance/expectation bridge -/

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
the first distribution is heavier. This is the canonical binary hypothesis
test induced by the two laws. Finite supports suffice even when the sample
carrier itself is infinite. -/
theorem statDist_eq_mass_sub_mass_pos {A : Type*}
    (X Y : Distribution A) :
    (statDist X Y : ℝ) =
      (X.mass (fun a => Y a < X a) : ℝ) -
        (Y.mass (fun a => Y a < X a) : ℝ) := by
  classical
  rw [statDist_eq_sum_of_support_subset X Y Finsupp.support_sub,
    Distribution.mass_eq_sum_of_support_subset X
      (s := X.support ∪ Y.support) Finset.subset_union_left,
    Distribution.mass_eq_sum_of_support_subset Y
      (s := X.support ∪ Y.support) Finset.subset_union_right,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : Y a < X a
  · rw [if_pos h, if_pos h, max_eq_left (sub_nonneg.mpr h.le)]
  · rw [if_neg h, if_neg h, max_eq_right (sub_nonpos.mpr (not_lt.mp h))]
    simp

/-! ### The optimal-test identity -/

/-- Success probability of the **binary hypothesis test** `g` at identifying
the source of a sample drawn from `X` or `Y` with equal prior ½: with
probability ½ the sample is drawn from `X` and the answer is correct iff `g`
answers `true`, with probability ½ it is drawn from `Y` and the answer is
correct iff `g` answers `false`.  Meaningful as a probability when `X` and `Y`
are probability distributions; defined for arbitrary signed distributions.

This is hypothesis testing rather than value guessing: it
decides *which of two hypotheses* produced the sample; the different task of
recovering an unknown *value* from correlated side information is
`Distribution.guessProb` / `Distribution.condGuessProb` (`Probability/Entropy.lean`), the
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

/-- A one-sided ratio lower bound controls the pointwise deficit. -/
theorem sub_le_mul_of_one_sub_mul_le {a b eps : ℝ}
    (h_lower : (1 - eps) * b ≤ a) :
    b - a ≤ eps * b := by
  nlinarith [h_lower]

/-! ### H-coefficient bound -/

/-- The mass of the bad event `B` under distribution `D`. -/
noncomputable def probBad {A : Type*}
    (D : Distribution A) (B : A → Prop) :
    ℝ :=
  D.mass B

/-- Adding deterministic terminal side information does
not change the mass of a bad event that ignores that terminal component. -/
@[simp]
theorem probBad_const_pair {A U : Type*}
    (D : Distribution A) (B : A → Prop) (u : U) :
    probBad (Distribution.fTransform (fun a : A => (a, u)) D)
        (fun p : A × U => B p.1) =
      probBad D B := by
  unfold probBad
  rw [Distribution.mass_fTransform]

/-- **The H-technique ratio bound on an arbitrary carrier.**  If the
real/ideal density ratio is at least `1 - eps` on good points then
`δ(real, ideal) ≤ Pr_ideal[Bad] + eps`.

`Distribution` is `A →₀ ℝ`: the sums run over
`(ideal - real).support ∪ ideal.support`, so no finiteness of the carrier is
used, and `hTechnique_ratio` below is the `[Fintype]` instance.  The carrier
that forces the general form is the transcript space
`List (X × Option Y)`, which is infinite even for finite alphabets — see
`RandomSystems/Technique/HCoefficient.lean`, whose endpoints all consume this
form. -/
theorem statDist_le_probBad_add_of_ratio_on_good {A : Type*}
    (real ideal : Distribution A) (Bad : A → Prop) (eps : ℝ≥0)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ Bad a → (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ probBad ideal Bad + eps := by
  classical
  set s : Finset A := (ideal - real).support ∪ ideal.support with hs
  have hsub : (ideal - real).support ⊆ s := Finset.subset_union_left
  have hsupp : ideal.support ⊆ s := Finset.subset_union_right
  rw [statDist_symm_of_eq_weight real ideal h_weight,
    statDist_eq_sum_of_support_subset ideal real hsub]
  have hterm : ∀ a ∈ s,
      max (ideal a - real a) 0 ≤ (if Bad a then ideal a else 0) + eps * ideal a := by
    intro a _
    by_cases hbad : Bad a
    · have h0 := h_ideal_nonneg a
      have h1 := h_real_nonneg a
      have h2 : 0 ≤ (eps : ℝ) * ideal a :=
        mul_nonneg eps.coe_nonneg (h_ideal_nonneg a)
      simp only [hbad, if_true]
      exact max_le (by linarith) (by linarith)
    · simp only [hbad, if_false, zero_add]
      exact max_le (sub_le_mul_of_one_sub_mul_le (h_ratio a hbad))
        (mul_nonneg eps.coe_nonneg (h_ideal_nonneg a))
  calc ∑ a ∈ s, max (ideal a - real a) 0
      ≤ ∑ a ∈ s, ((if Bad a then ideal a else 0) + (eps : ℝ) * ideal a) :=
        Finset.sum_le_sum hterm
    _ = (∑ a ∈ s.filter Bad, ideal a) + (eps : ℝ) * ∑ a ∈ s, ideal a := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter]
    _ = probBad ideal Bad + (eps : ℝ) * ideal.weight := by
        rw [probBad, Distribution.mass_eq_sum_of_support_subset ideal hsupp,
          Distribution.weight_eq_sum_of_support_subset ideal hsupp]
    _ ≤ probBad ideal Bad + eps := by
        have : (eps : ℝ) * ideal.weight ≤ (eps : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left h_ideal_le eps.coe_nonneg
        linarith

/-! ### Partition and data processing -/

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
  have : DecidableEq A := Classical.decEq A
  have : DecidableEq B := Classical.decEq B
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

/-! ### Injective pushforward -/

/-- Lemma 3+ (Data processing equality for injective functions).

For any injective function f : A → B:
  δ(f(X), f(Y)) = δ(X, Y).

An injective function preserves statistical distance exactly (not just ≤).

**No `Fintype`, no `DecidableEq`** — as for `statDist` itself, requiring them
was a spurious restriction.  The `≤` half is the data processing inequality,
which never needed them; the `≥` half re-indexes the source sum along `f`,
which is a `Finset.sum_image` on the *support* of the difference and lands
inside any finite superset of the image law's own difference support.  The
generality lets the lemma apply to infinite carriers such as transcript spaces
`List (X × Option Y)` and system laws
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

/-! ### Additivity across disjoint cells (Lanzenberger Lemma 2.5) -/

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
    rw [Finsupp.finsetSum_apply]
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
        (Finsupp.support_finsetSum h)
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_left _ hia⟩
    · obtain ⟨i, hi, hia⟩ := Finset.mem_biUnion.mp
        (Finsupp.support_finsetSum h)
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_right _ hia⟩
  rw [statDist_eq_sum_of_support_subset _ _ hsub, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [statDist_eq_sum_of_support_subset (Xf i) (Yf i)
    (Finsupp.support_sub.trans (Finset.union_subset_union
      (Finset.Subset.refl _) (Finset.Subset.refl _)))]
  exact Finset.sum_congr rfl fun a ha => by
    rw [hcell Xf (fun _ => Finset.subset_union_left) i hi a ha,
      hcell Yf (fun _ => Finset.subset_union_right) i hi a ha]

end Probability
