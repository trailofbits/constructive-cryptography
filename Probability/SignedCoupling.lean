import Probability.Coupling

noncomputable section

/-!
# Signed couplings and distribution differences

This module formalizes the signed-coupling theory of *Signed Couplings:
Distribution Differences as Proof Objects*, §§2–4.  A `Distribution` is already
real-valued in this library, so a signed coupling is represented by the existing
`IsCoupling`: only its two marginal equations are required.  Nonnegativity stays
an explicit hypothesis exactly where the source uses it.
-/

open scoped BigOperators

namespace Probability
namespace Distribution

/-- The off-diagonal `L¹` mass of a possibly signed joint distribution.

This is `offVar(J) = ∑_{a ≠ b} |J(a,b)|` from *Signed Couplings:
Distribution Differences as Proof Objects*, §2 (printed page to be fixed after
source pagination is checked). -/
def offVar {A : Type*} (J : Distribution (A × A)) : ℝ := by
  classical
  exact ∑ x ∈ J.support, if x.1 ≠ x.2 then |J x| else 0

/-- The negative part of the signed off-diagonal mass.

This is `offDiagNeg(J) = ∑_{a ≠ b} max(-J(a,b),0)` from *Signed Couplings:
Distribution Differences as Proof Objects*, §2 (printed page to be fixed). -/
def offDiagonalNeg {A : Type*} (J : Distribution (A × A)) : ℝ := by
  classical
  exact ∑ x ∈ J.support, if x.1 ≠ x.2 then (-J x)⁺ else 0

/-- **Signed Coupling Lemma.** Marginal equations alone bound statistical
 distance by off-diagonal `L¹` mass; no positivity hypothesis occurs.

Source: *Signed Couplings: Distribution Differences as Proof Objects*, Signed
Coupling Lemma, §2 (printed page to be fixed). -/
theorem statDist_le_offVar {A : Type*} {J : Distribution (A × A)}
    {X Y : Distribution A} (hJ : IsCoupling J X Y) :
    statDist X Y ≤ offVar J := by
  classical
  obtain ⟨hfst, hsnd⟩ := hJ
  let P : A → Prop := fun a => Y a < X a
  letI : DecidablePred P := Classical.decPred P
  -- Statistical distance is the signed mass of the points on which `X`
  -- exceeds `Y`; points with nonpositive difference contribute zero.
  have hdist : statDist X Y = (X - Y).mass P := by
    unfold statDist Distribution.mass
    apply Finset.sum_congr rfl
    intro a _
    change max (X a - Y a) 0 = if P a then X a - Y a else 0
    by_cases ha : P a
    · rw [if_pos ha, max_eq_left (sub_nonneg.mpr ha.le)]
    · rw [if_neg ha, max_eq_right (sub_nonpos.mpr (not_lt.mp ha))]
  -- Linearity turns that mass into the gap between the two marginal event
  -- masses, and the coupling equations pull both events back to `J`.
  have hmass : (X - Y).mass P =
      J.mass (fun p => P p.1) - J.mass (fun p => P p.2) := by
    calc
      (X - Y).mass P =
          (X - Y).expect (fun a => if P a then (1 : ℝ) else 0) :=
        (Distribution.expect_indicator (X - Y) P).symm
      _ = X.expect (fun a => if P a then (1 : ℝ) else 0) -
          Y.expect (fun a => if P a then (1 : ℝ) else 0) := by
        rw [Distribution.expect_sub_left]
      _ = X.mass P - Y.mass P := by
        rw [Distribution.expect_indicator, Distribution.expect_indicator]
      _ = J.mass (fun p => P p.1) - J.mass (fun p => P p.2) := by
        rw [← hfst, ← hsnd, Distribution.mass_fTransform,
          Distribution.mass_fTransform]
  rw [hdist, hmass]
  -- After expanding the two pulled-back events, each joint atom has
  -- coefficient `0`, `1`, or `-1`.  A nonzero coefficient forces the atom
  -- off the diagonal, where its contribution is bounded by its absolute mass.
  rw [← Distribution.expect_indicator J (fun p => P p.1),
    ← Distribution.expect_indicator J (fun p => P p.2),
    ← Distribution.expect_sub_right]
  unfold Distribution.expect offVar
  refine Finset.sum_le_sum fun p hp => ?_
  by_cases h₁ : P p.1 <;> by_cases h₂ : P p.2
  · by_cases hdiag : p.1 = p.2 <;> simp [h₁, h₂, hdiag, abs_nonneg]
  · have hne : p.1 ≠ p.2 := fun heq => h₂ (heq ▸ h₁)
    simpa [h₁, h₂, hne] using le_abs_self (J p)
  · have hne : p.1 ≠ p.2 := fun heq => h₁ (heq ▸ h₂)
    simpa [h₁, h₂, hne] using neg_le_abs (J p)
  · by_cases hdiag : p.1 = p.2 <;> simp [h₁, h₂, hdiag, abs_nonneg]

/-- A machine-checked `2 × 2` witness showing that the naïve signed bound by
`offDiagonalMass` is false.

Source: *Signed Couplings: Distribution Differences as Proof Objects*, §2,
the `X=(1,0)`, `Y=(0,1)`, `J=[[1/2,1/2],[-1/2,1/2]]` example (printed page to
be fixed). -/
theorem exists_signedCoupling_offDiagonalMass_lt_statDist :
    ∃ (J : Distribution (Fin 2 × Fin 2)) (X Y : Distribution (Fin 2)),
      IsCoupling J X Y ∧ offDiagonalMass J = 0 ∧ statDist X Y = 1 := by
  let J : Distribution (Fin 2 × Fin 2) :=
    Finsupp.single (0, 0) (1 / 2 : ℝ) +
      Finsupp.single (0, 1) (1 / 2 : ℝ) +
      Finsupp.single (1, 0) (-1 / 2 : ℝ) +
      Finsupp.single (1, 1) (1 / 2 : ℝ)
  let X : Distribution (Fin 2) := Finsupp.single 0 1
  let Y : Distribution (Fin 2) := Finsupp.single 1 1
  refine ⟨J, X, Y, ?_, ?_, ?_⟩
  · constructor <;> ext a <;> fin_cases a <;>
      rw [Distribution.fTransform_apply_eq_sum, Finset.sum_filter,
        Fintype.sum_prod_type] <;>
      simp_rw [Fin.sum_univ_two] <;>
      norm_num [J, X, Y, Finsupp.equivFunOnFinite]
  · rw [offDiagonalMass_eq_sum_filter J (Finset.subset_univ J.support),
      Finset.sum_filter, Fintype.sum_prod_type]
    simp_rw [Fin.sum_univ_two]
    norm_num [J, Finsupp.equivFunOnFinite]
  · rw [statDist_eq_sum_univ, Fin.sum_univ_two]
    norm_num [X, Y, Finsupp.equivFunOnFinite]

/-- The penalty form of the Signed Coupling Lemma.

It uses `|x| = x + 2 max(-x,0)` and therefore charges negative off-diagonal
mass exactly twice.  Source: *Signed Couplings: Distribution Differences as
Proof Objects*, Penalty Corollary, §2 (printed page to be fixed). -/
theorem statDist_le_offDiagonalMass_add_two_mul_offDiagonalNeg
    {A : Type*} {J : Distribution (A × A)} {X Y : Distribution A}
    (hJ : IsCoupling J X Y) :
    statDist X Y ≤ offDiagonalMass J + 2 * offDiagonalNeg J := by
  calc
    statDist X Y ≤ offVar J := statDist_le_offVar hJ
    _ = offDiagonalMass J + 2 * offDiagonalNeg J := by
      classical
      rw [offDiagonalMass_eq_sum_filter J (Finset.Subset.refl J.support)]
      unfold offVar offDiagonalNeg
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hne : p.1 ≠ p.2
      · simp only [if_pos hne]
        by_cases hmass : 0 ≤ J p
        · simp [abs_of_nonneg hmass, hmass]
        · have hmass' : J p ≤ 0 := le_of_not_ge hmass
          rw [abs_of_nonpos hmass']
          rw [posPart_of_nonneg (neg_nonneg.mpr hmass')]
          ring
      · simp [hne]

/-- **Free Diagonal.** An off-diagonally nonnegative signed coupling satisfies
 the classical coupling bound, with no restriction on its diagonal entries.

Source: *Signed Couplings: Distribution Differences as Proof Objects*, Free
Diagonal Proposition, §2, printed page 2. -/
theorem statDist_le_offDiagonalMass_of_offDiagonal_nonNeg
    {A : Type*} {J : Distribution (A × A)} {X Y : Distribution A}
    (hJ : IsCoupling J X Y)
    (hoff : ∀ a b, a ≠ b → 0 ≤ J (a, b)) :
    statDist X Y ≤ offDiagonalMass J := by
  calc
    statDist X Y ≤ offVar J := statDist_le_offVar hJ
    _ = offDiagonalMass J := by
      classical
      rw [offDiagonalMass_eq_sum_filter J (Finset.Subset.refl J.support)]
      unfold offVar
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hne : p.1 ≠ p.2
      · simp [hne, abs_of_nonneg (hoff p.1 p.2 hne)]
      · simp [hne]

/-- The `L¹` norm of the signed mass function of a distribution. -/
def l1Norm {A : Type*} (D : Distribution A) : ℝ :=
  ∑ a ∈ D.support, |D a|

/-- Equal-weight statistical distance is one half of the support-finite signed
`L¹` difference.

Lanzenberger--Maurer, Definition 3 (printed p. 9), states: “for distributions
of the same weight ... `δ(X,Y) = 1/2 ∑ₐ |X(a)-Y(a)|`.”  Unlike the existing
finite-carrier form, this statement sums over the finite support of `X - Y`,
so it applies directly to transcript and deterministic-system carriers. -/
theorem statDist_eq_half_l1Norm_of_weight_eq {A : Type*}
    (X Y : Distribution A) (hw : X.weight = Y.weight) :
    statDist X Y = (1 / 2 : ℝ) * l1Norm (X - Y) := by
  classical
  have hs : (Y - X).support ⊆ (X - Y).support := by
    intro a ha
    by_contra hnot
    have hzero : X a - Y a = 0 := by
      simpa using Finsupp.notMem_support_iff.mp hnot
    have hzero' : Y a - X a = 0 := by linarith
    exact (Finsupp.mem_support_iff.mp ha) (by simpa using hzero')
  have hsum : statDist X Y + statDist Y X = l1Norm (X - Y) := by
    rw [statDist, statDist_eq_sum_of_support_subset Y X hs]
    unfold l1Norm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simpa only [Finsupp.sub_apply, neg_sub] using
      max_zero_add_max_neg_zero_eq_abs_self (X a - Y a)
  have hsymm := statDist_symm_of_eq_weight X Y hw
  linarith

/-- **Weight-Zero Pairing.** Pairing a zero-weight signed distribution with a
`[0,1]`-valued test costs at most half its `L¹` norm.

Source: *Signed Couplings: Distribution Differences as Proof Objects*,
Weight-Zero Pairing Lemma, §3 (printed page to be fixed). -/
theorem abs_sum_mul_le_half_l1Norm_of_weight_eq_zero {A : Type*}
    (D : Distribution A) (f : A → ℝ) (hw : D.weight = 0)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    |∑ a ∈ D.support, f a * D a| ≤ (1 / 2 : ℝ) * l1Norm D := by
  -- Recenter the test at `1/2`; the constant term vanishes because the
  -- signed distribution has weight zero.
  have hcenter : D.expect f = D.expect (fun a => f a - (1 / 2 : ℝ)) := by
    rw [Distribution.expect_sub_right, Distribution.expect_const, hw]
    norm_num
  have hexpect (g : A → ℝ) :
      (∑ a ∈ D.support, g a * D a) = D.expect g := by
    rw [Distribution.expect_eq_sum_of_support_subset D g (by rfl)]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_comm]
  rw [hexpect f, hcenter, ← hexpect (fun a => f a - (1 / 2 : ℝ))]
  unfold l1Norm
  calc
    |∑ a ∈ D.support, (f a - (1 / 2 : ℝ)) * D a| ≤
        ∑ a ∈ D.support, |(f a - (1 / 2 : ℝ)) * D a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ D.support, (1 / 2 : ℝ) * |D a| := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg (D a))
      rw [abs_le]
      constructor <;> linarith [hf0 a, hf1 a]
    _ = (1 / 2 : ℝ) * ∑ a ∈ D.support, |D a| := by
      rw [Finset.mul_sum]

/-- **Signed Data Processing.** A positive linear channel that does not
increase the weight of nonnegative inputs contracts the signed `L¹` norm.
Weight-nonincreasing, rather than weight-preserving, deliberately covers
sub-stochastic filters.

Source: *Signed Couplings: Distribution Differences as Proof Objects*, Signed
Data Processing Theorem, §3 (printed page to be fixed). -/
theorem l1Norm_map_le {A B : Type*} (F : Distribution A →ₗ[ℝ] Distribution B)
    (hpos : ∀ P, P.NonNeg → (F P).NonNeg)
    (hweight : ∀ P, P.NonNeg → (F P).weight ≤ P.weight)
    (D : Distribution A) :
    l1Norm (F D) ≤ l1Norm D := by
  classical
  have l1Norm_eq_weight_of_nonNeg (P : Distribution B) (hP : P.NonNeg) :
      l1Norm P = P.weight := by
    unfold l1Norm Distribution.weight
    apply Finset.sum_congr rfl
    intro c _
    rw [abs_of_nonneg (hP c)]
  have l1Norm_sub_le (P Q : Distribution B) :
      l1Norm (P - Q) ≤ l1Norm P + l1Norm Q := by
    let U := P.support ∪ Q.support
    have hsupp : (P - Q).support ⊆ U := by
      intro b hb
      by_contra hnot
      simp only [U, Finset.mem_union, not_or] at hnot
      have hP0 : P b = 0 := Finsupp.notMem_support_iff.mp hnot.1
      have hQ0 : Q b = 0 := Finsupp.notMem_support_iff.mp hnot.2
      simp [hP0, hQ0] at hb
    have hPsum : ∑ b ∈ U, |P b| = l1Norm P := by
      unfold l1Norm
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro b _ hbP
      simp [Finsupp.notMem_support_iff.mp hbP]
    have hQsum : ∑ b ∈ U, |Q b| = l1Norm Q := by
      unfold l1Norm
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro b _ hbQ
      simp [Finsupp.notMem_support_iff.mp hbQ]
    calc
      l1Norm (P - Q) = ∑ b ∈ (P - Q).support, |P b - Q b| := by
        rfl
      _ ≤ ∑ b ∈ (P - Q).support, (|P b| + |Q b|) := by
        apply Finset.sum_le_sum
        intro b _
        exact abs_sub (P b) (Q b)
      _ ≤ ∑ b ∈ U, (|P b| + |Q b|) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsupp
        intro b _ _
        positivity
      _ = l1Norm P + l1Norm Q := by
        rw [Finset.sum_add_distrib, hPsum, hQsum]
  have hposSupp : D⁺.support ⊆ D.support := by
    intro a ha
    by_contra hnot
    have hzero : D a = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hzero] at ha
  have hnegSupp : D⁻.support ⊆ D.support := by
    intro a ha
    by_contra hnot
    have hzero : D a = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hzero] at ha
  have hJordan : (D⁺).weight + (D⁻).weight = l1Norm D := by
    rw [Distribution.weight_eq_sum_of_support_subset D⁺ hposSupp,
      Distribution.weight_eq_sum_of_support_subset D⁻ hnegSupp]
    unfold l1Norm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simpa only [Distribution.posPart_apply, Distribution.negPart_apply] using
      (max_zero_add_max_neg_zero_eq_abs_self (D a))
  -- Split the signed input into its positive and negative parts.
  calc
    l1Norm (F D) = l1Norm (F (D⁺ - D⁻)) := by
      rw [posPart_sub_negPart]
    _ = l1Norm (F D⁺ - F D⁻) := by
      rw [LinearMap.map_sub]
    _ ≤ l1Norm (F D⁺) + l1Norm (F D⁻) := l1Norm_sub_le _ _
    _ = (F D⁺).weight + (F D⁻).weight := by
      congr 1
      · exact l1Norm_eq_weight_of_nonNeg _
          (hpos _ (Distribution.nonNeg_posPart D))
      · exact l1Norm_eq_weight_of_nonNeg _
          (hpos _ (Distribution.nonNeg_negPart D))
    _ ≤ (D⁺).weight + (D⁻).weight :=
      add_le_add (hweight _ (Distribution.nonNeg_posPart D))
        (hweight _ (Distribution.nonNeg_negPart D))
    _ = l1Norm D := hJordan
/-- Pushforward as a linear channel on the signed distribution carrier.

This is a modeling adapter, not a second pushforward operation: its function is
exactly `Distribution.fTransform`, packaged so Signed Data Processing can be
applied without rebuilding linearity at every observation. -/
def fTransformLinear {A B : Type*} (f : A → B) :
    Distribution A →ₗ[ℝ] Distribution B where
  toFun := fTransform f
  map_add' := fTransform_add f
  map_smul' := fTransform_smul f

@[simp]
theorem fTransformLinear_apply {A B : Type*} (f : A → B)
    (D : Distribution A) : fTransformLinear f D = fTransform f D := rfl

/-- Deterministic pushforward contracts signed `L¹`.

This is the `fTransform` instance of Signed Data Processing: pushforward is
positive (`NonNeg.fTransform`) and exactly weight-preserving
(`weight_fTransform`). -/
theorem l1Norm_fTransform_le {A B : Type*} (f : A → B)
    (D : Distribution A) : l1Norm (fTransform f D) ≤ l1Norm D := by
  exact l1Norm_map_le (fTransformLinear f)
    (fun P hP => hP.fTransform f)
    (fun P _ => (weight_fTransform f P).le) D

/-- Restriction to an event as a linear sub-stochastic channel.

The underlying operation is the existing `Distribution.restrict` (implemented
by `Finsupp.filter`).  Its output weight is the retained event mass, hence is
nonincreasing on nonnegative inputs. -/
noncomputable def restrictLinear {A : Type*} (P : A → Prop) :
    Distribution A →ₗ[ℝ] Distribution A where
  toFun := fun D => D.restrict P
  map_add' := by
    intro D E
    apply Finsupp.ext
    intro a
    by_cases ha : P a <;> simp [Distribution.restrict_apply, ha]
  map_smul' := by
    intro c D
    apply Finsupp.ext
    intro a
    by_cases ha : P a <;> simp [Distribution.restrict_apply, ha]

@[simp]
theorem restrictLinear_apply {A : Type*} (P : A → Prop) (D : Distribution A) :
    restrictLinear P D = D.restrict P := rfl

/-- Filtering/restriction contracts signed `L¹`; this is the sub-stochastic
case motivating the weight-nonincreasing hypothesis in Signed Data Processing. -/
theorem l1Norm_restrict_le {A : Type*} (P : A → Prop) (D : Distribution A) :
    l1Norm (D.restrict P) ≤ l1Norm D := by
  exact l1Norm_map_le (restrictLinear P)
    (fun Q hQ => hQ.restrict P)
    (fun Q hQ => (Distribution.weight_restrict Q P).le.trans
      (Distribution.mass_le_weight hQ P)) D


/-- Telescoping in signed `L¹`: hybrid arguments require only the triangle
inequality, not coupling composition.

Source: *Signed Couplings: Distribution Differences as Proof Objects*,
Telescoping Corollary, §3 (printed page to be fixed). -/
theorem l1Norm_sub_le_sum_range {A : Type*} {n : Nat}
    (X : Fin (n + 1) → Distribution A) :
    l1Norm (X 0 - X (Fin.last n)) ≤
      ∑ i : Fin n, l1Norm (X i.castSucc - X i.succ) := by
  classical
  have l1Norm_add_le (P Q : Distribution A) :
      l1Norm (P + Q) ≤ l1Norm P + l1Norm Q := by
    let U := P.support ∪ Q.support
    have hsupp : (P + Q).support ⊆ U := by
      intro a ha
      by_contra hnot
      simp only [U, Finset.mem_union, not_or] at hnot
      have hP0 : P a = 0 := Finsupp.notMem_support_iff.mp hnot.1
      have hQ0 : Q a = 0 := Finsupp.notMem_support_iff.mp hnot.2
      simp [hP0, hQ0] at ha
    have hPsum : ∑ a ∈ U, |P a| = l1Norm P := by
      unfold l1Norm
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro a _ ha
      simp [Finsupp.notMem_support_iff.mp ha]
    have hQsum : ∑ a ∈ U, |Q a| = l1Norm Q := by
      unfold l1Norm
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro a _ ha
      simp [Finsupp.notMem_support_iff.mp ha]
    calc
      l1Norm (P + Q) = ∑ a ∈ (P + Q).support, |P a + Q a| := by rfl
      _ ≤ ∑ a ∈ (P + Q).support, (|P a| + |Q a|) := by
        apply Finset.sum_le_sum
        intro a _
        exact abs_add_le (P a) (Q a)
      _ ≤ ∑ a ∈ U, (|P a| + |Q a|) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsupp
        intro a _ _
        positivity
      _ = l1Norm P + l1Norm Q := by
        rw [Finset.sum_add_distrib, hPsum, hQsum]
  have l1Norm_sum_le (s : Finset (Fin n)) (D : Fin n → Distribution A) :
      l1Norm (∑ i ∈ s, D i) ≤ ∑ i ∈ s, l1Norm (D i) := by
    induction s using Finset.induction_on with
    | empty => simp [l1Norm]
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        exact (l1Norm_add_le _ _).trans (add_le_add (le_refl _) ih)
  let Y : Nat → Distribution A := fun k =>
    if h : k < n + 1 then X ⟨k, h⟩ else 0
  have htel :
      (∑ i : Fin n, (X i.castSucc - X i.succ)) = X 0 - X (Fin.last n) := by
    calc
      (∑ i : Fin n, (X i.castSucc - X i.succ)) =
          ∑ i : Fin n, (Y i - Y (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi0 : (i : Nat) < n + 1 := by omega
        have hi1 : (i : Nat) + 1 < n + 1 := by omega
        simp only [Y, dif_pos hi0, dif_pos hi1]
        congr 1
      _ = ∑ k ∈ Finset.range n, (Y k - Y (k + 1)) :=
        Fin.sum_univ_eq_sum_range (fun k => Y k - Y (k + 1)) n
      _ = Y 0 - Y n := Finset.sum_range_sub' Y n
      _ = X 0 - X (Fin.last n) := by
        simp [Y, Fin.last]
  rw [← htel]
  exact l1Norm_sum_le Finset.univ fun i => X i.castSucc - X i.succ

/-- The library's explicit `optimalJoint` minimizes `offVar` even among signed
couplings.  Nonnegativity is assumed only for the endpoint distributions, in
order to interpret the explicit witness as nonnegative.

Source: *Signed Couplings: Distribution Differences as Proof Objects*,
Optimal Couplings Proposition, §4 (printed page to be fixed). -/
theorem offVar_optimalJoint_le {A : Type*} {X Y : Distribution A}
    (hX : X.NonNeg) (hY : Y.NonNeg) (hw : X.weight = Y.weight)
    (J : Distribution (A × A)) (hJ : IsCoupling J X Y) :
    offVar (optimalJoint X Y) ≤ offVar J := by
  have hopt : (optimalJoint X Y).NonNeg := optimalJoint_nonNeg hX hY
  have hoffVar_eq : offVar (optimalJoint X Y) =
      offDiagonalMass (optimalJoint X Y) := by
    classical
    rw [offDiagonalMass_eq_sum_filter _
      (Finset.Subset.refl (optimalJoint X Y).support)]
    unfold offVar
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hne : p.1 ≠ p.2
    · simp [hne, abs_of_nonneg (hopt p)]
    · simp [hne]
  calc
    offVar (optimalJoint X Y) = offDiagonalMass (optimalJoint X Y) := hoffVar_eq
    _ = statDist X Y := offDiagonalMass_optimalJoint hw
    _ ≤ offVar J := statDist_le_offVar hJ

end Distribution
end Probability
