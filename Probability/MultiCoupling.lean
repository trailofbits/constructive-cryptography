/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Coupling

/-!
# Multi-law couplings: the `n`-ary maximal coupling and Lanzenberger Lemma 2.30

The distribution-level layer under Lanzenberger **Definition 2.27** (the
multi-system distance) and **Theorem 2.29** (its comparison with the pairwise
distance), read visually at printed pp. 18–19 of D. Lanzenberger, *A Theory of
Random Systems, Games, and Hardness Amplification*, DISS ETH No. 29554.

Nothing here mentions systems: Definition 2.27 consumes these objects at
`A = System.DDS X Y`, but every statement below is about a finite family of
finitely supported laws on an arbitrary carrier.

## What the layer contains

* `Distribution.pi` — the independent product of finitely many laws, the
  heterogeneous companion of `Distribution.iidPow`.
* `IsJointOf` — Definition 2.27's `ℰ`: a *non-negative* law on value tuples
  whose `i`-th coordinate marginal is `laws i`.  Non-negativity is a conjunct,
  not a carrier fact: on the signed carrier `A →₀ ℝ` dropping it makes the
  supremum below unbounded (add `+M` on the diagonal and `−M` off it and the
  marginals do not move).
* `agreementMass` / `supAgreement` — Definition 2.27's event `S₁ = ⋯ = Sₙ` and
  its inner supremum `sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)`.
* `overlapDist` — the pointwise minimum `a ↦ minᵢ lawsᵢ(a)`, and
  `supAgreement_eq_weight_overlapDist`, the `n`-ary maximal coupling: for laws
  of one common weight the inner supremum is *attained* and equals the overlap
  weight.  At `n = 2` this is Lanzenberger Lemma 2.8
  (`Probability.exists_coupling_offDiagonalMass_eq`) rewritten as
  `supAgreement_pair_eq_weight_sub_statDist`.
* `exists_pair_sum_min_le_of_forall_column_zero` — Lemma 2.30, pure
  real-matrix combinatorics.
* `exists_pair_one_sub_supAgreement_le` — the distribution-level step of
  Theorem 2.29's proof, **errata-corrected**, and
  `not_supAgreement_disagreement_le_every_pair`, the kernel-checked refutation of the
  printed form.

## Source errata (both travel with every statement below)

The thesis's Theorem 2.29 proof (printed p. 19, bottom display) reads

  `inf_ℰ Pr^ℰ(∃ i,j : Xᵢ ≠ Xⱼ) ≤ (min(n,|𝒳|) − 1) · min_{i,j} inf_ℰ Pr^ℰ(Xᵢ ≠ Xⱼ)`,

and the `min` over pairs is an erratum for `max`.  Lemma 2.30 bounds the
*smallest* pairwise overlap `Σ_k min(A_ik, A_jk)`, i.e. it controls the
multi-law disagreement by the *largest* pairwise distance.  The printed form
is false, and `not_supAgreement_disagreement_le_every_pair` is the kernel-checked witness
(`X₁ = δ₀`, `X₂ = ¾δ₀ + ¼δ₁`, `X₃ = δ₂` over `Fin 3`: the left side is `1`
while the closest pair contributes only `¼`).  The corrected bound is stated
in attained `∃ i ≠ j` form, which is exactly the `max_{i≠j}` form since the
pair set is finite.

The companion erratum — Definition 2.27/2.28's `inf` over representatives is a
`sup` — is system-level and is not formalized in this module.

The proof of Lemma 2.30 replaces the thesis's "WLOG reorder the rows" by an
explicit **zero-row selector** `z : column → row` whose fibers are the
partition cells.
-/

namespace Probability

universe u

namespace Distribution

variable {A : Type*} {n : ℕ}

/-! ## The independent product of a finite family -/

/-- The independent product of finitely many finitely supported laws:
`(⨂ᵢ μᵢ)(f) = ∏ᵢ μᵢ(f i)`.  This is `Distribution.iidPow` with the factors
allowed to differ, and it is what the `n`-ary maximal coupling glues onto the
diagonal. -/
noncomputable def pi (μ : Fin n → Distribution A) : Distribution (Fin n → A) :=
  Finsupp.onFinset (Fintype.piFinset fun i => (μ i).support)
    (fun f => ∏ i, μ i (f i))
    (fun _f hf => Fintype.mem_piFinset.mpr fun i =>
      Finsupp.mem_support_iff.mpr fun h0 =>
        hf (Finset.prod_eq_zero (Finset.mem_univ i) h0))

@[simp]
theorem pi_apply (μ : Fin n → Distribution A) (f : Fin n → A) :
    pi μ f = ∏ i, μ i (f i) := by
  rw [pi]; exact Finsupp.onFinset_apply

/-- An independent product of non-negative factors is non-negative. -/
theorem pi_nonNeg {μ : Fin n → Distribution A} (h : ∀ i, (μ i).NonNeg) :
    (pi μ).NonNeg := fun f => by
  rw [pi_apply]
  exact Finset.prod_nonneg fun i _ => h i (f i)

/-! ## Marginal bookkeeping -/

/-- Coordinate marginals are additive in the joint law. -/
theorem marginalAt_add {ι : Type*} {T : ι → Type*}
    (F G : Distribution ((i : ι) → T i)) (j : ι) :
    marginalAt (F + G) j = marginalAt F j + marginalAt G j :=
  Finsupp.sum_add_index' (fun _ => Finsupp.single_zero _)
    (fun x b₁ b₂ => Finsupp.single_add (x j) b₁ b₂)

/-- Coordinate marginals commute with scaling. -/
theorem marginalAt_smul {ι : Type*} {T : ι → Type*}
    (c : ℝ) (F : Distribution ((i : ι) → T i)) (j : ι) :
    marginalAt (c • F) j = c • marginalAt F j := by
  unfold marginalAt
  rw [Finsupp.sum_smul_index (fun _ => Finsupp.single_zero _), Finsupp.smul_sum]
  exact Finsupp.sum_congr fun x _ => by
    rw [Finsupp.smul_single, smul_eq_mul]

/-- The coordinate marginal of an independent product: the chosen factor,
scaled by the total weights of all the other factors. -/
theorem marginalAt_pi (μ : Fin n → Distribution A) (i : Fin n) :
    marginalAt (pi μ) i
      = (∏ j ∈ Finset.univ.erase i, (μ j).weight) • μ i := by
  classical
  refine Finsupp.ext fun b => ?_
  rw [marginalAt_apply, Finsupp.smul_apply, smul_eq_mul, mass]
  rw [Finsupp.sum_of_support_subset (pi μ)
    (s := Fintype.piFinset fun j => (μ j).support)
    Finsupp.support_onFinset_subset _
    (fun f _ => by simp only [ite_self])]
  have hgate : ∀ f ∈ Fintype.piFinset fun j => (μ j).support,
      (if f i = b then pi μ f else 0)
        = ∏ j, if j = i then (if f j = b then μ j (f j) else 0)
            else μ j (f j) := by
    intro f _
    by_cases hf : f i = b
    · rw [if_pos hf, pi_apply]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj
        rw [if_pos rfl, if_pos hf]
      · rw [if_neg hj]
    · rw [if_neg hf]
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [if_pos rfl, if_neg hf]
  have hfubini :
      (∑ f ∈ Fintype.piFinset fun j => (μ j).support,
        ∏ j, if j = i then (if f j = b then μ j (f j) else 0)
            else μ j (f j))
      = ∏ j, ∑ a ∈ (μ j).support,
          if j = i then (if a = b then μ j a else 0) else μ j a :=
    (Finset.prod_univ_sum _ fun j a =>
      if j = i then (if a = b then μ j a else 0) else μ j a).symm
  rw [Finset.sum_congr rfl hgate, hfubini,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hifactor :
      (∑ a ∈ (μ i).support,
          if i = i then (if a = b then μ i a else 0) else μ i a)
        = μ i b := by
    have hred : ∀ a ∈ (μ i).support,
        (if i = i then (if a = b then μ i a else 0) else μ i a)
          = (if a = b then μ i a else 0) := fun a _ => if_pos rfl
    rw [Finset.sum_congr rfl hred,
      Finset.sum_ite_eq' (μ i).support b (fun a => μ i a)]
    split
    · rfl
    · exact (Finsupp.notMem_support_iff.mp ‹_›).symm
  have hother : ∀ j ∈ Finset.univ.erase i,
      (∑ a ∈ (μ j).support,
          if j = i then (if a = b then μ j a else 0) else μ j a)
        = (μ j).weight := by
    intro j hj
    rw [weight_eq_finsupp_sum, Finsupp.sum]
    exact Finset.sum_congr rfl fun a _ => if_neg (Finset.ne_of_mem_erase hj)
  rw [hifactor, Finset.prod_congr rfl hother, mul_comm]

end Distribution

/-! ## Definition 2.27's joint distributions -/

section JointDistributions

variable {A : Type*} {n : ℕ}

/-- Lanzenberger **Definition 2.27**'s `ℰ`: a **joint distribution** of a
tuple of laws — a non-negative law on value tuples whose `i`-th coordinate
marginal is exactly `laws i`.  The `n`-ary companion of
`Distribution.IsCoupling`.

Non-negativity is a conjunct rather than a carrier fact.  On the signed
carrier `A →₀ ℝ` it has to be carried explicitly (the same discipline as
`Distribution.IsCoupling`'s callers), and it is not bookkeeping: Definition
2.27's `ℰ` is a *distribution*, and without the conjunct `supAgreement` below
is unbounded — add `+M` on the diagonal and `−M` off it and every marginal is
unchanged.

The thesis names the object only by the display `Pr^ℰ`. -/
def IsJointOf (joint : Distribution (Fin n → A)) (laws : Fin n → Distribution A) :
    Prop :=
  joint.NonNeg ∧ ∀ i, Distribution.marginalAt joint i = laws i

theorem IsJointOf.nonNeg {joint : Distribution (Fin n → A)}
    {laws : Fin n → Distribution A} (h : IsJointOf joint laws) :
    joint.NonNeg := h.1

theorem IsJointOf.marginalAt {joint : Distribution (Fin n → A)}
    {laws : Fin n → Distribution A} (h : IsJointOf joint laws) (i : Fin n) :
    Distribution.marginalAt joint i = laws i := h.2 i

/-- Marginals of a non-negative joint are non-negative, so the represented
laws inherit the layer. -/
theorem IsJointOf.nonNeg_law {joint : Distribution (Fin n → A)}
    {laws : Fin n → Distribution A} (h : IsJointOf joint laws) (i : Fin n) :
    (laws i).NonNeg := by
  rw [← h.2 i]
  exact h.1.fTransform (fun f => f i)

/-- A joint distribution has each marginal's total weight; in particular all
marginals of one joint weigh the same, so Definition 2.27's standing
same-weight hypothesis is forced rather than optional. -/
theorem weight_eq_of_isJointOf {joint : Distribution (Fin n → A)}
    {laws : Fin n → Distribution A} (h : IsJointOf joint laws) (i : Fin n) :
    joint.weight = (laws i).weight := by
  rw [← h.2 i]
  exact (Distribution.weight_fTransform (fun f => f i) joint).symm

/-- Lanzenberger **Definition 2.27**'s agreement event `S₁ = S₂ = ⋯ = Sₙ`, as
a mass. -/
noncomputable def agreementMass (joint : Distribution (Fin n → A)) : ℝ :=
  joint.mass fun tuple => ∀ i j, tuple i = tuple j

/-- Lanzenberger **Definition 2.27**'s inner supremum
`sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)`, at one representative tuple. -/
noncomputable def supAgreement (laws : Fin n → Distribution A) : ℝ :=
  sSup {b : ℝ | ∃ joint, IsJointOf joint laws ∧ b = agreementMass joint}

/-- The inner supremum is non-negative — also when no joint exists, where the
real `sSup` of the empty set is `0`. -/
theorem supAgreement_nonneg (laws : Fin n → Distribution A) :
    0 ≤ supAgreement laws :=
  Real.sSup_nonneg fun b hb => by
    obtain ⟨joint, hjoint, rfl⟩ := hb
    exact hjoint.nonNeg.mass_nonneg _

/-- The agreement masses of a representative tuple are bounded by the weight
of any one representative, so Definition 2.27's inner supremum set is bounded
above. -/
theorem bddAbove_agreementSet (laws : Fin n → Distribution A) (i : Fin n) :
    BddAbove {b : ℝ |
      ∃ joint, IsJointOf joint laws ∧ b = agreementMass joint} := by
  refine ⟨(laws i).weight, ?_⟩
  rintro b ⟨joint, hjoint, rfl⟩
  exact (Distribution.mass_le_weight hjoint.nonNeg _).trans_eq
    (weight_eq_of_isJointOf hjoint i)

/-- The inner supremum is bounded by the weight of any one representative.
The `NonNeg` side condition is what the empty-`sSup` convention costs: with no
joint at all the supremum is `0`, which a signed law's weight need not
bound. -/
theorem supAgreement_le_weight (laws : Fin n → Distribution A) (i : Fin n)
    (hnn : (laws i).NonNeg) :
    supAgreement laws ≤ (laws i).weight := by
  refine Real.sSup_le ?_ hnn.weight_nonneg
  rintro b ⟨joint, hjoint, rfl⟩
  exact (Distribution.mass_le_weight hjoint.nonNeg _).trans_eq
    (weight_eq_of_isJointOf hjoint i)

/-- On the signed carrier a representative tuple need not be non-negative,
and then Definition 2.27's inner set is **empty**: `IsJointOf` demands a
non-negative joint, and the coordinate marginals of a non-negative joint are
non-negative.  The real `sSup` of the empty set is `0`, so a signed tuple
contributes exactly `0`. -/
theorem supAgreement_eq_zero_of_not_nonNeg {laws : Fin n → Distribution A}
    (hsigned : ¬ ∀ i, (laws i).NonNeg) : supAgreement laws = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hsigned
  have hempty : {b : ℝ | ∃ joint, IsJointOf joint laws ∧
      b = agreementMass joint} = ∅ := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    rintro joint ⟨hjoint, -⟩
    exact hi (IsJointOf.nonNeg_law hjoint i)
  unfold supAgreement
  rw [hempty, Real.sSup_empty]

/-- The two-coordinate selector projecting an `n`-tuple to the pair of its
`i`-th and `j`-th entries.  Spelled with `Fin 2` literals and `if` rather than
the `![·,·]` vector notation, whose `Nat.succ`-shaped length forces a
numeral-form defeq check at every later `sSup`/`sInf` unification. -/
def selectPair {B : Type*} (i j : Fin n) (f : Fin n → B) : Fin 2 → B :=
  fun k => if k = 0 then f i else f j

@[simp]
theorem selectPair_zero {B : Type*} (i j : Fin n) (f : Fin n → B) :
    selectPair i j f 0 = f i := rfl

@[simp]
theorem selectPair_one {B : Type*} (i j : Fin n) (f : Fin n → B) :
    selectPair i j f 1 = f j := rfl

/-- Projecting an `n`-tuple joint to two chosen coordinates yields a pair
joint of the corresponding marginals. -/
theorem isJointOf_selectPair {joint : Distribution (Fin n → A)}
    {laws : Fin n → Distribution A}
    (h : IsJointOf joint laws) (i j : Fin n) (pair : Fin 2 → Distribution A)
    (h0 : pair 0 = laws i) (h1 : pair 1 = laws j) :
    IsJointOf (Distribution.fTransform (selectPair i j) joint) pair := by
  refine ⟨h.nonNeg.fTransform _, fun k => ?_⟩
  refine Finsupp.ext fun s => ?_
  rw [Distribution.marginalAt_apply, Distribution.mass_fTransform]
  fin_cases k
  · show (Distribution.mass joint fun f => selectPair i j f 0 = s) = pair 0 s
    simp only [selectPair_zero]
    rw [h0, ← h.2 i, Distribution.marginalAt_apply]
  · show (Distribution.mass joint fun f => selectPair i j f 1 = s) = pair 1 s
    simp only [selectPair_one]
    rw [h1, ← h.2 j, Distribution.marginalAt_apply]

/-- Total agreement implies agreement on any two chosen coordinates: the
projected pair joint agrees at least as often as the tuple joint. -/
theorem agreementMass_le_selectPair {joint : Distribution (Fin n → A)}
    (hjoint : joint.NonNeg) (i j : Fin n) :
    agreementMass joint ≤
      agreementMass (Distribution.fTransform (selectPair i j) joint) := by
  unfold agreementMass
  rw [Distribution.mass_fTransform]
  refine Distribution.mass_mono hjoint fun f hf a b => ?_
  unfold selectPair
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · simp [ha, hb]
  · simp [ha, hb, hf i j]
  · simp [ha, hb, hf j i]
  · simp [ha, hb]

/-- The inner-supremum comparison behind Theorem 2.29's trivial inequality:
whenever a pair of laws occurs as two chosen marginals of a tuple, every tuple
joint projects to a pair joint with at least the tuple's agreement, so the
tuple's inner supremum is at most the pair's. -/
theorem supAgreement_le_of_pair_marginals
    {laws : Fin n → Distribution A} (pairLaws : Fin 2 → Distribution A)
    (i j : Fin n) (h0 : pairLaws 0 = laws i) (h1 : pairLaws 1 = laws j) :
    supAgreement laws ≤ supAgreement pairLaws := by
  refine Real.sSup_le ?_ (supAgreement_nonneg pairLaws)
  rintro b ⟨joint, hjoint, rfl⟩
  have hmem : agreementMass (Distribution.fTransform (selectPair i j) joint) ∈
      {b : ℝ | ∃ joint', IsJointOf joint' pairLaws ∧
        b = agreementMass joint'} :=
    ⟨Distribution.fTransform (selectPair i j) joint,
      isJointOf_selectPair hjoint i j pairLaws h0 h1, rfl⟩
  unfold supAgreement
  exact (agreementMass_le_selectPair hjoint.nonNeg i j).trans
    (le_csSup (bddAbove_agreementSet pairLaws 0) hmem)

end JointDistributions

/-! ## The pointwise-minimum overlap and the `n`-ary maximal coupling -/

section Overlap

variable {A : Type*} {n : ℕ}

open Classical in
/-- The union of the supports of a tuple of laws.  Its cardinality is
Theorem 2.29's `ℓ` at one representative tuple. -/
noncomputable def supportUnion (laws : Fin n → Distribution A) : Finset A :=
  Finset.univ.biUnion fun i => (laws i).support

theorem support_subset_supportUnion (laws : Fin n → Distribution A) (i : Fin n) :
    (laws i).support ⊆ supportUnion laws := by
  classical
  intro a ha
  unfold supportUnion
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by convert ha⟩

/-- The pointwise minimum `a ↦ minᵢ lawsᵢ(a)` of a nonempty tuple of laws.
Its weight is the classical `Σ_a minᵢ lawsᵢ(a)`, the largest diagonal mass any
joint distribution of the tuple can achieve. -/
noncomputable def overlapDist [NeZero n] (laws : Fin n → Distribution A) :
    Distribution A :=
  Finsupp.onFinset (supportUnion laws)
    (fun a => Finset.univ.inf' Finset.univ_nonempty fun i => laws i a)
    (fun a ha => by
      classical
      by_contra hmem
      refine ha (le_antisymm ?_ ?_)
      · exact (Finset.inf'_le _ (Finset.mem_univ 0)).trans_eq
          (Finsupp.notMem_support_iff.mp fun h =>
            hmem (support_subset_supportUnion laws 0 h))
      · refine Finset.le_inf' _ _ fun i _ => ?_
        exact (Finsupp.notMem_support_iff.mp fun h =>
          hmem (support_subset_supportUnion laws i h)).ge)

@[simp]
theorem overlapDist_apply [NeZero n] (laws : Fin n → Distribution A) (a : A) :
    overlapDist laws a
      = Finset.univ.inf' Finset.univ_nonempty fun i => laws i a :=
  rfl

theorem overlapDist_apply_le [NeZero n] (laws : Fin n → Distribution A)
    (i : Fin n) (a : A) : overlapDist laws a ≤ laws i a :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem overlapDist_le [NeZero n] (laws : Fin n → Distribution A) (i : Fin n) :
    overlapDist laws ≤ laws i :=
  Finsupp.le_def.mpr fun a => overlapDist_apply_le laws i a

/-- A pointwise minimum of non-negative laws is non-negative (structural on a
`NNReal` carrier, a side condition on the signed one). -/
theorem overlapDist_nonNeg [NeZero n] {laws : Fin n → Distribution A}
    (hnn : ∀ i, (laws i).NonNeg) : (overlapDist laws).NonNeg := fun a => by
  rw [overlapDist_apply]
  exact Finset.le_inf' _ _ fun i _ => hnn i a

/-- The overlap weight as a sum over the support union. -/
theorem weight_overlapDist_eq_sum [NeZero n] (laws : Fin n → Distribution A) :
    (overlapDist laws).weight
      = ∑ a ∈ supportUnion laws, overlapDist laws a := by
  rw [Distribution.weight_eq_finsupp_sum, Finsupp.sum]
  exact Finset.sum_subset Finsupp.support_onFinset_subset
    fun a _ ha => Finsupp.notMem_support_iff.mp ha

/-- **Any joint agrees at most as often as the overlap allows** — the easy
half of the `n`-ary coupling lemma.  Total agreement happens on constant
tuples only, the constant value determines the tuple, and each constant
tuple's mass is below every coordinate marginal. -/
theorem agreementMass_le_weight_overlapDist [NeZero n]
    {joint : Distribution (Fin n → A)} {laws : Fin n → Distribution A}
    (h : IsJointOf joint laws) :
    agreementMass joint ≤ (overlapDist laws).weight := by
  classical
  have hpoint : ∀ f : Fin n → A, (∀ i j, f i = f j) →
      joint f ≤ overlapDist laws (f 0) := by
    intro f hf
    rw [overlapDist_apply]
    refine Finset.le_inf' _ _ fun i _ => ?_
    have hmono : joint.mass (fun g => g = f) ≤ joint.mass (fun g => g i = f i) :=
      Distribution.mass_mono h.nonNeg fun g hg => by rw [hg]
    rw [Distribution.mass_singleton] at hmono
    have hi := hmono.trans_eq (by rw [← Distribution.marginalAt_apply, h.2 i])
    rwa [hf i 0] at hi
  set agreeSet : Finset (Fin n → A) :=
      joint.support.filter (fun f => ∀ i j, f i = f j) with hagree
  have hmass : agreementMass joint = ∑ f ∈ agreeSet, joint f := by
    unfold agreementMass Distribution.mass
    rw [Finsupp.sum, hagree, Finset.sum_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hP : ∀ i j : Fin n, f i = f j
    · rw [if_pos hP, if_pos hP]
    · rw [if_neg hP, if_neg hP]
  rw [hmass]
  have hstep : ∑ f ∈ agreeSet, joint f
      ≤ ∑ f ∈ agreeSet, overlapDist laws (f 0) :=
    Finset.sum_le_sum fun f hf => hpoint f (Finset.mem_filter.mp hf).2
  refine hstep.trans ?_
  have hinj : Set.InjOn (fun f : Fin n → A => f 0) ↑agreeSet := by
    intro f hf g hg hfg
    have hfa := (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
    have hga := (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2
    funext k
    rw [hfa k 0, hga k 0]
    exact hfg
  rw [← Finset.sum_image (f := fun a => overlapDist laws a) hinj]
  rw [Distribution.weight_eq_finsupp_sum, Finsupp.sum,
    ← Finset.sum_filter_ne_zero (agreeSet.image fun f => f 0)]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun a ha => Finsupp.mem_support_iff.mpr (Finset.mem_filter.mp ha).2)
    fun a _ _ => overlapDist_nonNeg (fun i => h.nonNeg_law i) a

/-- **The `n`-ary maximal coupling exists** (the attainment half): for laws of
one common weight there is a joint distribution whose diagonal mass is at
least — hence, with the bound above, exactly — the overlap weight
`Σ_a minᵢ lawsᵢ(a)`.

Construction: embed the overlap diagonally and add an independent product of
the residuals `lawsᵢ − overlap`, normalized by the common residual weight;
each marginal reassembles to `overlap + residualᵢ = lawsᵢ`. -/
theorem exists_isJointOf_weight_overlapDist_le_agreementMass [NeZero n]
    (laws : Fin n → Distribution A) (hnn : ∀ i, (laws i).NonNeg) {w : ℝ}
    (hweight : ∀ i, (laws i).weight = w) :
    ∃ joint : Distribution (Fin n → A), IsJointOf joint laws ∧
      (overlapDist laws).weight ≤ agreementMass joint := by
  classical
  set β : Distribution A := overlapDist laws with hβ
  have hβnn : β.NonNeg := overlapDist_nonNeg hnn
  set resid : Fin n → Distribution A := fun i => laws i - β with hresid
  have hresidnn : ∀ i, (resid i).NonNeg := fun i a =>
    sub_nonneg.mpr (overlapDist_apply_le laws i a)
  have hresid_weight : ∀ i, (resid i).weight = w - β.weight := by
    intro i
    rw [hresid, Distribution.weight_sub, hweight i]
  have hwβ : 0 ≤ w - β.weight :=
    (hresid_weight 0) ▸ (hresidnn 0).weight_nonneg
  set c : ℝ := ((w - β.weight) ^ (n - 1))⁻¹ with hc
  have hcnn : 0 ≤ c := inv_nonneg.mpr (pow_nonneg hwβ _)
  set diag : Distribution (Fin n → A) :=
    Distribution.fTransform (fun a _ => a) β with hdiag
  have htailnn : (c • Distribution.pi resid).NonNeg := fun f => by
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg hcnn (Distribution.pi_nonNeg hresidnn f)
  refine ⟨diag + c • Distribution.pi resid, ⟨fun f => ?_, ?_⟩, ?_⟩
  · rw [Finsupp.add_apply]
    exact add_nonneg (Distribution.NonNeg.fTransform hβnn (fun a _ => a) f)
      (htailnn f)
  · intro i
    rw [Distribution.marginalAt_add, Distribution.marginalAt_smul,
      Distribution.marginalAt_pi]
    have hdiag_marginal : Distribution.marginalAt diag i = β := by
      refine Finsupp.ext fun b => ?_
      rw [Distribution.marginalAt_apply, hdiag, Distribution.mass_fTransform]
      exact Distribution.mass_singleton β b
    rw [hdiag_marginal]
    have hprod : ∏ j ∈ Finset.univ.erase i, (resid j).weight
        = (w - β.weight) ^ (n - 1) := by
      rw [Finset.prod_congr rfl fun j _ => hresid_weight j,
        Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]
    rw [hprod]
    by_cases hzero : w - β.weight = 0
    · have hresid0 : resid i = 0 :=
        Distribution.eq_zero_of_nonNeg_of_weight_eq_zero (hresidnn i)
          (by rw [hresid_weight i, hzero])
      have hlawsβ : laws i = β := sub_eq_zero.mp hresid0
      rw [hresid0, smul_zero, smul_zero, add_zero, hlawsβ]
    · rw [smul_smul, hc, inv_mul_cancel₀ (pow_ne_zero _ hzero), one_smul]
      refine Finsupp.ext fun a => ?_
      rw [Finsupp.add_apply, hresid]
      dsimp only
      rw [Finsupp.sub_apply]
      ring
  · have hdiag_agree : agreementMass diag = β.weight := by
      unfold agreementMass
      rw [hdiag, Distribution.mass_fTransform,
        Distribution.mass_congr β (Q := fun _ => True) (fun a => by simp)]
      exact Distribution.mass_true β
    unfold agreementMass
    rw [Distribution.mass_add]
    exact hdiag_agree.ge.trans
      (le_add_of_nonneg_right (htailnn.mass_nonneg _))

/-- **The `n`-ary coupling identity**: for laws of one common weight,
Definition 2.27's inner supremum is exactly the overlap weight
`Σ_a minᵢ lawsᵢ(a)`.  This is the `n`-ary form of Lanzenberger Lemma 2.8 — the
supremum over joint distributions of the diagonal mass is attained by the
maximal coupling. -/
theorem supAgreement_eq_weight_overlapDist [NeZero n]
    (laws : Fin n → Distribution A) (hnn : ∀ i, (laws i).NonNeg) {w : ℝ}
    (hweight : ∀ i, (laws i).weight = w) :
    supAgreement laws = (overlapDist laws).weight := by
  refine le_antisymm
    (Real.sSup_le ?_ (overlapDist_nonNeg hnn).weight_nonneg) ?_
  · rintro b ⟨joint, hjoint, rfl⟩
    exact agreementMass_le_weight_overlapDist hjoint
  · obtain ⟨joint, hjoint, hge⟩ :=
      exists_isJointOf_weight_overlapDist_le_agreementMass laws hnn hweight
    have hmem : agreementMass joint ∈
        {b : ℝ | ∃ joint', IsJointOf joint' laws ∧
          b = agreementMass joint'} := ⟨joint, hjoint, rfl⟩
    exact hge.trans (le_csSup (bddAbove_agreementSet laws 0) hmem)

end Overlap

/-! ## The pair case: Definition 2.28's coupling bridge -/

section PairCase

variable {A : Type*}

/-- The binary infimum over `Fin 2` is the `min` of the two values. -/
theorem inf'_univ_fin_two {α : Type*} [LinearOrder α] (f : Fin 2 → α) :
    Finset.univ.inf' Finset.univ_nonempty f = min (f 0) (f 1) := by
  refine le_antisymm
    (le_min (Finset.inf'_le f (Finset.mem_univ 0))
      (Finset.inf'_le f (Finset.mem_univ 1)))
    (Finset.le_inf' _ f fun b _ => ?_)
  fin_cases b
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- The pair overlap weight is the first weight minus the one-sided
statistical distance: `Σ_a min(μ(a), ν(a)) = |μ| − δ(μ, ν)`, at
sub-distribution generality — the classical overlap formula behind Definition
2.28's second display.

Hypothesis-free on the signed carrier: `statDist` sums over the support of the
*difference* and needs no side condition to see points where only the second
law is charged. -/
theorem weight_overlapDist_pair (P : Fin 2 → Distribution A) :
    (overlapDist P).weight = (P 0).weight - statDist (P 0) (P 1) := by
  classical
  have hδ : statDist (P 0) (P 1)
      = ∑ a ∈ supportUnion P, ((P 0) a - min ((P 0) a) ((P 1) a)) := by
    rw [statDist_eq_sum_of_support_subset (P 0) (P 1)
      (s := supportUnion P) (fun a ha => by
        rcases Finset.mem_union.mp (Finsupp.support_sub ha) with h' | h'
        · exact support_subset_supportUnion P 0 h'
        · exact support_subset_supportUnion P 1 h')]
    refine Finset.sum_congr rfl fun a _ => ?_
    rcases le_total ((P 1) a) ((P 0) a) with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h]
    · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h, sub_self]
  have hw : (P 0).weight = ∑ a ∈ supportUnion P, (P 0) a :=
    Distribution.weight_eq_sum_of_support_subset (P 0)
      (support_subset_supportUnion P 0)
  rw [weight_overlapDist_eq_sum, hδ, hw, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [overlapDist_apply, inf'_univ_fin_two]
  ring

/-- **Definition 2.28's coupling bridge**: for two laws of one common weight
the best diagonal mass of a coupling is `|law₀| − δ(law₀, law₁)` — Lanzenberger
Lemma 2.8, at the pair rendered as a `Fin 2` tuple. -/
theorem supAgreement_pair_eq_weight_sub_statDist (P : Fin 2 → Distribution A)
    (hnn : ∀ i, (P i).NonNeg) (hw : (P 1).weight = (P 0).weight) :
    supAgreement P = (P 0).weight - statDist (P 0) (P 1) := by
  rw [← weight_overlapDist_pair P]
  refine supAgreement_eq_weight_overlapDist P hnn (w := (P 0).weight)
    fun i => ?_
  fin_cases i
  · rfl
  · exact hw

end PairCase

/-! ## Lanzenberger Lemma 2.30: the zero-column matrix bound -/

/-- **Lanzenberger Lemma 2.30** (printed p. 19), in attained form over
abstract finite index types (the thesis's `[n]` rows and `[m]` columns): for a
non-negative matrix in which every column has a zero and every row sums to the
same total, some two *distinct* rows overlap by at most
`(1 − 1/(min(m,n) − 1))` of the row total.  This implies the thesis's
`min_{i,j∈[n]}` display.

The thesis's row-reordering WLOG ("the rows of `A` need to be appropriately
reordered") is presentation, not mathematics; it is replaced by a zero-row
selector `z : column → row`, whose fibers are the partition cells and whose
image `R` satisfies `|R| ≤ min(m,n)` with no reordering.  The thesis's two
cases then collapse into one dichotomy on whether some off-cell row mass
reaches `total/(min(m,n) − 1)`; the exact-value analysis of its second case is
not needed for the inequality. -/
theorem exists_pair_sum_min_le_of_forall_column_zero
    {row col : Type*} [Fintype row] [Fintype col]
    (hrows : 2 ≤ Fintype.card row) (hcols : 2 ≤ Fintype.card col)
    (A : row → col → ℝ) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hcolumn : ∀ j, ∃ i, A i j = 0) {total : ℝ}
    (hrow : ∀ i, ∑ j, A i j = total) :
    ∃ i i' : row, i ≠ i' ∧
      ∑ k, min (A i k) (A i' k)
        ≤ (1 - 1 / (((min (Fintype.card col) (Fintype.card row) : ℕ) : ℝ) - 1))
            * total := by
  classical
  obtain ⟨j₀⟩ : Nonempty col := Fintype.card_pos_iff.mp (by omega)
  haveI : Nontrivial row := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  choose z hz using hcolumn
  set R : Finset row := Finset.univ.image z with hR
  set cell : row → Finset col :=
    fun r => Finset.univ.filter (fun j => z j = r) with hcell
  have hzero_on_cell : ∀ r, ∀ j ∈ cell r, A r j = 0 := by
    intro r j hj
    have hzj : z j = r := (Finset.mem_filter.mp hj).2
    rw [← hzj]
    exact hz j
  set Mnat : ℕ := min (Fintype.card col) (Fintype.card row) with hMnat
  have hMnat2 : 2 ≤ Mnat := le_min hcols hrows
  set M : ℝ := (Mnat : ℝ) with hM
  have hM2 : (2 : ℝ) ≤ M := by
    rw [hM]
    exact_mod_cast hMnat2
  have hM1 : (0 : ℝ) < M - 1 := by linarith
  obtain ⟨i₀⟩ : Nonempty row := Fintype.card_pos_iff.mp (by omega)
  have htotal0 : 0 ≤ total :=
    (hrow i₀).symm.trans_ge (Finset.sum_nonneg fun j _ => hnonneg i₀ j)
  have key : ∀ i r : row,
      ∑ k, min (A i k) (A r k) ≤ total - ∑ j ∈ cell r, A i j := by
    intro i r
    have hsplit : ∑ k, min (A i k) (A r k)
        = ∑ k ∈ cell r, min (A i k) (A r k)
          + ∑ k ∈ (cell r)ᶜ, min (A i k) (A r k) :=
      (Finset.sum_add_sum_compl (cell r) _).symm
    have hcellpart : ∑ k ∈ cell r, min (A i k) (A r k) ≤ 0 :=
      Finset.sum_nonpos fun k hk =>
        (min_le_right _ _).trans_eq (hzero_on_cell r k hk)
    have hcomplpart : ∑ k ∈ (cell r)ᶜ, min (A i k) (A r k)
        ≤ ∑ k ∈ (cell r)ᶜ, A i k :=
      Finset.sum_le_sum fun k _ => min_le_left _ _
    have hrowsplit : ∑ j ∈ cell r, A i j + ∑ j ∈ (cell r)ᶜ, A i j = total :=
      (Finset.sum_add_sum_compl (cell r) _).trans (hrow i)
    linarith [hsplit, hcellpart, hcomplpart]
  by_cases hex : ∃ i r, r ∈ R ∧ i ≠ r ∧
      total / (M - 1) ≤ ∑ j ∈ cell r, A i j
  · obtain ⟨i, r, -, hir, hbig⟩ := hex
    refine ⟨i, r, hir, ?_⟩
    have h1 := key i r
    have harith : total - total / (M - 1) = (1 - 1 / (M - 1)) * total := by
      field_simp
    linarith [h1, hbig, harith]
  · exfalso
    rw [not_exists] at hex
    simp only [not_exists, not_and, not_le] at hex
    have hR0 : z j₀ ∈ R := Finset.mem_image_of_mem z (Finset.mem_univ j₀)
    set r0 : row := z j₀ with hr0
    have hfib : total = ∑ r ∈ R, ∑ j ∈ cell r, A r0 j := by
      rw [← hrow r0, ← Finset.sum_fiberwise Finset.univ z (A r0)]
      refine (Finset.sum_subset (Finset.subset_univ R) fun r _ hr => ?_).symm
      refine Finset.sum_eq_zero fun j hj => ?_
      exact absurd
        ((Finset.mem_filter.mp hj).2 ▸
          Finset.mem_image_of_mem z (Finset.mem_univ j)) hr
    have hsplitR : total = ∑ r ∈ R.erase r0, ∑ j ∈ cell r, A r0 j := by
      rw [hfib, ← Finset.add_sum_erase R _ hR0,
        Finset.sum_eq_zero (hzero_on_cell r0), zero_add]
    rcases Finset.eq_empty_or_nonempty (R.erase r0) with hempty | hne
    · have htz : total = 0 := by
        rw [hsplitR, hempty, Finset.sum_empty]
      obtain ⟨i₁, hi₁⟩ := exists_ne r0
      have hneg := hex i₁ r0 hR0 hi₁
      rw [htz, zero_div] at hneg
      exact absurd (Finset.sum_nonneg fun j _ => hnonneg i₁ j)
        (not_le.mpr hneg)
    · have h2 : R.card ≤ Mnat := by
        rw [hMnat]
        refine le_min ?_ (R.card_le_univ.trans_eq Finset.card_univ)
        calc R.card ≤ (Finset.univ : Finset col).card := Finset.card_image_le
          _ = Fintype.card col := Finset.card_univ
      have hcard : ((R.erase r0).card : ℝ) ≤ M - 1 := by
        have h5 : (R.erase r0).card ≤ Mnat - 1 := by
          rw [Finset.card_erase_of_mem hR0]
          omega
        calc ((R.erase r0).card : ℝ)
            ≤ ((Mnat - 1 : ℕ) : ℝ) := Nat.cast_le.mpr h5
          _ = M - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ Mnat), Nat.cast_one]
      have hstrict : total < (R.erase r0).card * (total / (M - 1)) := by
        calc total = ∑ r ∈ R.erase r0, ∑ j ∈ cell r, A r0 j := hsplitR
          _ < ∑ _r ∈ R.erase r0, total / (M - 1) := by
              refine Finset.sum_lt_sum_of_nonempty hne fun r hr => ?_
              exact hex r0 r (Finset.mem_of_mem_erase hr)
                (fun h => (Finset.ne_of_mem_erase hr) h.symm)
          _ = (R.erase r0).card * (total / (M - 1)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hdiv0 : 0 ≤ total / (M - 1) := div_nonneg htotal0 hM1.le
      have hlt : total < (M - 1) * (total / (M - 1)) :=
        hstrict.trans_le (mul_le_mul_of_nonneg_right hcard hdiv0)
      rw [mul_div_cancel₀ total (ne_of_gt hM1)] at hlt
      exact lt_irrefl total hlt

/-! ## The distribution-level step of Theorem 2.29's proof (errata-corrected) -/

/-- **The distribution-level inequality inside Lanzenberger Theorem 2.29's
proof** (printed p. 19, bottom display), in attained form and with the erratum
corrected: for probability laws `X₁, …, Xₙ` (`n ≥ 2`) over any carrier, with
`ℓ` the size of the union of their supports, some pair `i ≠ j` satisfies

  `1 − sup_ℰ Pr^ℰ(X₁ = ⋯ = Xₙ) ≤ (min(n,ℓ) − 1) · (1 − sup_ℰ Pr^ℰ(Xᵢ = Xⱼ))`.

Since the pair set is finite this is exactly the bound by
`(min(n,ℓ) − 1) · max_{i≠j} (…)`.  The thesis display writes `min_{i,j}` over
the pairs instead; that form is **false**
(`not_supAgreement_disagreement_le_every_pair`) — Lemma 2.30 bounds the smallest pairwise
overlap, which corresponds to the largest pairwise distance.

Proof: apply Lemma 2.30 to the residual matrix `A_{i,a} = Xᵢ(a) − minₖ Xₖ(a)`
over the support union, and translate both sides through the `n`-ary coupling
identity `supAgreement_eq_weight_overlapDist`. -/
theorem exists_pair_one_sub_supAgreement_le {A : Type*} {n : ℕ}
    (hn : 2 ≤ n) (laws : Fin n → Distribution A)
    (hprob : ∀ i, (laws i).isProbDist) :
    ∃ i j : Fin n, i ≠ j ∧
      1 - supAgreement laws
        ≤ (((min n (supportUnion laws).card : ℕ) : ℝ) - 1)
            * (1 - supAgreement (selectPair i j laws)) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hweight : ∀ i, (laws i).weight = 1 := fun i => (hprob i).2
  have hnn : ∀ i, (laws i).NonNeg := fun i => (hprob i).1
  have htuple : supAgreement laws = (overlapDist laws).weight :=
    supAgreement_eq_weight_overlapDist laws hnn hweight
  have hpair : ∀ i j : Fin n,
      supAgreement (selectPair i j laws)
        = (overlapDist (selectPair i j laws)).weight := by
    intro i j
    have hnn' : ∀ k, ((selectPair i j laws) k).NonNeg := by
      intro k
      fin_cases k
      · exact hnn i
      · exact hnn j
    refine supAgreement_eq_weight_overlapDist _ hnn' (w := 1) fun k => ?_
    fin_cases k
    · exact hweight i
    · exact hweight j
  have hU1 : 1 ≤ (supportUnion laws).card := by
    have hne : (laws 0).support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      intro h0
      have h1 := hweight 0
      rw [h0] at h1
      simp [Distribution.weight] at h1
    obtain ⟨a, ha⟩ := hne
    exact Finset.card_pos.mpr ⟨a, support_subset_supportUnion laws 0 ha⟩
  by_cases hU2 : 2 ≤ (supportUnion laws).card
  · set U : Finset A := supportUnion laws with hU
    set β : Distribution A := overlapDist laws with hβ
    have hsumlaw : ∀ i : Fin n, ∑ a ∈ U, (laws i) a = 1 := by
      intro i
      have h1 : ∑ a ∈ U, (laws i) a = (laws i).weight :=
        (Distribution.weight_eq_sum_of_support_subset (laws i)
          (support_subset_supportUnion laws i)).symm
      rw [h1, hweight i]
    have hsumβ : ∑ a ∈ U, β a = β.weight := by
      rw [hU, hβ]
      exact (weight_overlapDist_eq_sum laws).symm
    set Amat : Fin n → U → ℝ := fun i a => (laws i a.1 - β a.1) with hAmat
    have hnonneg : ∀ i a, 0 ≤ Amat i a := by
      intro i a
      rw [hAmat]
      dsimp only
      rw [sub_nonneg, hβ]
      exact overlapDist_apply_le laws i a.1
    have hcolumn : ∀ a : U, ∃ i, Amat i a = 0 := by
      intro a
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf'
        (Finset.univ_nonempty (α := Fin n)) (fun i => laws i a.1)
      refine ⟨i, ?_⟩
      rw [hAmat]
      dsimp only
      rw [sub_eq_zero, hβ, overlapDist_apply]
      exact hi.symm
    have hrowsum : ∀ i, ∑ a, Amat i a = 1 - β.weight := by
      intro i
      rw [hAmat]
      dsimp only
      rw [Finset.sum_coe_sort U (fun a => (laws i a - β a)),
        Finset.sum_sub_distrib, hsumlaw i, hsumβ]
    obtain ⟨i, j, hij, hbound⟩ :=
      exists_pair_sum_min_le_of_forall_column_zero
        (row := Fin n) (col := U)
        (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_coe])
        Amat hnonneg hcolumn hrowsum
    refine ⟨i, j, hij, ?_⟩
    have hUP : supportUnion (selectPair i j laws) ⊆ U := by
      rw [hU]
      refine Finset.biUnion_subset.mpr fun k _ => ?_
      fin_cases k
      · exact support_subset_supportUnion laws i
      · exact support_subset_supportUnion laws j
    have hpairsum : ∑ a ∈ U, min (laws i a) (laws j a)
          = (overlapDist (selectPair i j laws)).weight := by
      have hzero : ∀ a ∈ U, a ∉ supportUnion (selectPair i j laws) →
          min (laws i a) (laws j a) = 0 := by
        intro a _ ha
        have hi0 : laws i a = 0 := by
          by_contra hne
          exact ha (Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _,
            Finsupp.mem_support_iff.mpr hne⟩)
        rw [hi0, min_eq_left (hnn j a)]
      have hext : ∑ a ∈ supportUnion (selectPair i j laws),
            min (laws i a) (laws j a)
          = ∑ a ∈ U, min (laws i a) (laws j a) :=
        Finset.sum_subset hUP hzero
      rw [← hext, weight_overlapDist_eq_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [overlapDist_apply, inf'_univ_fin_two, selectPair_zero, selectPair_one]
    have hminsum : ∑ a, min (Amat i a) (Amat j a)
        = (overlapDist (selectPair i j laws)).weight - β.weight := by
      rw [← hpairsum, ← hsumβ, ← Finset.sum_sub_distrib]
      simp only [hAmat]
      rw [Finset.sum_coe_sort U
        (fun a => min ((laws i) a - β a) ((laws j) a - β a))]
      exact Finset.sum_congr rfl fun a _ => (min_sub_sub_right _ _ _)
    rw [htuple, hpair i j]
    set Mnat : ℕ := min (Fintype.card ↥U) (Fintype.card (Fin n)) with hMnat
    have hMnat2 : 2 ≤ Mnat := by
      rw [hMnat, Fintype.card_coe, Fintype.card_fin]
      exact le_min hU2 hn
    set M : ℝ := (Mnat : ℝ) with hM
    have hM2 : (2 : ℝ) ≤ M := by
      rw [hM]
      exact_mod_cast hMnat2
    have hM1 : (0 : ℝ) < M - 1 := by linarith
    have hMcast : (((min n U.card : ℕ) : ℝ)) = M := by
      rw [hM, hMnat, Fintype.card_coe, Fintype.card_fin, Nat.min_comm]
    rw [hMcast]
    rw [hminsum] at hbound
    have hfrac : (1 - β.weight) / (M - 1)
        ≤ 1 - (overlapDist (selectPair i j laws)).weight := by
      have hexpand : (1 - 1 / (M - 1)) * (1 - β.weight)
          = (1 - β.weight) - (1 - β.weight) / (M - 1) := by
        field_simp
      linarith [hbound, hexpand]
    calc 1 - β.weight
        = (M - 1) * ((1 - β.weight) / (M - 1)) :=
          (mul_div_cancel₀ _ hM1.ne').symm
      _ ≤ (M - 1) * (1 - (overlapDist (selectPair i j laws)).weight) :=
          mul_le_mul_of_nonneg_left hfrac hM1.le
  · have hcard : (supportUnion laws).card = 1 := by omega
    obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp hcard
    have hval : ∀ i, laws i a₀ = 1 := by
      intro i
      have hsub : (laws i).support ⊆ {a₀} :=
        ha₀ ▸ support_subset_supportUnion laws i
      have hw := hweight i
      rw [Distribution.weight_eq_finsupp_sum, Finsupp.sum] at hw
      rcases Finset.subset_singleton_iff.mp hsub with h | h
      · rw [h, Finset.sum_empty] at hw
        exact absurd hw.symm one_ne_zero
      · rwa [h, Finset.sum_singleton] at hw
    have hτ : (overlapDist laws).weight = 1 := by
      rw [weight_overlapDist_eq_sum, ha₀, Finset.sum_singleton,
        overlapDist_apply]
      refine le_antisymm
        (((Finset.inf'_le _ (Finset.mem_univ 0)).trans (hval 0).le)) ?_
      exact Finset.le_inf' _ _ fun b _ => (hval b).ge
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp, ?_⟩
    rw [htuple, hτ, hcard]
    have hmin1 : ((min n 1 : ℕ) : ℝ) = 1 := by
      rw [min_eq_right (by omega : 1 ≤ n)]
      exact Nat.cast_one
    rw [hmin1]
    simp

/-! ## The printed `min`-over-pairs form is false

The thesis's display (printed p. 19, proof of Theorem 2.29) claims, for `n`
distributions over a finite set,
`inf_ℰ Pr^ℰ(∃ i,j : Xᵢ ≠ Xⱼ) ≤ (min(n,|𝒳|) − 1) · min_{i,j} inf_ℰ Pr^ℰ(Xᵢ ≠ Xⱼ)`.
Since the constant is non-negative, bounding by the `min` over pairs is
equivalent to bounding by *every* pair; the witness below refutes that
universal form, hence the printed display.

Witness: `X₁ = δ₀`, `X₂ = ¾·δ₀ + ¼·δ₁`, `X₃ = δ₂` over `Fin 3` — the three
cannot agree at all (left side `1`), yet the closest pair disagrees with
probability only `¼`, and `(min(3,3) − 1) · ¼ = ½ < 1`. -/

open Classical in
/-- **Thesis erratum, kernel-checked**: the printed `min_{i,j}` form of the
distribution-level display in Theorem 2.29's proof is false.  (The corrected
`max` form is `exists_pair_one_sub_supAgreement_le`.) -/
theorem not_supAgreement_disagreement_le_every_pair :
    ¬ ∀ (laws : Fin 3 → Distribution (Fin 3)),
        (∀ i, (laws i).isProbDist) →
        ∀ i j : Fin 3, i ≠ j →
          1 - supAgreement laws
            ≤ (((min 3 (supportUnion laws).card : ℕ) : ℝ) - 1)
                * (1 - supAgreement (selectPair i j laws)) := by
  intro hclaim
  set laws : Fin 3 → Distribution (Fin 3) := fun i =>
    if i = 0 then Finsupp.single 0 1
    else if i = 1 then Finsupp.single 0 (3 / 4) + Finsupp.single 1 (1 / 4)
    else Finsupp.single 2 1 with hlaws
  have hlaws0 : laws 0 = Finsupp.single 0 1 := by simp [hlaws]
  have hlaws1 : laws 1
      = Finsupp.single 0 (3 / 4) + Finsupp.single 1 (1 / 4) := by
    simp [hlaws]
  have hlaws2 : laws 2 = Finsupp.single 2 1 := by simp [hlaws]
  have hwsingle : ∀ (a : Fin 3) (c : ℝ),
      Distribution.weight (Finsupp.single a c) = c :=
    fun a c => Distribution.weight_single a c
  have hw : ∀ i, (laws i).weight = 1 := by
    intro i
    fin_cases i
    · show (laws 0).weight = 1
      rw [hlaws0]
      exact hwsingle 0 1
    · show (laws 1).weight = 1
      rw [hlaws1, Distribution.weight_add, hwsingle, hwsingle]
      norm_num
    · show (laws 2).weight = 1
      rw [hlaws2]
      exact hwsingle 2 1
  have hnn : ∀ i, (laws i).NonNeg := by
    intro i a
    fin_cases i
    · show (0 : ℝ) ≤ laws 0 a
      rw [hlaws0, Finsupp.single_apply]
      split <;> norm_num
    · show (0 : ℝ) ≤ laws 1 a
      rw [hlaws1, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      split <;> split <;> norm_num
    · show (0 : ℝ) ≤ laws 2 a
      rw [hlaws2, Finsupp.single_apply]
      split <;> norm_num
  have hpd : ∀ i, (laws i).isProbDist := fun i => ⟨hnn i, hw i⟩
  have hv00 : laws 0 0 = 1 := by rw [hlaws0]; simp
  have hv01 : laws 0 1 = 0 := by rw [hlaws0]; simp
  have hv02 : laws 0 2 = 0 := by rw [hlaws0]; simp
  have hv10 : laws 1 0 = 3 / 4 := by rw [hlaws1]; simp
  have hv11 : laws 1 1 = 1 / 4 := by rw [hlaws1]; simp
  have hv12 : laws 1 2 = 0 := by rw [hlaws1]; simp
  have hv20 : laws 2 0 = 0 := by rw [hlaws2]; simp
  have hover : overlapDist laws = 0 := by
    refine Finsupp.ext fun a => ?_
    rw [Finsupp.coe_zero, Pi.zero_apply]
    refine le_antisymm ?_ (overlapDist_nonNeg hnn a)
    rw [overlapDist_apply]
    fin_cases a
    · exact (Finset.inf'_le _ (Finset.mem_univ 2)).trans_eq hv20
    · exact (Finset.inf'_le _ (Finset.mem_univ 0)).trans_eq hv01
    · exact (Finset.inf'_le _ (Finset.mem_univ 0)).trans_eq hv02
  have hsuplaws : supAgreement laws = 0 := by
    rw [supAgreement_eq_weight_overlapDist laws hnn hw, hover]
    simp [Distribution.weight]
  have hoverpair : overlapDist (selectPair 0 1 laws)
      = Finsupp.single 0 (3 / 4) := by
    refine Finsupp.ext fun a => ?_
    rw [overlapDist_apply, inf'_univ_fin_two, selectPair_zero, selectPair_one]
    fin_cases a
    · show min (laws 0 0) (laws 1 0) = Finsupp.single (0 : Fin 3) (3 / 4) 0
      rw [hv00, hv10, Finsupp.single_eq_same,
        min_eq_right (by norm_num : (3 / 4 : ℝ) ≤ 1)]
    · show min (laws 0 1) (laws 1 1) = Finsupp.single (0 : Fin 3) (3 / 4) 1
      rw [hv01, hv11, Finsupp.single_eq_of_ne (by decide),
        min_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    · show min (laws 0 2) (laws 1 2) = Finsupp.single (0 : Fin 3) (3 / 4) 2
      rw [hv02, hv12, Finsupp.single_eq_of_ne (by decide), min_self]
  have hsuppair : supAgreement (selectPair 0 1 laws) = 3 / 4 := by
    rw [supAgreement_eq_weight_overlapDist (selectPair 0 1 laws)
      (fun k => by
        fin_cases k
        · exact hnn 0
        · exact hnn 1)
      (w := 1)
      (fun k => by
        fin_cases k
        · exact hw 0
        · exact hw 1),
      hoverpair, hwsingle]
  have hclose := hclaim laws hpd 0 1 (by decide)
  rw [hsuplaws, hsuppair] at hclose
  have hC : ((min 3 (supportUnion laws).card : ℕ) : ℝ) ≤ 3 := by
    exact_mod_cast Nat.cast_le.mpr (min_le_left 3 _)
  linarith

end Probability
