/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Lift

/-!
# The coupling lemma

Lanzenberger **Lemma 2.8** (= Lemma 4 of Lanzenberger-Maurer, TCC 2020), in
two halves:

1. for **any** joint distribution of `X` and `Y`, `δ(X, Y) ≤ Pr(X ≠ Y)`;
2. there **exists** a joint distribution with `δ(X, Y) = Pr(X ≠ Y)`.

## Main definitions

* `Distribution.IsCoupling J X Y` — `J` is a joint law with marginals `X`, `Y`
* `Distribution.offDiagonalMass J` — the disagreement mass `Pr(X ≠ Y)` of a
  joint law on `A × A`
* `Distribution.optimalJoint X Y` — the joint law attaining the bound

## Main results

* `statDist_le_offDiagonalMass` — Lemma 2.8 (1)
* `exists_coupling_offDiagonalMass_eq` — Lemma 2.8 (2)
* `coupling_bound`, `optimal_coupling_exists` — the same two facts in the
  bundled `Coupling` presentation

## Design notes

**No `Fintype`.**  A coupling of laws on an infinite carrier is the case the
random-systems layer needs: the system law lives on `DDS X Y` and the
transcript law on `List (X × Option Y)`, neither of them finite.  Finite
support is already carried by `Distribution A = A →₀ ℝ`, so every statement
here runs over supports, and the bundled `Coupling` presentation at the end of
the file — which does assume `Fintype` — is a corollary of the general one,
not a second proof.

**The signed carrier.**  Over the `NNReal` carrier "joint distribution" forced
non-negativity structurally; over `Distribution A = A →₀ ℝ` it is a
hypothesis, and it is load-bearing in both halves.  In (1) it is what lets the
diagonal mass be dropped from a fiber; in (2) the constructed joint is
non-negative only because the marginals are.  Equal weight is the other honest
hypothesis of (2): a coupling forces the two marginals to share their mass.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Probability

/-! ## Couplings on an arbitrary carrier (Lanzenberger Lemma 2.8) -/

namespace Distribution

/-- **A coupling**: a joint law on `A × B` whose two marginals are the given
laws.  Lanzenberger Lemma 2.8's setup, "a joint distribution of `X` and `Y`",
with the marginals taken as pushforwards along the projections.

A `Prop` on an arbitrary joint law rather than a bundled structure: the joint
law is usually built first (or obtained from an interaction) and only then
recognized as a coupling, and the two theorems below take the recognition as a
hypothesis.  Non-negativity is deliberately *not* part of the predicate —
`IsCoupling` says the marginals are right, which is a statement about the
signed layer; the honesty of the joint law is the separate hypothesis
`∀ p, 0 ≤ J p` wherever it is needed. -/
def IsCoupling {A B : Type*} (J : Distribution (A × B)) (X : Distribution A)
    (Y : Distribution B) : Prop :=
  fTransform Prod.fst J = X ∧ fTransform Prod.snd J = Y

/-- **An honest coupling has honest marginals**, left slot.  A marginal is a
pushforward (`IsCoupling`'s own clause), and a pushforward of a non-negative
law is non-negative, so the honesty hypothesis that accompanies every coupling
statement is inherited by the two laws being coupled — it never has to be
assumed twice. -/
theorem IsCoupling.nonNeg_left {A B : Type*} {J : Distribution (A × B)}
    {X : Distribution A} {Y : Distribution B} (hJ : IsCoupling J X Y)
    (hnn : ∀ p, 0 ≤ J p) : X.NonNeg :=
  hJ.1 ▸ NonNeg.fTransform hnn Prod.fst

/-- **An honest coupling has honest marginals**, right slot
(`IsCoupling.nonNeg_left` at the second projection). -/
theorem IsCoupling.nonNeg_right {A B : Type*} {J : Distribution (A × B)}
    {X : Distribution A} {Y : Distribution B} (hJ : IsCoupling J X Y)
    (hnn : ∀ p, 0 ≤ J p) : Y.NonNeg :=
  hJ.2 ▸ NonNeg.fTransform hnn Prod.snd

/-- **The disagreement mass** `Pr_{(a,b) ∼ J}(a ≠ b)` of a joint law on
`A × A`: the mass `J` places off the diagonal.

Spelled with the library's event mass (`Distribution.mass`), which is exactly
the sum of `J` over the off-diagonal part of its support
(`offDiagonalMass_eq_sum_filter`) and brings the `mass` API — additivity,
homogeneity, pushforward — to the computations below. -/
def offDiagonalMass {A : Type*} (J : Distribution (A × A)) : ℝ :=
  J.mass (fun p => p.1 ≠ p.2)

/-- The disagreement mass as a filtered sum over **any** finite set containing
the support.  Decidability is an explicit binder, per the decidability policy
of `Probability.Distribution`. -/
theorem offDiagonalMass_eq_sum_filter {A : Type*} (J : Distribution (A × A))
    {s : Finset (A × A)} (hs : J.support ⊆ s)
    [DecidablePred fun p : A × A => p.1 ≠ p.2] :
    offDiagonalMass J = ∑ p ∈ s.filter (fun p => p.1 ≠ p.2), J p :=
  mass_eq_sum_of_support_subset J hs _

/-- An honest joint law has non-negative disagreement mass. -/
theorem offDiagonalMass_nonneg {A : Type*} {J : Distribution (A × A)}
    (hnn : ∀ p, 0 ≤ J p) : 0 ≤ offDiagonalMass J :=
  NonNeg.mass_nonneg hnn _

/-- A joint law supported entirely off the diagonal disagrees with probability
its own total weight.  This is how the transport half of an optimal coupling
is evaluated: it never charges a pair `(a, a)`. -/
theorem offDiagonalMass_eq_weight_of_forall_ne {A : Type*}
    (J : Distribution (A × A)) (h : ∀ p ∈ J.support, p.1 ≠ p.2) :
    offDiagonalMass J = J.weight := by
  classical
  rw [offDiagonalMass_eq_sum_filter J (Finset.Subset.refl _),
    Finset.filter_true_of_mem h, weight, Finsupp.sum]

/-! ### The optimal joint law -/

/-- **The optimal joint law** of `X` and `Y`: keep the shared mass `X ⊓ Y`
where it is, and transport what is left over.

  `optimalJoint X Y = diag(X ⊓ Y) + δ(X, Y)⁻¹ · ((X − Y)⁺ ⊗ (Y − X)⁺)`.

The two summands are the two things a coupling can do.  The first pushes the
pointwise meet along the diagonal `a ↦ (a, a)`: that is the mass on which the
two laws already agree, and it never disagrees.  The second is the transport
plan: the excess of `X` over `Y` has to be matched against the excess of `Y`
over `X`, and — the two residuals having equal weight `δ(X, Y)` at equal
total weight — the normalized independent product is a matching of exactly
that mass.  Nothing here is a limit or a choice: it is Lanzenberger's own
construction, written on finitely supported laws.

At `δ(X, Y) = 0` the transport term vanishes on its own (`(0 : ℝ)⁻¹ = 0` in
Lean, and the residual is `0` anyway), so the diagonal alone is the coupling
and no case split leaks into the definition. -/
def optimalJoint {A : Type*} (X Y : Distribution A) : Distribution (A × A) :=
  fTransform (fun a => (a, a)) (X ⊓ Y)
    + (statDist X Y)⁻¹ • prod ((X - Y)⁺) ((Y - X)⁺)

section OptimalJoint

variable {A : Type*} {X Y : Distribution A}

/-- The transported residual of `Y` against `X` is the negative part of the
same difference — the two residuals are the Jordan split of `X − Y`, which is
why they never charge a point together. -/
theorem posPart_sub_comm : (Y - X)⁺ = (X - Y)⁻ := by
  rw [posPart_def, negPart_def, neg_sub]

/-- The transport plan never charges the diagonal: its two factors are the
two halves of a Jordan split, and those have disjoint supports. -/
theorem forall_ne_of_mem_support_prod_posPart
    {p : A × A} (hp : p ∈ (prod ((X - Y)⁺) ((Y - X)⁺)).support) : p.1 ≠ p.2 := by
  intro hpe
  refine Finsupp.mem_support_iff.mp hp ?_
  rw [show p = (p.1, p.2) from rfl, prod_apply, hpe,
    posPart_sub_comm (X := X) (Y := Y)]
  exact posPart_mul_negPart_apply (X - Y) p.2

/-- Both residuals weigh `δ(X, Y)` when the two laws have equal total weight:
the first by definition of `δ` as the weight of a positive part, the second by
the equal-weight symmetry of `δ`.  This is what makes the normalized product a
transport plan of exactly the disagreement mass. -/
theorem weight_posPart_sub_eq_statDist (hw : X.weight = Y.weight) :
    ((X - Y)⁺).weight = statDist X Y ∧ ((Y - X)⁺).weight = statDist X Y :=
  ⟨(statDist_eq_weight_posPart X Y).symm,
    by rw [← statDist_eq_weight_posPart Y X, ← statDist_symm_of_eq_weight X Y hw]⟩

/-- The optimal joint law is honest whenever its marginals are: the diagonal
carries a pointwise meet of non-negative laws, and the transport term is a
non-negative multiple of a product of positive parts. -/
theorem optimalJoint_nonNeg (hX : X.NonNeg) (hY : Y.NonNeg) :
    (optimalJoint X Y).NonNeg := by
  have hinf : (X ⊓ Y).NonNeg :=
    nonNeg_iff_zero_le.mpr (le_inf (nonNeg_iff_zero_le.mp hX) (nonNeg_iff_zero_le.mp hY))
  intro p
  rw [optimalJoint, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  exact add_nonneg (hinf.fTransform _ p)
    (mul_nonneg (inv_nonneg.mpr (statDist_nonneg X Y))
      ((nonNeg_posPart _).prod (nonNeg_posPart _) p))

/-- **The optimal joint law is a coupling** of `X` and `Y`.

Each projection sees the diagonal term as the meet `X ⊓ Y` and the transport
term as its own residual, rescaled by `δ(X, Y)⁻¹ · δ(X, Y) = 1`; the meet plus
the one-sided excess rebuilds the marginal (`inf_add_posPart_sub`).  At
`δ(X, Y) = 0` the rescaling is `0`, but so is the residual — a non-negative
law of weight zero is zero — so the identity holds there too. -/
theorem isCoupling_optimalJoint (hw : X.weight = Y.weight) :
    IsCoupling (optimalJoint X Y) X Y := by
  obtain ⟨hP, hQ⟩ := weight_posPart_sub_eq_statDist hw
  -- Rescaling by `δ⁻¹` undoes the residual weight, `δ = 0` included.
  have hscale : ∀ Z : Distribution A, Z.NonNeg → Z.weight = statDist X Y →
      (statDist X Y)⁻¹ • (statDist X Y • Z) = Z := by
    intro Z hZ hZw
    rcases eq_or_ne (statDist X Y) 0 with h0 | h0
    · rw [eq_zero_of_nonNeg_of_weight_eq_zero hZ (by rw [hZw, h0]), smul_zero, smul_zero]
    · rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
  constructor
  · rw [optimalJoint, fTransform_add, fTransform_smul, fTransform_fTransform,
      fTransform_fst_prod, hQ, hscale _ (nonNeg_posPart _) hP,
      show fTransform (Prod.fst ∘ fun a : A => (a, a)) (X ⊓ Y) = X ⊓ Y from
        fTransform_id (X ⊓ Y)]
    exact inf_add_posPart_sub X Y
  · rw [optimalJoint, fTransform_add, fTransform_smul, fTransform_fTransform,
      fTransform_snd_prod, hP, hscale _ (nonNeg_posPart _) hQ,
      show fTransform (Prod.snd ∘ fun a : A => (a, a)) (X ⊓ Y) = X ⊓ Y from
        fTransform_id (X ⊓ Y),
      inf_comm]
    exact inf_add_posPart_sub Y X

/-- **The optimal joint law disagrees exactly with probability `δ(X, Y)`.**

The diagonal term contributes nothing — it is supported on `{(a, a)}` — and
the transport term contributes its whole weight, since it never charges the
diagonal; that weight is `δ(X, Y)⁻¹ · δ(X, Y) · δ(X, Y) = δ(X, Y)`, and at
`δ(X, Y) = 0` both sides are `0`. -/
theorem offDiagonalMass_optimalJoint (hw : X.weight = Y.weight) :
    offDiagonalMass (optimalJoint X Y) = statDist X Y := by
  obtain ⟨hP, hQ⟩ := weight_posPart_sub_eq_statDist hw
  have hdiag :
      (fTransform (fun a : A => (a, a)) (X ⊓ Y)).mass (fun p => p.1 ≠ p.2) = 0 := by
    rw [mass_fTransform]
    exact mass_eq_zero_of_forall_not _ (fun a => by simp)
  have htransport :
      offDiagonalMass (prod ((X - Y)⁺) ((Y - X)⁺)) = statDist X Y * statDist X Y := by
    rw [offDiagonalMass_eq_weight_of_forall_ne _
        (fun _ hp => forall_ne_of_mem_support_prod_posPart hp),
      weight_prod, hP, hQ]
  rw [offDiagonalMass, optimalJoint, mass_add, hdiag, mass_smul, zero_add,
    ← offDiagonalMass, htransport]
  rcases eq_or_ne (statDist X Y) 0 with h0 | h0
  · simp [h0]
  · field_simp

end OptimalJoint

end Distribution

/-- **Coupling lemma, upper bound** (Lanzenberger Lemma 2.8, part 1): for any
coupling `J` of `X` and `Y`, the statistical distance is at most the mass `J`
puts off the diagonal.

  `δ(X, Y) ≤ Pr_{(a,b) ∼ J}(a ≠ b)`.

Proof: `X a - Y a = ∑_b J(a, b) - ∑_b J(b, a)`; the diagonal entry `J(a, a)`
occurs in both fibers and cancels, leaving `X a - Y a ≤ ∑_{b ≠ a} J(a, b)`,
and summing over `a` collects exactly the off-diagonal mass.

**The non-negativity hypothesis is the signed-carrier caveat.**  Dropping the
diagonal entry from the second fiber is the step that needs `0 ≤ J (a, a)`; on
a signed joint law a negative diagonal entry would make the estimate false in
the wrong direction.  `IsCoupling` alone is a statement about marginals, so
the honesty of `J` has to be supplied separately — see the `Distribution.IsCoupling`
docstring.  No `Fintype`: all sums run over the support of `J` and its two
projections. -/
theorem statDist_le_offDiagonalMass {A : Type*} {J : Distribution (A × A)}
    {X Y : Distribution A} (hJ : Distribution.IsCoupling J X Y)
    (hnn : ∀ p, 0 ≤ J p) :
    statDist X Y ≤ Distribution.offDiagonalMass J := by
  classical
  obtain ⟨hfst, hsnd⟩ := hJ
  set s : Finset (A × A) := J.support with hs
  set t : Finset A := s.image Prod.fst ∪ s.image Prod.snd with ht
  -- The two marginals, as sums over the fibers of the two projections.
  have hX : ∀ a, X a = ∑ p ∈ s.filter (fun p => p.1 = a), J p := fun a => by
    rw [← hfst, Distribution.fTransform_apply_eq_mass,
      Distribution.mass_eq_sum_of_support_subset J (Finset.Subset.refl s)]
  have hY : ∀ a, Y a = ∑ p ∈ s.filter (fun p => p.2 = a), J p := fun a => by
    rw [← hsnd, Distribution.fTransform_apply_eq_mass,
      Distribution.mass_eq_sum_of_support_subset J (Finset.Subset.refl s)]
  -- Both marginals live on the projections of the support of `J`.
  have hsub : (X - Y).support ⊆ t := by
    intro a ha
    rcases Finset.mem_union.mp (Finsupp.support_sub ha) with h | h
    · rw [← hfst] at h
      obtain ⟨p, hp, rfl⟩ := Distribution.mem_support_fTransform _ _ h
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
    · rw [← hsnd] at h
      obtain ⟨p, hp, rfl⟩ := Distribution.mem_support_fTransform _ _ h
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
  -- Pointwise: the one-sided excess at `a` is charged to the off-diagonal
  -- pairs whose first coordinate is `a`.
  have hpt : ∀ a, max (X a - Y a) 0 ≤
      ∑ p ∈ (s.filter (fun p => p.1 ≠ p.2)).filter (fun p => p.1 = a), J p := by
    intro a
    refine max_le ?_ (Finset.sum_nonneg fun p _ => hnn p)
    have hoff :
        (s.filter (fun p => p.1 = a)).filter (fun p => ¬ p.2 = a) =
          (s.filter (fun p => p.1 ≠ p.2)).filter (fun p => p.1 = a) := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨⟨hps, h1⟩, h2⟩ => ⟨⟨hps, fun h => h2 (h.symm.trans h1)⟩, h1⟩,
        fun ⟨⟨hps, hne⟩, h1⟩ => ⟨⟨hps, h1⟩, fun h => hne (h1.trans h.symm)⟩⟩
    have hdiag :
        ∑ p ∈ (s.filter (fun p => p.1 = a)).filter (fun p => p.2 = a), J p ≤ Y a := by
      rw [hY a]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hnn p)
      intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1.1, hp.2⟩
    have hsplit :
        ∑ p ∈ (s.filter (fun p => p.1 = a)).filter (fun p => p.2 = a), J p +
          ∑ p ∈ (s.filter (fun p => p.1 = a)).filter (fun p => ¬ p.2 = a), J p =
        ∑ p ∈ s.filter (fun p => p.1 = a), J p :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [hX a, ← hsplit, ← hoff]
    linarith [hdiag]
  calc statDist X Y
      = ∑ a ∈ t, max (X a - Y a) 0 := statDist_eq_sum_of_support_subset X Y hsub
    _ ≤ ∑ a ∈ t,
          ∑ p ∈ (s.filter (fun p => p.1 ≠ p.2)).filter (fun p => p.1 = a), J p :=
        Finset.sum_le_sum fun a _ => hpt a
    _ = ∑ p ∈ s.filter (fun p => p.1 ≠ p.2), J p :=
        Finset.sum_fiberwise_of_maps_to
          (fun p hp => Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hp).1)) _
    _ = Distribution.offDiagonalMass J :=
        (Distribution.offDiagonalMass_eq_sum_filter J (Finset.Subset.refl s)).symm

/-- **Coupling lemma, attainment** (Lanzenberger Lemma 2.8, part 2): for
honest laws of equal total weight there is a coupling whose disagreement mass
is exactly the statistical distance.

  `∃ J, marginals (X, Y) ∧ J ≥ 0 ∧ Pr_J(X ≠ Y) = δ(X, Y)`.

Together with `statDist_le_offDiagonalMass` this makes `δ` the *minimum*
disagreement probability over all couplings, which is the reading the coupling
method uses: exhibiting one coupling bounds the distance, and no coupling
does better than `δ`.

Both hypotheses are honest, not technical.  Non-negativity is what makes the
constructed law a distribution at all; equal weight is forced — a coupling
shares its mass between the two marginals, so `|X| = |J| = |Y|`.  The witness
is `Distribution.optimalJoint`, and no `Fintype` is needed to build it. -/
theorem exists_coupling_offDiagonalMass_eq {A : Type*} {X Y : Distribution A}
    (hX : ∀ a, 0 ≤ X a) (hY : ∀ a, 0 ≤ Y a) (hw : X.weight = Y.weight) :
    ∃ J, Distribution.IsCoupling J X Y ∧ (∀ p, 0 ≤ J p) ∧
      Distribution.offDiagonalMass J = statDist X Y :=
  ⟨Distribution.optimalJoint X Y, Distribution.isCoupling_optimalJoint hw,
    Distribution.optimalJoint_nonNeg hX hY,
    Distribution.offDiagonalMass_optimalJoint hw⟩

/-! ## The bundled presentation

Lemma 2.8 packaged as a structure on a finite carrier. Both theorems are the
general ones above read through `prDisagree_eq_offDiagonalMass`; there is no
second proof. -/

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A coupling of two distributions over `A`: a joint (honest, non-negative)
distribution over `A × A` whose marginals are the given distributions.

Paper Lemma 4 setup: "Let Z be a joint distribution on A × A with
marginals X and Y." -/
structure Coupling (X Y : Distribution A) where
  /-- The joint distribution over A × A. -/
  joint : Distribution (A × A)
  /-- The joint law is an honest distribution: pointwise non-negative. -/
  nonneg : joint.NonNeg
  /-- First marginal equals X. -/
  marginal_fst : Distribution.fTransform Prod.fst joint = X
  /-- Second marginal equals Y. -/
  marginal_snd : Distribution.fTransform Prod.snd joint = Y

/-- The probability of disagreement in a coupling.
  Pr(X ≠ Y) := ∑_{(a,b) : a ≠ b} Z(a, b) -/
def Coupling.prDisagree {X Y : Distribution A} (C : Coupling X Y) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (A × A)).filter (fun p => p.1 ≠ p.2),
    C.joint p

omit [Fintype A] [DecidableEq A] in
/-- The bundled joint law is a coupling in the sense of
`Distribution.IsCoupling`. -/
theorem Coupling.isCoupling_joint {X Y : Distribution A} (C : Coupling X Y) :
    Distribution.IsCoupling C.joint X Y :=
  ⟨C.marginal_fst, C.marginal_snd⟩

/-- The bundled disagreement probability is the general disagreement mass: the
sum over the whole (finite) carrier and the sum over the support agree, since
the summands off the support vanish. -/
theorem Coupling.prDisagree_eq_offDiagonalMass {X Y : Distribution A}
    (C : Coupling X Y) :
    C.prDisagree = Distribution.offDiagonalMass C.joint := by
  classical
  rw [Coupling.prDisagree,
    Distribution.offDiagonalMass_eq_sum_filter C.joint (Finset.subset_univ _)]

/-- Disagreement mass of an honest coupling is non-negative. -/
theorem Coupling.prDisagree_nonneg {X Y : Distribution A}
    (C : Coupling X Y) : 0 ≤ C.prDisagree := by
  unfold Coupling.prDisagree
  exact Finset.sum_nonneg fun p _ ↦ C.nonneg p

/-- Push a coupling forward through a deterministic map on both coordinates. -/
def Coupling.fTransform {B : Type*} [Fintype B] [Nonempty B] [DecidableEq B]
    {X Y : Distribution A} (C : Coupling X Y) (f : A → B) :
    Coupling (Distribution.fTransform f X) (Distribution.fTransform f Y) where
  joint := Distribution.fTransform (fun p : A × A => (f p.1, f p.2)) C.joint
  nonneg := C.nonneg.fTransform _
  marginal_fst := by
    calc
      Distribution.fTransform Prod.fst
          (Distribution.fTransform (fun p : A × A => (f p.1, f p.2)) C.joint) =
          Distribution.fTransform (Prod.fst ∘ fun p : A × A => (f p.1, f p.2)) C.joint := by
            rw [Distribution.fTransform_comp]
      _ = Distribution.fTransform (f ∘ Prod.fst) C.joint := rfl
      _ = Distribution.fTransform f (Distribution.fTransform Prod.fst C.joint) := by
            rw [Distribution.fTransform_comp]
      _ = Distribution.fTransform f X := by
            rw [C.marginal_fst]
  marginal_snd := by
    calc
      Distribution.fTransform Prod.snd
          (Distribution.fTransform (fun p : A × A => (f p.1, f p.2)) C.joint) =
          Distribution.fTransform (Prod.snd ∘ fun p : A × A => (f p.1, f p.2)) C.joint := by
            rw [Distribution.fTransform_comp]
      _ = Distribution.fTransform (f ∘ Prod.snd) C.joint := rfl
      _ = Distribution.fTransform f (Distribution.fTransform Prod.snd C.joint) := by
            rw [Distribution.fTransform_comp]
      _ = Distribution.fTransform f Y := by
            rw [C.marginal_snd]

/-- Injective deterministic maps preserve the disagreement probability of a
pushed-forward coupling. -/
theorem Coupling.prDisagree_fTransform_of_injective
    {B : Type*} [Fintype B] [Nonempty B] [DecidableEq B] [Nonempty A]
    {X Y : Distribution A} (C : Coupling X Y) (f : A → B)
    (hf : Function.Injective f) :
    (C.fTransform f).prDisagree = C.prDisagree := by
  -- `prDisagree` is `evalPred (· ≠ ·)`, but the filter's `Decidable` instance differs
  -- from `evalPred`'s, so we bridge with `convert` and reconcile each filter (the right
  -- one via injectivity of `f`).
  simp only [Coupling.prDisagree, Coupling.fTransform]
  convert Distribution.evalPred_fTransform C.joint (fun p : A × A => (f p.1, f p.2))
      (fun x : B × B => x.1 ≠ x.2) using 1 <;>
    rw [Distribution.evalPred] <;> congr 1 <;> ext x <;> simp [Finset.mem_filter, hf.eq_iff]

/-- **Coupling lemma** (Lanzenberger Lemma 2.8, part 1) in the bundled
presentation: for any coupling `Z` of `X` and `Y`, `δ(X, Y) ≤ Pr_Z(X ≠ Y)`.

The general statement is `statDist_le_offDiagonalMass`; this is that theorem
read through `Coupling.prDisagree_eq_offDiagonalMass`. -/
theorem coupling_bound {X Y : Distribution A} (C : Coupling X Y) :
    statDist X Y ≤ C.prDisagree := by
  rw [C.prDisagree_eq_offDiagonalMass]
  exact statDist_le_offDiagonalMass C.isCoupling_joint C.nonneg

/-- **Optimal coupling existence** (Lanzenberger Lemma 2.8, part 2) in the
bundled presentation: for non-negative distributions of equal weight there is
a coupling `Z` with `δ(X, Y) = Pr_Z(X ≠ Y)`.

Equal weight is necessary, since a coupling forces the marginals to share
mass.  The general statement is `exists_coupling_offDiagonalMass_eq`, whose
witness is `Distribution.optimalJoint`; this is that theorem bundled. -/
theorem optimal_coupling_exists {X Y : Distribution A}
    (hX : X.NonNeg) (hY : Y.NonNeg) (hw : X.weight = Y.weight) :
    ∃ C : Coupling X Y, statDist X Y = C.prDisagree := by
  obtain ⟨J, hJ, hnn, hmass⟩ := exists_coupling_offDiagonalMass_eq hX hY hw
  exact ⟨⟨J, hnn, hJ.1, hJ.2⟩, by
    rw [Coupling.prDisagree_eq_offDiagonalMass, hmass]⟩

/-! ## The `n`-ary joint with prescribed marginals (Lanzenberger Lemma 2.3)

Lemma 2.8's optimal joint couples **two** laws.  Lemma 2.3 couples a whole
family: `n` laws of a *common* weight `u` admit a joint over profiles whose
`i`-th marginal is the `i`-th law.  The witness the thesis names is the
normalized product `u^{-(n-1)} ∏ᵢ Xᵢ`, built here by recursion on a list of
class indices — one factor at a time, each step normalizing by `u⁻¹`, so the
weight stays `u` throughout.

`d` is the inert profile value taken outside the coupled classes; the support
lemmas record that the joint never moves it.

This is the family joint used when each law is split into a shared component
and a residual component: apply it to each family of components, then combine
the resulting profiles pointwise.

Not stated through `IsCoupling`: that predicate is the two-marginal condition
on `A × B`, whereas the marginals here are the coordinate pushforwards
`fun p => p i` of a law on `I → CH`, which is the shape the reassembly
consumes.  `jointProfile_marginal` is the `n`-ary marginal condition. -/

namespace Distribution

/-- Thesis Lemma 2.33's joint, list form: the iterated normalized
independent coupling of a per-class family of equal-weight
sub-distributions, as one distribution over choice profiles (`d` is
the inert profile value outside the coupled classes). -/
noncomputable def jointProfileList {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (D : I → Distribution CH) : List I → Distribution (I → CH)
  | [] => Finsupp.single (fun _ => d) u
  | i :: l => u⁻¹ •
      fTransform (fun cp : CH × (I → CH) => Function.update cp.2 i cp.1)
        (prod (D i) (jointProfileList u d D l))

theorem jointProfileList_weight {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (D : I → Distribution CH) :
    ∀ l : List I, (∀ j ∈ l, (D j).weight = u) →
      (jointProfileList u d D l).weight = u := by
  intro l
  induction l with
  | nil => intro _; exact weight_single _ u
  | cons j l ih =>
      intro hw
      simp only [jointProfileList]
      rw [weight_smul, weight_fTransform, weight_prod,
        hw j (by simp), ih fun k hk => hw k (by simp [hk])]
      rcases eq_or_ne u 0 with rfl | hu
      · simp
      · rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]

theorem jointProfileList_marginal {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (D : I → Distribution CH) :
    ∀ l : List I, (∀ j ∈ l, (D j).NonNeg) →
      (∀ j ∈ l, (D j).weight = u) → ∀ i ∈ l,
      fTransform (fun p => p i) (jointProfileList u d D l) = D i := by
  intro l
  induction l with
  | nil => intro _ _ i hi; simp at hi
  | cons j l ih =>
      intro hDnn hw i hmem
      have hend : u⁻¹ • u • D i = D i := by
        rcases eq_or_ne u 0 with rfl | hu
        · rw [eq_zero_of_nonNeg_of_weight_eq_zero (hDnn i hmem) (by
            simpa using hw i hmem), smul_zero, smul_zero]
        · rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
      simp only [jointProfileList]
      rw [fTransform_smul, fTransform_comp]
      by_cases hij : i = j
      · subst hij
        have hfun : ((fun p : I → CH => p i)
            ∘ fun cp : CH × (I → CH) => Function.update cp.2 i cp.1)
            = Prod.fst := by
          funext cp
          exact Function.update_self i cp.1 cp.2
        rw [hfun, fTransform_fst_prod,
          jointProfileList_weight u d D l fun k hk => hw k (by simp [hk])]
        exact hend
      · have hi : i ∈ l := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h hij
          · exact h
        have hfun : ((fun p : I → CH => p i)
            ∘ fun cp : CH × (I → CH) => Function.update cp.2 j cp.1)
            = (fun p : I → CH => p i) ∘ Prod.snd := by
          funext cp
          exact Function.update_of_ne hij cp.1 cp.2
        rw [hfun, ← fTransform_comp, fTransform_snd_prod,
          fTransform_smul,
          ih (fun k hk => hDnn k (by simp [hk]))
            (fun k hk => hw k (by simp [hk])) i hi,
          hw j (by simp)]
        exact hend

/-- Thesis Lemma 2.33's joint over the class Finset. -/
noncomputable def jointProfile {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (C : Finset I) (D : I → Distribution CH) :
    Distribution (I → CH) :=
  jointProfileList u d D C.toList

theorem jointProfile_weight {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (C : Finset I) (D : I → Distribution CH)
    (hw : ∀ j ∈ C, (D j).weight = u) :
    (jointProfile u d C D).weight = u :=
  jointProfileList_weight u d D C.toList
    fun j hj => hw j (Finset.mem_toList.mp hj)

theorem jointProfile_marginal {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (C : Finset I) (D : I → Distribution CH)
    (hDnn : ∀ j ∈ C, (D j).NonNeg)
    (hw : ∀ j ∈ C, (D j).weight = u) {i : I} (hi : i ∈ C) :
    fTransform (fun p => p i) (jointProfile u d C D) = D i :=
  jointProfileList_marginal u d D C.toList
    (fun j hj => hDnn j (Finset.mem_toList.mp hj))
    (fun j hj => hw j (Finset.mem_toList.mp hj)) i
    (Finset.mem_toList.mpr hi)

theorem jointProfileList_nonNeg {I CH : Type*} [DecidableEq I]
    {u : ℝ} (hu : 0 ≤ u) (d : CH) (D : I → Distribution CH) :
    ∀ l : List I, (∀ j ∈ l, (D j).NonNeg) →
      (jointProfileList u d D l).NonNeg := by
  intro l
  induction l with
  | nil => intro _; exact single_nonNeg hu _
  | cons j l ih =>
      intro hD p
      simp only [jointProfileList]
      rw [Finsupp.smul_apply, smul_eq_mul]
      refine mul_nonneg (inv_nonneg.mpr hu) ?_
      exact (((hD j (by simp)).prod
        (ih fun k hk => hD k (by simp [hk]))).fTransform _) p

theorem jointProfile_nonNeg {I CH : Type*} [DecidableEq I]
    {u : ℝ} (hu : 0 ≤ u) (d : CH) (C : Finset I) {D : I → Distribution CH}
    (hD : ∀ j ∈ C, (D j).NonNeg) : (jointProfile u d C D).NonNeg :=
  jointProfileList_nonNeg hu d D C.toList
    fun j hj => hD j (Finset.mem_toList.mp hj)

/-- The joint never moves the inert value: a profile in its support takes the
value `d` at every class outside the coupled list. -/
theorem jointProfileList_support_default {I CH : Type*}
    [DecidableEq I] (u : ℝ) (d : CH) (D : I → Distribution CH) :
    ∀ (l : List I) (p : I → CH),
      p ∈ (jointProfileList u d D l).support → ∀ i, i ∉ l → p i = d := by
  classical
  intro l
  induction l with
  | nil =>
      intro p hp i _
      have hmem := Finsupp.support_single_subset hp
      rw [Finset.mem_singleton] at hmem
      rw [hmem]
  | cons j l ih =>
      intro p hp i hi
      simp only [jointProfileList] at hp
      have hp' := Finsupp.mapDomain_support (Finsupp.support_smul hp)
      obtain ⟨⟨c, q⟩, hcq, rfl⟩ := Finset.mem_image.mp hp'
      have hq : q ∈ (jointProfileList u d D l).support := by
        rw [Finsupp.mem_support_iff, prod_apply] at hcq
        exact Finsupp.mem_support_iff.mpr (mul_ne_zero_iff.mp hcq).2
      have hij : i ≠ j := fun h => hi (by simp [h])
      have hil : i ∉ l := fun h => hi (by simp [h])
      show Function.update q j c i = d
      rw [Function.update_of_ne hij]
      exact ih q hq i hil


/-- The joint of a family put together from two components leaves the inert
value untouched outside the coupled classes.  This is the two-summand form the
attainment construction consumes, where one summand is the shared component
and the other the residual. -/
theorem add_jointProfile_support_default {I CH : Type*} [DecidableEq I]
    (u u' : ℝ) (d : CH) (C : Finset I) (E F : I → Distribution CH) :
    ∀ p ∈ (jointProfile u d C E + jointProfile u' d C F).support,
      ∀ i, i ∉ C → p i = d := by
  classical
  intro p hp i hi
  have hi' : i ∉ C.toList := fun h => hi (Finset.mem_toList.mp h)
  rcases Finset.mem_union.mp (Finsupp.support_add hp) with h | h
  · exact jointProfileList_support_default u d E C.toList p h i hi'
  · exact jointProfileList_support_default u' d F C.toList p h i hi'

/-- The class-`Finset` form of `jointProfileList_support_default`. -/
theorem jointProfile_support_default {I CH : Type*} [DecidableEq I]
    (u : ℝ) (d : CH) (C : Finset I) (D : I → Distribution CH)
    {p : I → CH} (hp : p ∈ (jointProfile u d C D).support) {i : I}
    (hi : i ∉ C) : p i = d :=
  jointProfileList_support_default u d D C.toList p hp i
    fun h => hi (Finset.mem_toList.mp h)

end Distribution

end Probability
