import RandomSystems.Cumulative.CumulativeOperations
import Probability.Expectation
import Probability.Lift

/-!
# Revealed transcript laws

```text
real:  sample k ─► component k ─► transcript h ─► (h, reveal k h)
ideal: system S ────────────────► transcript h ─► sample z from K h ─► (h, z)
```

Jha, *Provable Security of Symmetric-key Cryptographic Schemes*, §2.2.1,
printed p. 19, permits “additional information” after interaction. `revealLaw` and
`kernelLaw` represent its two extended transcript laws. The marginal lemmas recover the
original transcript laws; the reveal is a proof device, not a new interface or quotient.
The point masses `revealMass` and `kernelMass` omit the common environment indicator.
-/

namespace SystemAlgebra.RandomSystem

open Probability

variable {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y} {κ Z : Type}

/-- **The revealed transcript law** of a mixture: sample `k`, interact, and reveal
`reveal k h` after the transcript `h`. -/
noncomputable def revealLaw (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (e : List Y →. X) (n : ℕ) :
    Distribution (List (X × Y) × Z) :=
  ∑ k ∈ P.1.support, P.1 k • Distribution.fTransform (fun h => (h, reveal k h)) ((R k).sLaw e n)

/-- **The kernel transcript law**: interact, then sample the revealed value from `K h`. -/
noncomputable def kernelLaw (S : RandomSystem X Y D) (K : List (X × Y) → Distribution Z)
    (e : List Y →. X) (n : ℕ) : Distribution (List (X × Y) × Z) :=
  ∑ h ∈ (S.sLaw e n).support, S.sLaw e n h • Distribution.fTransform (fun z => (h, z)) (K h)

open Classical in
/-- **The real probability of an extended transcript** `(h, z)`: the probability over the
sample that the system answers the transcript `h` and reveals `z`. It does not depend on the
environment. -/
noncomputable def revealMass (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (τ : List (X × Y) × Z) : ℝ :=
  ∑ k ∈ P.1.support, P.1 k * if reveal k τ.1 = τ.2 then R k τ.1 else 0

/-- **The ideal probability of an extended transcript** `(h, z)`: the system answers `h`, and
the kernel then reveals `z`. -/
noncomputable def kernelMass (S : RandomSystem X Y D) (K : List (X × Y) → Distribution Z)
    (τ : List (X × Y) × Z) : ℝ :=
  S τ.1 * K τ.1 τ.2

lemma revealMass_nonneg (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (τ : List (X × Y) × Z) : 0 ≤ revealMass P R reveal τ :=
  Finset.sum_nonneg fun k _ => mul_nonneg (P.2.1 k) (by
    split_ifs
    · exact (R k).mass_nonneg _
    · exact le_rfl)

open Classical in
/-- The revealed transcript law is the transcript indicator times the real probability. -/
lemma revealLaw_apply (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (e : List Y →. X) (n : ℕ) (τ : List (X × Y) × Z) :
    revealLaw P R reveal e n τ = if Good e n τ.1 then revealMass P R reveal τ else 0 := by
  classical
  -- Fix the transcript and sum only samples with the stated revealed value.
  obtain ⟨h, z⟩ := τ
  -- Projection to the transcript makes the graph map injective.
  have hpoint : ∀ k, Distribution.fTransform (fun h' => (h', reveal k h')) ((R k).sLaw e n)
      (h, z) = if reveal k h = z then (R k).sLaw e n h else 0 := by
    intro k
    split_ifs with hz
    · subst hz
      exact Distribution.fTransform_injective_apply _ _
        (fun a b hab => congrArg Prod.fst hab) h
    · rw [Distribution.fTransform_apply_eq_mass]
      exact Distribution.mass_eq_zero_of_forall_not _ fun h' he => hz (by
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        rfl)
  -- The same environment indicator applies to every real component.
  simp only [revealLaw, revealMass, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    hpoint, sLaw_apply]
  split_ifs with hg <;> simp

open Classical in
/-- The kernel transcript law is the transcript indicator times the ideal probability. -/
lemma kernelLaw_apply (S : RandomSystem X Y D) (K : List (X × Y) → Distribution Z)
    (e : List Y →. X) (n : ℕ) (τ : List (X × Y) × Z) :
    kernelLaw S K e n τ = if Good e n τ.1 then kernelMass S K τ else 0 := by
  classical
  obtain ⟨h, z⟩ := τ
  simp only [kernelLaw, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  -- Only the term with this transcript can contribute.
  rw [Finset.sum_eq_single h]
  · rw [Distribution.fTransform_injective_apply _ _ (fun a b hab => congrArg Prod.snd hab) z,
      sLaw_apply, kernelMass]
    split_ifs <;> simp
  · intro h' _ hne
    rw [Distribution.fTransform_apply_eq_mass,
      Distribution.mass_eq_zero_of_forall_not _ fun z' he => hne (congrArg Prod.fst he), mul_zero]
  · intro hh
    rw [Finsupp.notMem_support_iff.mp hh, zero_mul]

lemma kernelLaw_nonNeg (S : RandomSystem X Y D) {K : List (X × Y) → Distribution Z}
    (hK : ∀ h, (K h).isProbDist) (e : List Y →. X) (n : ℕ) : (kernelLaw S K e n).NonNeg := by
  -- Both the transcript mass and the conditional reveal mass are nonnegative.
  intro τ
  simp only [kernelLaw, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun h _ => mul_nonneg (sLaw_nonNeg n h) ((hK h).1.fTransform _ τ)

/-- The revealed law's transcript marginal is the transcript law. -/
lemma fTransform_fst_revealLaw (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (e : List Y →. X) (n : ℕ) :
    Distribution.fTransform Prod.fst (revealLaw P R reveal e n) = (mix P R).sLaw e n := by
  -- Forgetting the deterministic reveal leaves each component law unchanged.
  rw [revealLaw, Distribution.fTransform_sum, sLaw_mix]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Distribution.fTransform_smul, Distribution.fTransform_fTransform]
  exact congrArg _ (Distribution.fTransform_id _)

/-- The kernel law's transcript marginal is the transcript law. -/
lemma fTransform_fst_kernelLaw (S : RandomSystem X Y D) {K : List (X × Y) → Distribution Z}
    (hK : ∀ h, (K h).isProbDist) (e : List Y →. X) (n : ℕ) :
    Distribution.fTransform Prod.fst (kernelLaw S K e n) = S.sLaw e n := by
  -- Forgetting the conditional reveal leaves its total weight at the transcript.
  have hconst : ∀ (h : List (X × Y)) (W : Distribution Z),
      Distribution.fTransform (fun _ => h) W = Finsupp.single h W.weight := by
    intro h W
    rw [Distribution.fTransform, Distribution.weight_eq_finsupp_sum, Finsupp.sum, Finsupp.sum,
      Finsupp.single_finsetSum]
  -- Each conditional reveal law has weight one.
  rw [kernelLaw, Distribution.fTransform_sum]
  simp only [Distribution.fTransform_smul, Distribution.fTransform_fTransform, Function.comp_def,
    hconst, (hK _).weight_eq, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Finsupp.sum_single (S.sLaw e n)

/-- **The kernel law's probability of an event** is the transcript law's expectation of the
revealed value's probability of it. -/
lemma kernelLaw_mass_eq_expect (S : RandomSystem X Y D) (K : List (X × Y) → Distribution Z)
    (e : List Y →. X) (n : ℕ) (P : List (X × Y) × Z → Prop) :
    (kernelLaw S K e n).mass P =
      (S.sLaw e n).expect fun h => (K h).mass fun z => P (h, z) := by
  classical
  -- Sum the event probability conditional on each transcript.
  unfold kernelLaw Distribution.expect Finsupp.sum
  induction (S.sLaw e n).support using Finset.induction_on with
  | empty => simp [Distribution.mass]
  | insert h s hh ih =>
    rw [Finset.sum_insert hh, Finset.sum_insert hh, Distribution.mass_add, ih,
      Distribution.mass_smul, Distribution.mass_fTransform]

end SystemAlgebra.RandomSystem
