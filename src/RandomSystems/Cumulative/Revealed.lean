import RandomSystems.Cumulative.CumulativeOperations
import Probability.Expectation
import Probability.Lift

/-!
# Revealed transcript laws

The extended transcript laws `(h, z)` of the expectation method: a transcript `h` followed by
a value `z` revealed at the end of the interaction. The real system is a mixture
`mix P R = ∑ₖ P(k) · R k` and reveals `z = reveal k h`, a function of its sample and the
transcript; the ideal system `S` samples `z` from a law `K h` conditional on the transcript.

```text
          ┌───────────┐
  e ──x──▶│ k ← P     │    transcript h, then z = reveal k h
    ◀──y──│ R k       │
          └───────────┘
          ┌───────────┐
  e ──x──▶│ S         │    transcript h, then z ← K h
    ◀──y──│           │
          └───────────┘
```

Forgetting `z` (`Prod.fst`) gives back the transcript laws of `mix P R` and `S`.

## Main definitions

* `revealLaw P R reveal e n`, `kernelLaw S K e n`: the real and ideal extended transcript laws
* `revealMass P R reveal`, `kernelMass S K`: the systems' probabilities of an extended
  transcript, without the environment

## Main results

* `revealLaw_apply`, `kernelLaw_apply`: each law is `[Good e n h]` times its mass
* `fTransform_fst_revealLaw`, `fTransform_fst_kernelLaw`: the transcript marginals
* `kernelLaw_mass_eq_expect`: the ideal probability of an event, conditioned on the transcript

Source: Jha, *Provable Security of Symmetric-key Cryptographic Schemes*, §2.2.1, printed p. 19.
-/

namespace SystemAlgebra.RandomSystem

open Probability

variable {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y} {κ Z : Type}

/-- **The revealed transcript law** of the mixture `mix P R` under the environment `e` within
`n` rounds: sample `k ← P`, interact with `R k`, then append `reveal k h` to the transcript `h`,
`revealLaw = ∑ₖ P(k) • fTransform (h ↦ (h, reveal k h)) ((R k).sLaw e n)`.

Jha, §2.2.1, printed p. 19: the transcript “may also include any additional information the
oracle chooses to reveal to the distinguisher at the end of the query-response phase of the
game.” -/
noncomputable def revealLaw (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (e : List Y →. X) (n : ℕ) :
    Distribution (List (X × Y) × Z) :=
  ∑ k ∈ P.1.support, P.1 k • Distribution.fTransform (fun h => (h, reveal k h)) ((R k).sLaw e n)

/-- **The kernel transcript law** of `S` under `e` within `n` rounds: interact with `S`, then
sample the revealed value from `K h`,
`kernelLaw = ∑_h (S.sLaw e n)(h) • fTransform (z ↦ (h, z)) (K h)`. -/
noncomputable def kernelLaw (S : RandomSystem X Y D) (K : List (X × Y) → Distribution Z)
    (e : List Y →. X) (n : ℕ) : Distribution (List (X × Y) × Z) :=
  ∑ h ∈ (S.sLaw e n).support, S.sLaw e n h • Distribution.fTransform (fun z => (h, z)) (K h)

open Classical in
/-- **The real probability of an extended transcript** `(h, z)`: the probability, over
`k ← P`, that `R k` gives the replies of `h` to its queries and `reveal k h = z`,
`revealMass (h, z) = ∑ₖ P(k) · [reveal k h = z] · (R k)(h)`. No environment appears. -/
noncomputable def revealMass (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (τ : List (X × Y) × Z) : ℝ :=
  ∑ k ∈ P.1.support, P.1 k * if reveal k τ.1 = τ.2 then R k τ.1 else 0

/-- **The ideal probability of an extended transcript** `(h, z)`: `S` gives the replies of `h`,
and `K h` then samples `z`, `kernelMass (h, z) = S(h) · K h z`. No environment appears. -/
noncomputable def kernelMass (S : RandomSystem X Y D) (K : List (X × Y) → Distribution Z)
    (τ : List (X × Y) × Z) : ℝ :=
  S τ.1 * K τ.1 τ.2

/-- The real probability of an extended transcript is nonnegative. -/
lemma revealMass_nonneg (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (τ : List (X × Y) × Z) : 0 ≤ revealMass P R reveal τ :=
  Finset.sum_nonneg fun k _ => mul_nonneg (P.2.1 k) (by
    split_ifs
    · exact (R k).mass_nonneg _
    · exact le_rfl)

open Classical in
/-- **The revealed law at an extended transcript**:
`revealLaw (h, z) = [Good e n h] · revealMass (h, z)`, where `Good e n h` says that `h` follows
`e` and is complete within `n` rounds. -/
lemma revealLaw_apply (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (e : List Y →. X) (n : ℕ) (τ : List (X × Y) × Z) :
    revealLaw P R reveal e n τ = if Good e n τ.1 then revealMass P R reveal τ else 0 := by
  classical
  -- Only the samples `k` with `reveal k h = z` contribute.
  obtain ⟨h, z⟩ := τ
  -- The graph `h' ↦ (h', reveal k h')` is injective (its first coordinate is `h'`), so its
  -- pushforward at `(h, z)` is `[reveal k h = z] · (R k).sLaw e n h`.
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
  -- `(R k).sLaw e n h = [Good e n h] · (R k)(h)`; the indicator is the same for every `k`.
  simp only [revealLaw, revealMass, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    hpoint, sLaw_apply]
  split_ifs with hg <;> simp only [mul_ite, mul_zero, ite_self, Finset.sum_const_zero]

open Classical in
/-- **The kernel law at an extended transcript**:
`kernelLaw (h, z) = [Good e n h] · kernelMass (h, z)`. -/
lemma kernelLaw_apply (S : RandomSystem X Y D) (K : List (X × Y) → Distribution Z)
    (e : List Y →. X) (n : ℕ) (τ : List (X × Y) × Z) :
    kernelLaw S K e n τ = if Good e n τ.1 then kernelMass S K τ else 0 := by
  classical
  obtain ⟨h, z⟩ := τ
  simp only [kernelLaw, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  -- Only the summand of the transcript `h` charges `(h, z)`.
  rw [Finset.sum_eq_single h]
  -- That summand is `(S.sLaw e n)(h) · K h z = [Good e n h] · S(h) · K h z`.
  · rw [Distribution.fTransform_injective_apply _ _ (fun a b hab => congrArg Prod.snd hab) z,
      sLaw_apply, kernelMass]
    split_ifs <;> simp only [zero_mul]
  -- Another transcript `h'` puts no mass on `(h, z)`.
  · intro h' _ hne
    rw [Distribution.fTransform_apply_eq_mass,
      Distribution.mass_eq_zero_of_forall_not _ fun z' he => hne (congrArg Prod.fst he), mul_zero]
  -- A transcript outside the support of the transcript law has weight zero.
  · intro hh
    rw [Finsupp.notMem_support_iff.mp hh, zero_mul]

/-- The kernel transcript law is nonnegative when every conditional reveal law `K h` is:
`kernelLaw (h, z) = (S.sLaw e n)(h) · K h z ≥ 0`. No normalization of `K` is needed. -/
lemma kernelLaw_nonNeg (S : RandomSystem X Y D) {K : List (X × Y) → Distribution Z}
    (hK : ∀ h, (K h).NonNeg) (e : List Y →. X) (n : ℕ) : (kernelLaw S K e n).NonNeg := by
  -- Both the transcript mass and the conditional reveal mass are nonnegative.
  intro τ
  simp only [kernelLaw, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun h _ => mul_nonneg (sLaw_nonNeg n h) ((hK h).fTransform _ τ)

/-- **The transcript marginal of the revealed law** is the transcript law of the mixture:
`fTransform Prod.fst (revealLaw P R reveal e n) = (mix P R).sLaw e n`. -/
lemma fTransform_fst_revealLaw (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (reveal : κ → List (X × Y) → Z) (e : List Y →. X) (n : ℕ) :
    Distribution.fTransform Prod.fst (revealLaw P R reveal e n) = (mix P R).sLaw e n := by
  -- `Prod.fst ∘ (h ↦ (h, reveal k h)) = id`, so each component keeps its transcript law, and
  -- `sLaw_mix` sums them to the law of the mixture.
  rw [revealLaw, Distribution.fTransform_sum, sLaw_mix]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Distribution.fTransform_smul, Distribution.fTransform_fTransform]
  exact congrArg _ (Distribution.fTransform_id _)

/-- **The transcript marginal of the kernel law** is the transcript law of `S`, when every
`K h` is a probability law: `fTransform Prod.fst (kernelLaw S K e n) = S.sLaw e n`. -/
lemma fTransform_fst_kernelLaw (S : RandomSystem X Y D) {K : List (X × Y) → Distribution Z}
    (hK : ∀ h, (K h).isProbDist) (e : List Y →. X) (n : ℕ) :
    Distribution.fTransform Prod.fst (kernelLaw S K e n) = S.sLaw e n := by
  -- Forgetting `z` collapses the conditional law `K h` to its weight at `h`.
  have hconst : ∀ (h : List (X × Y)) (W : Distribution Z),
      Distribution.fTransform (fun _ => h) W = Finsupp.single h W.weight := by
    intro h W
    rw [Distribution.fTransform, Distribution.weight_eq_finsupp_sum, Finsupp.sum, Finsupp.sum,
      Finsupp.single_finsetSum]
  -- Each `K h` has weight one, which leaves `∑_h (S.sLaw e n)(h) • δ_h = S.sLaw e n`.
  rw [kernelLaw, Distribution.fTransform_sum]
  simp only [Distribution.fTransform_smul, Distribution.fTransform_fTransform, Function.comp_def,
    hconst, (hK _).weight_eq, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Finsupp.sum_single (S.sLaw e n)

/-- **The ideal probability of an event, conditioned on the transcript**:
`kernelLaw(P) = 𝔼_{h ∼ S.sLaw e n}[(K h){z | P (h, z)}]`. No normalization of `K` is needed. -/
lemma kernelLaw_mass_eq_expect (S : RandomSystem X Y D) (K : List (X × Y) → Distribution Z)
    (e : List Y →. X) (n : ℕ) (P : List (X × Y) × Z → Prop) :
    (kernelLaw S K e n).mass P =
      (S.sLaw e n).expect fun h => (K h).mass fun z => P (h, z) := by
  classical
  -- Linearity over the finite transcript support leaves each conditional event mass.
  rw [kernelLaw, Distribution.mass_finset_sum]
  -- Summand `h`: `(S.sLaw e n)(h) · (fTransform (z ↦ (h, z)) (K h))(P)`, and the pushforward's
  -- mass is `(K h){z | P (h, z)}`, the summand of the expectation.
  simp only [Distribution.mass_smul, Distribution.mass_fTransform, Distribution.expect,
    Finsupp.sum]

end SystemAlgebra.RandomSystem
