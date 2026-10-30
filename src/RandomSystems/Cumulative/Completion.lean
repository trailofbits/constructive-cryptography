import RandomSystems.Cumulative.Revealed

/-!
# Conditional completion of a sampled system's transcript

A sampled system `R = mix sample component` draws a retained sample `k ← sample` once and then
behaves as `component k`; an analysis record `z = record k h` depends on `k` and on the public
history `h`. At a history with `R(h) > 0`, `completionKernel` is the conditional law of the
record [1, §3.6.1],

  `completionKernel h z = ∑ₖ sample(k) · (component k)(h) · [record k h = z] / R(h)`,

The same kernel works for every environment; its inputs are `h` and the presentation
`(sample, component, record)`.

```text
  actual record:  k ← sample;  h from component k;  z = record k h
  completion:     h from R = mix sample component;  z ← completionKernel h
                  ⟹ the same joint law of (h, z), for every environment e and horizon n
```

## Main definitions

* `recordLikelihood`: the unnormalized record law at a public history `h`
* `completionKernel`: its normalization by `R(h)`, using `Distribution.normalizeOr` from
  `Probability.Lift` with an explicit point law at zero mass

## Main results

The completion reproduces the actual record's joint law in two rungs:

```text
  recordLikelihood h z = revealMass (h, z)            recordLikelihood_apply
  weight (recordLikelihood h) = R(h)                  weight_recordLikelihood
        │ weight_smul_normalizeOr: normalization followed by scaling recovers the law
        ▼
  R(h) · completionKernel h z = revealMass (h, z)     kernelMass_completionKernel
        │ both laws are [Good e n h] times these equal masses
        ▼
  kernelLaw R completionKernel e n                    kernelLaw_completionKernel
    = revealLaw sample component record e n
```

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

namespace SystemAlgebra.RandomSystem

open Probability

-- `X`, `Y`: queries and replies, `D`: the domain; `κ`: retained samples, `Z`: records.
variable {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y} {κ Z : Type}

/-- The unnormalized law of the record at public history `h`:
`recordLikelihood h = ∑ₖ sample(k) · (component k)(h) • δ(record k h)`. Sample `k` has
likelihood `sample(k) · (component k)(h)` of producing `h`. -/
noncomputable def recordLikelihood
    -- `sample : ProbDist κ`: the law of the retained sample `k`.
    (sample : Distribution.ProbDist κ)
    -- `component k`: the system with its sample fixed to `k`; `record k h`: its record.
    (component : κ → RandomSystem X Y D) (record : κ → List (X × Y) → Z)
    -- `h`: the complete public history.
    (h : List (X × Y)) : Distribution Z :=
  ∑ k ∈ sample.1.support,
    (sample.1 k * component k h) • Finsupp.single (record k h) 1

/-- The likelihood is the actual record's mass: `recordLikelihood h z = revealMass (h, z)`. -/
lemma recordLikelihood_apply (sample : Distribution.ProbDist κ)
    (component : κ → RandomSystem X Y D) (record : κ → List (X × Y) → Z)
    (h : List (X × Y)) (z : Z) :
    recordLikelihood sample component record h z = revealMass sample component record (h, z) := by
  classical
  -- Summand by summand: `δ(record k h)` charges `z` exactly when `record k h = z`.
  simp only [recordLikelihood, revealMass, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp only [mul_one, mul_zero]

/-- The likelihood is nonnegative, being a real record mass. -/
lemma recordLikelihood_nonNeg (sample : Distribution.ProbDist κ)
    (component : κ → RandomSystem X Y D) (record : κ → List (X × Y) → Z)
    (h : List (X × Y)) : (recordLikelihood sample component record h).NonNeg := by
  intro z
  rw [recordLikelihood_apply]
  exact revealMass_nonneg sample component record (h, z)

/-- Summing over every record leaves the public history mass:
`∑_z recordLikelihood h z = ∑ₖ sample(k) · (component k)(h) = R(h)`. -/
lemma weight_recordLikelihood (sample : Distribution.ProbDist κ)
    (component : κ → RandomSystem X Y D) (record : κ → List (X × Y) → Z)
    (h : List (X × Y)) :
    (recordLikelihood sample component record h).weight = mix sample component h := by
  rw [recordLikelihood, Distribution.weight_finset_sum]
  simp only [Distribution.weight_smul, Distribution.weight_single, mul_one, mix_mass]

/-- The conditional record law at public history `h`, with `R = mix sample component`:
`completionKernel h = R(h)⁻¹ • recordLikelihood h` when `R(h) ≠ 0`. When `R(h) = 0` it is
exactly the fallback `δ(record k₀ h)` for the sample `k₀ = Classical.choice sample.nonempty`;
`kernelMass` multiplies it by `R(h) = 0`. At positive mass it is a conditional law in the sense
of [1, §3.6.1, p. 65], “a probability distribution for each x ∈ X”, with the public history as
conditioning input. -/
noncomputable def completionKernel
    -- `sample` draws the retained state `k`; `component k` is the system with `k` fixed.
    (sample : Distribution.ProbDist κ) (component : κ → RandomSystem X Y D)
    -- `record k h : Z` is the analysis value of state `k` at public history `h`.
    (record : κ → List (X × Y) → Z) (h : List (X × Y)) : Distribution.ProbDist Z :=
  (recordLikelihood sample component record h).normalizeOr
    (recordLikelihood_nonNeg sample component record h)
    (Distribution.ProbDist.single (record (Classical.choice sample.nonempty) h))

/-- Multiplying the conditional law by the public history mass recovers the actual record
mass, `R(h) · completionKernel h z = revealMass (h, z)`, also where both sides are zero. -/
theorem kernelMass_completionKernel (sample : Distribution.ProbDist κ)
    (component : κ → RandomSystem X Y D) (record : κ → List (X × Y) → Z)
    (τ : List (X × Y) × Z) :
    kernelMass (mix sample component) (fun h => (completionKernel sample component record h).1) τ =
      revealMass sample component record τ := by
  obtain ⟨h, z⟩ := τ
  -- Probability level: `|recordLikelihood h| • completionKernel h = recordLikelihood h`, also
  -- at weight zero. System level: that weight is `R(h)` (`weight_recordLikelihood`) and the
  -- mass at `z` is `revealMass (h, z)` (`recordLikelihood_apply`).
  have he := Distribution.weight_smul_normalizeOr
    (recordLikelihood sample component record h)
    (recordLikelihood_nonNeg sample component record h)
    (Distribution.ProbDist.single (record (Classical.choice sample.nonempty) h))
  change mix sample component h * (completionKernel sample component record h).1 z = _
  simpa only [weight_recordLikelihood, Finsupp.smul_apply, smul_eq_mul,
    recordLikelihood_apply, completionKernel] using
      congrArg (fun μ : Distribution Z => μ z) he

/-- Conditional completion reproduces the joint law of the actual record,
`kernelLaw R completionKernel e n = revealLaw sample component record e n`, uniformly over all
environments `e` and horizons `n`; no environment enters the kernel. -/
theorem kernelLaw_completionKernel (sample : Distribution.ProbDist κ)
    (component : κ → RandomSystem X Y D) (record : κ → List (X × Y) → Z)
    -- `e`: the environment, its next query from the replies so far; `n`: the observed rounds.
    (e : List Y →. X) (n : ℕ) :
    kernelLaw (mix sample component) (fun h => (completionKernel sample component record h).1)
        e n = revealLaw sample component record e n := by
  -- Both laws are `[Good e n h]` times their masses, which agree.
  ext τ
  rw [kernelLaw_apply, revealLaw_apply, kernelMass_completionKernel]

end SystemAlgebra.RandomSystem
