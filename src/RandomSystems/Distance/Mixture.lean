import RandomSystems.Distance.Distinguisher
import Probability.Lift

/-!
# Decision probabilities of sampled systems

Choose `k` with law `P`, then interact with `R k` throughout:

```text
                         sample P R
                  ┌────────────────────┐
      queries     │ k ← P, once        │
   D ───────────► │ retain R k         │
     ◄─────────── │                    │
      replies     └────────────────────┘
```

The sample is retained inside the system across adaptive queries; only the replies cross
back to `D`. Its probability of deciding `1` is the component average:

```text
Pr[D(mix P R) = 1] = ∑ k, P(k) · Pr[D(R k) = 1].
```

## Main results and proof

* `RandomSystem.decisionProbability_mix`: for a deterministic distinguisher, the event of
  deciding `1` is evaluated in the transcript mixture `RandomSystem.sLaw_mix`.
  `Distribution.mass_finset_sum` and `mass_smul` give its weighted component masses.
* `Domain.Distinguisher.probability_mix`: a probabilistic distinguisher averages those
  deterministic decisions. Its random choice and the system's initial choice have product
  weights, so exchanging the two finite sums gives the same component average.

`TypedSystem.transcriptDistance_sample_le` in `RandomSystems.Typed.SamplingDistance` uses
the second identity to bound the advantage between two families sampled with a common law.
-/

open Probability

namespace SystemAlgebra

/-- **The decision probability of an initial mixture**: a deterministic distinguisher
outputs `1` with the `P`-weighted sum of its decision probabilities on `R k`.
The environment, decision event and stopping bound supplied by `hD` are fixed across
components. This event-mass identity does not require domain compatibility. -/
lemma RandomSystem.decisionProbability_mix {K I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {domain : Domain (Σ i, X i) (Σ i, Y i)}
    (P : Distribution.ProbDist K) (R : K → RandomSystem _ _ domain)
    (D : DDD I X Y) (hD : IsDDD D) :
    (RandomSystem.mix P R).decisionProbability D hD =
      ∑ k ∈ P.1.support, P.1 k * (R k).decisionProbability D hD := by
  -- Keep the decision event fixed and sum its masses in the component transcript laws.
  rw [RandomSystem.decisionProbability, RandomSystem.sLaw_mix, Distribution.mass_finset_sum]
  -- Each component event mass carries its initial sampling weight P(k).
  simp only [Distribution.mass_smul, RandomSystem.decisionProbability]

/-- **A probabilistic distinguisher on an initial mixture**: its probability of deciding `1`
is the expectation of `D.probability (R k)` under `P`. The same `D` is used for every `k`;
its deterministic components stop and are compatible with the common domain by definition
of `domain.Distinguisher`. Its random choice is independent of the initial system choice. -/
lemma Domain.Distinguisher.probability_mix {K I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {domain : Domain (Σ i, X i) (Σ i, Y i)}
    (P : Distribution.ProbDist K) (R : K → RandomSystem _ _ domain)
    (D : domain.Distinguisher) :
    D.probability (RandomSystem.mix P R) =
      P.1.sum (fun k w => w * D.probability (R k)) := by
  -- Average first over deterministic distinguishers d, then over system choices k.
  simp only [Domain.Distinguisher.probability, RandomSystem.decisionProbability_mix,
    Finsupp.sum, Finset.mul_sum]
  -- The choices have finite support; sum over k first to recover D's probability on R k.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro d _
  -- Both orders assign the decision probability the same product weight P(k) · D(d).
  ring

end SystemAlgebra
