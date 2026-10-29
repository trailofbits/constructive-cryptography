import RandomSystems.Distance.Distinguisher
import Probability.Lift

/-!
# Decision probabilities of sampled systems

The initial mixture `RandomSystem.mix P R` chooses `k` with law `P` once, then answers every
query as `R k`; its cumulative probabilities are
`(mix P R)(h) = ∑ k ∈ supp P, P(k) · (R k)(h)`. The sample type `K` may be infinite; `P` has
finite support.

```text
                          mix P R
                  ┌────────────────────┐
     x₁, x₂, …    │ k ← P, once        │
   D ───────────► │ answer as R k      │
     ◄─────────── │                    │
     y₁, y₂, …    └────────────────────┘
```

The choice `k` stays inside the system across adaptive queries; only the replies reach `D`.
The probability of deciding `1` is linear in this mixture:

```text
Pr[D(mix P R) = 1] = ∑ k ∈ supp P, P(k) · Pr[D(R k) = 1].
```

## Main results

* `RandomSystem.decisionProbability_mix`: the identity for a deterministic distinguisher.
  At its fixed stopping bound the transcript law of the mixture is
  `∑ k, P(k) · sLaw (R k)` (`RandomSystem.sLaw_mix`), and the mass of the fixed decision
  event is linear in the law (`Distribution.mass_finset_sum`, `mass_smul`).
* `Domain.Distinguisher.probability_mix`: the identity for a compatible probabilistic
  distinguisher, `∑ d, D(d) · Pr[d(·) = 1]`. Its choice `d` and the system's choice `k`
  carry the product weight `D(d) · P(k)`; exchanging the two finite sums gives the
  component average.

`TypedSystem.transcriptDistance_sample_le` in `RandomSystems.Typed.SamplingDistance` uses
the second identity to bound the advantage between two families sampled with a common law.
-/

open Probability

namespace SystemAlgebra

/-- **The decision probability of an initial mixture**: for a deterministic distinguisher `D`,
`Pr[D(mix P R) = 1] = ∑ k ∈ supp P, P(k) · Pr[D(R k) = 1]`.
The environment, the stopping bound chosen from `hD` and the decision event are the same for
every component, so the identity is linearity of event mass; it needs no domain compatibility. -/
lemma RandomSystem.decisionProbability_mix {K I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {domain : Domain (Σ i, X i) (Σ i, Y i)}
    (P : Distribution.ProbDist K) (R : K → RandomSystem _ _ domain)
    (D : DDD I X Y) (hD : IsDDD D) :
    (RandomSystem.mix P R).decisionProbability D hD =
      ∑ k ∈ P.1.support, P.1 k * (R k).decisionProbability D hD := by
  -- At the fixed bound, sLaw (mix P R) = ∑ k, P(k) · sLaw (R k); the event mass of a finite
  -- sum is the sum of the event masses.
  rw [RandomSystem.decisionProbability, RandomSystem.sLaw_mix, Distribution.mass_finset_sum]
  -- (P(k) · sLaw (R k))(E) = P(k) · Pr[D(R k) = 1].
  simp only [Distribution.mass_smul, RandomSystem.decisionProbability]

/-- **A probabilistic distinguisher on an initial mixture**: for `D = ∑ d, D(d) · δ_d`,
`D.probability (mix P R) = ∑ k ∈ supp P, P(k) · D.probability (R k)`.
The same `D` is used for every `k`; its deterministic components `d` stop and are compatible
with the common domain by definition of `domain.Distinguisher`. The choice of `d` is
independent of the system's initial choice of `k`. -/
lemma Domain.Distinguisher.probability_mix {K I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {domain : Domain (Σ i, X i) (Σ i, Y i)}
    (P : Distribution.ProbDist K) (R : K → RandomSystem _ _ domain)
    (D : domain.Distinguisher) :
    D.probability (RandomSystem.mix P R) =
      P.1.sum (fun k w => w * D.probability (R k)) := by
  -- Unfold D as ∑ d, D(d) · Pr[d(·) = 1], linearize each d on the mixture and distribute:
  --   LHS = ∑ d ∑ k, D(d) · (P(k) · Pr[d(R k) = 1]),
  --   RHS = ∑ k ∑ d, P(k) · (D(d) · Pr[d(R k) = 1]).
  simp only [Domain.Distinguisher.probability, RandomSystem.decisionProbability_mix,
    Finsupp.sum, Finset.mul_sum]
  -- Both sums run over finite supports; exchange them so k is outside on both sides.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro d _
  -- The summands agree: D(d) · (P(k) · p) = P(k) · (D(d) · p).
  ring

end SystemAlgebra
