module

public import RandomSystems.Distance.Distinguisher
public import Probability.Lift

/-!
# Observation and distance of sampled systems

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

* `RandomSystem.transcriptDistance_mix_le_expect`: the distance of two mixtures with the same
  law is at most the expected component error. `sLaw_mix` identifies each observed law with
  a kernel mixture; `statDist_bindK_le_expect` averages its conditional distances.
  The typed and public resource-distance laws apply this result directly.
-/

@[expose] public section

open Probability
open scoped NNReal

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

/-- Retaining an index drawn from `P` bounds the distance by the expected component error:
`Δ(mix P R, mix P S) ≤ E_P[ε]`. -/
theorem RandomSystem.transcriptDistance_mix_le_expect
    -- `I` indexes ports; `X i` and `Y i` are their finite query and reply alphabets.
    {I : Type} [Fintype I] {X Y : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    -- Both families use the same domain; `P` selects one retained component `k : K`.
    {domain : Domain (Σ i, X i) (Σ i, Y i)} {K : Type}
    (P : Distribution.ProbDist K) (R S : K → RandomSystem _ _ domain)
    -- `ε k` bounds the component distance wherever the sampling law has mass.
    (ε : K → ℝ≥0)
    (bound : ∀ k ∈ P.1.support, (R k).transcriptDistance (S k) ≤ (ε k : ENNReal)) :
    (mix P R).transcriptDistance (mix P S) ≤
      (Real.toNNReal (P.1.expect (fun k => (ε k : ℝ))) : ENNReal) := by
  -- Fix one compatible observation and apply the probability-level kernel mixture bound.
  apply transcriptDistance_le
  intro E n queries compatible
  rw [sLaw_mix, sLaw_mix]
  change statDist (Distribution.bindK P.1 (fun k => (R k).sLaw E.1 n))
    (Distribution.bindK P.1 (fun k => (S k).sLaw E.1 n)) ≤ _
  calc
    _ ≤ P.1.expect (fun k => statDist ((R k).sLaw E.1 n) ((S k).sLaw E.1 n)) :=
      statDist_bindK_le_expect P.1 P.2.1 _ _
    _ ≤ P.1.expect (fun k => (ε k : ℝ)) := by
      apply Distribution.expect_mono_of_support P.2.1
      intro k supported
      exact ENNReal.ofReal_le_coe.mp
        ((statDist_le_transcriptDistance queries compatible (R k) (S k)).trans
          (bound k supported))
    _ ≤ _ := Real.le_coe_toNNReal _

end SystemAlgebra
