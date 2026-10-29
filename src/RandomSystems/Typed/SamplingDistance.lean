import RandomSystems.Distance.Mixture
import RandomSystems.Typed.Functional

/-!
# Distance between systems sampled with a common law

Let `R k` and `S k` be typed systems on the same interface `A` with
`Δ(R k, S k) ≤ error` for every `k`. Sampling both families with the same normalized law `P`,
`sample P R = mix P R`, keeps the bound: `Δ(sample P R, sample P S) ≤ error`. `P` may be
nonuniform and `K` infinite; `P` has finite support.

```text
             sample P R                           sample P S
       ┌─────────────────────┐              ┌─────────────────────┐
 D ◄──►│ k ← P, once; R k    │        D ◄──►│ k ← P, once; S k    │
       └─────────────────────┘              └─────────────────────┘
```

These are two separate experiments with the same distinguisher `D` and law `P`. Each wire
carries queries and replies; each box retains its own choice of `k` for every query.

## Main results

* `TypedSystem.transcriptDistance_sample_le`: a uniform component bound survives sampling with
  a common law.

## Proof

For a fixed compatible `D`, both decision probabilities are averages over the same `k`:

```text
|Pr[D(sample P R) = 1] − Pr[D(sample P S) = 1]|
  = |∑ k ∈ supp P, P(k) · (Pr[D(R k) = 1] − Pr[D(S k) = 1])|     probability_mix
  ≤ ∑ k ∈ supp P, P(k) · error = error                            abs_average_sub_le
```

* `RandomSystem.transcriptDistance_le_of_advantage_le` reduces the distance to the
  advantage of an arbitrary distinguisher compatible with the interface domain.
* `Domain.Distinguisher.probability_mix` (`RandomSystems.Distance.Mixture`) writes both
  decision probabilities as `P`-averages.
* `abs_average_sub_le` (`RandomSystems.Distance.Transcript`) bounds the gap of two averages by
  a common bound on the gaps at each `k`; it uses `P(k) ≥ 0` and `∑ k, P(k) = 1`.
* `Domain.Distinguisher.advantage_le_transcriptDistance` bounds the gap at `k` by
  `Δ(R k, S k) ≤ error`.
-/

open Probability
open scoped NNReal

namespace SystemAlgebra

/-- **A common distance bound survives initial sampling**:
`(∀ k, Δ(R k, S k) ≤ error) → Δ(sample P R, sample P S) ≤ error`.
Both experiments use the same normalized law `P` and are compared at the same `k`; since
`P(k) ≥ 0` and `∑ k, P(k) = 1`, the weighted bound `∑ k, P(k) · error` is `error`. Each
experiment samples `k` once and answers every query with that component. -/
lemma TypedSystem.transcriptDistance_sample_le {A : Interface} {K : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (h : ∀ k, (R k).1.transcriptDistance (S k).1 ≤ (error : ENNReal)) :
    (TypedSystem.sample P R).1.transcriptDistance (TypedSystem.sample P S).1 ≤
      (error : ENNReal) := by
  -- The distance is the supremum of advantages; fix any compatible distinguisher D.
  apply RandomSystem.transcriptDistance_le_of_advantage_le
    (TypedSystem.sample P R).2 (TypedSystem.sample P S).2
  intro D
  -- sample P R = mix P R, so the two decision probabilities are ∑ k, P(k) · f k and
  -- ∑ k, P(k) · g k, with f k = D.probability (R k) and g k = D.probability (S k).
  simp only [TypedSystem.sample, Domain.Distinguisher.probability_mix]
  -- |∑ k, P(k) · (f k − g k)| ≤ error once |f k − g k| ≤ error at each k, as ∑ k, P(k) = 1.
  apply abs_average_sub_le ⟨P, Distribution.IsProbability.isProbDist P⟩
  intro k
  -- ofReal |f k − g k| = adv_D(R k, S k) ≤ Δ(R k, S k) ≤ error; read back as a real bound.
  exact (ENNReal.ofReal_le_coe).mp
    ((D.advantage_le_transcriptDistance (R k).2 (S k).2).trans (h k))

end SystemAlgebra
