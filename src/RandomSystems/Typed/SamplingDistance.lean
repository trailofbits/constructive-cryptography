module

public import RandomSystems.Distance.Mixture
public import RandomSystems.Typed.Functional

/-!
# Distance between systems sampled with a common law

Draw `k` once with a finite-support probability law `P` and keep it throughout the interaction.
If the components differ by at most `ε k`, the sampled systems differ by at most `E_P[ε]`.
The type of indices may be infinite.

```text
             sample P R                           sample P S
       ┌─────────────────────┐              ┌─────────────────────┐
 D ◄──►│ k ← P, once; R k    │        D ◄──►│ k ← P, once; S k    │
       └─────────────────────┘              └─────────────────────┘
```

These are two separate experiments with the same distinguisher `D` and law `P`. Each wire
carries queries and replies; each box retains its own choice of `k` for every query.

`TypedSystem.transcriptDistance_sample_le_expect` applies
`RandomSystem.transcriptDistance_mix_le_expect` to the underlying systems.
`TypedSystem.transcriptDistance_sample_le` specializes to a constant error, whose expectation
is unchanged because `P` is normalized.
-/

@[expose] public section

open Probability
open scoped NNReal

namespace SystemAlgebra

/-- Retaining one index throughout each experiment bounds the distance by the expected
component error, `Δ(sample P R, sample P S) ≤ E_P[ε]`. -/
lemma TypedSystem.transcriptDistance_sample_le_expect {A : Interface} {K : Type}
    -- Both experiments draw their component index with law `P`.
    (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (ε : K → ℝ≥0)
    -- The component at index `k` contributes at most `ε k` to a test's advantage.
    (bound : ∀ k, (R k).1.transcriptDistance (S k).1 ≤ (ε k : ENNReal)) :
    (TypedSystem.sample P R).1.transcriptDistance (TypedSystem.sample P S).1 ≤
      (Real.toNNReal (P.expect (fun k => (ε k : ℝ))) : ENNReal) :=
  RandomSystem.transcriptDistance_mix_le_expect
    ⟨P, Distribution.IsProbability.isProbDist P⟩ (fun k => (R k).1) (fun k => (S k).1) ε
    (fun k _ => bound k)

/-- A uniform component error survives initial sampling because the weights sum to one. -/
lemma TypedSystem.transcriptDistance_sample_le {A : Interface} {K : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (h : ∀ k, (R k).1.transcriptDistance (S k).1 ≤ (error : ENNReal)) :
    (TypedSystem.sample P R).1.transcriptDistance (TypedSystem.sample P S).1 ≤
      (error : ENNReal) := by
  simpa only [Distribution.expect_const, Distribution.IsProbability.weight_eq_one, mul_one,
    Real.toNNReal_coe] using transcriptDistance_sample_le_expect P R S (fun _ => error) h

end SystemAlgebra
