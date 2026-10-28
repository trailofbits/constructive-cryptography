import RandomSystems.Typed.SamplingDistance

/-!
# Observation and distance of initially sampled systems

The observation identity is used as an expectation, then the distance theorem is applied
to an arbitrary normalized law and to zero error. The last example checks that this theorem
cannot be applied when the second family uses an unrelated law; it is an elaboration guard,
not a counterexample about the resulting distance. The final commands audit both endpoints.
-/

open Probability SystemAlgebra
open scoped NNReal

/-- A fixed compatible distinguisher's decision probability is the expectation of its
component decision probabilities. This checks the `expect` spelling of the mixture identity. -/
example {A : Interface} {K : Type} (P : Distribution.ProbDist K)
    (R : K → TypedSystem A) (D : A.inputDomain.Distinguisher) :
    D.probability (RandomSystem.mix P (fun k => (R k).1)) =
      P.1.expect (fun k => D.probability (R k).1) :=
  Domain.Distinguisher.probability_mix P _ D

/-- The bound applies to any normalized law on `K`, including nonuniform laws and infinite
sample types: finite support is supplied by `Distribution`, not by a `Fintype K` assumption. -/
example {A : Interface} {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (bound : ∀ k, (R k).1.transcriptDistance (S k).1 ≤ error) :
    (TypedSystem.sample P R).1.transcriptDistance (TypedSystem.sample P S).1 ≤ error :=
  TypedSystem.transcriptDistance_sample_le P R S error bound

/-- Equal component systems have distance zero; sampling either family with the uniform
Boolean law therefore also gives distance zero. -/
example {A : Interface} (R S : Bool → TypedSystem A)
    (same : ∀ b, R b = S b) :
    (TypedSystem.sample (Distribution.uniform Bool) R).1.transcriptDistance
      (TypedSystem.sample (Distribution.uniform Bool) S).1 ≤ (0 : ℝ≥0) := by
  -- Reduce the mixture bound to the distance of each pair of components.
  apply TypedSystem.transcriptDistance_sample_le
  intro b
  -- The components coincide, so every transcript law has zero distance from itself.
  rw [same b]
  simp [RandomSystem.transcriptDistance, statDist_self]

/-- A component bound alone does not let the common-law theorem apply to unrelated `P` and
`Q`. The guard checks that the proposed application fails to establish this stronger goal. -/
example {A : Interface} {K : Type} (P Q : Distribution K)
    [Distribution.IsProbability P] [Distribution.IsProbability Q]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (_bound : ∀ k, (R k).1.transcriptDistance (S k).1 ≤ error) : True := by
  fail_if_success
    have : (TypedSystem.sample P R).1.transcriptDistance (TypedSystem.sample Q S).1 ≤ error :=
      TypedSystem.transcriptDistance_sample_le P R S error _bound
  trivial

#print axioms Domain.Distinguisher.probability_mix
#print axioms TypedSystem.transcriptDistance_sample_le
