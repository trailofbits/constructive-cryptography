import RandomSystems.Typed.SamplingDistance

/-! # Observation and distance of retained samples -/

open Probability SystemAlgebra
open scoped NNReal

/-- One stopping observer sees the expectation over the retained sample. -/
example {A : Interface} {K : Type} (P : Distribution.ProbDist K)
    (R : K → TypedSystem A) (D : A.inputDomain.Distinguisher) :
    D.probability (RandomSystem.mix P (fun k => (R k).1)) =
      P.1.expect (fun k => D.probability (R k).1) :=
  Domain.Distinguisher.probability_mix P _ D

/-- The common initial sample can be nonuniform; the same component bound survives. -/
example {A : Interface} {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (error : ℝ≥0)
    (bound : ∀ k, (R k).1.transcriptDistance (S k).1 ≤ error) :
    (TypedSystem.sample P R).1.transcriptDistance (TypedSystem.sample P S).1 ≤ error :=
  TypedSystem.transcriptDistance_sample_le P R S error bound

/-- A zero component error remains zero after a shared Boolean draw. -/
example {A : Interface} (R S : Bool → TypedSystem A)
    (same : ∀ b, R b = S b) :
    (TypedSystem.sample (Distribution.uniform Bool) R).1.transcriptDistance
      (TypedSystem.sample (Distribution.uniform Bool) S).1 ≤ (0 : ℝ≥0) := by
  apply TypedSystem.transcriptDistance_sample_le
  intro b
  rw [same b]
  simp [RandomSystem.transcriptDistance, statDist_self]

/-- The rule cannot silently replace the common sample by a different distribution. -/
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
