import RandomSystems.Typed.SamplingAlgebra

/-! # Retained-sample algebra in attachment proofs -/

namespace SystemAlgebra.Tests.SamplingAlgebra

open Probability

/-- A converter sees the same two initial choices whether they are sampled as one product or
through nested sampling. -/
example {A B : Interface} {K L : Type} (α : TypedConverter A B)
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K × L → TypedSystem B) :
    α • TypedSystem.sample (P.prod Q) R =
      TypedSystem.sample P (fun k => TypedSystem.sample Q (fun l => α • R (k, l))) := by
  rw [TypedSystem.sample_prod, TypedConverter.smul_sample]
  simp only [TypedConverter.smul_sample]

/-- The right component keeps each product draw while running beside a fixed left system. -/
example {A B : Interface} {K L : Type} (R : TypedSystem A)
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (S : K × L → TypedSystem B) :
    TypedSystem.parallel R (TypedSystem.sample (P.prod Q) S) =
      TypedSystem.sample P (fun k =>
        TypedSystem.sample Q (fun l => TypedSystem.parallel R (S (k, l)))) := by
  rw [TypedSystem.parallel_sample_right, TypedSystem.sample_prod]

end SystemAlgebra.Tests.SamplingAlgebra
