module

public import ConstructiveCryptography.Instances.Algebra
public import ConstructiveCryptography.Specification.Mixture

/-!
# Constructions from retained samples

A converter commutes with one retained draw. If the ideal specification admits samples with the
chosen law, component constructions give a construction with their expected error.
-/

@[expose] public section

namespace SystemAlgebra.Interface

open Probability ConstructiveCryptography
open scoped SystemAlgebra NNReal

/-- Attach `α` after sampling from the input specifications. At index `k`, choose an ideal
with error `ε k`. The ideal mixture belongs to `target` and the error averages to `E_P[ε]`. -/
lemma constructsWithin_sample {A B : Interface} {K : Type}
    -- `α` exposes interface `A` using a resource at `B`; `P` selects the retained component.
    (α : TypedConverter A B) (P : Distribution K) [Distribution.IsProbability P]
    {source : K → Specification (TypedSystem B)} {target : Specification (TypedSystem A)}
    (ε : K → ℝ≥0)
    (component : ∀ k, CryptographicAlgebra.Specification.ConstructsWithin α
      (source k) target (ε k))
    -- Closure is relative to this particular law `P`.
    (closed : ∀ s : K → TypedSystem A, (∀ k, s k ∈ target) → TypedSystem.sample P s ∈ target) :
    CryptographicAlgebra.Specification.ConstructsWithin α
      (TypedSystem.sample P '' {r | ∀ k, r k ∈ source k}) target
      (Real.toNNReal (P.expect (fun k => (ε k : ℝ)))) := by
  let _ := TypedSystem.transcriptPseudoEMetricSpace A
  exact Specification.ConstructsWithin.mixture (f := fun r => α • r)
    (ε := fun k => (ε k : ENNReal)) component (TypedSystem.sample P) (TypedSystem.sample P)
    (TypedConverter.smul_sample α P) closed (fun a b => distance_sample_le_expect P a b ε)

end SystemAlgebra.Interface
