module

public import ConstructiveCryptography.Instances.Mixture
public import Tests.MixtureObservation

/-!
# Closure of a specification under a retained sample

The two constant-bit systems form a specification on one Boolean reply. Their biased mixture
answers true with probability `2/3`; neither member of the specification has this behavior.
-/

@[expose] public section

namespace SystemAlgebra.Tests.SpecificationMixture

open Probability ConstructiveCryptography MixtureObservation

/-- The guarantee that transcript `h` has probability at most `p` survives a retained draw. -/
example {A B : Interface} {K : Type} (α : TypedConverter A B)
    (P : Distribution K) [Distribution.IsProbability P]
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) (p : ℝ)
    (source : K → Specification (TypedSystem B)) (ε : K → NNReal)
    (component : ∀ k, CryptographicAlgebra.Specification.ConstructsWithin α (source k)
      {R : TypedSystem A | R.1 h ≤ p} (ε k)) :
    CryptographicAlgebra.Specification.ConstructsWithin α
      (TypedSystem.sample P '' {r | ∀ k, r k ∈ source k}) {R : TypedSystem A | R.1 h ≤ p}
      (Real.toNNReal (P.expect (fun k => (ε k : ℝ)))) := by
  apply Interface.constructsWithin_sample α P ε component
  intro s admitted
  -- The mixture's transcript mass is an average of numbers bounded by the same threshold.
  change (TypedSystem.sample P s).1 h ≤ p
  rw [TypedSystem.sample_mass]
  calc
    P.expect (fun k => (s k).1 h) ≤ P.expect (fun _ => p) :=
      Distribution.expect_mono Distribution.IsProbability.nonNeg admitted
    _ = p := by rw [Distribution.expect_const, Distribution.IsProbability.weight_eq_one, mul_one]


/-- Mixing the two admitted constant replies can leave their specification. -/
example : TypedSystem.sample biasedNat natBit ∉ Set.range fixedBit := by
  rintro ⟨b, equal⟩
  -- The single true-reply transcript separates the mixture from either constant.
  have same := congrArg
    (fun R : TypedSystem bitInterface => R.1 [(⟨(), ()⟩, ⟨(), true⟩)]) equal
  cases b <;> norm_num [TypedSystem.sample_mass, biasedNat, Finsupp.support_add_eq, natBit,
    fixedBit, TypedSystem.ofFunction_mass, bitInterface] at same

#print axioms Interface.constructsWithin_sample

end SystemAlgebra.Tests.SpecificationMixture
