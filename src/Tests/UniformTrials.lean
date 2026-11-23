module

public import RandomSystems.Distance.UniformTrials

/-!
# Empty, full and repeated observer trials

The equalities exercise multiplicity of occupied slots and the padding observer at zero slots.
-/

@[expose] public section

namespace Tests.UniformTrials

open SystemAlgebra Domain.Distinguisher

variable {I : Type} [Fintype I] {X Y : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}
    (pad : 𝒟.Distinguisher) (R S : RandomSystem _ _ 𝒟)
    (zeroGap : pad.signedGap R S = 0)

/-- Zero slots run the supplied fallback without sampling an empty alphabet. -/
example : uniformTrials pad (∅ : Finset (Fin 0)) Fin.elim0 = pad := rfl

/-- A nonempty slot space with no occupied trial has total signed gap zero. -/
example (trials : Fin 2 → 𝒟.Distinguisher) :
    2 * (uniformTrials pad ∅ trials).signedGap R S = 0 := by
  simpa only [Nat.cast_ofNat, Finset.sum_empty] using
    signedGap_uniformTrials pad ∅ trials R S zeroGap

/-- A full two-slot space contributes both signed gaps. -/
example (trials : Fin 2 → 𝒟.Distinguisher) :
    2 * (uniformTrials pad Finset.univ trials).signedGap R S =
      (trials 0).signedGap R S + (trials 1).signedGap R S := by
  simpa only [Nat.cast_ofNat, Fin.sum_univ_two] using
    signedGap_uniformTrials pad Finset.univ trials R S zeroGap

/-- Two occupied slots containing the same observer count its gap twice; the third is padding. -/
example (D : 𝒟.Distinguisher) :
    3 * (uniformTrials pad ({0, 1} : Finset (Fin 3)) (fun _ => D)).signedGap R S =
      D.signedGap R S + D.signedGap R S := by
  simpa [two_mul] using
    signedGap_uniformTrials pad ({0, 1} : Finset (Fin 3)) (fun _ => D) R S zeroGap

/-- A bound on deterministic query cost is required only of the occupied trials and padding. -/
example (trials : Fin 3 → 𝒟.Distinguisher) (cost : DDD I X Y → ℕ) (q : ℕ)
    (padBound : ∀ d ∈ pad.1.support, cost d.1 ≤ q)
    (trialBound : ∀ i ∈ ({0, 1} : Finset (Fin 3)), ∀ d ∈ (trials i).1.support, cost d.1 ≤ q) :
    ∀ d ∈ (uniformTrials pad {0, 1} trials).1.support, cost d.1 ≤ q :=
  uniformTrials_support pad {0, 1} trials (fun d => cost d.1 ≤ q) padBound trialBound

end Tests.UniformTrials
