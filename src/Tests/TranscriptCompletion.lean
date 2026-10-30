import Commons.Constructions.TranscriptCompletion
import RandomSystems.Typed.Completion

/-!
# System applications of probability-level observation bounds

`Tests.ProbabilityObservation` checks the distribution theorem without importing systems.
Here the zero-mass check covers conditional completion at impossible public histories, and
`BoundedTranscript A` keeps the full interface bound independently of the environment.
The reversed-history check applies the observation theorem on the list type of all histories,
with `reverse` as the projection.
-/

namespace SystemAlgebra.Tests.TranscriptCompletion

open Probability Distribution Distribution.ProbDist Commons.TranscriptCompletion RandomSystem

/-- At an impossible history, `R(h) = 0`, the explicit `normalizeOr` fallback contributes no
mass: `kernelMass R completionKernel (h, z) = R(h) · completionKernel h z = 0`. -/
example {X Y κ Z : Type} [Fintype X] [Fintype Y] {D : Domain X Y}
    -- `P` samples the retained state `k : κ`; `component k` is the system with `k` fixed;
    -- `record k h : Z` is the record of state `k` at history `h`.
    (P : ProbDist κ) (component : κ → RandomSystem X Y D)
    (record : κ → List (X × Y) → Z) (h : List (X × Y))
    -- `hz`: the mixture gives `h` probability zero; `z` is any record.
    (hz : mix P component h = 0) (z : Z) :
    kernelMass (mix P component)
      (fun h => (completionKernel P component record h).1) (h, z) = 0 := by
  simp only [kernelMass, hz, zero_mul]

/-- The finite public alphabet `BoundedTranscript A` is inferred for every interface `A`,
including a restricted one; it depends on no system or environment. -/
noncomputable example (A : Interface) : Fintype (TypedSystem.BoundedTranscript A) := inferInstance

/-- An H-coefficient comparison of reversed histories bounds the original distance. The
observations are `μ_T = reverse_* (T.sLaw E n)` on the unbounded list type, with no finiteness
assumption or product encoding; `π = reverse` decodes them. The premises are required only
for compatible stopping environments. -/
example
    -- `R S : TypedSystem A` are systems on the public interface `A`.
    {A : Interface} (R S : TypedSystem A)
    -- `ε h ≥ 0` is the loss on the reversed history `h`; `b` bounds its ideal expectation.
    (ε : List ((Σ i, A.X i) × (Σ i, A.Y i)) → ℝ) (hε : ∀ h, 0 ≤ ε h) {b : NNReal}
    -- `ratio`: `(1 − ε h) · μ_S(h) ≤ μ_R(h)` for each compatible `E` stopping within `n`.
    (ratio : ∀ (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) n,
      QueryBounded n E → A.inputDomain.Compatible E → ∀ h,
      (1 - ε h) * fTransform List.reverse (S.1.sLaw E.1 n) h ≤
        fTransform List.reverse (R.1.sLaw E.1 n) h)
    -- `bound`: `𝔼_μ_S[ε] ≤ b` for each such experiment.
    (bound : ∀ (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) n,
      QueryBounded n E → A.inputDomain.Compatible E →
      (fTransform List.reverse (S.1.sLaw E.1 n)).expect ε ≤ b) :
    R.1.transcriptDistance S.1 ≤ b := by
  -- `μ_T = reverse_* (T.sLaw E n)`, a probability law because `E` is compatible.
  let observation (T : TypedSystem A)
      (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ)
      (_hn : QueryBounded n E) (hE : A.inputDomain.Compatible E) :=
    ProbDist.map List.reverse ⟨T.1.sLaw E.1 n, T.1.sLaw_isProbDist (hE _ T.2) n⟩
  -- Exact marginal: `reverse_* μ_T = (reverse ∘ reverse)_* (T.sLaw E n) = T.sLaw E n`.
  -- `reverse` is an invertible encoding of the public history.
  have marginal (T : TypedSystem A) E n hn hE :
      fTransform List.reverse (observation T E n hn hE).1 = T.1.sLaw E.1 n := by
    change fTransform List.reverse (fTransform List.reverse (T.1.sLaw E.1 n)) = _
    exact (fTransform_comp_eq_of_pointwise List.reverse List.reverse _
      (T.1.sLaw E.1 n) (fun h => List.reverse_reverse h)).trans (fTransform_id _)
  -- The observation ratio theorem with `π = reverse`, `W` the list type, and both marginals.
  exact transcriptDistance_le_of_observation_ratio R.1 S.1 List.reverse
    (observation R) (observation S) (marginal R) (marginal S) ε hε ratio bound

#print axioms RandomSystem.transcriptDistance_le_iSup_observation
#print axioms RandomSystem.transcriptDistance_le_of_observation_ratio
#print axioms RandomSystem.kernelMass_completionKernel
#print axioms RandomSystem.kernelLaw_completionKernel
#print axioms TypedSystem.fTransform_boundedTranscriptLaw
#print axioms TypedSystem.transcriptDistance_le_of_completion
#print axioms exists_completion_converters

end SystemAlgebra.Tests.TranscriptCompletion
