module

public import Commons.Constructions.TranscriptCompletion
public import RandomSystems.Typed.Completion

/-!
# System applications of probability-level observation bounds

`Tests.ProbabilityObservation` checks the distribution theorem without importing systems.
The zero-mass checks pin the fallback law and show that the completed mass and actual record
mass are both zero: `R(h) · completionKernel h z = revealMass (h, z) = 0`.
`finite_transcript_completions` assembles completion converters on `BoundedTranscript A` and
decodes their completed laws to the original list-based kernel laws.
The reversed-history check applies the observation theorem on the list type of all histories,
with `reverse` as the projection.
-/

@[expose] public section

namespace SystemAlgebra.Tests.TranscriptCompletion

open Probability Distribution Distribution.ProbDist Commons.TranscriptCompletion RandomSystem
open scoped SystemAlgebra

/-- At an impossible history, the completed mass `R(h) · completionKernel h z` and the actual
record mass are both zero. -/
example {X Y κ Z : Type} [Fintype X] [Fintype Y] {D : Domain X Y}
    -- `P` draws the retained sample `k : κ`; `component k` is the system with `k` fixed;
    -- `record k h : Z` is the record of sample `k` at history `h`.
    (P : ProbDist κ) (component : κ → RandomSystem X Y D)
    (record : κ → List (X × Y) → Z) (h : List (X × Y))
    -- `hz`: the mixture gives `h` probability zero; `z` is any record.
    (hz : mix P component h = 0) (z : Z) :
    kernelMass (mix P component)
      (fun h => (completionKernel P component record h).1) (h, z) = 0 ∧
      revealMass P component record (h, z) = 0 := by
  -- The completed mass has the factor `R(h) = 0`.
  have completed : kernelMass (mix P component)
      (fun h => (completionKernel P component record h).1) (h, z) = 0 := by
    simp only [kernelMass, hz, zero_mul]
  -- Completion reproduces the actual record mass, including at impossible histories.
  exact ⟨completed, (kernelMass_completionKernel P component record (h, z)).symm.trans completed⟩

/-- At zero history mass, completion returns the explicit point-law fallback. -/
example {X Y κ Z : Type} [Fintype X] [Fintype Y] {D : Domain X Y}
    -- `P` draws retained sample `k`; `component k` fixes it, and `record k h` gives its record.
    (P : ProbDist κ) (component : κ → RandomSystem X Y D)
    (record : κ → List (X × Y) → Z) (h : List (X × Y))
    -- `hz` makes the normalization denominator zero.
    (hz : mix P component h = 0) :
    completionKernel P component record h =
      ProbDist.single (record (Classical.choice P.nonempty) h) := by
  simp only [completionKernel, Distribution.normalizeOr, weight_recordLikelihood, hz, dite_eq_left]

/-- The finite public alphabet `BoundedTranscript A` is inferred for every interface `A`,
including a restricted one; it depends on no system or environment. -/
noncomputable example (A : Interface) : Fintype (TypedSystem.BoundedTranscript A) := inferInstance

/-- Completion converters on the finite transcript alphabet decode to the original kernel laws.
Both kernels use the same public transcript law and the same decoding map. -/
lemma finite_transcript_completions
    -- `R` supplies public transcripts on interface `A`; `K h`, `L h` are two record laws on `Z`.
    {A : Interface} {Z : Type} (R : TypedSystem A)
    (K L : List ((Σ i, A.X i) × (Σ i, A.Y i)) → ProbDist Z) :
    -- `Z'` is the finite record alphabet, decoded by `decodeZ`; `K' h`, `L' h` are the
    -- record laws at encoded history `h`.
    ∃ (Z' : Type) (instZ : Fintype Z'),
      letI := instZ
      ∃ (decodeZ : Z' → Z) (K' L' : TypedSystem.BoundedTranscript A → ProbDist Z')
        -- `cR`, `cS` append a record to the one-trigger public experiment.
        (cR cS : TypedConverter
          (experimentInterface (TypedSystem.BoundedTranscript A × Z'))
          (experimentInterface (TypedSystem.BoundedTranscript A))),
        -- `E` is the environment, `n` the cutoff; `hE` asserts compatibility with the domain.
        ∀ (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ) (hE : A.inputDomain.Compatible E),
        -- `μ` is the public transcript law of `R` on the finite alphabet.
        let μ := TypedSystem.boundedTranscriptLaw R E n hE
        cR • experiment μ = experiment (jointLaw μ K') ∧
        cS • experiment μ = experiment (jointLaw μ L') ∧
        fTransform (Prod.map Subtype.val decodeZ) (jointLaw μ K').1 =
          kernelLaw R.1 (fun h => (K h).1) E.1 n ∧
        fTransform (Prod.map Subtype.val decodeZ) (jointLaw μ L').1 =
          kernelLaw R.1 (fun h => (L h).1) E.1 n := by
  classical
  obtain ⟨Z', instZ, decodeZ, K', L', cR, cS, _, completed⟩ :=
    exists_completion_converters
      (fun h : TypedSystem.BoundedTranscript A => K h.val) (fun h => L h.val)
  let := instZ
  refine ⟨Z', instZ, decodeZ, K', L', cR, cS, ?_⟩
  intro E n hE
  let μ := TypedSystem.boundedTranscriptLaw R E n hE
  obtain ⟨hR, hS, _, _, hK, hL⟩ := completed μ
  -- Decoding the public alphabet recovers the normalized transcript law of `R`.
  let publicLaw : ProbDist (List ((Σ i, A.X i) × (Σ i, A.Y i))) :=
    ⟨R.1.sLaw E.1 n, R.1.sLaw_isProbDist (hE _ R.2) n⟩
  have publicMarginal : ProbDist.map Subtype.val μ = publicLaw :=
    Subtype.ext (TypedSystem.fTransform_boundedTranscriptLaw R E n hE)
  -- Decode the record first, then the public history. The same map works for either kernel.
  have decode (J : List ((Σ i, A.X i) × (Σ i, A.Y i)) → ProbDist Z)
      (J' : TypedSystem.BoundedTranscript A → ProbDist Z')
      (hJ : ProbDist.map (Prod.map id decodeZ) (jointLaw μ J') =
        jointLaw μ (fun h => J h.val)) :
      fTransform (Prod.map Subtype.val decodeZ) (jointLaw μ J').1 =
        kernelLaw R.1 (fun h => (J h).1) E.1 n := by
    have jointMarginal := jointLaw_map Subtype.val id publicLaw μ J (fun h => J h.val)
      publicMarginal (fun _ => Subtype.ext (fTransform_id _))
    calc
      _ = fTransform (Prod.map Subtype.val id)
          (fTransform (Prod.map id decodeZ) (jointLaw μ J').1) :=
        (fTransform_fTransform _ _ _).symm
      _ = fTransform (Prod.map Subtype.val id) (jointLaw μ (fun h => J h.val)).1 :=
        congrArg (fTransform (Prod.map Subtype.val id)) (congrArg Subtype.val hJ)
      _ = (jointLaw publicLaw J).1 := congrArg Subtype.val jointMarginal
      _ = _ := (kernelLaw_eq_jointLaw R.1 J E.1 n (hE _ R.2)).symm
  exact ⟨hR, hS, decode K K' hK, decode L L' hL⟩

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
#print axioms RandomSystem.kernelLaw_eq_jointLaw
#print axioms TypedSystem.fTransform_boundedTranscriptLaw
#print axioms TypedSystem.transcriptDistance_le_of_completion
#print axioms exists_completion_converters
#print axioms finite_transcript_completions

end SystemAlgebra.Tests.TranscriptCompletion
