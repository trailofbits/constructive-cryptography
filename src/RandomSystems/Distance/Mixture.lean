import RandomSystems.Distance.Distinguisher
import Probability.Lift

/-!
# Observing an initially sampled system

Decision probabilities commute with a retained initial sample. The environment and its
stopping bound are unchanged. These linearity laws follow from `RandomSystem.sLaw_mix`
and finite event-mass additivity; they use the existing compatible distinguisher carrier.
Jost's system/converter structure needs no additional independence assumption: the same
sample is retained throughout one interaction, and no adaptive sample is moved to its start.
-/

open Probability

namespace SystemAlgebra

/-- A deterministic observer's decision probability is linear in the sampled system. -/
lemma RandomSystem.decisionProbability_mix {K I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {domain : Domain (Σ i, X i) (Σ i, Y i)}
    (P : Distribution.ProbDist K) (R : K → RandomSystem _ _ domain)
    (D : DDD I X Y) (hD : IsDDD D) :
    (RandomSystem.mix P R).decisionProbability D hD =
      ∑ k ∈ P.1.support, P.1 k * (R k).decisionProbability D hD := by
  -- A decision is an event in the common once-sampled transcript law.
  rw [RandomSystem.decisionProbability, RandomSystem.sLaw_mix, Distribution.mass_finset_sum]
  simp only [Distribution.mass_smul, RandomSystem.decisionProbability]

/-- A stopping domain-compatible observer commutes with once-sampled mixtures. -/
lemma Domain.Distinguisher.probability_mix {K I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {domain : Domain (Σ i, X i) (Σ i, Y i)}
    (P : Distribution.ProbDist K) (R : K → RandomSystem _ _ domain)
    (D : domain.Distinguisher) :
    D.probability (RandomSystem.mix P R) =
      P.1.sum (fun k w => w * D.probability (R k)) := by
  -- Exchange the independent initial sample and observer-mixture sums.
  simp only [Domain.Distinguisher.probability, RandomSystem.decisionProbability_mix,
    Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro d _
  ring


end SystemAlgebra
