module

public import RandomSystems.Distance.Distinguisher
public import Probability.Kernel
public import Probability.Expectation

/-!
# Signed gaps of sampled distinguishers

Draw one index `k ∼ μ` and run the chosen distinguisher `D k` for the whole interaction.
`probability_bind` averages its decision probabilities. Subtracting them for two systems gives
`signedGap_bind`: opposite signs can cancel before taking absolute advantage.
-/

@[expose] public section

namespace SystemAlgebra.Domain.Distinguisher

open Probability Distribution

variable
  -- At port `i : I`, a query has type `X i` and a reply has type `Y i`.
  {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  -- `𝒟` specifies the histories and queries admitted by both systems.
  {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

/-- The signed decision gap is `Pr[D(R) = 1] − Pr[D(S) = 1]`. -/
noncomputable def signedGap (D : 𝒟.Distinguisher)
    (R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) : ℝ :=
  D.probability R - D.probability S

variable
  -- `μ` chooses the index once. Each `family k` is a law of compatible stopping observers.
  {K : Type*} (μ : ProbDist K) (family : K → 𝒟.Distinguisher)

/-- The probability of deciding one is the mean of the selected observers' probabilities. -/
lemma probability_bind (R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) :
    probability (μ.bind family) R = μ.1.expect (fun k => (family k).probability R) :=
  -- Decision probability evaluates a linear functional on the mixture of observers.
  Finsupp.apply_linearCombination ℝ
    (Finsupp.linearCombination ℝ fun D : {D : DDD I X Y // IsDDD D ∧ 𝒟.DecisionCompatible D} =>
      R.decisionProbability D.1 D.2.1)
    (fun k => (family k).1) μ.1

/-- The signed gap of the sampled observer is the mean of the signed gaps on `R` and `S`. -/
theorem signedGap_bind (R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) :
    signedGap (μ.bind family) R S = μ.1.expect (fun k => (family k).signedGap R S) := by
  -- Average both decision probabilities with the same weights and subtract.
  simp only [signedGap, probability_bind, Distribution.expect_sub_right]

end SystemAlgebra.Domain.Distinguisher
