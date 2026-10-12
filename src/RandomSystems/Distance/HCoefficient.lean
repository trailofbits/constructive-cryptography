import RandomSystems.Distance.Decision

/-!
# The H-coefficient bound for random systems

The H-coefficient technique bounds the distance of a real system `R` from an ideal system `S`:
if every transcript outside a set of bad transcripts is at least `1 - ε₁` times as likely for
`R` as for `S`, and the bad transcripts have probability at most `ε₂` in the transcript law of
`S` under every compatible query-bounded environment, the transcript distance is at most
`ε₁ + ε₂`. The transcript law of a system under an environment is the system's probability of
the transcript, restricted to the transcripts the environment produces. The restriction is the
same for both systems, so the ratio of the systems' probabilities is a ratio of their
transcript laws, and the bound for distributions applies under every environment.

Sources: Patarin's H-coefficient technique, in the form for distributions
`Probability.statDist_le_probBad_add_of_ratio_on_good`.

## Main results

* `RandomSystem.transcriptDistance_le_add_of_ratio_on_good`: the H-coefficient bound on the
  transcript distance
-/

namespace SystemAlgebra

open Probability
open scoped NNReal

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

namespace RandomSystem

/-- **The H-coefficient bound for random systems** (Patarin's H-coefficient technique; the
form for distributions is `statDist_le_probBad_add_of_ratio_on_good`): if every transcript `h`
outside `Bad` has `(1 - ε₁) · S(h) ≤ R(h)`, where `R(h)` is the probability that `R` replies
with the replies of `h` to its queries, and under every compatible query-bounded environment
the bad transcripts have probability at most `ε₂` in the transcript law of the ideal system `S`,
then the real system `R` is within `ε₁ + ε₂` of `S`. -/
theorem transcriptDistance_le_add_of_ratio_on_good
    {R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface)
    {Bad : List ((Σ i, X i) × (Σ i, Y i)) → Prop} {ε₁ ε₂ : ℝ≥0}
    (hratio : ∀ h, ¬ Bad h → (1 - ε₁) * S h ≤ R h)
    (hbad : ∀ (E : DDE (Σ i, X i) (Σ i, Y i)) (n : ℕ), QueryBounded n E → 𝒟.Compatible E →
      probBad (S.sLaw E.1 n) Bad ≤ ε₂) :
    R.transcriptDistance S ≤ ε₁ + ε₂ := by
  -- Plan:
  -- 1. The transcript distance is a supremum over environments, so it suffices to bound the
  --    statistical distance of the transcript laws under one compatible environment `E`,
  --    bounded to `n` queries:
  --
  --        E ──x──▶ R            E ──x──▶ S
  --          ◀──y──                ◀──y──
  --       tr(R, E, n)           tr(S, E, n)
  --
  -- 2. Both transcript laws are probability distributions.
  -- 3. The ratio on good transcripts carries over from the systems to the transcript laws.
  -- 4. The bound for distributions bounds the statistical distance of the transcript laws by
  --    `Pr_{tr(S, E, n)}[Bad] + ε₁`, which is at most `ε₁ + ε₂`.
  rw [← ENNReal.coe_add]
  refine transcriptDistance_le fun E n hn hc => ?_
  -- Step 2: `E` is compatible with every system on `𝒟` that replies at the queried interface,
  -- so the transcript laws of `R` and `S` have weight one.
  have hRlaw := R.sLaw_isProbDist (hc R hR) n
  have hSlaw := S.sLaw_isProbDist (hc S hS) n
  -- Step 3: `tr(R, E, n)(h) = [h follows E within n queries] · R(h)`, and likewise for `S`
  -- with the same indicator. On a transcript `E` produces both sides are the systems'
  -- probabilities, so the ratio is the hypothesis; elsewhere both sides are zero.
  have hlaw : ∀ h, ¬ Bad h → (1 - ε₁) * S.sLaw E.1 n h ≤ R.sLaw E.1 n h := by
    intro h hh
    rw [sLaw_apply, sLaw_apply]
    split_ifs
    · exact hratio h hh
    · rw [mul_zero]
  -- Step 4: the H-coefficient bound for distributions, with the law of `R` as the real and
  -- the law of `S` as the ideal distribution, then the bound `ε₂` on the bad transcripts.
  have hdist := statDist_le_probBad_add_of_ratio_on_good _ _ Bad ε₁ hRlaw.1 hSlaw.1
    (hRlaw.weight_eq.trans hSlaw.weight_eq.symm) hSlaw.weight_eq.le hlaw
  push_cast
  linarith [hbad E n hn hc]

end RandomSystem

end SystemAlgebra
