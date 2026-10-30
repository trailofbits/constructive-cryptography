import RandomSystems.Distance.Decision

/-!
# Distance bounds from observations with the public transcript as a projection

Two systems `R S` on a common domain are compared through observation laws `μ_R`, `μ_S` on a
type `W`, one pair for each compatible environment `E` stopping within `n` queries. A common map
`π` links them to the public interaction by exact marginals, `π_* μ_R = R.sLaw E n` and
`π_* μ_S = S.sLaw E n`.

## Main results

* `transcriptDistance_le_iSup_observation`: `Δ(R, S) ≤ sup_{E,n} δ(μ_R, μ_S)`
* `transcriptDistance_le_of_observation_ratio`: a ratio bound with ideal expected loss at
  most `b` gives `Δ(R, S) ≤ b`

Both apply inequalities of `Probability.StatisticalDistance` to each admissible experiment and
then take the supremum over compatible stopping environments. The ratio result applies
`statDist_fTransform_le_expect_of_ratio` to the exact transcript marginals:

```text
  δ(R.sLaw E n, S.sLaw E n)
    = δ(π_* μ_R, π_* μ_S)     realMarginal, idealMarginal
    ≤ δ(μ_R, μ_S)              statDist_fTransform_le [1, Lemma 3]
    ≤ 𝔼_μ_S[ε]                statDist_le_expect_of_ratio [2, Lemma 2.2.1]
    ≤ b                        bound
```

Conditional completions in `RandomSystems.Typed.Completion` instantiate this with pairs
`(h, z)` of a public history and a record, and `π(h, z) = h`.
For a sampled presentation `x` with observation `aug x`,
`Distribution.fTransform_comp_eq_of_pointwise` establishes the marginal from the pointwise
identity `π (aug x) = publicHistory x`.

## References

1. D. Lanzenberger and U. Maurer. Coupling of Random Systems. In *Theory of Cryptography
   (TCC 2020)*, Springer, 2020. Cryptology ePrint Archive, Paper 2020/1187.
2. Jha. *Provable Security of Symmetric-key Cryptographic Schemes*.
-/

namespace SystemAlgebra.RandomSystem

open Probability
open scoped NNReal

variable
    -- `I` labels the public ports; `X i` and `Y i` are the query and reply types at port `i`.
    {I : Type} [Fintype I] {X Y : I → Type}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    -- `D` selects admissible query histories; `R` and `S` are systems on that same domain.
    {D : Domain (Σ i, X i) (Σ i, Y i)}
    (R S : RandomSystem (Σ i, X i) (Σ i, Y i) D)
    -- `W` carries observations; `π w` recovers the public query–reply history from `w : W`.
    -- `W` is an arbitrary type; each probability law on it has finite support.
    {W : Type*} (π : W → List ((Σ i, X i) × (Σ i, Y i)))
    -- `realObservation E n hn hE` and `idealObservation E n hn hE` are the normalized laws
    -- `μ_R`, `μ_S` on `W` for environment `E` observed for `n` rounds. `hn` says `E` stops
    -- within `n` queries; `hE` says it respects `D`. Laws are required only for these
    -- admissible experiments.
    (realObservation idealObservation :
      (E : DDE (Σ i, X i) (Σ i, Y i)) → (n : ℕ) →
        QueryBounded n E → D.Compatible E → Distribution.ProbDist W)
    -- `realMarginal`, `idealMarginal`: `π_* μ_R = R.sLaw E n` and `π_* μ_S = S.sLaw E n`
    -- exactly. Both sides use the same `E`, horizon `n` and projection `π`.
    (realMarginal : ∀ E n hn hE,
      Distribution.fTransform π (realObservation E n hn hE).1 = R.sLaw E.1 n)
    (idealMarginal : ∀ E n hn hE,
      Distribution.fTransform π (idealObservation E n hn hE).1 = S.sLaw E.1 n)

include realMarginal idealMarginal

/-- Observation distance bounds public transcript distance, uniformly over compatible stopping
environments: data processing [1, Lemma 3] under the supremum of [1, Definition 11, p. 15],
“the supremum is over all compatible (Y, X)-DDE.” -/
theorem transcriptDistance_le_iSup_observation :
    R.transcriptDistance S ≤
      ⨆ (E : DDE (Σ i, X i) (Σ i, Y i)) (n : ℕ)
        (hn : QueryBounded n E) (hE : D.Compatible E),
        ENNReal.ofReal (statDist (realObservation E n hn hE).1
          (idealObservation E n hn hE).1) := by
  -- Fix a compatible `E` stopping within `n` queries; its transcript distance is compared with
  -- the observation distance of the same experiment `(E, n, hn, hE)` on the right.
  refine iSup_le fun E => iSup_le fun n => iSup_le fun hn => iSup_le fun hE => ?_
  refine le_iSup_of_le E (le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le hE ?_)))
  apply ENNReal.ofReal_le_ofReal
  -- Exact marginals: `δ(R.sLaw E n, S.sLaw E n) = δ(π_* μ_R, π_* μ_S)`.
  rw [← realMarginal E n hn hE, ← idealMarginal E n hn hE]
  -- Data processing [1, Lemma 3]: the common map `π` does not increase distance.
  exact statDist_fTransform_le _ _ π

/-- A ratio bound on any observations with the public transcript as a common projection gives
`Δ(R, S) ≤ b`. [2, Lemma 2.2.1, p. 20]: “Adv_{O₁;O₀}(A) ≤ ϵ_bad + Ex[ϵ_ratio(Θ₀)]”. Here `ε`
includes any bad-event contribution. -/
theorem transcriptDistance_le_of_observation_ratio
    -- `ε w`: the scalar loss at observation `w`, a real number; `hε` gives `ε ≥ 0`, and `ε w`
    -- may exceed one.
    (ε : W → ℝ) (hε : ∀ w, 0 ≤ ε w)
    -- `b : ℝ≥0` is the uniform distance budget, coerced to `ℝ≥0∞` in the conclusion.
    {b : ℝ≥0}
    -- `ratio`: `(1 − ε w) · μ_S(w) ≤ μ_R(w)` for every admissible experiment and every `w`;
    -- both laws are nonnegative, so it holds automatically where `ε w ≥ 1`.
    (ratio : ∀ E n hn hE w,
      (1 - ε w) * (idealObservation E n hn hE).1 w ≤ (realObservation E n hn hE).1 w)
    -- `bound`: `𝔼_μ_S[ε] ≤ b`, uniformly over admissible experiments.
    (bound : ∀ E n hn hE, (idealObservation E n hn hE).1.expect ε ≤ b) :
    R.transcriptDistance S ≤ b := by
  -- The supremum: it suffices to bound one compatible `E` stopping within `n` queries.
  refine transcriptDistance_le fun E n hn hE => ?_
  -- Exact marginals: `δ(R.sLaw E n, S.sLaw E n) = δ(π_* μ_R, π_* μ_S)`.
  rw [← realMarginal E n hn hE, ← idealMarginal E n hn hE]
  -- `statDist_fTransform_le_expect_of_ratio` with `P = μ_R`, `Q = μ_S`, `f = π`: both laws
  -- have weight one and `μ_S ≥ 0`; then `bound`.
  exact (statDist_fTransform_le_expect_of_ratio _ _ π ε
    ((realObservation E n hn hE).2.weight_eq.trans
      (idealObservation E n hn hE).2.weight_eq.symm)
    (idealObservation E n hn hE).2.1 hε (ratio E n hn hE)).trans (bound E n hn hE)

end SystemAlgebra.RandomSystem
