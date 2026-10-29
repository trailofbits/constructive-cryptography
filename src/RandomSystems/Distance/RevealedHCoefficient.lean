import RandomSystems.Distance.HCoefficient
import RandomSystems.Cumulative.Revealed

/-!
# H-coefficient arguments with revealed values and transcript classes

The expectation method for random systems on extended transcripts `τ = (h, z)`. The real system
`R` is a mixture of components and reveals `z` from its sample and the transcript; the ideal
system `S` samples `z` conditionally on the transcript. If every `τ` has
`(1 − ε τ) · kernelMass τ ≤ revealMass τ`, the statistical distance of the transcript laws under
a compatible query-bounded environment is at most the ideal expectation of `ε`; with `ε` constant
on the classes of a finite partition, a uniform bound on that expectation bounds the transcript
distance:

```text
δ(tr(R), tr(S)) ≤ δ(revealLaw, kernelLaw)              forget z (data processing)
                ≤ 𝔼_{kernelLaw}[ε]                     expectation method
                = ∑_c classError c · Pr[classOf τ = c]  ε constant on classes
                ≤ error
```

## Main definitions

* `RandomSystem.HCoefficient R S error`: the evidence of an H-coefficient argument
* `RandomSystem.HCoefficient.ofGoodBad`: the argument with good and bad transcripts

## Main results

* `RandomSystem.statDist_sLaw_le_of_reveal`: the expectation method under one environment
* `RandomSystem.HCoefficient.transcriptDistance_le`, `transcriptDistance_le_nnreal`: an
  H-coefficient argument bounds the transcript distance

Source: Jha, *Provable Security of Symmetric-key Cryptographic Schemes*, Lemma 2.2.1 and
Corollary 2.2.2, printed pp. 19–20.
-/

namespace SystemAlgebra

open Probability
open scoped NNReal

variable {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y} {κ Z : Type}

namespace RandomSystem

/-- **The expectation method with a reveal**, under one environment `e` within `n` rounds
(Jha, Lemma 2.2.1, printed pp. 19–20, with Jha's `Θ₁` the real and `Θ₀` the ideal transcript):
if every extended transcript has `(1 − ε τ) · kernelLaw(τ) ≤ revealLaw(τ)`, with `ε ≥ 0`, then
`δ((mix P R).sLaw e n, S.sLaw e n) ≤ 𝔼_{kernelLaw}[ε]`.
Jha: “Adv_{O₁;O₀}(A) ≤ ϵ_bad + Ex[ϵ_ratio(Θ₀)]”. Compatibility of `e` with every component and
with `S` makes both extended laws probability laws. -/
theorem statDist_sLaw_le_of_reveal (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (S : RandomSystem X Y D) (e : List Y →. X) (n : ℕ) (hR : ∀ k, (R k).Compatible e)
    (hS : S.Compatible e) (reveal : κ → List (X × Y) → Z) (K : List (X × Y) → Distribution Z)
    (hK : ∀ h, (K h).isProbDist) (ε : List (X × Y) × Z → ℝ) (hε : ∀ τ, 0 ≤ ε τ)
    (ratio : ∀ τ, (1 - ε τ) * kernelLaw S K e n τ ≤ revealLaw P R reveal e n τ) :
    statDist ((mix P R).sLaw e n) (S.sLaw e n) ≤ (kernelLaw S K e n).expect ε := by
  -- `|tr(mix P R)| = ∑ₖ P(k) · |tr(R k)| = ∑ₖ P(k) = 1`, each `tr(R k)` normalized by
  -- compatibility.
  have hmixw : ((mix P R).sLaw e n).weight = 1 := by
    rw [sLaw_mix, Distribution.weight_finset_sum]
    simp only [Distribution.weight_smul, ((R _).sLaw_isProbDist (hR _) n).weight_eq, mul_one]
    simpa only [Distribution.weight, Finsupp.sum] using P.2.2
  -- A pushforward keeps the weight, so both extended laws weigh what their marginals do: one.
  have hwR : (revealLaw P R reveal e n).weight = 1 := by
    rw [← Distribution.weight_fTransform Prod.fst, fTransform_fst_revealLaw, hmixw]
  have hwS : (kernelLaw S K e n).weight = 1 := by
    rw [← Distribution.weight_fTransform Prod.fst, fTransform_fst_kernelLaw S hK,
      (S.sLaw_isProbDist hS n).weight_eq]
  -- Write the transcript laws as marginals, then
  --   δ(fst₊ revealLaw, fst₊ kernelLaw) ≤ δ(revealLaw, kernelLaw)   data processing
  --                                     ≤ 𝔼_{kernelLaw}[ε]          expectation method
  rw [← fTransform_fst_revealLaw P R reveal e n, ← fTransform_fst_kernelLaw S hK e n]
  exact (statDist_fTransform_le _ _ Prod.fst).trans
    (Probability.statDist_le_expect_of_ratio _ _ ε (hwR.trans hwS.symm) hε
      (kernelLaw_nonNeg S (fun h => (hK h).1) e n) ratio)

end RandomSystem

variable {I : Type} [Fintype I] {Xi Yi : I → Type} [∀ i, Fintype (Xi i)] [∀ i, Fintype (Yi i)]
  {𝒟 : Domain (Σ i, Xi i) (Σ i, Yi i)}

/-- **An H-coefficient argument** that the real system `R` is within `error` of the ideal system
`S` on `𝒟`: the evidence of the expectation method (Jha, Lemma 2.2.1, printed pp. 19–20) on
extended transcripts `τ = (h, z)`, with `ε τ = classError (classOf τ)`.

* Mixture: `R = mix sample component = ∑ₖ sample(k) · component k`.
* Reveals: on the sample `k` the real system reveals `z = realReveal k h`; the ideal system
  samples `z ← idealReveal h`, a probability law for every `h`.
* Classes: a finite type `Class`, the class `classOf τ`, and errors `classError c ≥ 0`. The
  classes present a piecewise-constant error; they restrict neither environments nor reveals.
* Ratio, on the systems' probabilities, with no environment:
  `(1 − ε τ) · kernelMass S idealReveal τ ≤ revealMass sample component realReveal τ`.
* Bound: under every environment `E` compatible with `𝒟` and query-bounded by `n`,
  `∑_c classError c · Pr_{kernelLaw S idealReveal E n}[classOf τ = c] ≤ error`.

The sample, reveals and classes are part of the evidence, chosen by the proof. -/
structure RandomSystem.HCoefficient (R S : RandomSystem (Σ i, Xi i) (Σ i, Yi i) 𝒟)
    (error : ℝ) where
  /-- The real system's randomness. -/
  Sample : Type
  /-- The law of the real system's randomness. -/
  sample : Distribution.ProbDist Sample
  /-- The real system on each sample. -/
  component : Sample → RandomSystem (Σ i, Xi i) (Σ i, Yi i) 𝒟
  /-- `R` is the mixture of its components. -/
  presents : R = RandomSystem.mix sample component
  /-- Each component replies at the queried interface. -/
  component_replies : ∀ k, (component k).RepliesAtQueriedInterface
  /-- The revealed values. -/
  Revealed : Type
  /-- The real system's revealed value, a function of its sample and the transcript. -/
  realReveal : Sample → List ((Σ i, Xi i) × (Σ i, Yi i)) → Revealed
  /-- The ideal system's law of the revealed value, conditional on the transcript. -/
  idealReveal : List ((Σ i, Xi i) × (Σ i, Yi i)) → Distribution Revealed
  /-- Each conditional law is a probability law. -/
  idealReveal_isProbDist : ∀ h, (idealReveal h).isProbDist
  /-- The classes of the partition of the extended transcripts. -/
  Class : Type
  [instFintypeClass : Fintype Class]
  /-- The class of an extended transcript. -/
  classOf : List ((Σ i, Xi i) × (Σ i, Yi i)) × Revealed → Class
  /-- The error of a class. -/
  classError : Class → ℝ
  /-- Class errors are nonnegative. -/
  classError_nonneg : ∀ c, 0 ≤ classError c
  /-- **The ratio**: every extended transcript `τ` is at least `1 − classError (classOf τ)`
  times as likely for the real system as for the ideal one,
  `(1 − ε τ) · S(h) · idealReveal h z ≤ ∑ₖ sample(k) · [realReveal k h = z] · (component k)(h)`.
  A product, not a quotient: at `kernelMass = 0` it holds trivially. -/
  ratio : ∀ τ, (1 - classError (classOf τ)) * RandomSystem.kernelMass S idealReveal τ ≤
    RandomSystem.revealMass sample component realReveal τ
  /-- **The expected error**: under every environment `E` compatible with `𝒟` and
  query-bounded by `n`, the class errors weighted by the ideal class probabilities are at most
  `error`, `∑_c classError c · Pr_{kernelLaw S idealReveal E n}[classOf τ = c] ≤ error`. -/
  bound : ∀ (E : DDE (Σ i, Xi i) (Σ i, Yi i)) n, QueryBounded n E → 𝒟.Compatible E →
    ∑ c, classError c *
      (RandomSystem.kernelLaw S idealReveal E.1 n).mass (fun τ => classOf τ = c) ≤ error

attribute [instance] RandomSystem.HCoefficient.instFintypeClass

namespace RandomSystem.HCoefficient

variable {R S : RandomSystem (Σ i, Xi i) (Σ i, Yi i) 𝒟} {error : ℝ}

/-- **An H-coefficient argument bounds the transcript distance**: `Δ(R, S) ≤ error`, where
`Δ(R, S)` is the supremum of `δ(tr(R), tr(S))` over compatible query-bounded environments. The
ideal system must reply at the queried interface, so that those environments normalize its
transcript law. -/
theorem transcriptDistance_le (w : HCoefficient R S error) (hS : S.RepliesAtQueriedInterface) :
    R.transcriptDistance S ≤ ENNReal.ofReal error := by
  -- Bound `δ(tr(R), tr(S))` under one compatible environment `E` bounded by `n`.
  refine iSup_le fun E => iSup_le fun n => iSup_le fun hn => iSup_le fun hE => ?_
  apply ENNReal.ofReal_le_ofReal
  rw [w.presents]
  -- With `ε τ = classError (classOf τ)`:
  --   δ(tr(mix sample component), tr(S)) ≤ 𝔼_{kernelLaw}[ε]                 expectation method
  --                                     = ∑_c classError c · Pr[classOf τ = c]
  --                                     ≤ error                              `bound`
  -- The ratio on the laws is `[Good E n h]` times the ratio on the masses: the field `ratio`
  -- on transcripts of `E`, and `0 ≤ 0` elsewhere.
  calc _ ≤ (kernelLaw S w.idealReveal E.1 n).expect fun τ => w.classError (w.classOf τ) :=
        statDist_sLaw_le_of_reveal w.sample w.component S E.1 n
          (fun k => hE _ (w.component_replies k)) (hE _ hS) w.realReveal w.idealReveal
          w.idealReveal_isProbDist _ (fun _ => w.classError_nonneg _) (fun τ => by
            rw [kernelLaw_apply, revealLaw_apply]
            split_ifs
            · exact w.ratio τ
            · simp only [mul_zero, Std.le_refl])
    _ = _ := Probability.Distribution.expect_comp_eq_sum_mass _ _ _
    _ ≤ error := w.bound E n hn hE

/-- **An H-coefficient argument bounds the transcript distance**, for an error in `ℝ≥0`:
`Δ(R, S) ≤ error`, the form of a security bound. -/
lemma transcriptDistance_le_nnreal {error : ℝ≥0} (w : HCoefficient R S error)
    (hS : S.RepliesAtQueriedInterface) : R.transcriptDistance S ≤ error := by
  simpa only [ENNReal.ofReal_coe_nnreal] using w.transcriptDistance_le hS

/-- **Good and bad transcripts**: the H-coefficient technique, Jha, Corollary 2.2.2, printed
p. 20, “a simple corollary of this result where ϵratio is a constant function”, which Jha
attributes to Patarin. Two classes: `true` for `Bad τ`, with error `1`, and `false` for the
good transcripts, with error `ε₁`. If every good `τ` has
`(1 − ε₁) · kernelMass(τ) ≤ revealMass(τ)` and, under every compatible query-bounded
environment, `Pr_{kernelLaw}[Bad] ≤ ε₂`, the error is `ε₁ + ε₂`, not truncated at one. -/
noncomputable def ofGoodBad {Sample Revealed : Type} (sample : Distribution.ProbDist Sample)
    (component : Sample → RandomSystem (Σ i, Xi i) (Σ i, Yi i) 𝒟)
    (presents : R = RandomSystem.mix sample component)
    (component_replies : ∀ k, (component k).RepliesAtQueriedInterface)
    (hS : S.RepliesAtQueriedInterface)
    (realReveal : Sample → List ((Σ i, Xi i) × (Σ i, Yi i)) → Revealed)
    (idealReveal : List ((Σ i, Xi i) × (Σ i, Yi i)) → Distribution Revealed)
    (idealReveal_isProbDist : ∀ h, (idealReveal h).isProbDist)
    (Bad : List ((Σ i, Xi i) × (Σ i, Yi i)) × Revealed → Prop) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁)
    (ratio : ∀ τ, ¬ Bad τ → (1 - ε₁) * kernelMass S idealReveal τ ≤
      revealMass sample component realReveal τ)
    (bad : ∀ (E : DDE (Σ i, Xi i) (Σ i, Yi i)) n, QueryBounded n E → 𝒟.Compatible E →
      (kernelLaw S idealReveal E.1 n).mass Bad ≤ ε₂) :
    HCoefficient R S (ε₁ + ε₂) := by
  classical
  -- `classOf τ = [Bad τ]`; `classError true = 1`, `classError false = ε₁`.
  exact
  { Sample := Sample
    sample := sample
    component := component
    presents := presents
    component_replies := component_replies
    Revealed := Revealed
    realReveal := realReveal
    idealReveal := idealReveal
    idealReveal_isProbDist := idealReveal_isProbDist
    Class := Bool
    classOf := fun τ => if Bad τ then true else false
    classError := fun b => if b then 1 else ε₁
    classError_nonneg := fun b => by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, hε₁,
      zero_le_one]
    -- On a bad `τ` the ratio is `(1 − 1) · kernelMass τ = 0 ≤ revealMass τ`; on a good one it
    -- is the hypothesis.
    ratio := fun τ => by
      by_cases hb : Bad τ
      · simp only [if_pos hb, if_true, sub_self, zero_mul]
        exact revealMass_nonneg _ _ _ τ
      · simpa only [if_neg hb, Bool.false_eq_true, if_false] using ratio τ hb
    -- `1 · Pr[Bad] + ε₁ · Pr[good] ≤ ε₂ + ε₁ · 1`: the ideal law has weight one, so the good
    -- transcripts have probability at most one.
    bound := fun E n hn hE => by
      have hK := kernelLaw_nonNeg S (fun h => (idealReveal_isProbDist h).1) E.1 n
      have hw : (kernelLaw S idealReveal E.1 n).weight = 1 := by
        rw [← Distribution.weight_fTransform Prod.fst,
          fTransform_fst_kernelLaw S idealReveal_isProbDist,
          (S.sLaw_isProbDist (hE _ hS) n).weight_eq]
      have hgood : (kernelLaw S idealReveal E.1 n).mass
          (fun τ => (if Bad τ then true else false) = false) ≤ 1 :=
        (Distribution.mass_le_weight hK _).trans hw.le
      have hbad : (kernelLaw S idealReveal E.1 n).mass
          (fun τ => (if Bad τ then true else false) = true) ≤ ε₂ := by
        simpa only [Bool.if_false_right, Bool.and_true, decide_eq_true_eq] using bad E n hn hE
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left hgood hε₁] }

end RandomSystem.HCoefficient

end SystemAlgebra
