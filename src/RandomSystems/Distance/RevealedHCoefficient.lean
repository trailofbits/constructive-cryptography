import RandomSystems.Distance.HCoefficient
import RandomSystems.Cumulative.Revealed

/-!
# H-coefficient arguments with revealed values and transcript classes

`HCoefficient.transcriptDistance_le_nnreal` bounds the existing transcript distance from
an explicit real mixture, real and ideal reveals, a finite classification, a pointwise
ratio, and the expected class error under every compatible bounded environment.
`HCoefficient.ofGoodBad` specializes to two classes without a new distance or observer class.

Source: Hoang–Tessaro, CRYPTO 2016, §3; Jha, *Provable Security of Symmetric-key
Cryptographic Schemes*, Lemma 2.2.1 and Corollary 2.2.2, printed pp. 19–20:
“ϵratio is a constant function” in the good/bad specialization. The proof follows the
source's ideal expected deficit, using the existing data-processing theorem to forget reveals.

Jost's Definitions 2.2.1–2.2.2 concern the system and converter structure; they do not
require reveals or transcript classes. These are optional evidence for a distance bound,
derived without changing the resource carrier, domains, or attachment. Finite classes
are a representation of a piecewise error, not an assumption on the distinguisher's choices.
-/

namespace SystemAlgebra

open Probability
open scoped NNReal

variable {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y} {κ Z : Type}

namespace RandomSystem

/-- **The H-coefficient technique with a reveal**, in expectation form: if every extended
transcript `τ` is at least `1 − ε τ` times as likely in the revealed real law as in the ideal
kernel law, the transcript laws are at most the ideal expectation of `ε` apart. -/
theorem statDist_sLaw_le_of_reveal (P : Distribution.ProbDist κ) (R : κ → RandomSystem X Y D)
    (S : RandomSystem X Y D) (e : List Y →. X) (n : ℕ) (hR : ∀ k, (R k).Compatible e)
    (hS : S.Compatible e) (reveal : κ → List (X × Y) → Z) (K : List (X × Y) → Distribution Z)
    (hK : ∀ h, (K h).isProbDist) (ε : List (X × Y) × Z → ℝ) (hε : ∀ τ, 0 ≤ ε τ)
    (ratio : ∀ τ, (1 - ε τ) * kernelLaw S K e n τ ≤ revealLaw P R reveal e n τ) :
    statDist ((mix P R).sLaw e n) (S.sLaw e n) ≤ (kernelLaw S K e n).expect ε := by
  -- Compatibility normalizes the component transcript laws and their mixture.
  have hmixw : ((mix P R).sLaw e n).weight = 1 := by
    rw [sLaw_mix, Distribution.weight_finset_sum]
    simp only [Distribution.weight_smul, ((R _).sLaw_isProbDist (hR _) n).weight_eq, mul_one]
    simpa only [Distribution.weight, Finsupp.sum] using P.2.2
  -- Both extended laws have weight one because their marginals do.
  have hwR : (revealLaw P R reveal e n).weight = 1 := by
    rw [← Distribution.weight_fTransform Prod.fst, fTransform_fst_revealLaw, hmixw]
  have hwS : (kernelLaw S K e n).weight = 1 := by
    rw [← Distribution.weight_fTransform Prod.fst, fTransform_fst_kernelLaw S hK,
      (S.sLaw_isProbDist hS n).weight_eq]
  -- Forget the reveals by data processing, then apply the expectation method.
  rw [← fTransform_fst_revealLaw P R reveal e n, ← fTransform_fst_kernelLaw S hK e n]
  exact (statDist_fTransform_le _ _ Prod.fst).trans
    (Probability.statDist_le_expect_of_ratio _ _ ε (hwR.trans hwS.symm) hε
      (kernelLaw_nonNeg S hK e n) ratio)

end RandomSystem

variable {I : Type} [Fintype I] {Xi Yi : I → Type} [∀ i, Fintype (Xi i)] [∀ i, Fintype (Yi i)]
  {𝒟 : Domain (Σ i, Xi i) (Σ i, Yi i)}

/-- **An H-coefficient argument** between the random systems `R` (real) and `S` (ideal) on
`𝒟`, with error `error` (the H-coefficient technique with classes of transcripts, as in
Hoang–Tessaro's expectation method).

* The real system is a mixture: `sample` a value, then run `component`.
* After the interaction, the real system reveals `realReveal k h` for its sample `k`; the ideal
  system samples its revealed value from `idealReveal h`.
* The extended transcripts are partitioned into finitely many classes, each with an error.
* On every class `c`, the real probability of an extended transcript is at least
  `1 − classError c` times the ideal one. Both are the systems' probabilities, independent of the environment.
* For every environment compatible with `𝒟`, the expected class error under the ideal system
  is at most `error`. -/
structure RandomSystem.HCoefficient (R S : RandomSystem (Σ i, Xi i) (Σ i, Yi i) 𝒟)
    (error : ℝ) where
  /-- The real system's randomness. -/
  Sample : Type
  /-- The law of the real system's randomness. -/
  sample : Distribution.ProbDist Sample
  /-- The real system for each sample. -/
  component : Sample → RandomSystem (Σ i, Xi i) (Σ i, Yi i) 𝒟
  presents : R = RandomSystem.mix sample component
  component_replies : ∀ k, (component k).RepliesAtQueriedInterface
  /-- The revealed values. -/
  Revealed : Type
  /-- The real system's revealed value, from its sample and the transcript. -/
  realReveal : Sample → List ((Σ i, Xi i) × (Σ i, Yi i)) → Revealed
  /-- The ideal system's revealed value, sampled after the transcript. -/
  idealReveal : List ((Σ i, Xi i) × (Σ i, Yi i)) → Distribution Revealed
  idealReveal_isProbDist : ∀ h, (idealReveal h).isProbDist
  /-- The classes of the partition of the extended transcripts. -/
  Class : Type
  [instFintypeClass : Fintype Class]
  /-- The class of an extended transcript. -/
  classOf : List ((Σ i, Xi i) × (Σ i, Yi i)) × Revealed → Class
  /-- The error of a class. -/
  classError : Class → ℝ
  classError_nonneg : ∀ c, 0 ≤ classError c
  /-- **The ratio**: on every class `c`, the real probability of an extended transcript is at
  least `1 − classError c` times the ideal one. -/
  ratio : ∀ τ, (1 - classError (classOf τ)) * RandomSystem.kernelMass S idealReveal τ ≤
    RandomSystem.revealMass sample component realReveal τ
  /-- **The expected error**: the class errors weighted by the ideal class masses. -/
  bound : ∀ (E : DDE (Σ i, Xi i) (Σ i, Yi i)) n, QueryBounded n E → 𝒟.Compatible E →
    ∑ c, classError c *
      (RandomSystem.kernelLaw S idealReveal E.1 n).mass (fun τ => classOf τ = c) ≤ error

attribute [instance] RandomSystem.HCoefficient.instFintypeClass

namespace RandomSystem.HCoefficient

variable {R S : RandomSystem (Σ i, Xi i) (Σ i, Yi i) 𝒟} {error : ℝ}

/-- **An H-coefficient argument bounds the transcript distance.** -/
theorem transcriptDistance_le (w : HCoefficient R S error) (hS : S.RepliesAtQueriedInterface) :
    R.transcriptDistance S ≤ ENNReal.ofReal error := by
  -- Bound the transcript distance under each compatible bounded environment.
  refine iSup_le fun E => iSup_le fun n => iSup_le fun hn => iSup_le fun hE => ?_
  apply ENNReal.ofReal_le_ofReal
  rw [w.presents]
  -- The common environment indicator cancels in the ratio; group errors by class.
  calc _ ≤ (kernelLaw S w.idealReveal E.1 n).expect fun τ => w.classError (w.classOf τ) :=
        statDist_sLaw_le_of_reveal w.sample w.component S E.1 n
          (fun k => hE _ (w.component_replies k)) (hE _ hS) w.realReveal w.idealReveal
          w.idealReveal_isProbDist _ (fun _ => w.classError_nonneg _) (fun τ => by
            rw [kernelLaw_apply, revealLaw_apply]
            split_ifs
            · exact w.ratio τ
            · simp)
    _ = _ := Probability.Distribution.expect_comp_eq_sum_mass _ _ _
    _ ≤ error := w.bound E n hn hE

/-- **An H-coefficient argument bounds the transcript distance**, for an error in `ℝ≥0`. -/
lemma transcriptDistance_le_nnreal {error : ℝ≥0} (w : HCoefficient R S error)
    (hS : S.RepliesAtQueriedInterface) : R.transcriptDistance S ≤ error := by
  simpa only [ENNReal.ofReal_coe_nnreal] using w.transcriptDistance_le hS

/-- **Good and bad transcripts** (the H-coefficient technique as usually stated: Patarin;
Chen–Steinberger, Theorem 1): the partition into two classes, the bad one with error one. If every
good extended transcript is at least `1 − ε₁` times as likely in the real system as in the ideal
one, and the bad transcripts have ideal probability at most `ε₂` under every compatible
query-bounded environment, the error is `ε₁ + ε₂`. -/
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
  -- Bad transcripts receive error one; good transcripts receive the ratio error.
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
    classError_nonneg := fun b => by cases b <;> simp [hε₁]
    -- On bad transcripts the required lower bound is zero.
    ratio := fun τ => by
      by_cases hb : Bad τ
      · simp only [if_pos hb, if_true, sub_self, zero_mul]
        exact revealMass_nonneg _ _ _ τ
      · simpa only [if_neg hb, Bool.false_eq_true, if_false] using ratio τ hb
    -- Good mass is at most one; the explicit bad-mass hypothesis pays for the rest.
    bound := fun E n hn hE => by
      have hK := kernelLaw_nonNeg S idealReveal_isProbDist E.1 n
      have hw : (kernelLaw S idealReveal E.1 n).weight = 1 := by
        rw [← Distribution.weight_fTransform Prod.fst,
          fTransform_fst_kernelLaw S idealReveal_isProbDist,
          (S.sLaw_isProbDist (hE _ hS) n).weight_eq]
      have hgood : (kernelLaw S idealReveal E.1 n).mass (fun τ => (if Bad τ then true else false) = false) ≤ 1 :=
        (Distribution.mass_le_weight hK _).trans hw.le
      have hbad : (kernelLaw S idealReveal E.1 n).mass (fun τ => (if Bad τ then true else false) = true) ≤ ε₂ := by
        simpa using bad E n hn hE
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left hgood hε₁] }

end RandomSystem.HCoefficient

end SystemAlgebra
