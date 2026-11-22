module

public import RandomSystems.Typed.SamplingDistance
public import Probability.Kernel
public import RandomSystems.Typed.Parallel

/-!
# Complete transcripts of stopping observers

`Domain.Distinguisher.transcriptLaw D R` draws the observer's initial choice and then its
complete interaction with `R`. It averages over the observer's randomness and includes adaptive
query choices.
`probability_gap_le_bad_mass` bounds a decision gap by bad mass in the ideal transcript when
the systems agree elsewhere. `sample_probability_gap_le_bad_mass` averages this law over
an independent retained choice `k ∼ P`; its bound is evaluated under `P × transcriptLaw D S`.
-/

@[expose] public section

namespace SystemAlgebra

open Probability
open scoped BigOperators NNReal

/-- Equality outside `Bad` bounds a deterministic observer's decision gap by ideal bad mass. -/
lemma RandomSystem.decisionProbability_gap_le_bad_mass {A : Interface}
    -- `R`, `S` share interface `A`; `D` is a stopping deterministic observer.
    (R S : TypedSystem A) (D : DDD A.I A.X A.Y) (hD : IsDDD D)
    -- `hc` admits every query made by `D` on the declared domain.
    (hc : A.inputDomain.DecisionCompatible D)
    (Bad : List ((Σ i, A.X i) × (Σ i, A.Y i)) → Prop)
    -- `he` identifies cumulative probabilities outside the transcript event `Bad`.
    (he : ∀ h, ¬ Bad h → R.1 h = S.1 h) :
    |R.1.decisionProbability D hD - S.1.decisionProbability D hD| ≤
      (S.1.sLaw (ddeOf hD).1 hD.2.1.choose).mass Bad := by
  have hr := R.1.sLaw_isProbDist (hc.environment hD R.1 R.2) hD.2.1.choose
  have hs := S.1.sLaw_isProbDist (hc.environment hD S.1 S.2) hD.2.1.choose
  have hratio (h) (hb : ¬ Bad h) :
      (1 - ((0 : ℝ≥0) : ℝ)) * S.1.sLaw (ddeOf hD).1 hD.2.1.choose h ≤
        R.1.sLaw (ddeOf hD).1 hD.2.1.choose h := by
    rw [RandomSystem.sLaw_apply, RandomSystem.sLaw_apply]
    split_ifs
    · rw [he h hb]
      simp only [NNReal.coe_zero, sub_zero, one_mul, le_refl]
    · simp only [mul_zero, le_refl]
  have hd := statDist_le_probBad_add_of_ratio_on_good _ _ Bad 0 hr.1 hs.1
    (hr.weight_eq.trans hs.weight_eq.symm) hs.weight_eq.le hratio
  have hb := abs_mass_sub_le_statDist
    ⟨_, hr⟩ ⟨_, hs⟩ (fun h =>
      (⟨.dec, true⟩ : Σ p, dOut A.X p) ∈ (trim D) (dHist (h.map Prod.snd)))
  exact hb.trans (by simpa only [probBad, NNReal.coe_zero, add_zero] using hd)

/-- Draw the stopping observer, then its complete transcript against `R`. -/
noncomputable def Domain.Distinguisher.transcriptLaw {A : Interface}
    -- `D` is a random stopping observer compatible with `A`; `R` supplies its replies.
    (D : A.inputDomain.Distinguisher) (R : TypedSystem A) :
    Distribution.ProbDist (List ((Σ i, A.X i) × (Σ i, A.Y i))) :=
  D.bind fun choice => ⟨R.1.sLaw (ddeOf choice.2.1).1 choice.2.1.2.1.choose,
    R.1.sLaw_isProbDist (choice.2.2.environment choice.2.1 R.1 R.2) _⟩

/-- Every sampled complete transcript satisfies the original input domain, including the
empty transcript. Thus simulating the ideal system preserves its aggregate budgets. -/
lemma Domain.Distinguisher.transcriptLaw_mem_support {A : Interface}
    -- `D` is a random stopping observer compatible with `A`; `R` supplies its replies.
    (D : A.inputDomain.Distinguisher) (R : TypedSystem A)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    (hh : h ∈ (D.transcriptLaw R).1.support) : h = [] ∨ A.domain (h.map Prod.fst) := by
  obtain ⟨choice, _, hchoice⟩ := Distribution.mem_support_bindK hh
  have hr : R.1 h ≠ 0 := by
    intro hz
    apply Finsupp.mem_support_iff.mp hchoice
    change R.1.sLaw (ddeOf choice.2.1).1 choice.2.1.2.1.choose h = 0
    simp only [RandomSystem.sLaw_apply, hz, ite_self]
  simpa only [List.map_eq_nil_iff] using TypedSystem.possible_domain R hr


lemma Domain.Distinguisher.transcriptLaw_mass {A : Interface}
    -- `D` is a random stopping observer compatible with `A`; `R` supplies its replies.
    (D : A.inputDomain.Distinguisher) (R : TypedSystem A)
    (event : List ((Σ i, A.X i) × (Σ i, A.Y i)) → Prop) :
    (D.transcriptLaw R).1.mass event = D.1.sum (fun choice w => w *
      (R.1.sLaw (ddeOf choice.2.1).1 choice.2.1.2.1.choose).mass event) :=
  Distribution.mass_bindK D.1 _ event

/-- A probabilistic observer's ideal transcript law averages over its initial randomness.
Equality on good transcripts bounds its decision gap by bad mass under that same law. -/
lemma Domain.Distinguisher.probability_gap_le_bad_mass {A : Interface}
    (D : A.inputDomain.Distinguisher) (R S : TypedSystem A)
    (Bad : List ((Σ i, A.X i) × (Σ i, A.Y i)) → Prop)
    -- `he` identifies cumulative probabilities outside the transcript event `Bad`.
    (he : ∀ h, ¬ Bad h → R.1 h = S.1 h) :
    |D.probability R.1 - D.probability S.1| ≤ (D.transcriptLaw S).1.mass Bad := by
  rw [Domain.Distinguisher.probability, Domain.Distinguisher.probability,
    Domain.Distinguisher.transcriptLaw_mass]
  -- Average the deterministic gap under the observer's initial choice.
  exact Distribution.abs_expect_sub_expect_le_expect D.2.1 _ _ _ (fun choice =>
    RandomSystem.decisionProbability_gap_le_bad_mass R S choice.1
      choice.2.1 choice.2.2 Bad he)


/-- Averaging equality off `Bad k` bounds the decision gap by its mass under
the independent pair of a hidden draw `k ∼ P` and the ideal transcript. -/
lemma Domain.Distinguisher.sample_probability_gap_le_bad_mass {A : Interface} {K : Type}
    -- `D` is the compatible observer; `P` independently chooses the retained hidden `k : K`.
    (D : A.inputDomain.Distinguisher) (P : Distribution.ProbDist K)
    -- `R k` is the real system; the ideal system `S` does not depend on `k`.
    (R : K → TypedSystem A) (S : TypedSystem A)
    -- `Bad k h` is the exceptional event; `he` identifies all other transcript masses.
    (Bad : K → List ((Σ i, A.X i) × (Σ i, A.Y i)) → Prop)
    (he : ∀ k h, ¬ Bad k h → (R k).1 h = S.1 h) :
    |D.probability (TypedSystem.sample P.1 R).1 - D.probability S.1| ≤
      (P.1.prod (D.transcriptLaw S).1).mass (fun pair => Bad pair.1 pair.2) := by
  have heq : D.probability (TypedSystem.sample P.1 R).1 =
      P.1.sum (fun k w => w * D.probability (R k).1) :=
    Domain.Distinguisher.probability_mix P (fun k => (R k).1) D
  rw [heq, Distribution.mass_prod_eq_sum P.1 (D.transcriptLaw S).1 Bad]
  -- The same expectation law averages the hidden choice; the ideal term is constant.
  have bound := Distribution.abs_expect_sub_expect_le_expect P.2.1
    (fun k => D.probability (R k).1) (fun _ => D.probability S.1)
    (fun k => (D.transcriptLaw S).1.mass (Bad k))
    (fun k => D.probability_gap_le_bad_mass (R k) S (Bad k) (he k))
  rw [Distribution.expect_const, P.2.weight_eq, mul_one] at bound
  simpa only [Distribution.expect] using bound


end SystemAlgebra
