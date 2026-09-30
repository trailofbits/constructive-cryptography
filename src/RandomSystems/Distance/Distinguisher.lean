import RandomSystems.Distance.Absorption
import RandomSystems.Distance.ParallelObservation

/-!
# Probabilistic distinguishers

A probabilistic distinguisher compatible with a domain is a finite distribution over the
deterministic distinguishers compatible with it (Lanzenberger–Maurer, Definition 9). Its
probability of outputting `1` on a random system is the average of the decision
probabilities, and the largest difference of these probabilities on two resources is their
transcript distance. Absorbing a PDC from `E` to `F` into a distinguisher compatible with
`F` gives a distinguisher compatible with `E`; so does absorbing a resource with domain `F`
run beside a distinguisher compatible with the parallel domain of `E` and `F`.

## Main definitions

* `Domain.Distinguisher 𝒟`: probabilistic distinguishers compatible with `𝒟`
* `Domain.Distinguisher.probability`: the probability of outputting `1`
* `Domain.Distinguisher.advantage`: the difference of these probabilities on two systems
* `Domain.Distinguisher.absorb`: the distinguisher with a PDC absorbed

## Main results

* `Domain.DecisionCompatible.absorbAll`: absorbing a DDC preserves compatibility
* `RandomSystem.decisionProbability_attach`: attaching a PDC averages the absorbed
  decisions over a presentation of the PDC
* `Domain.Distinguisher.advantage_self`, `advantage_symm`, `advantage_triangle`: the
  advantage is a pseudo-distance for each distinguisher
* `RandomSystem.transcriptDistance_eq_iSup`, `Domain.Distinguisher.advantage_le_transcriptDistance`:
  the transcript distance is the largest advantage of a probabilistic distinguisher
* `Domain.Distinguisher.exists_absorbAll`, `Domain.Distinguisher.exists_absorbRight`:
  absorbing a PDC, or a resource run beside, gives a probabilistic distinguisher
-/

namespace SystemAlgebra

open Classical Probability

section Attachment

variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- Absorbing a DDC from `E` to `F` into a distinguisher compatible with `F` gives a
distinguisher compatible with `E`. -/
theorem Domain.DecisionCompatible.absorbAll
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    {D : DDD O U V}
    (hc : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).DecisionCompatible D)
    (hD : IsDDD D) {α : InsideOutsideSystem O J U V X Y} {b : ℕ} (hα : IsDDCFrom E F b α) :
    (Domain.ofInputs E m hE : Domain (Σ j, X j) (Σ j, Y j)).DecisionCompatible
      (trim (absorbAll D α)) := by
  apply (Domain.decisionCompatible_iff_deterministic hE' (absorbAll_isDDD hD hα.isDDC)).mpr
  intro s hs hr he
  have htarget := hα.mapsDomain hF' s hs hr he
  have hdds : IsDDS (trim (apply α s)) :=
    SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq])
  have hd := (Domain.decisionCompatible_iff_deterministic hF' hD).mp hc
    (trim (apply α s)) hdds htarget.1 htarget.2
  have hcTrim := close_start_eq
    ((behEq_iff_transcript.mp (trim_behEq (apply α s))) (envOf D))
  rw [hcTrim] at hd
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨c, rfl⟩ := eq_decOut v
  rw [close_trim_start]
  exact Part.dom_iff_mem.mpr ⟨decOut c,
    (decision_apply D α s hD.2.1.choose_spec.terminating hα.isDDC c).mp hv⟩

/-- **Attaching a PDC averages the absorbed decisions** over a presentation of the PDC by
DDCs. -/
theorem RandomSystem.decisionProbability_attach
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (D : DDD O U V) (hD : IsDDD D) (α : PDCBehavior O J U V X Y E m hE F n hF) {b : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U V X Y // IsDDCFrom E F b a})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = α.1 h)
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) :
    (PDCBehavior.attach hE' hF' α R hR).decisionProbability D hD =
      ∑ a ∈ P.1.support, P.1 a * R.decisionProbability (trim (absorbAll D a.1))
        (absorbAll_isDDD hD a.2.isDDC) := by
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation hE' R hR
  rw [decisionProbability_of_presents D hD (attachPDS hF' P Q)
    (fun h => (PDCBehavior.attach_presents hE' hF' α R hR P Q hP hQ h).symm)]
  simp only [attachPDS, Distribution.mass_fTransform]
  rw [Distribution.mass_prod_eq_double_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [decisionProbability_of_presents _ _ Q hQ]
  simp only [Distribution.mass, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have ht := close_start_eq
    ((behEq_iff_transcript.mp (trim_behEq (SystemAlgebra.apply a.1 s.1))) (envOf D))
  simp only [ht, close_trim_start,
    decision_apply D a.1 s.1 hD.2.1.choose_spec.terminating a.2.isDDC true]
  split_ifs <;> simp

end Attachment

section Distinguisher

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

/-- A probabilistic distinguisher compatible with a domain: a finite distribution over the
deterministic distinguishers compatible with it (Lanzenberger–Maurer, Definition 9). -/
abbrev Domain.Distinguisher (𝒟 : Domain (Σ i, X i) (Σ i, Y i)) :=
  Distribution.ProbDist {D : DDD I X Y // IsDDD D ∧ 𝒟.DecisionCompatible D}

/-- The probability that a probabilistic distinguisher outputs `1` on a random system. -/
noncomputable def Domain.Distinguisher.probability {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}
    (P : 𝒟.Distinguisher) (R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) : ℝ :=
  P.1.sum fun D w => w * R.decisionProbability D.1 D.2.1

/-- The advantage of a probabilistic distinguisher between two random systems: the difference
of its probabilities of outputting `1`. -/
noncomputable def Domain.Distinguisher.advantage {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}
    (P : 𝒟.Distinguisher) (R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) : ENNReal :=
  ENNReal.ofReal |P.probability R - P.probability S|

namespace Domain.Distinguisher

variable {𝒟 : Domain (Σ i, X i) (Σ i, Y i)} (P : 𝒟.Distinguisher)
  (R S T : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟)

@[simp] theorem advantage_self : P.advantage R R = 0 := by simp [advantage]

theorem advantage_symm : P.advantage R S = P.advantage S R := by
  rw [advantage, advantage, abs_sub_comm]

theorem advantage_triangle : P.advantage R T ≤ P.advantage R S + P.advantage S T := by
  rw [advantage, advantage, advantage, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

end Domain.Distinguisher

/-- **The transcript distance is the largest advantage of a probabilistic
distinguisher.** -/
theorem RandomSystem.transcriptDistance_eq_iSup {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}
    {R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface) :
    R.transcriptDistance S = ⨆ P : 𝒟.Distinguisher, P.advantage R S := by
  simp only [Domain.Distinguisher.advantage]
  apply le_antisymm
  · refine iSup_le fun E => iSup_le fun n => iSup_le fun hn => iSup_le fun hc => ?_
    let event := fun h => S.sLaw E.1 n h < R.sLaw E.1 n h
    let test := fun t : List (Σ i, X i) × List (Σ i, Y i) => event (t.1.zip t.2)
    let P : 𝒟.Distinguisher := ⟨Finsupp.single ⟨envProbe E test, envProbe_isDDD hn,
      Domain.envProbe_decisionCompatible hc test⟩ 1, Distribution.isProbDist_single _⟩
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_iSup_of_le P le_rfl)
    simp only [P, Domain.Distinguisher.probability, Finsupp.sum_single_index, zero_mul,
      one_mul]
    rw [decisionProbability_envProbe hn test hR, decisionProbability_envProbe hn test hS]
    have hz (h : List ((Σ i, X i) × (Σ i, Y i))) :
        (h.map Prod.fst).zip (h.map Prod.snd) = h := (List.zip_of_prod rfl rfl).symm
    simp only [test, hz]
    rw [statDist_eq_mass_sub_mass_pos]
    exact le_abs_self _
  · refine iSup_le fun P => ?_
    have hb := abs_average_sub_le P _ _
      (fun D => decisionProbability_gap_le D.2.1 D.2.2 hR hS)
    calc ENNReal.ofReal |P.probability R - P.probability S|
        ≤ ENNReal.ofReal (R.transcriptDistance S).toReal := ENNReal.ofReal_le_ofReal hb
      _ = R.transcriptDistance S := ENNReal.ofReal_toReal
          (ne_top_of_le_ne_top ENNReal.one_ne_top (transcriptDistance_le_one hR hS))

/-- The advantage of a probabilistic distinguisher is at most the transcript distance. -/
theorem Domain.Distinguisher.advantage_le_transcriptDistance {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}
    (P : 𝒟.Distinguisher) {R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface) :
    P.advantage R S ≤ R.transcriptDistance S := by
  rw [RandomSystem.transcriptDistance_eq_iSup hR hS]
  exact le_iSup (fun P : 𝒟.Distinguisher => P.advantage R S) P

end Distinguisher

section Closure

variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- Absorbing a PDC from `E` to `F` into a probabilistic distinguisher compatible with `F`
gives a probabilistic distinguisher compatible with `E`. -/
theorem Domain.Distinguisher.exists_absorbAll
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (P : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).Distinguisher) :
    ∃ Q : (Domain.ofInputs E m hE : Domain (Σ j, X j) (Σ j, Y j)).Distinguisher,
      ∀ (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
        (hR : R.RepliesAtQueriedInterface),
        Q.probability R = P.probability (PDCBehavior.attach hE' hF' α R hR) := by
  obtain ⟨b, Pα, hPα⟩ := α.2
  refine ⟨⟨Distribution.fTransform (fun p => (⟨trim (absorbAll p.1.1 p.2.1),
      absorbAll_isDDD p.1.2.1 p.2.2.isDDC, p.1.2.2.absorbAll hE' hF' p.1.2.1 p.2.2⟩ :
        {D : DDD J X Y // IsDDD D ∧
          (Domain.ofInputs E m hE : Domain (Σ j, X j) (Σ j, Y j)).DecisionCompatible D}))
      (Distribution.prod P.1 Pα.1),
    Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _ P.2 Pα.2)⟩,
    fun R hR => ?_⟩
  simp only [Domain.Distinguisher.probability, Distribution.sum_fTransform_mul,
    Distribution.sum_prod_mul]
  apply Finsupp.sum_congr
  intro D _
  rw [RandomSystem.decisionProbability_attach hE' hF' D.1 D.2.1 α Pα hPα R hR]
  rfl

/-- **The distinguisher `P ∘ α`**: `P` with the PDC `α` absorbed. -/
noncomputable def Domain.Distinguisher.absorb
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (P : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).Distinguisher) :
    (Domain.ofInputs E m hE : Domain (Σ j, X j) (Σ j, Y j)).Distinguisher :=
  (Domain.Distinguisher.exists_absorbAll hE' hF' α P).choose

/-- `P ∘ α` decides `1` on `R` with the probability that `P` decides `1` on `α` attached to `R`. -/
theorem Domain.Distinguisher.probability_absorb
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (P : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).Distinguisher)
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
    (hR : R.RepliesAtQueriedInterface) :
    (P.absorb hE' hF' α).probability R = P.probability (PDCBehavior.attach hE' hF' α R hR) :=
  (Domain.Distinguisher.exists_absorbAll hE' hF' α P).choose_spec R hR

end Closure

section ParallelClosure

variable {I J : Type} [Fintype I] [Fintype J] {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type}
  [∀ i, Fintype (X₁ i)] [∀ i, Fintype (Y₁ i)] [∀ j, Fintype (X₂ j)] [∀ j, Fintype (Y₂ j)]
  {E : List (Σ i, X₁ i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ j, X₂ j) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- Absorbing a resource with domain `F` run beside, given by a presentation `U`, into a
probabilistic distinguisher compatible with the parallel domain gives a probabilistic
distinguisher compatible with `E`. -/
theorem Domain.Distinguisher.exists_absorbRight
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (P : (Domain.ofInputs (parallelInputs (F := Sum.rec X₁ X₂) E F) (m + n)
      (parallelInputs_length_le hE hF) :
        Domain (Σ l, Sum.rec X₁ X₂ l) (Σ l, Sum.rec Y₁ Y₂ l)).Distinguisher)
    (U : Distribution.ProbDist {t : InterfaceSystem J X₂ Y₂ //
      IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ F h}) :
    ∃ Q : (Domain.ofInputs E m hE : Domain (Σ i, X₁ i) (Σ i, Y₁ i)).Distinguisher,
      ∀ (T : Distribution.ProbDist {s : InterfaceSystem I X₁ Y₁ //
          IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h})
        (R : RandomSystem (Σ i, X₁ i) (Σ i, Y₁ i) (Domain.ofInputs E m hE))
        (S : RandomSystem (Σ l, Sum.rec X₁ X₂ l) (Σ l, Sum.rec Y₁ Y₂ l)
          (Domain.ofInputs (parallelInputs (F := Sum.rec X₁ X₂) E F) (m + n)
            (parallelInputs_length_le hE hF))),
        (∀ h, behaviorMass T.1 (h.map Prod.fst) (h.map Prod.snd) = R h) →
        (∀ h, behaviorMass (parallelPDS T U).1 (h.map Prod.fst) (h.map Prod.snd) = S h) →
          Q.probability R = P.probability S := by
  refine ⟨⟨Distribution.fTransform (fun p => (⟨absorbRight p.1.1 p.2.1,
      absorbRight_isDDD p.1.2.1 p.2.1, p.1.2.2.absorbRight (hF := hF) hE' hF' p.1.2.1 p.2.2⟩ :
        {D : DDD I X₁ Y₁ // IsDDD D ∧
          (Domain.ofInputs E m hE : Domain (Σ i, X₁ i) (Σ i, Y₁ i)).DecisionCompatible D}))
      (Distribution.prod P.1 U.1),
    Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist _ _ P.2 U.2)⟩,
    fun T R S hR hS => ?_⟩
  simp only [Domain.Distinguisher.probability, Distribution.sum_fTransform_mul,
    Distribution.sum_prod_mul]
  apply Finsupp.sum_congr
  intro D _
  rw [RandomSystem.decisionProbability_parallel (hF := hF) D.1 D.2.1 T U hR hS]
  rfl

end ParallelClosure

end SystemAlgebra
