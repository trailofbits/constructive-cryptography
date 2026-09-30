import RandomSystems.Distance.Decision
import RandomSystems.Converter.ParallelPDS

/-!
# Absorbing a system run beside

A distinguisher on two systems run in parallel can instead test the left system with the
right one connected internally. When the right system is a deterministic resource with
domain `F`, the absorbing distinguisher is compatible with the left domain `E`, because the
parallel domain is exact. On presentations, the decision probability on the parallel
composition is the average over samples of the right resource of the absorbing decisions on
the left one.

## Main definitions

* `absorbRight D t`: the distinguisher `D` with the system `t` connected at the right
  interface

## Main results

* `decision_parallel_system`: `D` decides on `s ∥ t` as `absorbRight D t` decides on `s`
* `Domain.DecisionCompatible.absorbRight`: absorption preserves compatibility
* `RandomSystem.decisionProbability_parallel`: averaging over the right presentation
-/

namespace SystemAlgebra

open Classical Probability

variable {I J : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type}

def pairObserverInput : (Σ p : DPort (Two I J), dIn (twoFam Y₁ Y₂) p) →
    Σ p : DPort (I ⊕ J), dIn (Sum.rec Y₁ Y₂) p
  | ⟨.start, u⟩ => ⟨.start, u⟩
  | ⟨.dec, e⟩ => e.elim
  | ⟨.res ⟨none, i⟩, y⟩ => ⟨.res (.inl i), y⟩
  | ⟨.res ⟨some (), j⟩, y⟩ => ⟨.res (.inr j), y⟩

def pairObserverOutput : (Σ p : DPort (I ⊕ J), dOut (Sum.rec X₁ X₂) p) →
    Σ p : DPort (Two I J), dOut (twoFam X₁ X₂) p
  | ⟨.start, e⟩ => e.elim
  | ⟨.dec, b⟩ => ⟨.dec, b⟩
  | ⟨.res (.inl i), x⟩ => ⟨.res ⟨none, i⟩, x⟩
  | ⟨.res (.inr j), x⟩ => ⟨.res ⟨some (), j⟩, x⟩

noncomputable def pairObserver (D : DDD (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂)) :
    DDD (Two I J) (twoFam X₁ X₂) (twoFam Y₁ Y₂) :=
  relabel D pairObserverInput pairObserverOutput

theorem pairObserver_isDDD {D : DDD (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂)}
    (hD : IsDDD D) : IsDDD (pairObserver D) :=
  hD.relabel _ _ (twoSum I J)
    (by rintro ⟨_ | _ | ⟨_ | ⟨⟨⟩⟩, i⟩, v⟩ <;> first | exact v.elim | rfl)
    (by rintro ⟨_ | _ | (i | j), v⟩ <;> first | exact v.elim | rfl)

theorem close_parallel_system
    (D : DDD (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂))
    (s : InterfaceSystem I X₁ Y₁) (t : InterfaceSystem J X₂ Y₂) :
    close D (relabel (pair s t) (sumAlphabet (Sum.rec X₁ X₂)).symm
      (sumAlphabet (Sum.rec Y₁ Y₂))) =
      relabel (close (pairObserver D) (pairI s t)) trigMap decMap := by
  rw [close_eq, close_eq]
  unfold pairObserver pairI
  rw [pair_relabel_right, interconnect_relabel, pair_relabel_left, pair_relabel_right,
    interconnect_relabel, interconnect_relabel, relabel_interconnect]
  congr 1
  · funext o
    rcases o with ⟨(_ | ⟨⟨⟩⟩), o⟩
    · rcases o with ⟨_ | _ | (i | j), v⟩
      · exact v.elim
      all_goals rfl
    · rcases o with ⟨(_ | ⟨⟨⟩⟩), ⟨i, y⟩⟩ <;> rfl
  · funext z
    rcases z with ⟨⟨⟨(_ | ⟨⟨⟩⟩), l⟩, hl⟩, v⟩
    · rcases l with _ | _ | i
      · rfl
      · exact v.elim
      · exact (hl (res_mem_closeSet i)).elim
    · exact (hl (sys_mem_closeSet l)).elim

/-- The right neighbor is absorbed using the partial closing. -/
noncomputable def absorbRight (D : DDD (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂))
    (t : InterfaceSystem J X₂ Y₂) : DDD I X₁ Y₁ :=
  trim (partialClose (pairObserver D) t)

theorem absorbRight_isDDD {D : DDD (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂)}
    (hD : IsDDD D) (t : InterfaceSystem J X₂ Y₂) : IsDDD (absorbRight D t) :=
  partialClose_isDDD (pairObserver_isDDD hD)

theorem decision_parallel_system {D : DDD (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂)}
    (hD : IsDDD D) (s : InterfaceSystem I X₁ Y₁) (t : InterfaceSystem J X₂ Y₂) (b : Bool) :
    decOut b ∈ close D (relabel (trim (pair s t))
      (sumAlphabet (Sum.rec X₁ X₂)).symm (sumAlphabet (Sum.rec Y₁ Y₂))) [startIn] ↔
      decOut b ∈ close (absorbRight D t) s [startIn] := by
  rw [← trim_relabel]
  have he := close_start_eq ((behEq_iff_transcript.mp
    (trim_behEq (relabel (pair s t) (sumAlphabet (Sum.rec X₁ X₂)).symm
      (sumAlphabet (Sum.rec Y₁ Y₂))))) (envOf D))
  rw [he, close_parallel_system,
    close_pair _ s t (pairObserver_isDDD hD).2.1.choose_spec.terminating]
  simp only [relabel, List.map_cons, List.map_nil, trigMap_eq]
  rw [decOut_mem_map_iff _ (fun _ => rfl), decOut_mem_map_iff _ (fun _ => rfl)]
  exact (congrArg (fun z => decOut b ∈ z)
    (close_trim_start (partialClose (pairObserver D) t) s)).symm.to_iff

variable [Fintype I] [Fintype J] [∀ i, Fintype (X₁ i)] [∀ i, Fintype (Y₁ i)]
  [∀ j, Fintype (X₂ j)] [∀ j, Fintype (Y₂ j)]
  {E : List (Σ i, X₁ i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ j, X₂ j) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- Absorbing a deterministic resource run beside preserves compatibility. -/
theorem Domain.DecisionCompatible.absorbRight
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    {D : DDD (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂)}
    (hc : (Domain.ofInputs (parallelInputs (F := Sum.rec X₁ X₂) E F) (m + n)
      (parallelInputs_length_le hE hF) :
        Domain (Σ l, Sum.rec X₁ X₂ l) (Σ l, Sum.rec Y₁ Y₂ l)).DecisionCompatible D)
    (hD : IsDDD D) {t : InterfaceSystem J X₂ Y₂}
    (ht : IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ F h) :
    (Domain.ofInputs E m hE : Domain (Σ i, X₁ i) (Σ i, Y₁ i)).DecisionCompatible
      (SystemAlgebra.absorbRight D t) := by
  apply (Domain.decisionCompatible_iff_deterministic hE' (absorbRight_isDDD hD t)).mpr
  intro s hs hr he
  have hst := parallel_system_valid ⟨hs, hr, he⟩ ht
  have hd := (Domain.decisionCompatible_iff_deterministic
    (parallelInputs_nonempty_prefix hE'.2 hF'.2) hD).mp hc _ hst.1 hst.2.1 hst.2.2
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨b, rfl⟩ := eq_decOut v
  exact Part.dom_iff_mem.mpr ⟨_, (decision_parallel_system hD s t b).mp hv⟩

/-- On presentations, the decision probability on the parallel composition averages the
absorbing decisions over the samples of the right resource. -/
theorem RandomSystem.decisionProbability_parallel
    (D : DDD (I ⊕ J) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂)) (hD : IsDDD D)
    (P : Distribution.ProbDist {s : InterfaceSystem I X₁ Y₁ //
      IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h})
    (Q : Distribution.ProbDist {t : InterfaceSystem J X₂ Y₂ //
      IsDDS t ∧ SystemAlgebra.RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ F h})
    {R : RandomSystem (Σ i, X₁ i) (Σ i, Y₁ i) (Domain.ofInputs E m hE)}
    {S : RandomSystem (Σ l, Sum.rec X₁ X₂ l) (Σ l, Sum.rec Y₁ Y₂ l)
      (Domain.ofInputs (parallelInputs (F := Sum.rec X₁ X₂) E F) (m + n)
        (parallelInputs_length_le hE hF))}
    (hR : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = R h)
    (hS : ∀ h, behaviorMass (parallelPDS P Q).1 (h.map Prod.fst) (h.map Prod.snd) = S h) :
    S.decisionProbability D hD =
      ∑ t ∈ Q.1.support, Q.1 t *
        R.decisionProbability (absorbRight D t.1) (absorbRight_isDDD hD t.1) := by
  rw [RandomSystem.decisionProbability_of_presents D hD _ hS]
  simp only [parallelPDS, Distribution.mass_fTransform]
  rw [Distribution.mass_prod_eq_sum_right P.1 Q.1 (fun s t => decOut true ∈ close D
    (SystemAlgebra.relabel (trim (pair s.1 t.1)) (sumAlphabet (Sum.rec X₁ X₂)).symm
      (sumAlphabet (Sum.rec Y₁ Y₂))) [startIn])]
  apply Finset.sum_congr rfl
  intro t _
  rw [RandomSystem.decisionProbability_of_presents _ _ P hR]
  apply congrArg (fun x : ℝ => Q.1 t * x)
  apply Distribution.mass_congr
  intro s
  exact decision_parallel_system hD s.1 t.1 true

end SystemAlgebra
