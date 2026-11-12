module

public import RandomSystems.Cumulative.Presentation.Defs
public import RandomSystems.Cumulative.Presentation.FiniteCuts

/-!
# Finite presentations of cumulative behavior

`IsSubprobabilistic.presentation` samples supported finite choice tables.
`presentation_mass` identifies their behavior and `presentation_possible` records their supported
transcripts. The `exists_presentation` endpoint collects these facts.
`RandomSystem.exists_presentation` supplies the domain certificate and identifies
bounded random systems with equivalence classes of finite PDSs.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution Presentation

variable {A B : Type} [Fintype A] [Fintype B]

namespace IsSubprobabilistic

variable {p : List (A × B) → ℝ} (hp : IsSubprobabilistic p) {n : ℕ}

/-- A supported choice table is mapped to its own realization. -/
lemma presentationSample_val_of_mem
    (hn : ∀ h, n < h.length → p h = 0) (P : System A B → Prop)
    (hP : ∀ g, hp.PossibleChoice g → P (realization g).1)
    (c : Node A B n → Option B) (hc : c ∈ (hp.choiceLaw n).support) :
    (hp.presentationSample hn P hP c).1 = (realization (choiceAt c)).1 := by
  simp only [presentationSample, dite_eq_left hc]

/-- The explicit presentation has exactly the original cumulative masses. -/
lemma presentation_mass
    (hn : ∀ h, n < h.length → p h = 0) (P : System A B → Prop)
    (hP : ∀ g, hp.PossibleChoice g → P (realization g).1) (h : List (A × B)) :
    behaviorMass (hp.presentation hn P hP).1 (h.map Prod.fst) (h.map Prod.snd) = p h := by
  rw [presentation, ProbDist.map_val, behaviorMass, mass_fTransform, ← hp.mass_replies hn h]
  exact mass_congr_of_support _ fun c hc => by rw [hp.presentationSample_val_of_mem hn P hP c hc]

/-- Every transcript of a supported presentation sample has nonzero cumulative mass. -/
lemma presentation_possible
    (hn : ∀ h, n < h.length → p h = 0) (P : System A B → Prop)
    (hP : ∀ g, hp.PossibleChoice g → P (realization g).1)
    (s : {s : System A B // P s}) (hs : s ∈ (hp.presentation hn P hP).1.support)
    (h : List (A × B)) (hr : Replies s.1 (h.map Prod.fst) (h.map Prod.snd)) : p h ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := mem_support_fTransform _ _ hs
  rw [hp.presentationSample_val_of_mem hn P hP c hc] at hr
  exact hp.realization_possible _ (hp.choiceAt_supported hn hc) hr

omit [Fintype A] [Fintype B] in
/-- A bounded cumulative behavior is represented by its explicit finite choice-table law. -/
theorem exists_presentation [_root_.Finite A] [_root_.Finite B]
    (hn : ∀ h, n < h.length → p h = 0) (P : System A B → Prop)
    (hP : ∀ g, hp.PossibleChoice g → P (realization g).1) :
    ∃ μ : Distribution.ProbDist {s : System A B // P s},
      (∀ h, behaviorMass μ.1 (h.map Prod.fst) (h.map Prod.snd) = p h) ∧
      ∀ s ∈ μ.1.support, ∀ h, Replies s.1 (h.map Prod.fst) (h.map Prod.snd) → p h ≠ 0 := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  exact ⟨hp.presentation hn P hP, hp.presentation_mass hn P hP, hp.presentation_possible hn P hP⟩

omit [Fintype A] [Fintype B] in
/-- Every possible transcript is produced by a deterministic system with every
property of the realizations of possible choices. -/
lemma exists_replies [_root_.Finite A] [_root_.Finite B]
    (hn : ∀ h, n < h.length → p h = 0) (P : System A B → Prop)
    (hP : ∀ g, hp.PossibleChoice g → P (realization g).1) {h : List (A × B)} (hm : p h ≠ 0) :
    ∃ s, P s ∧ Replies s (h.map Prod.fst) (h.map Prod.snd) := by
  obtain ⟨μ, hμ, -⟩ := hp.exists_presentation hn P hP
  rw [← hμ h] at hm
  obtain ⟨s, -, hs⟩ := behaviorMass_ne_zero hm
  exact ⟨s.1, s.2, hs⟩

end IsSubprobabilistic

namespace RandomSystem

variable {D : Domain A B}

/-- **Presentation theorem.** Every random system over finite alphabets on a bounded
domain is the behavior of a finite PDS. -/
theorem exists_presentation (R : RandomSystem A B D) :
    ∃ (P : PDS A B D) (hP : P.isProbDist), PDS.behavior P hP = R := by
  have hp := R.2.isSubprobabilistic
  obtain ⟨μ, hμ, -⟩ := hp.exists_presentation (n := D.bound)
    (fun h hl => R.mass_eq_zero_of_bound_lt hl)
    (fun s => IsDDS s ∧ HasDomain D s)
    (fun g hg => ⟨(realization g).2, R.hasDomain_realization hg⟩)
  exact ⟨μ.1, μ.2, RandomSystem.ext fun t => hμ t⟩

/-- Random systems are exactly the classes of equivalent finite PDSs. -/
lemma ofPDSClass_bijective (D : Domain A B) :
    Function.Bijective (ofPDSClass (A := A) (B := B) D) := by
  refine ⟨ofPDSClass_injective, fun R => ?_⟩
  obtain ⟨P, hP, hR⟩ := exists_presentation R
  exact ⟨Quotient.mk _ ⟨P, hP⟩, hR⟩

end RandomSystem

end SystemAlgebra
