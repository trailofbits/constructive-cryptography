module

public import RandomSystems.Typed.ProbAutomaton
public import RandomSystems.Typed.Game

/-!
# Probabilistic automata with a monotone binary output

`TypedGame.ofProbAutomaton` starts with an unset hidden bit, samples each transition,
and requires that the reply bit agrees with the next state and never resets.
`TypedGame.visible_ofProbAutomaton` erases that bit by mapping each reply through
`ProbStep.forgetMBO`. Summing over bit assignments commutes with the transition law.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

section ProbAutomatonMBO

-- `A` specifies the ports and domain; `S` is the retained state before adding the hidden bit.
variable {A : Interface} {S : Type}

/-- Drop the MBO bit from a probabilistic step on `A.withMBO`. -/
noncomputable def ProbStep.forgetMBO (step : ProbStep S A.I A.X (withMBO A.Y)) :
    ProbStep S A.I A.X A.Y :=
  fun s i x => (step s i x).map fun p => (p.1, p.2.1)

/-- Sum a distribution-valued transcript function over all MBO assignments. -/
noncomputable def sumMBODist {Q : Type} {J : Type} {Y : J → Type}
    (f : List (Q × Σ j, withMBO Y j) → Distribution S) :
    List (Q × Σ j, Y j) → Distribution S
  | [] => f []
  | z :: t =>
    sumMBODist (fun k => f ((z.1, tagMBO false z.2) :: k)) t +
      sumMBODist (fun k => f ((z.1, tagMBO true z.2) :: k)) t

lemma sumMBODist_weight {Q : Type} {J : Type} {Y : J → Type}
    (f : List (Q × Σ j, withMBO Y j) → Distribution S) (h : List (Q × Σ j, Y j)) :
    (sumMBODist f h).weight = sumMBO (fun k => (f k).weight) h := by
  induction h generalizing f with
  | nil => rfl
  | cons z t ih =>
    simp only [sumMBODist, sumMBO, Distribution.weight_add]
    rw [ih, ih]

/-- A final visible reply splits into its unset-bit and set-bit cases. -/
lemma sumMBODist_snoc {Q : Type} {J : Type} {Y : J → Type}
    (f : List (Q × Σ j, withMBO Y j) → Distribution S)
    (h : List (Q × Σ j, Y j)) (z : Q × Σ j, Y j) :
    sumMBODist f (h ++ [z]) =
      sumMBODist (fun k => f (k ++ [(z.1, tagMBO false z.2)]) +
        f (k ++ [(z.1, tagMBO true z.2)])) h := by
  induction h generalizing f with
  | nil => rfl
  | cons w t ih =>
    simp only [List.cons_append, sumMBODist]
    rw [ih, ih]

/-- Summing zero mass over bit assignments gives zero. -/
lemma sumMBODist_zero {Q : Type} {J : Type} {Y : J → Type} (h : List (Q × Σ j, Y j)) :
    sumMBODist (fun _ : List (Q × Σ j, withMBO Y j) => (0 : Distribution S)) h = 0 := by
  induction h with
  | nil => rfl
  | cons z t ih => simp only [sumMBODist, ih, add_zero]

/-- A transition preserves addition of input state distributions. -/
lemma ProbStep.transition_add {I : Type} {X Y : I → Type} (step : ProbStep S I X Y)
    (β₁ β₂ : Distribution S) (x : Σ i, X i) (y : Σ i, Y i) :
    step.transition (β₁ + β₂) x y = step.transition β₁ x y + step.transition β₂ x y := by
  simp only [ProbStep.transition, bindK_add]

/-- A transition carries zero input mass to zero output mass. -/
lemma ProbStep.transition_zero {I : Type} {X Y : I → Type} (step : ProbStep S I X Y)
    (x : Σ i, X i) (y : Σ i, Y i) :
    step.transition 0 x y = 0 := by
  simp only [ProbStep.transition, bindK_zero]

/-- Summing over hidden bit histories commutes with one visible transition. -/
lemma sumMBODist_transition {Q : Type} {I : Type} {X Y : I → Type}
    (step : ProbStep S I X Y)
    (f : List (Q × Σ j, withMBO Y j) → Distribution S)
    (h : List (Q × Σ j, Y j)) (x : Σ i, X i) (y : Σ i, Y i) :
    sumMBODist (fun k => step.transition (f k) x y) h =
      step.transition (sumMBODist f h) x y := by
  induction h generalizing f with
  | nil => rfl
  | cons z t ih =>
    simp only [sumMBODist]
    rw [ih, ih, ProbStep.transition_add]

/-- Adding both possible reply bits recovers the transition with that bit forgotten. -/
lemma transition_tagMBO_add (step : ProbStep S A.I A.X (withMBO A.Y))
    (β : Distribution S) (x : Σ i, A.X i) (y : Σ i, A.Y i) :
    step.transition β x (tagMBO false y) + step.transition β x (tagMBO true y) =
      (ProbStep.forgetMBO step).transition β x y := by
  simp only [ProbStep.transition, ← bindK_add_right]
  apply bindK_congr
  intro s _
  ext s'
  simp only [Finsupp.add_apply, fTransform_apply_eq_mass, ProbStep.outcome, ProbStep.forgetMBO,
    ProbDist.map_val, fTransform_fTransform, Function.comp_def, ProbStep.tagged]
  rw [mass_restrict, mass_restrict, mass_restrict,
    mass_fTransform, mass_fTransform, mass_fTransform]
  have hsplit := mass_and_add_mass_not_and (step s x.1 x.2).1
    (fun a : S × A.Y x.1 × Bool => a.2.2 = false)
    (fun a : S × A.Y x.1 × Bool =>
      a.1 = s' ∧ (⟨x.1, a.2.1⟩ : Σ i, A.Y i) = y)
  have h1 : (step s x.1 x.2).1.mass (fun a =>
      a.1 = s' ∧ (⟨x.1, a.2⟩ : Σ i, withMBO A.Y i) = tagMBO false y) =
      (step s x.1 x.2).1.mass (fun a =>
        a.2.2 = false ∧ (a.1 = s' ∧ (⟨x.1, a.2.1⟩ : Σ i, A.Y i) = y)) :=
    mass_congr _ fun a => by
      simp only [eq_tagMBO_iff, forgetMBO]
      tauto
  have h2 : (step s x.1 x.2).1.mass (fun a =>
      a.1 = s' ∧ (⟨x.1, a.2⟩ : Σ i, withMBO A.Y i) = tagMBO true y) =
      (step s x.1 x.2).1.mass (fun a =>
        ¬ a.2.2 = false ∧ (a.1 = s' ∧ (⟨x.1, a.2.1⟩ : Σ i, A.Y i) = y)) :=
    mass_congr _ fun a => by
      simp only [eq_tagMBO_iff, forgetMBO, Bool.not_eq_false]
      tauto
  dsimp only [ProbStep.tagged]
  rw [h1, h2, hsplit]

open Classical in
/-- The visible state law is the sum over all compatible hidden-bit histories. -/
lemma sumMBODist_belief (step : ProbStep S A.I A.X (withMBO A.Y))
    (init : Distribution S) (h : List ((Σ i, A.X i) × Σ i, A.Y i)) :
    sumMBODist (step.belief A.withMBO.inputDomain init) h =
      (ProbStep.forgetMBO step).belief A.inputDomain init h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    rw [sumMBODist_snoc]
    have hfst (k : List ((Σ i, A.X i) × Σ i, withMBO A.Y i)) :
        k.map Prod.fst = h.map Prod.fst →
        step.belief A.withMBO.inputDomain init (k ++ [(z.1, tagMBO false z.2)]) +
          step.belief A.withMBO.inputDomain init (k ++ [(z.1, tagMBO true z.2)]) =
        if A.domain (h.map Prod.fst ++ [z.1]) then
          (ProbStep.forgetMBO step).transition (step.belief A.withMBO.inputDomain init k) z.1 z.2
        else 0 := by
      intro hk
      rw [ProbStep.belief_snoc, ProbStep.belief_snoc]
      change (if A.domain (k.map Prod.fst ++ [z.1]) then _ else 0) +
          (if A.domain (k.map Prod.fst ++ [z.1]) then _ else 0) = _
      rw [hk]
      by_cases hadm : A.domain (h.map Prod.fst ++ [z.1])
      · rw [ite_eq_left hadm, ite_eq_left hadm, ite_eq_left hadm]
        exact transition_tagMBO_add step _ z.1 z.2
      · rw [ite_eq_right hadm, ite_eq_right hadm, ite_eq_right hadm, add_zero]
    have hsum : ∀ (f : List ((Σ i, A.X i) × Σ i, withMBO A.Y i) → Distribution S)
        (g : List ((Σ i, A.X i) × Σ i, withMBO A.Y i) → Distribution S),
        (∀ k, k.map Prod.fst = h.map Prod.fst → f k = g k) →
        sumMBODist f h = sumMBODist g h := by
      clear ih hfst
      induction h with
      | nil =>
        intro f g hfg
        exact hfg [] rfl
      | cons w t iht =>
        intro f g hfg
        simp only [sumMBODist]
        congr 1
        · exact iht _ _ fun k hk => hfg _ (by simp only [List.map_cons, hk])
        · exact iht _ _ fun k hk => hfg _ (by simp only [List.map_cons, hk])
    rw [hsum _ _ hfst, ProbStep.belief_snoc]
    change sumMBODist (fun k => if A.domain (h.map Prod.fst ++ [z.1]) then _ else 0) h =
      if A.domain (h.map Prod.fst ++ [z.1]) then _ else 0
    by_cases hadm : A.domain (h.map Prod.fst ++ [z.1])
    · simp only [hadm, ↓reduceIte]
      rw [sumMBODist_transition, ih]
    · simp only [hadm, ↓reduceIte]
      exact sumMBODist_zero h

/-- Forgetting the MBO on a probabilistic automaton equals running `ProbStep.forgetMBO`. -/
lemma TypedSystem.ofProbAutomaton_visible
    (step : ProbStep S A.I A.X (withMBO A.Y)) (init : ProbDist S) :
    (TypedSystem.ofProbAutomaton A.withMBO step init).1.visible =
      (TypedSystem.ofProbAutomaton A (ProbStep.forgetMBO step) init).1 := by
  apply RandomSystem.ext
  intro h
  rw [RandomSystem.visible_apply, TypedSystem.ofProbAutomaton_val]
  change sumMBO (fun k => (step.belief A.withMBO.inputDomain init.1 k).weight) h =
    ((ProbStep.forgetMBO step).belief A.inputDomain init.1 h).weight
  rw [← sumMBODist_weight, sumMBODist_belief]

/-- Every supported next state comes from a supported state and a supported reply. -/
lemma ProbStep.mem_support_transition {I : Type} {X Y : I → Type} (step : ProbStep S I X Y)
    {β : Distribution S} (x : Σ i, X i) (y : Σ i, Y i)
    {s' : S} (hs' : s' ∈ (step.transition β x y).support) :
    ∃ s ∈ β.support, (s', y) ∈ (step.outcome s x).support := by
  have hne : step.transition β x y s' ≠ 0 := Finsupp.mem_support_iff.mp hs'
  rw [ProbStep.transition, bindK_apply] at hne
  obtain ⟨s, hs, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨s, hs, ?_⟩
  have hfne : fTransform Prod.fst ((step.outcome s x).restrict fun sy => sy.2 = y) s' ≠ 0 :=
    right_ne_zero_of_mul hterm
  have hmem := Finsupp.mem_support_iff.mpr hfne
  obtain ⟨⟨s'', y''⟩, hsupp, rfl⟩ := mem_support_fTransform _ _ hmem
  have hrne : (step.outcome s x).restrict (fun sy => sy.2 = y) (s'', y'') ≠ 0 :=
    Finsupp.mem_support_iff.mp hsupp
  rw [restrict_apply] at hrne
  split_ifs at hrne with hy
  · subst hy
    exact Finsupp.mem_support_iff.mpr hrne
  · exact absurd rfl hrne

/-- A flag-carrying probabilistic step whose output MBO equals the next flag and never resets a set
flag produces a monotone MBO game. -/
lemma TypedSystem.ofProbAutomaton_monotoneMBO
    -- `step` samples the next state and reply; `init` samples the state before the first query.
    (step : ProbStep (S × Bool) A.I A.X (withMBO A.Y)) (init : ProbDist S)
    -- `hflag` identifies the reply bit with the next state bit and prevents resetting it.
    (hflag : ∀ (s : S) (b : Bool) (i : A.I) (x : A.X i)
      (p : (S × Bool) × (A.Y i × Bool)),
      p ∈ (step (s, b) i x).1.support → p.2.2 = p.1.2 ∧ (b = true → p.1.2 = true)) :
    (TypedSystem.ofProbAutomaton A.withMBO step (init.map fun s => (s, false))).1.MonotoneMBO := by
  have hinv : ∀ (h : List ((Σ i, A.X i) × Σ i, withMBO A.Y i)),
      (∀ sb ∈ (step.belief A.withMBO.inputDomain (init.map fun s => (s, false)).1 h).support,
        (h.map fun z => z.2.2.2).Pairwise (· ≤ ·) ∧
          ∀ b ∈ h.map fun z => z.2.2.2, b ≤ sb.2) := by
    intro h
    induction h using List.reverseRecOn with
    | nil =>
      intro sb _
      exact ⟨List.Pairwise.nil, fun _ hm => by cases hm⟩
    | append_singleton h z ih =>
      intro sb' hsb'
      rw [ProbStep.belief_snoc] at hsb'
      split_ifs at hsb' with hadm
      · obtain ⟨sb, hsb, hout⟩ := ProbStep.mem_support_transition step z.1 z.2 hsb'
        obtain ⟨hpw, hle⟩ := ih sb hsb
        obtain ⟨p, hp, htag⟩ := mem_support_fTransform _ _ hout
        have hsbeq : p.1 = sb' := congrArg Prod.fst htag
        have hzeq : (⟨z.1.1, p.2⟩ : Σ i, withMBO A.Y i) = z.2 := congrArg Prod.snd htag
        have ⟨hmb, hmono⟩ := hflag sb.1 sb.2 z.1.1 z.1.2 p hp
        have hzb : z.2.2.2 = sb'.2 := by
          rw [← hzeq, ← hsbeq]
          exact hmb
        have hsb_le : sb.2 ≤ sb'.2 := by
          cases h2 : sb.2
          · exact Bool.false_le _
          · rw [← hsbeq, hmono h2]
        rw [List.map_append, List.map_singleton]
        refine ⟨List.pairwise_append.mpr ⟨hpw, List.pairwise_singleton _ _, ?_⟩, ?_⟩
        · intro b hb c hc
          rw [List.mem_singleton.mp hc, hzb]
          exact le_trans (hle b hb) hsb_le
        · intro b hb
          rcases List.mem_append.mp hb with hb | hb
          · exact le_trans (hle b hb) hsb_le
          · rw [List.mem_singleton.mp hb, hzb]
      · simp only [Finsupp.support_zero, Finset.notMem_empty] at hsb'
  intro h hne
  have hwt : (step.belief A.withMBO.inputDomain (init.map fun s => (s, false)).1 h).weight ≠ 0 :=
    hne
  have hsupp : (step.belief A.withMBO.inputDomain
      (init.map fun s => (s, false)).1 h).support.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hwt
    rw [Distribution.weight, Finsupp.sum, hemp, Finset.sum_empty]
  obtain ⟨sb, hsb⟩ := hsupp
  exact (hinv h sb hsb).1

/-- Package a flag-carrying probabilistic automaton as a `TypedGame A`. -/
noncomputable def TypedGame.ofProbAutomaton
    -- `step` samples the next state and reply; `init` samples the state before the first query.
    (step : ProbStep (S × Bool) A.I A.X (withMBO A.Y)) (init : ProbDist S)
    -- `hflag` identifies the reply bit with the next state bit and prevents resetting it.
    (hflag : ∀ (s : S) (b : Bool) (i : A.I) (x : A.X i)
      (p : (S × Bool) × (A.Y i × Bool)),
      p ∈ (step (s, b) i x).1.support → p.2.2 = p.1.2 ∧ (b = true → p.1.2 = true)) :
    TypedGame A :=
  ⟨TypedSystem.ofProbAutomaton A.withMBO step (init.map fun s => (s, false)),
    TypedSystem.ofProbAutomaton_monotoneMBO step init hflag⟩

/-- Hiding the monotone bit leaves the automaton with that bit erased from its replies. -/
lemma TypedGame.visible_ofProbAutomaton
    -- `step` samples the next state and reply; `init` samples the state before the first query.
    (step : ProbStep (S × Bool) A.I A.X (withMBO A.Y)) (init : ProbDist S)
    -- `hflag` identifies the reply bit with the next state bit and prevents resetting it.
    (hflag : ∀ (s : S) (b : Bool) (i : A.I) (x : A.X i)
      (p : (S × Bool) × (A.Y i × Bool)),
      p ∈ (step (s, b) i x).1.support → p.2.2 = p.1.2 ∧ (b = true → p.1.2 = true)) :
    (TypedGame.ofProbAutomaton step init hflag).visible =
      TypedSystem.ofProbAutomaton A (ProbStep.forgetMBO step) (init.map fun s => (s, false)) :=
  Subtype.ext (TypedSystem.ofProbAutomaton_visible step (init.map fun s => (s, false)))

end ProbAutomatonMBO

end SystemAlgebra
