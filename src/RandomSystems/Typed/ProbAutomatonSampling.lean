module

public import RandomSystems.Typed.ProbAutomaton
public import RandomSystems.Typed.SamplingAlgebra

/-!
# Retained parameters in probabilistic automata

`sample_ofProbAutomaton_eq` presents a mixture of automata as one automaton on `(θ, s)`.
The initial distribution draws `θ` and then `s`; every transition retains that same `θ`.
This representation preserves the cumulative law at every admitted transcript.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability Probability.Distribution

/-- A mixture of probabilistic automata over `θ ∼ μ` equals a single automaton retaining `θ`. -/
lemma sample_ofProbAutomaton_eq
    -- `A` fixes the interface; `Θ` carries the retained parameter and `S` the evolving state.
    {A : Interface} {Θ S : Type}
    -- Draw `θ` once from `μ`, then initialize and run the automaton selected by that same `θ`.
    (μ : ProbDist Θ) (step : Θ → ProbStep S A.I A.X A.Y) (init : Θ → ProbDist S) :
    TypedSystem.sample μ.1 (fun θ => TypedSystem.ofProbAutomaton A (step θ) (init θ)) =
      TypedSystem.ofProbAutomaton A
        (fun ps o u => (step ps.1 ps.2 o u).map fun sy => ((ps.1, sy.1), sy.2))
        (μ.bind fun θ => (init θ).map fun s => (θ, s)) := by
  classical
  let liftStep : ProbStep (Θ × S) A.I A.X A.Y :=
    fun ps o u => (step ps.1 ps.2 o u).map fun sy => ((ps.1, sy.1), sy.2)
  have htrans : ∀ (ν : Θ → Distribution S) (xq : Σ i, A.X i) (yq : Σ i, A.Y i),
      liftStep.transition (μ.1.bindK fun θ => fTransform (fun s => (θ, s)) (ν θ)) xq yq =
        μ.1.bindK fun θ => fTransform (fun s => (θ, s)) ((step θ).transition (ν θ) xq yq) := by
    intro ν ⟨o, u⟩ yq
    simp only [ProbStep.transition, ProbStep.outcome, liftStep]
    rw [bindK_bindK]
    apply bindK_congr
    intro θ _
    rw [bindK_fTransform, fTransform_bindK]
    apply bindK_congr
    intro s _
    simp only [Function.comp_def, ProbDist.map_val, fTransform_fTransform]
    rw [Distribution.restrict_fTransform, Distribution.restrict_fTransform,
      fTransform_fTransform, fTransform_fTransform]
    have hpred : ∀ x : S × A.Y o,
        ((ProbStep.tagged ⟨o, u⟩ ((θ, x.1), x.2)).2 = yq) ↔
        ((ProbStep.tagged ⟨o, u⟩ x).2 = yq) := fun _ => Iff.rfl
    have hr := Distribution.restrict_congr (step θ s o u).1 hpred
    simp only [Function.comp_def, ProbStep.tagged]
  have hbel : ∀ h : List ((Σ i, A.X i) × Σ i, A.Y i),
      liftStep.belief A.inputDomain
        (μ.bind fun θ => (init θ).map fun s => (θ, s)).1 h =
      μ.1.bindK fun θ =>
        fTransform (fun s => (θ, s)) ((step θ).belief A.inputDomain (init θ).1 h) := by
    intro h
    induction h using List.reverseRecOn with
    | nil =>
      simp only [ProbStep.belief, ProbStep.beliefRev, List.reverse_nil, ProbDist.bind_val,
        ProbDist.map_val]
    | append_singleton h z ih =>
      rw [ProbStep.belief_snoc, ih]
      by_cases hd : A.inputDomain h z.1
      · rw [ite_eq_left hd, htrans]
        apply bindK_congr
        intro θ _
        rw [ProbStep.belief_snoc, ite_eq_left hd]
      · rw [ite_eq_right hd]
        have hz : ∀ θ : Θ,
            fTransform (fun s => (θ, s))
              ((step θ).belief A.inputDomain (init θ).1 (h ++ [z])) = 0 := by
          intro θ
          rw [ProbStep.belief_snoc, ite_eq_right hd, fTransform_zero]
        simp only [hz, bindK_zero_right]
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [TypedSystem.sample_mass, TypedSystem.ofProbAutomaton_mass, hbel]
  rw [Distribution.weight_bindK]
  simp only [Distribution.weight_fTransform, TypedSystem.ofProbAutomaton_mass]
  rfl

end SystemAlgebra.TypedSystem
