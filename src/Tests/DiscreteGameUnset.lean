module

public import Tests.GameTranscript

/-!
# Unset mass before and after a reply

The existing echo game starts with a true condition. Its empty transcript has unset mass one;
a completed two-query transcript has unset mass zero. With a false condition, the same visible
transcript retains mass one. These cases use the generic discrete-game law.
-/

@[expose] public section

namespace Tests.DiscreteGameUnset

open SystemAlgebra Probability Probability.Distribution Tests.GameTranscript

/-- The echo interaction asks `false`, then `true`, as established in `adaptive_transcript`. -/
noncomputable def interaction := game.1.1.tr adaptive.1 2

/-- Even an initially true condition has emitted no MBO on the empty transcript. -/
example : (PDG.behavior samples.1 samples.2) (unsetMBOs []) = 1 ∧
    PDG.goodProbability samples.1 [] = 0 := by
  constructor
  · rw [PDG.behavior_unsetMBOs]
    simp only [List.map_nil, replies_nil, true_or, and_self, mass_true, samples.2.2]
  · rw [PDG.goodProbability, samples, PDG.ofAutomaton, ProbDist.map_val, mass_fTransform]
    simp only [always, not_true_eq_false, and_false]
    exact mass_eq_zero_of_forall_not _ (fun _ h => h)

/-- After replies occur, the initially true condition leaves no all-unset mass. -/
example : (PDG.behavior samples.1 samples.2) (unsetMBOs interaction) = 0 := by
  have nonempty : interaction ≠ [] := by
    rw [interaction, adaptive_transcript]
    exact List.cons_ne_nil _ _
  rw [PDG.behavior_unsetMBOs, samples, PDG.ofAutomaton, ProbDist.map_val, mass_fTransform]
  simp only [nonempty, false_or, always, not_true_eq_false, and_false]
  exact mass_eq_zero_of_forall_not _ (fun _ h => h)

/-- A condition that is false on every input history. -/
def never : MC (Σ i, port.X i) := ⟨fun _ => False, fun _ _ _ h => h⟩

/-- Echo the same queries with a condition that never sets the hidden bit. -/
noncomputable def neverSamples :=
  PDG.ofAutomaton port echo (ProbDist.single ()) (fun _ => never)

/-- A false condition retains the full visible mass of the actual adaptive interaction. -/
example : (PDG.behavior neverSamples.1 neverSamples.2) (unsetMBOs interaction) = 1 := by
  rw [PDG.behavior_unsetMBOs, neverSamples, PDG.ofAutomaton, ProbDist.map_val, mass_fTransform]
  apply (ProbDist.single ()).mass_eq_one_of_support
  intro s _
  cases s
  exact ⟨System.replies_tr 2, Or.inr (fun h => h)⟩

#print axioms PDG.behavior_unsetMBOs
#print axioms PDG.conditionallyEquivalent_behavior
#print axioms TypedGame.ofAutomaton_mass_unsetMBOs

end Tests.DiscreteGameUnset
