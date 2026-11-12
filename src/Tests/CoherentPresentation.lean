module

public import RandomSystems.Cumulative.Presentation.Sequence
public import RandomSystems.System.Source

/-! Coherent presentations cover unlimited fresh replies, zero horizons and empty reply types. -/

@[expose] public section

namespace Tests.CoherentPresentation

open SystemAlgebra Probability Probability.Distribution

/-- The unlimited fair source is the behavior of one exactly coherent normalized presentation. -/
lemma fair_source : ∃ P : PDSSequence Unit Bool (fun _ _ => True),
    P.behavior = sourceMass (𝒰[Bool]) :=
  (sourceMass_isRandomSystem (A := Unit) (𝒰[Bool])).exists_pdsSequence

/-- Restricting the one-query fair table gives its zero-query presentation law. -/
lemma fair_zero_cut :
    let hp := sourceMass_isRandomSystem (A := Unit) (𝒰[Bool])
    (hp.presentationLevel 1).map (PDS.cutSample _ (Nat.zero_le 1)) = hp.presentationLevel 0 :=
  (sourceMass_isRandomSystem (A := Unit) (𝒰[Bool])).presentationLevel_map_cutSample _

/-- An empty reply alphabet supports the domain admitting no queries. -/
lemma empty_reply : ∃ P : PDSSequence Unit Empty (fun _ _ => False),
    P.behavior = fun _ => 1 := by
  have hp : IsRandomSystem (fun (_ : List (Unit × Empty)) _ => False) (fun _ => 1) := by
    refine ⟨rfl, fun _ => zero_le_one, fun h x => ⟨0, ?_, ?_⟩⟩
    · intro y
      exact Empty.elim y
    · norm_num [Distribution.weight]
  exact hp.exists_pdsSequence

#print axioms SystemAlgebra.IsRandomSystem.presentationLevel_map_cutSample
#print axioms SystemAlgebra.IsRandomSystem.presentationLevel_behavior
#print axioms SystemAlgebra.IsRandomSystem.exists_pdsSequence
#print axioms fair_source
#print axioms fair_zero_cut
#print axioms empty_reply

end Tests.CoherentPresentation
