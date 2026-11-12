module

public import RandomSystems.Cumulative.Presentation
public import RandomSystems.System.Memoryless

/-! Explicit presentations recover a bounded fair source; deterministic tables restrict at zero. -/

@[expose] public section

namespace Tests.ConditionalTableRestriction

open SystemAlgebra Probability Probability.Distribution

/-- A two-query source returns an independent fair Boolean at every trigger. -/
noncomputable def fairSystem : RandomSystem Unit Bool (cutDomain (fun _ _ => True) 2) :=
  RandomSystem.memoryless _ (fun _ => 𝒰[Bool])

/-- The explicit conditional-table presentation of the two-query fair source. -/
noncomputable def fairPresentation :
    ProbDist {s : System Unit Bool // IsDDS s ∧ HasDomain (cutDomain (fun _ _ => True) 2) s} :=
  fairSystem.2.isSubprobabilistic.presentation
    (fun _ hh => fairSystem.mass_eq_zero_of_bound_lt hh) _
    (fun g hg => ⟨(realization g).2, fairSystem.hasDomain_realization hg⟩)

/-- The named sampler has the cumulative behavior of the existing bounded source. -/
lemma fairPresentation_behavior :
    PDS.behavior fairPresentation.1 fairPresentation.2 = fairSystem := by
  apply RandomSystem.ext
  intro h
  exact fairSystem.2.isSubprobabilistic.presentation_mass _ _ _ h

/-- The old bounded presentation endpoint remains available at its original signature. -/
example : ∃ (P : PDS Unit Bool (cutDomain (fun _ _ => True) 2)) (hP : P.isProbDist),
    PDS.behavior P hP = fairSystem := fairSystem.exists_presentation

/-- This concrete choice table returns true at every node before horizon two. -/
def trueTable : Presentation.Node Unit Bool 2 → Option Bool := fun _ => some true

/-- A zero-horizon cut equals realization of the empty restriction of the same table. -/
lemma zero_cut :
    cutSystem (realization (Presentation.choiceAt trueTable)).1 0 =
      (realization (Presentation.choiceAt
        (trueTable ∘ Presentation.nodeInclusion (Nat.zero_le 2)))).1 :=
  Presentation.cutSystem_realization_choiceAt _ _

/-- Retaining the first query realizes precisely that prefix of the same table. -/
lemma one_cut :
    cutSystem (realization (Presentation.choiceAt trueTable)).1 1 =
      (realization (Presentation.choiceAt
        (trueTable ∘ Presentation.nodeInclusion (Nat.le_succ 1)))).1 :=
  Presentation.cutSystem_realization_choiceAt _ _

#print axioms SystemAlgebra.IsSubprobabilistic.presentation_mass
#print axioms SystemAlgebra.IsSubprobabilistic.presentation_possible
#print axioms SystemAlgebra.IsSubprobabilistic.replyChoice_congr
#print axioms SystemAlgebra.Presentation.realization_choiceAt_finite
#print axioms SystemAlgebra.Presentation.cutSystem_realization_choiceAt
#print axioms SystemAlgebra.IsRandomSystem.choiceLaw_cutMass
#print axioms fairPresentation_behavior
#print axioms zero_cut
#print axioms one_cut

end Tests.ConditionalTableRestriction
