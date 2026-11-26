module

public import RandomSystems.Typed.SubmissionMap
public import ConstructiveCryptography.Instances.SubmissionGame

/-! # Submission decoding, including empty and noninjective maps -/

@[expose] public section

open SystemAlgebra ConstructiveCryptography CategoryTheory

namespace Tests.SubmissionMap

/-- Boolean negation turns success at `true` into success at `false`. -/
lemma negation :
    (TypedConverter.submissionMap Bool.not).attachGame (TypedGame.submission {true}) =
      TypedGame.submission {false} := by
  rw [TypedConverter.submissionMap_attachGame]
  congr 1
  ext b
  cases b
  · exact Iff.intro (fun _ => rfl) (fun _ => rfl)
  · exact Iff.intro (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)

/-- A many-to-one decoder still retains the exact successful event. -/
example :
    (TypedConverter.submissionMap (fun _ : Bool => ())).attachGame
      (TypedGame.submission (Set.univ : Set Unit)) =
        TypedGame.submission (Set.univ : Set Bool) := by
  simpa only [Set.preimage_univ] using
    TypedConverter.submissionMap_attachGame (fun _ : Bool => ()) Set.univ

/-- No fallback submission is needed when both value carriers are empty. -/
example :
    (TypedConverter.submissionMap (id : Empty → Empty)).attachGame
      (TypedGame.submission (Set.univ : Set Empty)) =
        TypedGame.submission (Set.univ : Set Empty) := by
  simpa only [Set.preimage_univ] using
    TypedConverter.submissionMap_attachGame (id : Empty → Empty) Set.univ

/-- Negation as an arrow of the interface instance of the abstract game action. -/
noncomputable abbrev decoder : Interface.submission Bool ⟶ Interface.submission Bool :=
  TypedConverter.submissionMap Bool.not

/-- The abstract reduction uses the chosen admitted-winner closure, with identity loss. -/
example (q : Set Bool) (hq : q ⊆ {false}) (ε : ℝ)
    (closed : ∀ W ∈ Games.winners (Interface.submission Bool),
      Games.absorb W decoder ∈
        Games.winners (Interface.submission Bool))
    (hardness : ∀ W ∈ Games.winners (Interface.submission Bool),
      W (TypedGame.submission {true}) ≤ ε)
    (W : TypedGame (Interface.submission Bool) → ℝ)
    (admitted : W ∈ Games.winners (Interface.submission Bool)) :
    W (TypedGame.submission q) ≤ ε := by
  apply Games.win_le_of_reduction
    (fun V => Games.absorb V decoder)
    id monotone_id closed ?_ hardness admitted
  intro V hV
  change V (TypedGame.submission q) ≤
    V ((TypedConverter.submissionMap Bool.not).attachGame (TypedGame.submission {true}))
  exact ((Interface.submissionGame Bool).mono V hV hq).trans
    (le_of_eq (congrArg V negation.symm))

#print axioms TypedGame.submission_eq_ofFunction
#print axioms TypedConverter.submissionMap_attachGame

end Tests.SubmissionMap
