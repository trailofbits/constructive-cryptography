module

public import ConstructiveCryptography.Game.Submission
public import ConstructiveCryptography.Instances.Game
public import RandomSystems.Typed.Submission

/-!
# Submission games on interfaces

`Interface.submissionGame` instantiates the abstract submission contracts with the typed
one-query game. Its order and union laws are the corresponding laws of one transcript measure.
-/

@[expose] public section

namespace SystemAlgebra.Interface

open ConstructiveCryptography

/-- Test successful submissions in `p ⊆ X` using the existing typed game and admitted solvers. -/
noncomputable def submissionGame (X : Type) [Fintype X] :
    SubmissionGame TypedGame ℝ X (submission X) where
  game := TypedGame.submission
  mono := by
    rintro _ ⟨s, rfl⟩
    exact s.submission_mono
  union_le := by
    rintro _ ⟨s, rfl⟩ p q
    exact s.submission_union_le p q

end SystemAlgebra.Interface
