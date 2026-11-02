module

public import RandomSystems.Typed.Game
public import RandomSystems.Typed.Distinguisher

/-!
# Typed joint solvers

`TypedSolver A` abbreviates `Domain.SolverBehavior` on interface `A`: one compatible
stopping distinguisher supplies both decision and winning evaluations. `decision` projects
the decision view; `TypedSolver.winProbability` evaluates the winning view on a typed game.

`TypedSolver.absorb` connects the solver to a converter. `decision_absorb` and
`winProbability_absorb` show that both evaluations describe the same attached interaction.
-/

@[expose] public section

namespace SystemAlgebra

/-- The joint solver behavior on `A`: decision probabilities on systems and
winning probabilities on games, realized by the same compatible stopping distinguisher. -/
abbrev TypedSolver
    -- `A` fixes the ports, alphabets and domain on which the solver interacts.
    (A : Interface) := Domain.SolverBehavior (Y := A.Y) A.domain A.bound A.length_le

namespace TypedSolver

/-- The decision view of joint solver `s`: the probability of outputting `true` on each
system of interface `A`. -/
abbrev decision {A : Interface} (s : TypedSolver A) : TypedDistinguisher A :=
  Domain.SolverBehavior.decision s

/-- Run solver `s` around `α`: `(sα)(R) = s(α • R)` for decisions,
and `(sα)(G) = s(α.attachGame G)` for winning. -/
noncomputable def absorb
    -- `s` observes the outside interface `A`; `α` connects it to the inside interface `B`.
    {A B : Interface} (s : TypedSolver A) (α : TypedConverter A B) : TypedSolver B :=
  Domain.SolverBehavior.absorb s B.nonempty_prefix A.nonempty_prefix α

/-- Evaluate the winning view of joint solver `s` on game `G`. -/
noncomputable def winProbability
    -- `G` is played on interface `A`; its MBO is hidden from `s` and used only to score winning.
    {A : Interface} (s : TypedSolver A) (G : TypedGame A) : ℝ :=
  s.1.2 ⟨G.1.1, G.1.2, G.2⟩

/-- One compatible distinguisher realizes both views of the joint solver. -/
lemma exists_realization
    -- `s` evaluates systems and games on interface `A` through the same interaction.
    {A : Interface} (s : TypedSolver A) :
    ∃ P : A.inputDomain.Distinguisher,
      (∀ R : TypedSystem A, s.decision.1 R = P.probability R.1) ∧
      ∀ G : TypedGame A, s.winProbability G = P.winProbability G.1.1 := by
  obtain ⟨P, hP, hW⟩ := s.2
  exact ⟨P, hP, fun G => hW ⟨G.1.1, G.1.2, G.2⟩⟩

/-- Taking the decision view after absorption gives `TypedDistinguisher.absorb s.decision α`. -/
lemma decision_absorb
    -- `s` observes outside `A`; `α` connects it to inside `B`.
    {A B : Interface} (s : TypedSolver A) (α : TypedConverter A B) :
    (absorb s α).decision = TypedDistinguisher.absorb s.decision α :=
  Domain.SolverBehavior.decision_absorb s B.nonempty_prefix A.nonempty_prefix α

/-- The absorbed solver wins `G` exactly as the original solver wins the attached game. -/
lemma winProbability_absorb
    -- `s` observes outside `A`; `α` and game `G` supply its inside interaction on `B`.
    {A B : Interface} (s : TypedSolver A) (α : TypedConverter A B) (G : TypedGame B) :
    winProbability (absorb s α) G = winProbability s (α.attachGame G) := rfl

end TypedSolver

end SystemAlgebra
