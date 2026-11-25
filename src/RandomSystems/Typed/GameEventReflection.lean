module

public import RandomSystems.Game.EventReflection
public import RandomSystems.Typed.Solver

/-!
# Event reflection under typed attachment

A compatible randomized caller `P` gives one joint solver, `TypedSolver.ofDistinguisher P`.
`probability_attach_le_winProbability_absorb` turns its completed-interaction contract into
`Pr[success on α • G.visible] ≤ Win(s.absorb α, G)`.
The same caller supplies decisions and winning, including its final oracle calls.
-/

@[expose] public section

namespace SystemAlgebra
namespace TypedSolver

/-- Solver `s` has one realization whose accepting completed interactions with `α,G`
set the inside MBO. Both decision and winning views must be those of this same caller. -/
def ReflectsMBO
    -- `s` interacts on `A`; `α` connects it to the game `G` on `B`.
    {A B : Interface} (s : TypedSolver A) (α : TypedConverter A B) (G : TypedGame B) : Prop :=
  ∃ P : A.inputDomain.Distinguisher,
    (∀ R : TypedSystem A, s.decision.1 R = P.probability R.1) ∧
    (∀ H : TypedGame A, s.winProbability H = P.winProbability H.1.1) ∧
    P.ReflectsMBO α G.1.1

/-- A caller's completed-interaction contract supplies the contract of its joint solver. -/
lemma ofDistinguisher_reflectsMBO
    {A B : Interface} (P : A.inputDomain.Distinguisher)
    (α : TypedConverter A B) (G : TypedGame B) (hreflect : P.ReflectsMBO α G.1.1) :
    (ofDistinguisher P).ReflectsMBO α G :=
  ⟨P, fun _ => rfl, fun _ => rfl, hreflect⟩

/-- Success on the attached visible system is bounded by the absorbed solver's winning
probability. The reduction obligation is success implying the inside MBO at completion. -/
theorem probability_attach_le_winProbability_absorb
    -- `s` observes outside `A`; `α` connects it to game `G` on inside `B`.
    {A B : Interface} (s : TypedSolver A) (α : TypedConverter A B) (G : TypedGame B)
    (hreflect : s.ReflectsMBO α G) :
    s.decision.1 (α • G.visible) ≤ (s.absorb α).winProbability G := by
  obtain ⟨P, hdecision, hwin, hP⟩ := hreflect
  -- Use one caller for both views, then transport winning through attachment.
  rw [winProbability_absorb, hdecision, hwin]
  exact α.probability_attach_le_winProbability B.nonempty_prefix A.nonempty_prefix
    G.1.1 G.1.2 G.2 P hP

end TypedSolver
end SystemAlgebra
